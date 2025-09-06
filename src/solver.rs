use crate::collapse::{Collapse, CollapseOut, ExprContext};
use crate::core_ops::Eq;
use crate::exp::*;
use crate::full_theory::{FullTheory, TopLevelCollapse};
use crate::intern::*;
use crate::junction::*;
use crate::recorder::Recorder;
use crate::theory::{TheoryArg, TheoryWrapper};
use crate::tseitin::SatTheoryArgT;
use crate::util::{DefaultHashBuilder, Either};
use crate::Symbol;
use hashbrown::HashMap;
use internal_iterator::{InternalIterator, IteratorExt};
use log::{debug, trace};
use no_std_compat::prelude::v1::*;
use perfect_derive::perfect_derive;
use platsat::theory::ClauseRef;
use platsat::{lbool, Callbacks, Lit, SolverInterface, SolverOpts};
use std::fmt::Debug;

/// [`Solver`] methods that return [`BoolExp`]s often have an `approx` variant that take an
/// [`Approx`] when allows for optimizations when the result doesn't have to match exactly
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum Approx {
    /// The returned boolean exactly matches
    Exact,
    /// If `approx` is `Approx(false)` the returned boolean is assigned false whenever the expected result is assigned to false,
    /// and when the expected result is assigned to true the returned boolean is either also true or unconstrained
    ///
    /// If `approx` is `Approx(true)` the returned boolean is assigned true whenever the expected result is assigned to true,
    /// and when the expected result is assigned to false the returned boolean is either false true or unconstrained
    Approx(bool),
}

#[derive(Default)]
pub(crate) struct NoCb;
impl Callbacks for NoCb {}
type BatSolver = platsat::Solver<NoCb>;

/// The main solver structure including the sat solver and egraph.
///
/// It allows constructing and asserting expressions [`Exp`] within the solver
pub struct Solver<Euf: FullTheory<R>, R> {
    pub(crate) th: TheoryWrapper<Euf, R>,
    pub(crate) sat: BatSolver,
}

impl<Th: FullTheory<R> + Default, R: Recorder> Default for Solver<Th, R> {
    fn default() -> Self {
        let mut res = Solver {
            th: Default::default(),
            sat: Default::default(),
        };
        res.open(
            |th: &mut Th, acts| {
                th.init(acts);
            },
            (),
        );
        res
    }
}

pub type BLit = Lit;

#[derive(Debug, Copy, Clone)]
/// Result of calling [`Solver::check_sat_assuming`]
pub enum SolveResult {
    Sat,
    Unsat,
    Unknown,
}

impl SolveResult {
    pub fn valid_when_expecting(self, oth: SolveResult) -> bool {
        matches!(
            (self, oth),
            (SolveResult::Sat, SolveResult::Sat)
                | (SolveResult::Unsat, SolveResult::Unsat)
                | (_, SolveResult::Unknown)
        )
    }

    pub fn as_lower_str(self) -> &'static str {
        match self {
            SolveResult::Sat => "sat",
            SolveResult::Unsat => "unsat",
            SolveResult::Unknown => "unknown",
        }
    }
}

pub trait SolverCollapse<T: CollapseOut, M> {
    /// Similar to [`collapse`](Collapse::collapse), but includes the `ctx` for passing additional
    /// assumptions that may lead to optimizations.
    ///
    /// To assert two expressions are equal it is preferable to use [`assert_eq`](Solver::assert_eq)
    /// which guarantees the expressions will be asserted as equal, as opposed to calling this
    /// method with [`ExprContext::AssertEq`] which this allows the assertion to be made as an
    /// optimization
    fn collapse_in_ctx(&mut self, t: T, ctx: ExprContext<T::Out>) -> T::Out;

    /// Collapse a type representing an expression into a copiable handle that can be used later by
    /// the solver.
    ///
    /// Collapsing the result of a previous call to collapse will canonize the result
    fn collapse(&mut self, t: T) -> T::Out {
        self.collapse_in_ctx(t, ExprContext::Exact)
    }
}

impl<R: Recorder, Th: FullTheory<R>, T: CollapseOut, M> SolverCollapse<T, M> for Solver<Th, R>
where
    Th: TopLevelCollapse<T, M, R>,
{
    fn collapse_in_ctx(&mut self, t: T, ctx: ExprContext<T::Out>) -> T::Out {
        let p = Collapse::<T, TheoryArg<Th::LevelMarker, R>, M>::placeholder(&*self.th, &t);
        self.open(|th, acts| th.collapse(t, acts, ctx), p)
    }
}

impl<'a, 'b, R, Th: FullTheory<R>, T: CollapseOut, M> SolverCollapse<T, M>
    for (&'a mut Th, &'a mut TheoryArg<'b, Th::LevelMarker, R>)
where
    Th: TopLevelCollapse<T, M, R>,
{
    fn collapse_in_ctx(&mut self, t: T, ctx: ExprContext<T::Out>) -> T::Out {
        self.0.collapse(t, self.1, ctx)
    }
}

#[derive(Default, Clone)]
pub struct SolverWithBound<S, B> {
    pub solver: S,
    pub bound: B,
}

impl<T: CollapseOut, M, S: SolverCollapse<T, M>, B> SolverCollapse<T, M> for SolverWithBound<S, B> {
    fn collapse_in_ctx(&mut self, t: T, ctx: ExprContext<T::Out>) -> T::Out {
        self.solver.collapse_in_ctx(t, ctx)
    }
}

pub trait ReuseMem<T> {
    fn reuse_mem(&mut self) -> T;
}

impl<Th: FullTheory<R>, R, const B: bool> ReuseMem<Junction<B>> for Solver<Th, R> {
    fn reuse_mem(&mut self) -> Junction<B> {
        self.th.new_junction()
    }
}

impl<T, S: ReuseMem<T>, B> ReuseMem<T> for SolverWithBound<S, B> {
    fn reuse_mem(&mut self) -> T {
        self.solver.reuse_mem()
    }
}

impl<Th: FullTheory<R>, R: Recorder> Solver<Th, R> {
    pub fn is_ok(&self) -> bool {
        self.sat.is_ok()
    }

    /// Generate a fresh boolean variable
    pub fn fresh_bool(&mut self) -> BoolExp {
        BoolExp::unknown(Lit::new(self.sat.new_var_default(), true))
    }

    pub(crate) fn open<U>(
        &mut self,
        f: impl FnOnce(&mut Th, &mut TheoryArg<Th::LevelMarker, R>) -> U,
        default: U,
    ) -> U {
        let mut ret = default;
        self.sat.with_theory_arg(|acts| {
            let (euf, mut acts) = self.th.open(acts);
            ret = f(euf, &mut acts)
        });
        ret
    }

    pub fn assert_eq<M, MEq, T>(&mut self, t: T, target: T::Out) -> Result<(), (Sort, Sort)>
    where
        T: CollapseOut,
        Th: TopLevelCollapse<T, M, R> + TopLevelCollapse<Eq<T::Out>, MEq, R>,
    {
        let p: T::Out = Collapse::<T, TheoryArg<Th::LevelMarker, R>, M>::placeholder(&*self.th, &t);
        if p.sort() != target.sort() {
            return Err((p.sort(), target.sort()));
        }
        self.open(
            |euf, acts| {
                let res = euf.collapse(t, acts, ExprContext::AssertEq(target));
                if res != target {
                    let b = euf.collapse(
                        Eq::new_unchecked(res, target),
                        acts,
                        ExprContext::AssertEq(BoolExp::TRUE),
                    );
                    acts.assert(b);
                }
            },
            (),
        );
        Ok(())
    }

    pub fn intern(&self) -> &InternInfo {
        self.th.intern()
    }

    pub fn intern_mut(&mut self) -> &mut InternInfo {
        self.th.intern_mut()
    }

    /// Assert that `b` is true
    pub fn assert(&mut self, b: BoolExp) {
        if !self.is_ok() {
            return;
        }
        debug!("assert {b}");
        match SolverCollapse::collapse(self, b).to_lit() {
            Err(true) => {}
            Ok(l) => {
                self.sat.add_clause_unchecked([l]);
            }
            Err(false) => {
                self.sat.add_clause_unchecked([]);
            }
        }
    }

    /// Check if the current assertions are satisfiable
    pub fn check_sat(&mut self) -> SolveResult {
        self.check_sat_assuming(&Default::default())
    }

    /// Check if the current assertions combined with the assertions in `c` are satisfiable
    /// Leave the solver in a state representing the model
    pub fn check_sat_assuming_preserving_trail(&mut self, c: &Conjunction) -> SolveResult {
        let res = match c.absorbing {
            true => lbool::FALSE,
            false => self
                .sat
                .solve_limited_preserving_trail_th(&mut self.th, &c.lits),
        };
        if res == lbool::FALSE {
            debug!("check-sat {c:?} returned unsat",);
            SolveResult::Unsat
        } else if res == lbool::TRUE {
            debug!(
                "check-sat {c:?} returned sat, model:\n{:?}",
                self.sat.raw_model()
            );
            SolveResult::Sat
        } else {
            SolveResult::Unknown
        }
    }

    /// Check if the current assertions combined with the assertions in `c` are satisfiable
    pub fn check_sat_assuming(&mut self, c: &Conjunction) -> SolveResult {
        let res = self.check_sat_assuming_preserving_trail(c);
        self.pop_model();
        res
    }

    pub(crate) fn analyze_final_conflict(&mut self) {
        self.sat.analyze_final_conflict(&mut self.th)
    }

    pub(crate) fn clauses(&self) -> impl DoubleEndedIterator<Item = ClauseRef> + '_ {
        self.sat.clauses()
    }

    /// Restores the state after calling `raw_check_sat_assuming`
    pub fn pop_model(&mut self) {
        self.sat.pop_model(&mut self.th);
    }

    pub fn clear(&mut self) {
        self.sat.reset();
        self.th.clear();
        self.open(|th, acts| th.init(acts), ());
    }

    pub fn simplify(&mut self) {
        self.sat.simplify_th(&mut self.th);
    }

    /// Like [`check_sat_assuming`](Solver::check_sat_assuming) but takes in an
    /// [`UnsatCoreConjunction`] which associates its elements values and returns an iterator
    /// over the values associated with the elements of the unsat core if the result is unsat
    pub fn check_sat_assuming_for_core<'a, T>(
        &'a mut self,
        c: &'a UnsatCoreConjunction<T>,
    ) -> Option<impl InternalIterator<Item = &'a T>> {
        let (conj, info) = c.parts();
        match self.check_sat_assuming(conj) {
            SolveResult::Unsat => Some(info.core(self.last_unsat_core())),
            _ => None,
        }
    }

    /// Returns the boolean sort
    pub fn bool_sort(&self) -> Sort {
        BOOL_SORT
    }

    // /// Simplifies `t` based on the current assertions
    // pub fn canonize<T: ExpLike<Euf>>(&self, t: T) -> T {
    //     if !self.is_ok() {
    //         return t;
    //     }
    //     let res = t.canonize(self);
    //     debug!(
    //         "{} canonized to {}",
    //         t.with_intern(self.intern()),
    //         res.with_intern(self.intern())
    //     );
    //     res
    // }

    pub(crate) fn last_unsat_core(&mut self) -> impl InternalIterator<Item = Lit> + '_ {
        self.sat.unsat_core(&mut self.th)
    }

    pub fn function_info<'a>(&'a mut self) -> (impl Fn(Symbol) -> Th::FunctionInfo<'a>, &'a Self) {
        self.th.init_function_info();
        (|f| self.th.get_function_info(f), self)
    }

    pub fn theory(&self) -> &Th {
        &self.th
    }

    pub fn sat_options(&self) -> SolverOpts {
        self.sat.options()
    }

    pub fn set_sat_options(&mut self, options: SolverOpts) -> core::result::Result<(), ()> {
        self.sat.set_options(options)
    }

    pub fn interpolant(
        &mut self,
        pre_solve_level: LevelMarker<Th::LevelMarker>,
        assumptions: &mut Conjunction,
        a: R::BoolBufMarker,
        b: R::BoolBufMarker,
    ) -> Option<R::Interpolant<'_>> {
        R::interpolant(self, pre_solve_level, assumptions, a, b)
    }
}

/// Marker of the state of a [`Solver`] which can be created by [`Solver::create_level`] and later
/// used by [`Solver::pop_to_level`]
#[derive(Clone)]
pub struct LevelMarker<M> {
    sat: platsat::core::CheckPoint,
    euf: Option<M>,
}

impl<Euf: FullTheory<R>, R: Recorder> Solver<Euf, R> {
    /// Creates a [`LevelMarker`] which can later be used with [`pop_to_level`](Self::pop_to_level)
    /// to reset the solver to the state it has now
    ///
    /// This also calls [`simplify`](Self::simplify) to simplify the state of the solver
    pub fn create_level(&mut self) -> LevelMarker<Euf::LevelMarker> {
        self.simplify();
        trace!("Push sat model: {:?}", self.sat.raw_model());
        LevelMarker {
            sat: self.sat.checkpoint(),
            euf: self.is_ok().then(|| self.th.create_level()),
        }
    }

    /// Resets the solver to the state it had when `marker` was created by [`create_level`](Self::create_level)
    pub fn pop_to_level(&mut self, marker: LevelMarker<Euf::LevelMarker>) {
        self.th.restore_trail_len(marker.sat.trail_len());
        self.sat.restore_checkpoint(marker.sat);
        trace!("Pop sat model: {:?}", self.sat.raw_model());
        if let Some(x) = marker.euf {
            self.th.pop_to_level(x, true);
        }
    }
}

#[perfect_derive(Default)]
pub(crate) struct UnsatCoreInfo<T> {
    false_by: Option<T>,
    data: HashMap<Lit, T, DefaultHashBuilder>,
}

impl<T> UnsatCoreInfo<T> {
    fn add(&mut self, bool_exp: BoolExp, t: T) {
        match bool_exp.to_lit() {
            Err(false) => {
                if self.false_by.is_none() {
                    self.false_by = Some(t)
                }
            }
            Err(true) => {}
            Ok(l) => {
                if self.false_by.is_none() {
                    self.data.insert(!l, t);
                }
            }
        }
    }

    pub(crate) fn core(
        &self,
        lits: impl InternalIterator<Item = Lit>,
    ) -> impl InternalIterator<Item = &T> {
        match &self.false_by {
            Some(x) => Either::Right(core::iter::once(x).into_internal()),
            None => Either::Left(lits.filter_map(|x| self.data.get(&x))),
        }
    }
}

#[perfect_derive(Default)]
pub struct UnsatCoreConjunction<T> {
    pub(crate) conj: Conjunction,
    info: UnsatCoreInfo<T>,
}

impl<T> FromIterator<(BoolExp, T)> for UnsatCoreConjunction<T> {
    fn from_iter<I: IntoIterator<Item = (BoolExp, T)>>(iter: I) -> Self {
        let mut info = UnsatCoreInfo::default();
        let conj = iter
            .into_iter()
            .map(|(b, t)| {
                info.add(b, t);
                b
            })
            .collect();
        UnsatCoreConjunction { info, conj }
    }
}

impl<T> Extend<(BoolExp, T)> for UnsatCoreConjunction<T> {
    fn extend<I: IntoIterator<Item = (BoolExp, T)>>(&mut self, iter: I) {
        let conj = iter.into_iter().map(|(b, t)| {
            self.info.add(b, t);
            b
        });
        self.conj.extend(conj);
    }
}

impl<T> UnsatCoreConjunction<T> {
    pub(crate) fn parts(&self) -> (&Conjunction, &UnsatCoreInfo<T>) {
        (&self.conj, &self.info)
    }

    pub(crate) fn push(&self) -> u32 {
        if self.conj.absorbing {
            u32::MAX
        } else {
            self.conj.lits.len() as u32
        }
    }

    pub(crate) fn pop_to(&mut self, push_info: u32) {
        if push_info != u32::MAX {
            self.conj.absorbing = false;
            self.info.false_by = None;
            for l in self.conj.lits.drain(push_info as usize..) {
                self.info.data.remove(&!l);
            }
        }
    }
}
