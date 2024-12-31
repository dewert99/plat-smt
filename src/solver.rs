use crate::euf::EufT;
use crate::exp::*;
use crate::intern::*;
use crate::junction::*;
use crate::theory::{TheoryArg, TheoryWrapper};
use crate::util::{display_debug, DefaultHashBuilder, Either};
use crate::Symbol;
use core::hash::Hash;
use core::ops::Deref;
use hashbrown::HashMap;
use internal_iterator::{InternalIterator, IteratorExt};
use log::{debug, trace};
use no_std_compat::prelude::v1::*;
use perfect_derive::perfect_derive;
use platsat::{lbool, Callbacks, Lit, SolverInterface, SolverOpts};
use std::fmt::{Debug, Formatter};

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
struct NoCb;
impl Callbacks for NoCb {}
type BatSolver = platsat::Solver<NoCb>;

/// The main solver structure including the sat solver and egraph.
///
/// It allows constructing and asserting expressions [`Exp`] within the solver
#[perfect_derive(Default)]
pub struct Solver<Euf: EufT> {
    euf: TheoryWrapper<Euf>,
    sat: BatSolver,
}

impl Debug for BoolExp {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self.to_lit() {
            Err(c) => Debug::fmt(&c, f),
            Ok(l) => {
                if l.sign() {
                    write!(f, "(as b{:?} Bool)", l.var())
                } else {
                    write!(f, "(as (not b{:?}) Bool)", l.var())
                }
            }
        }
    }
}

display_debug!(BoolExp);

impl<UExp: Debug> Debug for Exp<UExp> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Exp::Bool(b) => Debug::fmt(&b, f),
            Exp::Other(u) => Debug::fmt(&u, f),
        }
    }
}

impl<UExp: DisplayInterned> DisplayInterned for Exp<UExp> {
    fn fmt(&self, i: &InternInfo, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Exp::Bool(b) => DisplayInterned::fmt(b, i, f),
            Exp::Other(u) => DisplayInterned::fmt(u, i, f),
        }
    }
}

pub trait ExpLike<Euf: EufT>:
    Into<Exp<Euf::UExp>> + Copy + Debug + DisplayInterned + HasSort + Eq + Hash + Ord
{
    fn canonize(self, solver: &Solver<Euf>) -> Self;
}

impl<Euf: EufT> ExpLike<Euf> for BoolExp {
    fn canonize(self, solver: &Solver<Euf>) -> Self {
        match self.to_lit() {
            Ok(x) => {
                let val = solver.sat.raw_value_lit(x);
                if val == lbool::TRUE {
                    BoolExp::TRUE
                } else if val == lbool::FALSE {
                    BoolExp::FALSE
                } else {
                    self
                }
            }
            _ => self,
        }
    }
}

impl<Euf: EufT> ExpLike<Euf> for Exp<Euf::UExp> {
    fn canonize(self, solver: &Solver<Euf>) -> Self {
        match self {
            Exp::Bool(b) => b.canonize(solver).into(),
            Exp::Other(u) => u.canonize(solver).into(),
        }
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

impl<Euf: EufT> Solver<Euf> {
    pub fn is_ok(&self) -> bool {
        self.sat.is_ok()
    }

    /// Generate a fresh boolean variable
    pub fn fresh_bool(&mut self) -> BoolExp {
        BoolExp::unknown(Lit::new(self.sat.new_var_default(), true))
    }

    fn open<U>(
        &mut self,
        f: impl FnOnce(&mut Euf, &mut TheoryArg<Euf::LevelMarker>) -> U,
        default: U,
    ) -> U {
        let mut ret = default;
        self.sat.with_theory_arg(|acts| {
            let (euf, mut acts) = self.euf.open(acts);
            ret = f(euf, &mut acts)
        });
        ret
    }

    /// Collapse a [`Conjunction`] or [`Disjunction`] into a [`BoolExp`]
    ///
    /// To reuse memory you can pass mutable reference instead of an owned value
    /// Doing this will leave `j` in an unspecified state, so it should be
    /// [`clear`](Junction::clear)ed before it is used again
    pub fn collapse_bool<const IS_AND: bool>(&mut self, j: Junction<IS_AND>) -> BoolExp {
        self.collapse_bool_approx(j, Approx::Exact)
    }

    /// Similar to [`collapse_bool`](Self::collapse_bool), but returns a boolean that approximates `j`
    ///
    /// If `approx` is `None` the returned boolean exactly matches `j` (same behaviour as  [`collapse_bool`](Self::collapse_bool))
    ///
    /// If `approx` is `Some(false)` the returned boolean is assigned false whenever `j` is assigned to false,
    /// and when `j` is assigned to true the returned boolean is either also true or unconstrained
    ///
    /// If `approx` is `Some(true)` the returned boolean is assigned true whenever `j` is assigned to true,
    /// and when `j` is assigned to false the returned boolean is either also false or unconstrained
    ///
    /// ## Example
    /// ```
    /// use plat_smt::Approx;
    /// use plat_smt::euf::Euf;
    /// use plat_smt::Solver;
    /// use plat_smt::SolveResult;
    /// let mut s = Solver::<Euf>::default();
    /// let a = s.fresh_bool();
    /// let b = s.fresh_bool();
    /// let ab = s.collapse_bool_approx(a | b, Approx::Approx(false));
    /// s.assert(!a);
    /// s.assert(!b);
    /// s.assert(ab);
    /// assert!(matches!(s.check_sat(), SolveResult::Unsat))
    /// ```
    pub fn collapse_bool_approx<const IS_AND: bool>(
        &mut self,
        j: Junction<IS_AND>,
        approx: Approx,
    ) -> BoolExp {
        self.open(
            |_, acts| acts.collapse_bool_approx(j, approx),
            BoolExp::TRUE,
        )
    }

    pub fn assert_junction_eq<const IS_AND: bool>(&mut self, j: Junction<IS_AND>, target: BoolExp) {
        self.open(|_, acts| acts.assert_junction_eq(j, target), ())
    }

    /// Returns an empty [`Conjunction`] or [`Disjunction`]  which reuses memory from the last call
    /// to [`collapse_bool`](Self::collapse_bool)
    pub fn new_junction<const IS_AND: bool>(&mut self) -> Junction<IS_AND> {
        self.euf.new_junction()
    }

    pub fn xor(&mut self, b1: BoolExp, b2: BoolExp) -> BoolExp {
        self.xor_approx(b1, b2, Approx::Exact)
    }

    pub fn xor_approx(&mut self, b1: BoolExp, b2: BoolExp, approx: Approx) -> BoolExp {
        self.open(|_, acts| acts.xor_approx(b1, b2, approx), BoolExp::TRUE)
    }

    pub fn assert_xor_eq(&mut self, b1: BoolExp, b2: BoolExp, target: BoolExp) {
        self.open(|_, acts| acts.assert_xor_eq(b1, b2, target), ())
    }

    /// Produce a boolean expression representing the equality of the two expressions
    ///
    /// If the two expressions have different sorts returns an error containing both sorts
    pub fn eq(&mut self, exp1: Exp<Euf::UExp>, exp2: Exp<Euf::UExp>) -> BoolExp {
        self.eq_approx(exp1, exp2, Approx::Exact)
    }

    pub fn eq_approx(
        &mut self,
        exp1: Exp<Euf::UExp>,
        exp2: Exp<Euf::UExp>,
        approx: Approx,
    ) -> BoolExp {
        self.open(
            |euf, acts| euf.eq_approx(exp1, exp2, approx, acts),
            BoolExp::TRUE,
        )
    }

    /// Equivalent to `self.`[`assert`](Self::assert)`(self.`[`eq`](Self::eq)`(exp1, exp2)?)` but
    /// more efficient
    pub fn assert_eq(&mut self, exp1: Exp<Euf::UExp>, exp2: Exp<Euf::UExp>) {
        let c1 = self.canonize(exp1);
        let c2 = self.canonize(exp2);
        self.open(|euf, acts| euf.assert_eq(c1, c2, acts), ());
        self.simplify();
    }

    /// Assert that no pair of expressions in `exps` are equal to each other
    ///
    /// Requires all expressions in `exps` have the same sort
    pub fn assert_distinct(&mut self, exps: impl IntoIterator<Item = Exp<Euf::UExp>>) {
        self.open(|euf, acts| euf.assert_distinct(exps.into_iter(), acts), ());
        self.simplify()
    }

    pub fn intern(&self) -> &InternInfo {
        self.euf.intern()
    }

    pub fn intern_mut(&mut self) -> &mut InternInfo {
        self.euf.intern_mut()
    }

    /// Equivalent to `self.`[`assert`](Self::assert_eq)`(self.`[`sorted_fn`](Self::sorted_fn)`(f, children, exp.sort()), exp)`
    /// but more efficient
    pub fn assert_fn_eq(
        &mut self,
        f: Symbol,
        children: impl IntoIterator<Item = Exp<Euf::UExp>>,
        exp: Exp<Euf::UExp>,
    ) -> Result<(), Euf::Unsupported> {
        self.open(
            |euf, acts| euf.assert_fn_eq(f, children.into_iter(), exp, acts),
            Ok(()),
        )?;
        self.simplify();
        Ok(())
    }

    /// Equivalent to `self.`[`assert`](Self::assert)`(self.`[`bool_fn`](Self::bool_fn)`(f, children) ^ negate)`
    /// but more efficient
    pub fn assert_bool_fn(
        &mut self,
        f: Symbol,
        children: impl IntoIterator<Item = Exp<Euf::UExp>>,
        negate: bool,
    ) -> Result<(), Euf::Unsupported> {
        self.assert_fn_eq(f, children, BoolExp::from_bool(!negate).into())
    }

    /// Produce an expression representing that is equivalent to `t` if `i` is true or `e` otherwise
    ///
    /// Requires `t` and `e` have the same sorts
    pub fn ite_approx(
        &mut self,
        i: BoolExp,
        t: Exp<Euf::UExp>,
        e: Exp<Euf::UExp>,
        approx: Approx,
    ) -> Result<Exp<Euf::UExp>, Euf::Unsupported> {
        let i = self.canonize(i);
        self.open(
            |euf, acts| euf.ite_approx(i, t, e, approx, acts),
            Ok(Euf::placeholder_exp_from_sort(t.sort())),
        )
    }

    /// Produce an expression representing that is equivalent to `t` if `i` is true or `e` otherwise
    ///
    /// Requires `t` and `e` have the same sorts
    pub fn ite(
        &mut self,
        i: BoolExp,
        t: Exp<Euf::UExp>,
        e: Exp<Euf::UExp>,
    ) -> Result<Exp<Euf::UExp>, Euf::Unsupported> {
        self.ite_approx(i, t, e, Approx::Exact)
    }

    /// Equivalent to `self.`[`assert_eq`](Self::assert_eq)`(self.`[`ite`](Self::ite)`(i, t, e)?, target)`
    /// but possibly more efficient
    pub fn assert_ite_eq(
        &mut self,
        i: BoolExp,
        t: Exp<Euf::UExp>,
        e: Exp<Euf::UExp>,
        target: Exp<Euf::UExp>,
    ) -> Result<(), Euf::Unsupported> {
        self.open(|euf, acts| euf.assert_ite_eq(i, t, e, target, acts), Ok(()))
    }

    /// Creates a function call expression with a given name and children and return sort
    ///
    /// [`Id`]s for the children can be created with [`id`](Solver::id)
    ///
    /// This method does not check sorts of the children so callers need to ensure that functions
    /// call expressions with the same name but different return sorts do not become congruently
    /// equal (This would cause a panic when it happens)
    pub fn sorted_fn(
        &mut self,
        fn_name: Symbol,
        children: impl IntoIterator<Item = Exp<Euf::UExp>>,
        sort: Sort,
    ) -> Result<Exp<Euf::UExp>, Euf::Unsupported> {
        self.open(
            |euf, acts| euf.sorted_fn(fn_name, children.into_iter(), sort, acts),
            Ok(Euf::placeholder_exp_from_sort(sort)),
        )
    }

    /// Similar to calling [`sorted_fn`](Solver::sorted_fn) with the boolean sort, but returns
    /// a [`BoolExp`] instead of an [`Exp`]
    pub fn bool_fn(
        &mut self,
        fn_name: Symbol,
        children: impl IntoIterator<Item = Exp<Euf::UExp>>,
    ) -> Result<BoolExp, Euf::Unsupported> {
        Ok(self
            .sorted_fn(fn_name, children, BOOL_SORT)?
            .as_bool()
            .unwrap())
    }

    /// Assert that `b` is true
    pub fn assert(&mut self, b: BoolExp) {
        if !self.is_ok() {
            return;
        }
        debug!("assert {b}");
        match self.canonize(b).to_lit() {
            Err(true) => {}
            Ok(l) => {
                self.sat.add_clause_unchecked([l]);
                self.simplify();
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
                .solve_limited_preserving_trail_th(&mut self.euf, &c.lits),
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

    /// Restores the state after calling `raw_check_sat_assuming`
    pub fn pop_model(&mut self) {
        self.sat.pop_model(&mut self.euf);
    }

    pub fn clear(&mut self) {
        self.sat.reset();
        self.euf.clear();
    }

    pub fn simplify(&mut self) {
        self.sat.simplify_th(&mut self.euf);
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

    /// Simplifies `t` based on the current assertions
    pub fn canonize<T: ExpLike<Euf>>(&self, t: T) -> T {
        if !self.is_ok() {
            return t;
        }
        let res = t.canonize(self);
        debug!(
            "{} canonized to {}",
            t.with_intern(self.intern()),
            res.with_intern(self.intern())
        );
        res
    }

    pub(crate) fn last_unsat_core(&mut self) -> impl InternalIterator<Item = Lit> + '_ {
        self.sat.unsat_core(&mut self.euf)
    }

    pub fn function_info<'a>(&'a mut self) -> (impl Fn(Symbol) -> Euf::FunctionInfo<'a>, &'a Self) {
        self.euf.init_function_info();
        (|f| self.euf.get_function_info(f), self)
    }

    pub fn theory(&self) -> &Euf {
        &self.euf
    }

    pub fn sat_options(&self) -> SolverOpts {
        self.sat.options()
    }

    pub fn set_sat_options(&mut self, options: SolverOpts) -> core::result::Result<(), ()> {
        self.sat.set_options(options)
    }
}

#[derive(Clone)]
pub struct LevelMarker<M> {
    sat: platsat::core::CheckPoint,
    euf: Option<M>,
}

impl<Euf: EufT> Solver<Euf> {
    pub fn create_level(&self) -> LevelMarker<Euf::LevelMarker> {
        LevelMarker {
            sat: self.sat.checkpoint(),
            euf: self.is_ok().then(|| self.euf.deref().create_level()),
        }
    }

    pub fn pop_to_level(&mut self, maker: LevelMarker<Euf::LevelMarker>) {
        self.euf.restore_trail_len(maker.sat.trail_len());
        self.sat.restore_checkpoint(maker.sat);
        trace!("Sat model: {:?}", self.sat.raw_model());
        if let Some(x) = maker.euf {
            self.euf.pop_to_level(x, true);
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
    conj: Conjunction,
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
