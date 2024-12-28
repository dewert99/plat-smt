use crate::euf::EufT;
use crate::exp::*;
use crate::intern::*;
use crate::junction::*;
use crate::local_error::LocalError::SortMismatch;
use crate::local_error::{IResult, Result};
use crate::theory::{IncrementalWrapper, TheoryArg};
use crate::util::{display_debug, DefaultHashBuilder, Either};
use crate::Symbol;
use core::cmp::Ordering;
use core::hash::Hash;
use core::ops::Deref;
use hashbrown::HashMap;
use internal_iterator::{InternalIterator, IteratorExt};
use log::{debug, trace};
use no_std_compat::prelude::v1::*;
use perfect_derive::perfect_derive;
use platsat::{lbool, Callbacks, Lit, SolverInterface, SolverOpts, Var};
use std::fmt::{Debug, Formatter};
use std::mem;

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
    euf: IncrementalWrapper<Euf>,
    sat: BatSolver,
    junction_buf: Vec<Lit>,
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
    fn fresh(&mut self) -> Var {
        let fresh = self.sat.new_var_default();
        fresh
    }

    /// Generate a fresh boolean variable
    pub fn fresh_bool(&mut self) -> BoolExp {
        BoolExp::unknown(Lit::new(self.fresh(), true))
    }

    #[inline]
    fn andor_reuse(&mut self, exps: &mut Vec<BLit>, is_and: bool, approx: Approx) -> BoolExp {
        exps.sort_unstable();

        let mut last_lit = Lit::UNDEF;
        let mut j = 0;
        // remove duplicates, true literals, etc.
        for i in 0..exps.len() {
            let lit_i = exps[i];
            let value = self.sat.raw_value_lit(lit_i);
            if (value == lbool::TRUE ^ is_and) || lit_i == !last_lit {
                return BoolExp::from_bool(!is_and);
            } else if !(value ^ is_and == lbool::FALSE) && lit_i != last_lit {
                // not a duplicate
                last_lit = lit_i;
                exps[j] = lit_i;
                j += 1;
            }
        }
        exps.truncate(j);

        if let [exp] = &**exps {
            return BoolExp::unknown(*exp);
        }
        let fresh = self.fresh();
        let res = Lit::new(fresh, true);
        for lit in &mut *exps {
            if approx != Approx::Approx(is_and) {
                self.sat.add_clause_unchecked(
                    [*lit ^ !is_and, Lit::new(fresh, !is_and)].iter().copied(),
                );
            }
            *lit ^= is_and;
        }
        if approx != Approx::Approx(!is_and) {
            exps.push(Lit::new(fresh, is_and));
            self.sat.add_clause_unchecked(exps.iter().copied());
        }
        BoolExp::unknown(res)
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
        mut j: Junction<IS_AND>,
        approx: Approx,
    ) -> BoolExp {
        if !self.is_ok() {
            return BoolExp::TRUE;
        }
        debug!("{j:?} (approx: {approx:?}) was collapsed to ...");
        let res = match j.absorbing {
            true => BoolExp::from_bool(!IS_AND),
            false if j.lits.is_empty() => BoolExp::from_bool(IS_AND),
            false => self.andor_reuse(&mut j.lits, IS_AND, approx),
        };
        self.junction_buf = j.lits;
        debug!("... {res}");
        res
    }

    /// Returns an empty [`Conjunction`] or [`Disjunction`]  which reuses memory from the last call
    /// to [`collapse_bool`](Self::collapse_bool)
    pub fn new_junction<const IS_AND: bool>(&mut self) -> Junction<IS_AND> {
        self.junction_buf.clear();
        Junction {
            absorbing: false,
            lits: mem::take(&mut self.junction_buf),
        }
    }

    pub fn xor(&mut self, b1: BoolExp, b2: BoolExp) -> BoolExp {
        self.xor_approx(b1, b2, Approx::Exact)
    }

    pub fn xor_approx(&mut self, b1: BoolExp, b2: BoolExp, approx: Approx) -> BoolExp {
        if !self.is_ok() {
            return BoolExp::TRUE;
        }
        let b1 = self.canonize(b1);
        let b2 = self.canonize(b2);
        let res = match (b1.to_lit(), b2.to_lit()) {
            (_, Err(b2)) => b1 ^ b2,
            (Err(b1), _) => b2 ^ b1,
            (Ok(l1), Ok(l2)) => {
                let (l1, l2) = match l1.var().cmp(&l2.var()) {
                    Ordering::Less => (l1, l2),
                    Ordering::Equal if l1 == l2 => return BoolExp::FALSE,
                    Ordering::Equal => return BoolExp::TRUE,
                    Ordering::Greater => (l2, l1),
                };
                let fresh = self.fresh();
                let fresh = Lit::new(fresh, true);
                if approx != Approx::Approx(true) {
                    self.sat
                        .add_clause_unchecked([l1, l2, !fresh].iter().copied());
                    self.sat
                        .add_clause_unchecked([!l1, !l2, !fresh].iter().copied());
                }
                if approx != Approx::Approx(false) {
                    self.sat
                        .add_clause_unchecked([!l1, l2, fresh].iter().copied());
                    self.sat
                        .add_clause_unchecked([l1, !l2, fresh].iter().copied());
                }
                BoolExp::unknown(fresh)
            }
        };
        debug!("{res} = (xor {b1} {b2})");
        res
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

    /// Produce a boolean expression representing the equality of the two expressions
    ///
    /// If the two expressions have different sorts returns an error containing both sorts
    pub fn eq(&mut self, exp1: Exp<Euf::UExp>, exp2: Exp<Euf::UExp>) -> Result<BoolExp> {
        self.eq_approx(exp1, exp2, Approx::Exact)
    }

    pub fn eq_approx(
        &mut self,
        exp1: Exp<Euf::UExp>,
        exp2: Exp<Euf::UExp>,
        approx: Approx,
    ) -> Result<BoolExp> {
        self.open(
            |euf, acts| euf.eq_approx(exp1, exp2, approx, acts),
            Ok(BoolExp::TRUE),
        )
    }

    /// Equivalent to `self.`[`assert`](Self::assert)`(self.`[`eq`](Self::eq)`(exp1, exp2)?)` but
    /// more efficient
    pub fn assert_eq(&mut self, exp1: Exp<Euf::UExp>, exp2: Exp<Euf::UExp>) -> Result<()> {
        let c1 = self.canonize(exp1);
        let c2 = self.canonize(exp2);
        self.open(|euf, acts| euf.assert_eq(c1, c2, acts), Ok(()))?;
        self.simplify();
        Ok(())
    }

    /// Assert that no pair of `Id`s from `ids` are equal to each other
    pub fn assert_distinct(
        &mut self,
        exps: impl IntoIterator<Item = Exp<Euf::UExp>>,
    ) -> IResult<()> {
        self.open(
            |euf, acts| euf.assert_distinct(exps.into_iter(), acts),
            Ok(()),
        )?;
        self.simplify();
        Ok(())
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
    ) -> Result<()> {
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
    ) -> Result<()> {
        self.assert_fn_eq(f, children, BoolExp::from_bool(!negate).into())
    }

    /// Produce an expression representing that is equivalent to `t` if `i` is true or `e` otherwise
    ///
    /// If `t` and `e` have different sorts returns an error containing both sorts
    pub fn ite(
        &mut self,
        i: BoolExp,
        t: Exp<Euf::UExp>,
        e: Exp<Euf::UExp>,
    ) -> Result<Exp<Euf::UExp>> {
        if t.sort() != e.sort() {
            return Err(SortMismatch {
                actual: e.sort(),
                expected: t.sort(),
            });
        }
        let i = self.canonize(i);
        self.open(
            |euf, acts| euf.ite(i, t, e, acts),
            Ok(Euf::placeholder_exp_from_sort(t.sort())),
        )
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
    ) -> Result<Exp<Euf::UExp>> {
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
    ) -> Result<BoolExp> {
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
