use crate::buffered_solver::BufferedSolver;
use crate::egraph::Children;
use crate::euf::{FullFunctionInfo, FunctionInfo, SatSolver, EUF};
use crate::explain::Justification;
use crate::intern::{DisplayInterned, InternInfo, Sort, BOOL_SORT};
use crate::junction::*;
use crate::util::display_debug;
use crate::Symbol;
use batsat::{lbool, Callbacks, Lit, SolverInterface, SolverOpts, Var};
use egg::Id;
use either::Either;
use hashbrown::HashMap;
use log::debug;
use std::borrow::BorrowMut;
use std::fmt::{Debug, Formatter};
use std::ops::{BitXor, Deref, Not};

#[derive(Default)]
struct NoCb;
impl Callbacks for NoCb {}
type BatSolver = batsat::Solver<NoCb>;

/// The main solver structure including the sat solver and egraph.
///
/// It allows constructing and asserting expressions [`Exp`] within the solver
#[derive(Default)]
pub struct Solver {
    euf: EUF,
    pending_equalities: Vec<(Id, Id)>,
    sat: BufferedSolver<BatSolver>,
    function_info_buf: FunctionInfo,
    pub intern: InternInfo,
}

#[derive(Copy, Clone, Debug)]
pub(crate) struct UExp {
    pub(crate) id: Id,
    pub(crate) sort: Sort,
}

impl DisplayInterned for UExp {
    fn fmt(&self, i: &InternInfo, f: &mut Formatter<'_>) -> std::fmt::Result {
        let sym = i.sorts.resolve(self.sort).0;
        write!(f, "@{}_{:?}", sym.with_intern(i), self.id)
    }
}

/// A boolean sorted expression within a [`Solver`]
///
/// It can be upcast to a dynamically sorted [`Exp`] using [`into`](Into::into), and downcast using
/// [`Exp::as_bool`].
///
/// It also implements [`BitAnd`](core::ops::BitAnd), [`BitOr`](core::ops::BitOr), and
/// [`Not`], but its [`BitAnd`](core::ops::BitAnd) and [`BitOr`](core::ops::BitOr)
/// implementations produces [`Conjunction`]s and [`Disjunction`]s respectively.
/// [`Solver::collapse_bool`] can be used to collapse these types back into [`BoolExp`]s
#[derive(Copy, Clone, Eq, PartialEq)]
pub enum BoolExp {
    Const(bool),
    Unknown(BLit),
}

impl From<BoolExp> for Exp {
    fn from(value: BoolExp) -> Self {
        Exp(EExp::Bool(value))
    }
}

impl From<UExp> for Exp {
    fn from(value: UExp) -> Self {
        Exp(EExp::Uninterpreted(value))
    }
}

impl Exp {
    /// Try to downcast into a [`BoolExp`]
    pub fn as_bool(self) -> Option<BoolExp> {
        match self.0 {
            EExp::Bool(b) => Some(b),
            _ => None,
        }
    }
}

impl BoolExp {
    pub const TRUE: BoolExp = BoolExp::Const(true);
    pub const FALSE: BoolExp = BoolExp::Const(false);
}

impl Not for BoolExp {
    type Output = BoolExp;

    fn not(self) -> Self::Output {
        match self {
            BoolExp::Const(b) => BoolExp::Const(!b),
            BoolExp::Unknown(lit) => BoolExp::Unknown(!lit),
        }
    }
}

impl BitXor<bool> for BoolExp {
    type Output = BoolExp;

    fn bitxor(self, rhs: bool) -> Self::Output {
        match self {
            BoolExp::Const(b) => BoolExp::Const(b ^ rhs),
            BoolExp::Unknown(lit) => BoolExp::Unknown(lit ^ rhs),
        }
    }
}

impl Debug for BoolExp {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            BoolExp::Const(c) => Debug::fmt(c, f),
            BoolExp::Unknown(l) => {
                if l.sign() {
                    write!(f, "@Bool_{:?}", l.var())
                } else {
                    write!(f, "(not @Bool_{:?})", l.var())
                }
            }
        }
    }
}

display_debug!(BoolExp);

#[derive(Copy, Clone)]
enum EExp {
    Bool(BoolExp),
    Uninterpreted(UExp),
}

/// A dynamically sorted expression within a [`Solver`]
#[derive(Copy, Clone)]
pub struct Exp(EExp);

impl Debug for Exp {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match &self.0 {
            EExp::Bool(b) => Debug::fmt(b, f),
            EExp::Uninterpreted(u) => Debug::fmt(u, f),
        }
    }
}

impl DisplayInterned for Exp {
    fn fmt(&self, i: &InternInfo, f: &mut Formatter<'_>) -> std::fmt::Result {
        match &self.0 {
            EExp::Bool(b) => DisplayInterned::fmt(b, i, f),
            EExp::Uninterpreted(u) => DisplayInterned::fmt(u, i, f),
        }
    }
}

pub trait ExpLike: Into<Exp> + Copy + Debug + DisplayInterned {
    fn canonize(self, solver: &Solver) -> Self;
}

impl ExpLike for BoolExp {
    fn canonize(self, solver: &Solver) -> Self {
        match self {
            BoolExp::Unknown(x) => {
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

impl ExpLike for UExp {
    fn canonize(self, solver: &Solver) -> Self {
        UExp {
            id: solver.euf.find(self.id),
            sort: self.sort,
        }
    }
}

impl ExpLike for Exp {
    fn canonize(self, solver: &Solver) -> Self {
        match self.0 {
            EExp::Bool(b) => b.canonize(solver).into(),
            EExp::Uninterpreted(u) => u.canonize(solver).into(),
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

impl SatSolver for BufferedSolver<BatSolver> {
    fn is_ok(&self) -> bool {
        self.deref().is_ok()
    }

    fn propagate(&mut self, l: Lit) -> bool {
        self.add_clause([l]);
        self.is_ok()
    }

    fn raise_conflict(&mut self, _: &[Lit], _: bool) {
        self.add_clause([])
    }
}

impl SolveResult {
    pub fn valid_when_expecting(self, oth: SolveResult) -> bool {
        match (self, oth) {
            (SolveResult::Sat, SolveResult::Sat)
            | (SolveResult::Unsat, SolveResult::Unsat)
            | (_, SolveResult::Unknown) => true,
            _ => false,
        }
    }

    pub fn as_lower_str(self) -> &'static str {
        match self {
            SolveResult::Sat => "sat",
            SolveResult::Unsat => "unsat",
            SolveResult::Unknown => "unknown",
        }
    }
}
impl Solver {
    fn fresh(&mut self) -> Var {
        let fresh = self.sat.new_var_default();
        self.euf.reserve(fresh);
        fresh
    }

    /// Generate a fresh boolean variable
    pub fn fresh_bool(&mut self) -> BoolExp {
        BoolExp::Unknown(Lit::new(self.fresh(), true))
    }

    #[inline]
    fn andor_reuse(&mut self, exps: &mut Vec<BLit>, is_and: bool) -> BLit {
        if let [exp] = &**exps {
            return *exp;
        }
        let fresh = self.fresh();
        let res = Lit::new(fresh, true);
        for lit in &mut *exps {
            self.sat
                .add_clause([*lit ^ !is_and, Lit::new(fresh, !is_and)]);
            *lit = *lit ^ is_and;
        }
        exps.push(Lit::new(fresh, is_and));
        self.sat.add_clause_reuse_lv(exps);
        res
    }

    /// Collapse a [`Conjunction`] or [`Disjunction`] into a [`BoolExp`]
    ///
    /// To reuse memory you can pass mutable reference instead of an owned value
    /// Doing this will leave `j` in an unspecified state, so it should be
    /// [`clear`](Junction::clear)ed before it is used again
    pub fn collapse_bool<const IS_AND: bool>(
        &mut self,
        mut j: impl BorrowMut<Junction<IS_AND>> + Debug,
    ) -> BoolExp {
        debug!("{j:?} was collapsed to ...");
        let res = match &mut j.borrow_mut().0 {
            Err(_) => BoolExp::Const(!IS_AND),
            Ok(x) if x.is_empty() => BoolExp::Const(IS_AND),
            Ok(x) => BoolExp::Unknown(self.andor_reuse(x, IS_AND)),
        };
        debug!("... {res}");
        res
    }

    pub fn xor(&mut self, b1: BoolExp, b2: BoolExp) -> BoolExp {
        let res = match (b1, b2) {
            (BoolExp::Const(b1), BoolExp::Const(b2)) => BoolExp::Const(b1 ^ b2),
            (BoolExp::Const(b), BoolExp::Unknown(l)) | (BoolExp::Unknown(l), BoolExp::Const(b)) => {
                BoolExp::Unknown(l ^ b)
            }
            (BoolExp::Unknown(l1), BoolExp::Unknown(l2)) => {
                let fresh = self.fresh();
                let fresh = Lit::new(fresh, true);
                self.sat.add_clause([l1, l2, !fresh]);
                self.sat.add_clause([!l1, l2, fresh]);
                self.sat.add_clause([l1, !l2, fresh]);
                self.sat.add_clause([!l1, !l2, !fresh]);
                BoolExp::Unknown(fresh)
            }
        };
        debug!("{res} = (xor {b1} {b2})");
        res
    }

    pub(crate) fn raw_eq(&mut self, id1: Id, id2: Id) -> BoolExp {
        let res = self
            .euf
            .add_eq_node(id1, id2, || Lit::new(self.sat.new_var_default(), true));
        debug!("{res:?} is defined as (= id{id1:?} id{id2:?})");
        res
    }

    pub(crate) fn assert_raw_eq(&mut self, id1: Id, id2: Id) {
        if !self.euf.has_parents(id1) || !self.euf.has_parents(id2) {
            let _ = self.euf.union(&mut self.sat, id1, id2, Justification::NOOP);
        } else {
            self.pending_equalities.push((id1, id2));
        }
    }

    /// Produce a boolean expression representing the equality of the two expressions
    ///
    /// If the two expressions have different sorts returns an error containing both sorts
    pub fn eq(&mut self, exp1: Exp, exp2: Exp) -> Result<BoolExp, (Sort, Sort)> {
        let (id1, sort1) = self.id_sort(exp1);
        let (id2, sort2) = self.id_sort(exp2);
        if sort1 != sort2 {
            Err((sort1, sort2))
        } else {
            Ok(self.raw_eq(id1, id2))
        }
    }

    /// Equivalent to `self.`[`assert`](Self::assert)`(self.`[`eq`](Self::eq)`(exp1, exp2)?)` but
    /// more efficient
    pub fn assert_eq(&mut self, exp1: Exp, exp2: Exp) -> Result<(), (Sort, Sort)> {
        let (id1, sort1) = self.id_sort(exp1);
        let (id2, sort2) = self.id_sort(exp2);
        if sort1 != sort2 {
            Err((sort1, sort2))
        } else {
            Ok(self.assert_raw_eq(id1, id2))
        }
    }

    /// Assert that no pair of `Id`s from `ids` are equal to each other
    pub fn assert_distinct(&mut self, ids: impl IntoIterator<Item = Id>) {
        if let Err(()) = self.euf.make_distinct(ids, &mut self.intern.symbols) {
            self.sat.add_clause([]);
        }
    }

    /// Equivalent to `self.`[`assert`](Self::assert)`(self.`[`bool_fn`](Self::bool_fn)`(f, children) ^ negate)`
    /// but more efficient
    pub fn assert_bool_fn(&mut self, f: Symbol, children: Children, negate: bool) {
        let (id1, _) = self.euf.add_blank_bool_node(f.into(), children);
        let id2 = self.euf.id_for_bool(!negate);
        self.assert_raw_eq(id1, id2);
    }

    /// Produce an expression representing that is equivalent to `t` if `i` is true or `e` otherwise
    ///
    /// If `t` and `e` have different sorts returns an error containing both sorts
    pub fn ite(&mut self, i: BoolExp, t: Exp, e: Exp) -> Result<Exp, (Sort, Sort)> {
        let tsort = self.sort(t);
        let esort = self.sort(e);
        if tsort != esort {
            return Err((tsort, esort));
        }
        let res = match i {
            BoolExp::TRUE => t,
            BoolExp::FALSE => e,
            BoolExp::Unknown(u) => {
                let tid = self.id_sort(t).0;
                let eid = self.id_sort(e).0;
                let sym = self
                    .intern
                    .symbols
                    .intern(&format!("if|{u:?}|id{tid}|id{eid}"));
                let fresh = self.sorted_fn(sym, Children::new(), tsort);
                let fresh_id = self.id_sort(fresh).0;
                let eqt = self.raw_eq(fresh_id, tid);
                let BoolExp::Unknown(eqt) = eqt else {
                    unreachable!()
                };
                let eqe = self.raw_eq(fresh_id, eid);
                let BoolExp::Unknown(eqe) = eqe else {
                    unreachable!()
                };
                self.sat.add_clause([!u, eqt]);
                self.sat.add_clause([u, eqe]);
                fresh
            }
        };
        debug!("{res:?} is bound to (ite {i:?} {t:?} {e:?})");
        Ok(res)
    }

    /// Creates a function call expression with a given name and children and return sort
    ///
    /// [`Id`]s for the children can be created with [`id_sort`](Solver::id_sort)
    ///
    /// This method does not check sorts of the children so callers need to ensure that functions
    /// call expressions with the same name but different return sorts do not become congruently
    /// equal (This would cause a panic when it happens)
    pub fn sorted_fn(&mut self, fn_name: Symbol, children: Children, sort: Sort) -> Exp {
        if sort == BOOL_SORT {
            self.bool_fn(fn_name, children).into()
        } else {
            let id = self
                .euf
                .add_uninterpreted_node(fn_name.into(), children, sort);
            UExp { id, sort }.into()
        }
    }

    /// Similar to calling [`sorted_fn`](Solver::sorted_fn) with the boolean sort, but returns
    /// a [`BoolExp`] instead of an [`Exp`]
    pub fn bool_fn(&mut self, fn_name: Symbol, children: Children) -> BoolExp {
        self.euf
            .add_bool_node(fn_name.into(), children, || {
                Lit::new(self.sat.new_var_default(), true)
            })
            .0
    }

    /// Assert that `b` is true
    pub fn assert(&mut self, b: BoolExp) {
        debug!("assert {b}");
        match b {
            BoolExp::TRUE => {}
            BoolExp::Unknown(l) => {
                self.sat.add_clause([l]);
            }
            BoolExp::FALSE => {
                self.sat.add_clause([]);
            }
        }
    }

    fn flush_pending(&mut self) {
        let _ = self.pending_equalities.iter().try_for_each(|(id1, id2)| {
            self.euf
                .union(&mut self.sat, *id1, *id2, Justification::NOOP)
        });
        self.pending_equalities.clear();
    }

    /// Check if the current assertions are satisfiable
    pub fn check_sat(&mut self) -> SolveResult {
        self.check_sat_assuming(&Default::default())
    }

    /// Check if the current assertions combined with the assertions in `c` are satisfiable
    /// Leave the solver in a state representing the model
    pub fn check_sat_assuming_preserving_trail(&mut self, c: &Conjunction) -> SolveResult {
        self.flush_pending();
        let res = match &c.0 {
            Err(_) => lbool::FALSE,
            Ok(x) => self
                .sat
                .solve_limited_preserving_trail_th(&mut self.euf, &x),
        };
        if res == lbool::FALSE {
            debug!(
                "check-sat {c:?} returned unsat, core:\n{:?}",
                self.sat.unsat_core(),
            );
            SolveResult::Unsat
        } else if res == lbool::TRUE {
            debug!(
                "check-sat {c:?} returned sat, model:\n{:?}",
                self.sat.get_model()
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

    pub fn push(&mut self) {
        let var = self.sat.new_var(lbool::UNDEF, false);
        self.euf.reserve(var);
        self.sat.assumptions_mut().push(Lit::new(var, true));
        // Run propagations at this level and then return Unsat because of the assumptions
        let res =
            self.check_sat_assuming_preserving_trail(&Junction::from_iter([BoolExp::Unknown(
                Lit::new(var, false),
            )]));
        debug_assert!(matches!(res, SolveResult::Unsat));
        self.euf.smt_push(Lit::new(var, true));
        self.pop_model()
    }

    pub fn pop(&mut self, n: usize) {
        if n > self.euf.assertion_level() {
            self.clear();
        } else if n > 0 {
            let new_level = self.sat.assumptions().len() - n;
            let old_num_vars = self.sat.assumptions()[new_level].var().idx();
            for v in (old_num_vars..self.sat.num_vars()).map(Var::unsafe_from_idx) {
                self.sat.set_decision_var(v, false);
            }
            self.sat.assumptions_mut().truncate(new_level);
            self.euf
                .smt_pop_to(new_level, self.sat.assumptions().last().copied());
        }
    }

    pub fn clear(&mut self) {
        self.sat.reset();
        self.euf.clear();
    }

    /// Like [`check_sat_assuming`](Solver::check_sat_assuming) but takes in an
    /// [`UnsatCoreConjunction`] which associates its elements values and returns an iterator
    /// over the values associated with the elements of the unsat core if the result is unsat
    pub fn check_sat_assuming_for_core<'a, T>(
        &'a mut self,
        c: &'a UnsatCoreConjunction<T>,
    ) -> Option<impl Iterator<Item = &'a T>> {
        let (conj, info) = c.parts();
        match self.check_sat_assuming(conj) {
            SolveResult::Unsat => Some(info.core(self.last_unsat_core())),
            _ => None,
        }
    }

    /// Returns the id and sort of `exp`
    ///
    /// See [`sorted_fn`](Solver::sorted_fn) and  [`bool_fn`](Solver::bool_fn)
    pub fn id_sort(&mut self, exp: Exp) -> (Id, Sort) {
        match exp.0 {
            EExp::Bool(BoolExp::Const(b)) => (self.euf.id_for_bool(b), BOOL_SORT),
            EExp::Bool(BoolExp::Unknown(lit)) => (
                self.euf.id_for_lit(lit, &mut self.intern.symbols),
                BOOL_SORT,
            ),
            EExp::Uninterpreted(u) => (u.id, u.sort),
        }
    }

    /// Returns the sort of `exp`
    pub fn sort(&self, exp: Exp) -> Sort {
        match exp.0 {
            EExp::Bool(_) => BOOL_SORT,
            EExp::Uninterpreted(u) => u.sort,
        }
    }

    /// Returns the boolean sort
    pub fn bool_sort(&self) -> Sort {
        BOOL_SORT
    }

    /// Simplifies `t` based on the current assertions
    pub fn canonize<T: ExpLike>(&self, t: T) -> T {
        let res = t.canonize(self);
        debug!("{t:?} canonized to {res:?}");
        res
    }

    pub(crate) fn last_unsat_core(&self) -> &[Lit] {
        self.sat.unsat_core()
    }

    pub fn function_info(&mut self) -> (FullFunctionInfo<'_>, &Self) {
        self.euf.function_info(&mut self.function_info_buf);
        (self.function_info_buf.with_euf(&self.euf), &*self)
    }
    pub fn sat_options(&self) -> SolverOpts {
        self.sat.options()
    }

    pub fn set_sat_options(&mut self, options: SolverOpts) -> Result<(), ()> {
        self.sat.set_options(options)
    }
}

pub(crate) enum UnsatCoreInfo<T> {
    FalseBy(T),
    Map(HashMap<Lit, T>),
}

impl<T> Default for UnsatCoreInfo<T> {
    fn default() -> Self {
        UnsatCoreInfo::Map(Default::default())
    }
}

impl<T> UnsatCoreInfo<T> {
    fn add(&mut self, bool_exp: BoolExp, t: T) {
        match bool_exp {
            BoolExp::FALSE => *self = UnsatCoreInfo::FalseBy(t),
            BoolExp::TRUE => {}
            BoolExp::Unknown(l) => {
                if let UnsatCoreInfo::Map(m) = self {
                    m.insert(!l, t);
                }
            }
        }
    }

    pub(crate) fn core<'a>(&'a self, lits: &'a [Lit]) -> impl Iterator<Item = &'a T> {
        match self {
            UnsatCoreInfo::Map(m) => Either::Left(lits.iter().filter_map(|x| m.get(x))),
            UnsatCoreInfo::FalseBy(x) => Either::Right(core::iter::once(x)),
        }
    }
}

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

    pub(crate) fn take_core(self) -> UnsatCoreInfo<T> {
        self.info
    }
}
