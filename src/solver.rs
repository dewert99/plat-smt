use crate::egraph::Children;
use crate::euf::EUF;
use crate::junction::*;
use crate::sort::{BaseSort, Sort};
use crate::util::display_debug;
use batsat::{lbool, Lit, SolverInterface, Theory, Var};
use egg::{Id, Symbol};
use either::Either;
use hashbrown::HashMap;
use log::debug;
use std::borrow::BorrowMut;
use std::fmt::{Debug, Display, Formatter};
use std::ops::Not;
/// The main solver structure including the sat solver and egraph.
///
/// It allows constructing and asserting expressions [`Exp`] within the solver
pub struct Solver {
    euf: EUF,
    sat: batsat::BasicSolver,
    clause_adder: Vec<Lit>,
    bool_sort: Sort,
}

impl Default for Solver {
    fn default() -> Self {
        Solver {
            euf: Default::default(),
            sat: Default::default(),
            clause_adder: vec![],
            bool_sort: Sort::new(BaseSort {
                name: Symbol::new("Bool"),
                params: Box::new([]),
            }),
        }
    }
}

#[derive(Copy, Clone)]
struct UExp {
    id: Id,
    sort: Sort,
}

impl Debug for UExp {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}${:?}", self.sort, self.id)
    }
}

display_debug!(UExp);

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

impl Debug for BoolExp {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            BoolExp::Const(c) => Debug::fmt(c, f),
            BoolExp::Unknown(l) => write!(f, "Bool${l:?}"),
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

display_debug!(Exp);

pub trait ExpLike: Into<Exp> + Copy + Debug + Display {
    fn canonize(self, solver: &Solver) -> Self;
}

impl ExpLike for BoolExp {
    fn canonize(self, solver: &Solver) -> Self {
        match self {
            BoolExp::Unknown(x) => {
                let val = solver.sat.value_lvl_0(x);
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

#[derive(Debug)]
/// Result of calling [`Solver::check_sat_assuming`]
pub enum SolveResult {
    Sat,
    Unsat,
    Unknown,
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
    fn andor_reuse(&mut self, exps: &mut Vec<BLit>, is_and: bool) -> BLit {
        let fresh = self.fresh();
        let res = Lit::new(fresh, true);
        debug!(
            "{res:?} is defined as {} {exps:?}",
            if is_and { "and" } else { "or" }
        );
        if let [exp] = &**exps {
            return *exp;
        }
        for lit in &mut *exps {
            self.clause_adder.clear();
            self.clause_adder.push(*lit ^ !is_and);
            self.clause_adder.push(Lit::new(fresh, !is_and));
            self.sat.add_clause_reuse(&mut self.clause_adder);
            *lit = *lit ^ is_and;
        }
        exps.push(Lit::new(fresh, is_and));
        self.sat.add_clause_reuse(exps);
        res
    }

    /// Collapse a [`Conjunction`] or [`Disjunction`] into a [`BoolExp`]
    ///
    /// To reuse memory you can pass mutable reference instead of an owned value
    /// Doing this will leave `j` in an unspecified state, so it should be
    /// [`clear`](Junction::clear)ed before it is used again
    pub fn collapse_bool<const IS_AND: bool>(
        &mut self,
        mut j: impl BorrowMut<Junction<IS_AND>>,
    ) -> BoolExp {
        match &mut j.borrow_mut().0 {
            None => BoolExp::Const(!IS_AND),
            Some(x) if x.is_empty() => BoolExp::Const(IS_AND),
            Some(x) => BoolExp::Unknown(self.andor_reuse(x, IS_AND)),
        }
    }

    fn raw_eq(&mut self, id1: Id, id2: Id) -> BoolExp {
        self.euf
            .add_eq_node(id1, id2, || Lit::new(self.sat.new_var_default(), true))
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
                let sym = Symbol::new(format!("if|{u:?}|id{tid}|id{eid}"));
                let fresh = self.sorted_fn(sym, Children::from_iter([]), tsort);
                let fresh_id = self.id_sort(fresh).0;
                let eqt = self.raw_eq(fresh_id, tid);
                let BoolExp::Unknown(eqt) = eqt else {
                    unreachable!()
                };
                let eqe = self.raw_eq(fresh_id, eid);
                let BoolExp::Unknown(eqe) = eqe else {
                    unreachable!()
                };
                self.clause_adder.clear();
                self.clause_adder.extend([!u, eqt]);
                self.sat.add_clause_reuse(&mut self.clause_adder);
                self.clause_adder.clear();
                self.clause_adder.extend([u, eqe]);
                self.sat.add_clause_reuse(&mut self.clause_adder);
                fresh
            }
        };
        debug!("{res} is bound to (ite {i} {t} {e})");
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
        if sort == self.bool_sort {
            self.bool_fn(fn_name, children).into()
        } else {
            let id = self.euf.add_uninterpreted_node(fn_name, children, sort);
            UExp { id, sort }.into()
        }
    }

    /// Similar to calling [`sorted_fn`](Solver::sorted_fn) with the boolean sort, but returns
    /// a [`BoolExp`] instead of an [`Exp`]
    pub fn bool_fn(&mut self, fn_name: Symbol, children: Children) -> BoolExp {
        self.euf
            .add_bool_node(fn_name, children, || {
                Lit::new(self.sat.new_var_default(), true)
            })
            .0
    }

    /// Assert that `b` is true
    pub fn assert(&mut self, b: BoolExp) {
        debug!("assert {b}");
        self.clause_adder.clear();
        match b {
            BoolExp::Const(true) => {}
            BoolExp::Unknown(l) => {
                self.clause_adder.push(l);
                self.sat.add_clause_reuse(&mut self.clause_adder);
            }
            BoolExp::Const(false) => {
                self.sat.add_clause_reuse(&mut self.clause_adder);
            }
        }
    }

    /// Check if the current assertions are satisfiable
    pub fn check_sat(&mut self) -> SolveResult {
        self.check_sat_assuming(&Default::default())
    }

    /// Check if the current assertions combined with the assertions in `c` are satisfiable
    pub fn check_sat_assuming(&mut self, c: &Conjunction) -> SolveResult {
        let res = match &c.0 {
            None => lbool::FALSE,
            Some(x) => self.sat.solve_limited_th(&mut self.euf, &x),
        };
        if res == lbool::FALSE {
            debug!(
                "check-sat {c:?} returned unsat (level = {})\n{:?}",
                self.euf.n_levels(),
                self.sat.unsat_core(),
            );
            SolveResult::Unsat
        } else if res == lbool::TRUE {
            debug!(
                "check-sat {c:?} returned sat (level = {})\n{:?}",
                self.euf.n_levels(),
                self.sat.get_model()
            );
            SolveResult::Sat
        } else {
            SolveResult::Unknown
        }
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
            EExp::Bool(BoolExp::Const(b)) => (self.euf.id_for_bool(b), self.bool_sort),
            EExp::Bool(BoolExp::Unknown(lit)) => (self.euf.id_for_lit(lit), self.bool_sort),
            EExp::Uninterpreted(u) => (u.id, u.sort),
        }
    }

    /// Returns the sort of `exp`
    pub fn sort(&self, exp: Exp) -> Sort {
        match exp.0 {
            EExp::Bool(_) => self.bool_sort,
            EExp::Uninterpreted(u) => u.sort,
        }
    }

    /// Returns the boolean sort
    pub fn bool_sort(&self) -> Sort {
        self.bool_sort
    }

    /// Simplifies `t` based on the current assertions
    pub fn canonize<T: ExpLike>(&self, t: T) -> T {
        let res = t.canonize(self);
        debug!("{t} canonized to {res}");
        res
    }

    pub(crate) fn last_unsat_core(&self) -> &[Lit] {
        self.sat.unsat_core()
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
            UnsatCoreInfo::Map(m) => Either::Left(lits.iter().map(|x| m.get(x).unwrap())),
            UnsatCoreInfo::FalseBy(x) => Either::Right(core::iter::once(x)),
        }
    }
}

#[derive(Default)]
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
