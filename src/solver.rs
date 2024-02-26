use crate::egraph::Children;
use crate::euf::EUF;
use crate::junction::*;
use crate::sort::{BaseSort, Sort};
use crate::util::display_debug;
use batsat::{lbool, Lit, SolverInterface, Theory, Var};
use egg::{Id, Symbol};
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
/// It also implements [`BitAnd`], [`BitOr`], and [`BitNot`], but its [`BitAnd`], [`BitOr`]
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

    pub fn eq(&mut self, id1: Id, id2: Id) -> BoolExp {
        self.euf
            .add_eq_node(id1, id2, || Lit::new(self.sat.new_var_default(), true))
    }

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
                let eqt = self.eq(fresh_id, tid);
                let BoolExp::Unknown(eqt) = eqt else {
                    unreachable!()
                };
                let eqe = self.eq(fresh_id, eid);
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

    pub fn bool_fn(&mut self, fn_name: Symbol, children: Children) -> BoolExp {
        self.euf
            .add_bool_node(fn_name, children, || {
                Lit::new(self.sat.new_var_default(), true)
            })
            .0
    }

    pub fn sorted_fn(&mut self, fn_name: Symbol, children: Children, sort: Sort) -> Exp {
        if sort == self.bool_sort {
            self.bool_fn(fn_name, children).into()
        } else {
            let id = self.euf.add_uninterpreted_node(fn_name, children, sort);
            UExp { id, sort }.into()
        }
    }
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
    pub fn check_sat_assuming(&mut self, c: &Conjunction) -> SolveResult {
        let res = match &c.0 {
            None => lbool::FALSE,
            Some(x) => self.sat.solve_limited_th(&mut self.euf, &x),
        };
        if res == lbool::FALSE {
            SolveResult::Unsat
        } else if res == lbool::TRUE {
            debug!(
                "check-sat returned sat (level = {})\n{:?}",
                self.euf.n_levels(),
                self.sat.get_model()
            );
            SolveResult::Sat
        } else {
            SolveResult::Unknown
        }
    }
    pub fn id_sort(&mut self, term: Exp) -> (Id, Sort) {
        match term.0 {
            EExp::Bool(BoolExp::Const(b)) => (self.euf.id_for_bool(b), self.bool_sort),
            EExp::Bool(BoolExp::Unknown(lit)) => (self.euf.id_for_lit(lit), self.bool_sort),
            EExp::Uninterpreted(u) => (u.id, u.sort),
        }
    }

    pub fn sort(&self, term: Exp) -> Sort {
        match term.0 {
            EExp::Bool(_) => self.bool_sort,
            EExp::Uninterpreted(u) => u.sort,
        }
    }
    pub fn bool_sort(&self) -> Sort {
        self.bool_sort
    }

    pub fn canonize<T: ExpLike>(&self, t: T) -> T {
        let res = t.canonize(self);
        debug!("{t} canonized to {res}");
        res
    }
}
