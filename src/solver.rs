use crate::egraph::Children;
use crate::euf::EUF;
use crate::junction::{Conjunction, Junction};
use crate::sort::{BaseSort, Sort};
use crate::util::display_debug;
use batsat::{lbool, Lit, SolverInterface, Theory, Var};
use egg::{Id, Symbol};
use log::debug;
use std::fmt::{Debug, Formatter};
use std::ops::Not;

// pub fn gen_sym(name: &str) -> Symbol {
//     static COUNT: AtomicUsize = AtomicUsize::new(0);
//
//     let count = COUNT.fetch_add(1, Ordering::Relaxed);
//
//     let name = format!("gensym${name}${count}");
//     Symbol::new(name)
// }

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
pub struct UExp {
    id: Id,
    sort: Sort,
}

impl Debug for UExp {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}${:?}", self.sort, self.id)
    }
}

display_debug!(UExp);

#[derive(Copy, Clone)]
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

pub trait Canonize {
    fn canonize(self, solver: &Solver) -> Self;
}

impl Canonize for BoolExp {
    fn canonize(self, solver: &Solver) -> Self {
        match self {
            BoolExp::Unknown(x) => {
                let val = solver.sat.value_lit(x);
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

impl Canonize for UExp {
    fn canonize(self, solver: &Solver) -> Self {
        UExp {
            id: solver.euf.find(self.id),
            sort: self.sort,
        }
    }
}

impl Canonize for Exp {
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
    pub fn collapse_bool<const IS_AND: bool>(&mut self, j: Junction<IS_AND>) -> BoolExp {
        match j.0 {
            None => BoolExp::Const(!IS_AND),
            Some(x) if x.is_empty() => BoolExp::Const(IS_AND),
            Some(mut x) => BoolExp::Unknown(self.andor_reuse(&mut x, IS_AND)),
        }
    }

    pub fn and_reuse(&mut self, exps: &mut Vec<BLit>) -> BLit {
        self.andor_reuse(exps, true)
    }

    pub fn or_reuse(&mut self, exps: &mut Vec<BLit>) -> BLit {
        self.andor_reuse(exps, false)
    }

    pub fn eq(&mut self, id1: Id, id2: Id) -> BoolExp {
        self.euf
            .add_eq_node(id1, id2, || Lit::new(self.sat.new_var_default(), true))
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
    pub fn bool_sort(&self) -> Sort {
        self.bool_sort
    }

    pub fn canonize<T: Canonize>(&self, t: T) -> T {
        t.canonize(self)
    }
}
