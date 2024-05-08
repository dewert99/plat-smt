use crate::egraph::Children;
use crate::euf::FullFunctionInfo;
use crate::index::Idx;
use crate::intern::*;
use crate::intern::{InternInfo, Symbol};
use crate::slice_vec::SliceVec;
use crate::{BoolExp, Conjunction, Exp, SolveResult, Solver};
use batsat::intmap::{AsIndex, IntMapBool};
use batsat::{Lit, SolverOpts};
use no_std_compat::prelude::v1::*;

pub struct SExpK;
pub type SExp = Idx<SExpK>;

type Ast = SliceVec<SExp, Symbol, SExp>;

#[derive(Default)]
struct AstSolverInner {
    core: Solver,
    /// Sorts of unresolved terms
    sorts: Vec<Sort>,
    resolved: Vec<Exp>,
    assert: [IntMapBool<SExp>; 2],
    assert_pending: Vec<(SExp, bool)>,
}

impl AstSolverInner {
    pub fn assert(&mut self, term: SExp, negate: bool) {
        if term.as_index() < self.resolved.len() {
            self.core
                .assert(self.resolved[term.as_index()].as_bool().unwrap())
        } else {
            let assert = &mut self.assert[negate as usize];
            assert.reserve(term);
            if !assert[term] {
                assert.set(term, true);
                self.assert_pending.push((term, negate));
            }
        }
    }
}

#[derive(Default)]
pub struct AstSolver {
    ast: Ast,
    inner: AstSolverInner,
}

impl AstSolver {
    pub fn intern(&self) -> &InternInfo {
        &self.inner.core.intern
    }

    pub fn intern_mut(&mut self) -> &mut InternInfo {
        &mut self.inner.core.intern
    }
    pub fn add_sexp(&mut self, f: Symbol, args: &[SExp], sort: Sort) -> SExp {
        self.inner.sorts.push(sort);
        self.ast.push(f, args)
    }

    pub fn declare_const(&mut self, c: Symbol, sort: Sort) -> SExp {
        self.flush();
        let res = self.ast.push(c, &[]);
        let exp = if sort == BOOL_SORT {
            self.inner.core.fresh_bool().into()
        } else {
            self.inner.core.sorted_fn(c, Children::new(), sort)
        };
        self.inner.resolved.push(exp);
        res
    }

    pub fn assert(&mut self, term: SExp, negate: bool) {
        self.inner.assert(term, negate)
    }
    fn flush_assert(&mut self) {
        for a in &mut self.inner.assert {
            a.reserve(SExp::new(self.ast.len()))
        }
        while let Some((term, negate)) = self.inner.assert_pending.pop() {
            let (sym, children) = self.ast.lookup(term);
            match (*sym, negate) {
                (AND_SYM, false) | (OR_SYM, true) => {
                    for &child in children {
                        self.inner.assert(child, negate)
                    }
                }
                (NOT_SYM, _) => self.inner.assert(children[0], !negate),
                _ => {}
            }
        }
    }

    pub fn flush(&mut self) {
        self.flush_assert();
        let len = self.ast.len();
        let mut sorts = self.inner.sorts.drain(..);
        while self.inner.resolved.len() < len as usize {
            let current = SExp::from_index(self.inner.resolved.len());
            let sort = sorts.next().unwrap();
            let assert_neg = self.inner.assert[true as usize][current];
            let assert = self.inner.assert[false as usize][current];
            let (&f, args) = self.ast.lookup(current);
            let args = args.iter().map(|x| self.inner.resolved[x.as_index()]);
            let e: Exp = match (assert, assert_neg) {
                (true, true) => {
                    self.inner.core.assert(BoolExp::FALSE);
                    BoolExp::TRUE.into()
                }
                (true, false) | (false, true) => {
                    self.inner.core.assert_sexp(f, args, assert_neg, sort);
                    BoolExp::Const(assert).into()
                }
                _ => self.inner.core.add_sexp(f, args, sort),
            };
            self.inner.resolved.push(e)
        }
    }

    pub fn resolve(&self, t: SExp) -> Exp {
        let exp = self.inner.resolved[t.as_index()];
        self.inner.core.canonize(exp)
    }

    pub fn last_unsat_core(&self) -> &[Lit] {
        self.inner.core.last_unsat_core()
    }

    pub fn check_sat_assuming_preserving_trail(&mut self, c: &Conjunction) -> SolveResult {
        self.flush();
        self.inner.core.check_sat_assuming_preserving_trail(c)
    }

    pub fn pop_model(&mut self) {
        self.inner.core.pop_model()
    }

    pub fn get_restore_point(&self) -> u32 {
        self.ast.len()
    }

    pub fn restore_to(&mut self, point: u32) {
        assert!(point >= self.inner.resolved.len() as u32);
        self.ast.truncate(point);
    }

    pub fn sat_options(&self) -> SolverOpts {
        self.inner.core.sat_options()
    }

    pub fn set_sat_options(&mut self, options: SolverOpts) -> Result<(), ()> {
        self.inner.core.set_sat_options(options)
    }

    pub fn push(&mut self) {
        self.flush();
        self.inner.core.push()
    }

    pub fn pop(&mut self, n: usize) {
        self.inner.core.pop(n)
    }

    pub fn clear(&mut self) {
        self.inner.core.clear();
        self.inner.sorts.clear();
        self.inner.resolved.clear();
        self.inner.assert.iter_mut().for_each(|x| x.clear());
        self.ast.clear();
        self.inner.assert_pending.clear();
    }

    pub fn init_function_info(&mut self) {
        self.inner.core.init_function_info()
    }

    pub fn function_info(&self) -> FullFunctionInfo<'_> {
        self.inner.core.function_info()
    }
}
