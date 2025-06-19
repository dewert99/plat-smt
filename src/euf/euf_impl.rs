use super::egraph::{children, Children, Op, EQ_OP};
use super::euf::{litvec, BoolClass, EClass, Euf, Exp, FunctionInfoIter, PushInfo};
use super::explain::Justification;
use crate::collapse::{Collapse, CollapseOut, ExprContext};
use crate::core_ops::{CoreOpsPf, Distinct, Eq};
use crate::exp::Fresh;
use crate::full_theory::FullTheory;
use crate::intern::{DisplayInterned, InternInfo, Symbol, BOOL_SORT};
use crate::outer_solver::Bound;
use crate::parser_fragment::{index_iter, ParserFragment, PfResult};
use crate::solver::{SolverCollapse, SolverWithBound};
use crate::theory::TheoryArg;
use crate::util::{format_args2, pairwise_sym, HashMap};
use crate::{AddSexpError, BoolExp, Conjunction, HasSort, Solver, Sort, SubExp, SuperExp};
use alloc::borrow::Cow;
use core::fmt::Formatter;
use log::debug;
use plat_egg::raw::Language;
use plat_egg::Id;
use platsat::Lit;

#[derive(Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Debug)]
pub struct UExp {
    pub(super) id: Id,
    pub(super) sort: Sort,
}

impl CollapseOut for UExp {
    type Out = UExp;
}

impl UExp {
    pub fn id(self) -> Id {
        self.id
    }

    pub fn new(id: Id, sort: Sort) -> Self {
        UExp { id, sort }
    }

    pub fn with_id(self, new_id: Id) -> Self {
        UExp {
            id: new_id,
            sort: self.sort,
        }
    }
}

impl DisplayInterned for UExp {
    fn fmt(&self, i: &InternInfo, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "(as @v{:?} {})", self.id(), self.sort().with_intern(i))
    }
}

impl HasSort for UExp {
    fn sort(self) -> Sort {
        self.sort
    }
    fn can_have_sort(s: Sort) -> bool {
        s != BOOL_SORT
    }
}

#[derive(Debug)]
pub enum Never {}

impl Into<Cow<'static, str>> for Never {
    fn into(self) -> Cow<'static, str> {
        match self {}
    }
}

impl FullTheory for Euf {
    type Exp = Exp;
    fn init_function_info(&mut self) {
        self.init_function_info()
    }

    type FunctionInfo<'a>
        = FunctionInfoIter<'a>
    where
        Self: 'a;

    fn get_function_info(&self, f: Symbol) -> FunctionInfoIter<'_> {
        self.get_function_info(f)
    }
}

impl Euf {
    fn sorted_fn_id(
        &mut self,
        f: Op,
        children: Children,
        target_sort: Sort,
        ctx: ExprContext<Exp>,
        acts: &mut TheoryArg<PushInfo>,
    ) -> (Id, Exp, bool) {
        let mut added = false;
        let id = self.egraph.add(f.into(), children, |id| {
            added = true;
            debug!("adding for id {id} in {ctx:?}");
            if target_sort == BOOL_SORT {
                let lits = if let ExprContext::AssertEq(_) = ctx {
                    litvec![]
                } else {
                    let l = Lit::new(acts.new_var_default(), true);
                    self.lit.add_id_to_lit(id, l);
                    litvec![l]
                };

                EClass::Bool(BoolClass::Unknown(lits))
            } else {
                EClass::Uninterpreted(target_sort)
            }
        });

        if let ExprContext::AssertEq(exp) = ctx {
            if exp.sort() == target_sort {
                self.union_exp(exp, id, acts);
                return (id, exp, added);
            }
        }
        let intern = acts.intern();
        let exp = self.id_to_exp(id);
        if exp.sort() != target_sort {
            panic!(
                "trying to create function {}{:?} with sort {}, but it already has sort {}",
                f.sym().with_intern(intern),
                self.egraph.id_to_node(id).children(),
                target_sort.with_intern(intern),
                exp.sort().with_intern(intern)
            )
        };
        (id, exp, added)
    }

    pub(super) fn add_eq_node(
        &mut self,
        id1: Id,
        id2: Id,
        ctx: ExprContext<BoolExp>,
        acts: &mut TheoryArg<PushInfo>,
    ) -> BoolExp {
        let cid1 = self.find(id1);
        let cid2 = self.find(id2);
        if cid1 == cid2 {
            return acts.collapse_const(true, ctx);
        }
        let (_, exp, added) =
            self.sorted_fn_id(EQ_OP, children![cid1, cid2], BOOL_SORT, ctx.upcast(), acts);
        let exp: BoolExp = exp.downcast().unwrap();
        if added {
            if let Ok(l) = exp.to_lit() {
                self.finish_eq_node(l, cid1, cid2, acts);
            }
        }
        exp
    }

    fn assert_eq(&mut self, e1: Exp, e2: Exp, acts: &mut TheoryArg<PushInfo>) -> () {
        match (e1, e2) {
            (Exp::Left(b1), Exp::Left(b2)) => match (b1.to_lit(), b2.to_lit()) {
                (Err(pol), Ok(l)) | (Ok(l), Err(pol)) => {
                    acts.propagate(l ^ !pol);
                }
                (Err(b1), Err(b2)) => {
                    if b1 != b2 {
                        acts.raise_conflict(&[], false);
                    }
                }
                (Ok(b1), Ok(b2)) => {
                    acts.xor(
                        BoolExp::unknown(b1),
                        BoolExp::unknown(b2),
                        ExprContext::AssertEq(BoolExp::FALSE),
                    );
                    self.unify_lits(acts, b1, b2);
                    self.unify_lits(acts, !b1, !b2);
                }
            },
            (Exp::Right(u1), Exp::Right(u2)) => {
                let _ = self.union(acts, u1.id, u2.id, Justification::NOOP);
            }
            _ => unreachable!(),
        }
    }

    fn unify_lits(&mut self, acts: &mut TheoryArg<PushInfo>, b1: Lit, b2: Lit) {
        match (self.check_id_for_lit(b1), self.check_id_for_lit(b2)) {
            (Some(id1), Some(id2)) => {
                let _ = self.union(acts, id1, id2, Justification::NOOP);
            }
            (Some(id1), None) => self.lit.weak_add_id_to_lit(id1, b2),
            (None, Some(id2)) => self.lit.weak_add_id_to_lit(id2, b1),
            (None, None) => {
                let sym = acts
                    .intern_mut()
                    .symbols
                    .gen_sym(&format_args2!("bool|lit|{b1:?}"));
                let id = self.egraph.add(sym.into(), Children::new(), |_| {
                    EClass::Bool(BoolClass::Unknown(litvec![]))
                });
                self.lit.weak_add_id_to_lit(id, b1);
                self.lit.weak_add_id_to_lit(id, b2);
            }
        }
    }
}

pub struct EufMarker;

impl<'a, Arg> Collapse<UExp, Arg, EufMarker> for Euf {
    fn collapse(&mut self, t: UExp, _: &mut Arg, _: ExprContext<UExp>) -> UExp {
        UExp::new(self.find(t.id), t.sort)
    }

    fn placeholder(&self, t: &UExp) -> UExp {
        *t
    }
}

impl<'a, Arg> Collapse<Fresh<UExp>, Arg, EufMarker> for Euf {
    fn collapse(&mut self, fresh: Fresh<UExp>, _: &mut Arg, _: ExprContext<UExp>) -> UExp {
        let id = self.egraph.add(fresh.name.into(), Children::new(), |_| {
            EClass::Uninterpreted(fresh.sort)
        });
        UExp::new(id, fresh.sort)
    }

    fn placeholder(&self, fresh: &Fresh<UExp>) -> UExp {
        UExp::new(Id::MAX, fresh.sort)
    }
}

impl<'a, 'b> Collapse<Distinct<'b, Exp>, TheoryArg<'a, PushInfo>, EufMarker> for Euf {
    fn collapse(
        &mut self,
        Distinct(exps): Distinct<Exp>,
        acts: &mut TheoryArg<'a, PushInfo>,
        ctx: ExprContext<BoolExp>,
    ) -> BoolExp {
        if ctx != ExprContext::Approx(false) && ctx != ExprContext::AssertEq(BoolExp::TRUE) {
            let mut c: Conjunction = acts.new_junction();
            c.extend(
                pairwise_sym(exps)
                    .map(|(e1, e2)| !self.collapse(Eq(*e1, *e2), acts, ExprContext::Exact)),
            );
            return acts.collapse_bool(c, ctx);
        }

        let Some(e0) = exps.first() else {
            return acts.collapse_const(true, ctx);
        };

        let Exp::Right(_) = e0 else {
            let b0 = e0.downcast().unwrap();
            let mut bools = exps[1..].iter().map(|exp| exp.downcast().unwrap());
            let Some(b1) = bools.next() else {
                return acts.collapse_const(true, ctx);
            };
            return if let Some(_) = bools.next() {
                return acts.collapse_const(false, ctx);
            } else {
                acts.xor(b0, b1, ctx)
            };
        };

        let distinct_sym = acts.intern_mut().symbols.gen_sym("distinct");
        self.distinct_gensym += 1;
        let b = if ctx == ExprContext::AssertEq(BoolExp::TRUE) {
            BoolExp::TRUE
        } else {
            BoolExp::unknown(Lit::new(acts.new_var_default(), true))
        };
        for exp in exps {
            let id = self.id_for_exp(*exp, acts);
            let mut added = false;
            self.egraph
                .add(distinct_sym.into(), Children::from_slice(&[id]), |_| {
                    added = true;
                    EClass::Singleton(!b)
                });
            if !added {
                return acts.collapse_const(false, ctx);
            }
        }
        b
    }

    fn placeholder(&self, _: &Distinct<Exp>) -> BoolExp {
        BoolExp::TRUE
    }
}

impl<'a> Collapse<Eq<Exp>, TheoryArg<'a, PushInfo>, EufMarker> for Euf {
    fn collapse(
        &mut self,
        Eq(e1, e2): Eq<Exp>,
        acts: &mut TheoryArg<'a, PushInfo>,
        ctx: ExprContext<BoolExp>,
    ) -> BoolExp {
        if e1 == e2 {
            BoolExp::TRUE
        } else if e1
            .downcast()
            .is_some_and(|b1: BoolExp| e2.downcast() == Some(!b1))
        {
            BoolExp::FALSE
        } else if ctx == ExprContext::AssertEq(BoolExp::TRUE) {
            self.assert_eq(e1, e2, acts);
            BoolExp::TRUE
        } else {
            match (e1.downcast(), e2.downcast()) {
                (Some(BoolExp::TRUE), Some(b)) | (Some(b), Some(BoolExp::TRUE)) => b,
                (Some(BoolExp::FALSE), Some(b)) | (Some(b), Some(BoolExp::FALSE)) => !b,
                _ => {
                    let id1 = self.id_for_exp(e1, acts);
                    let id2 = self.id_for_exp(e2, acts);
                    self.add_eq_node(id1, id2, ctx, acts)
                }
            }
        }
    }

    fn placeholder(&self, _: &Eq<Exp>) -> BoolExp {
        BoolExp::TRUE
    }
}

pub struct UFn<I: Iterator>(Symbol, I, Sort);

impl<'a, I: Iterator> UFn<I> {
    pub fn new_unchecked(f: Symbol, children: I, sort: Sort) -> Self {
        UFn(f, children, sort)
    }
}

impl<I: Iterator<Item = Exp>> CollapseOut for UFn<I> {
    type Out = Exp;
}

impl<'a, I: Iterator<Item = Exp>> Collapse<UFn<I>, TheoryArg<'a, PushInfo>, EufMarker> for Euf {
    fn collapse(
        &mut self,
        UFn(f, children, sort): UFn<I>,
        acts: &mut TheoryArg<'a, PushInfo>,
        ctx: ExprContext<Exp>,
    ) -> Exp {
        let children = self.resolve_children(children, acts);
        self.sorted_fn_id(f.into(), children, sort, ctx, acts).1
    }

    fn placeholder(&self, &UFn(_, _, sort): &UFn<I>) -> Exp {
        if sort == BOOL_SORT {
            BoolExp::TRUE.upcast()
        } else {
            Exp::Right(UExp { id: Id::MAX, sort })
        }
    }
}

#[derive(Default)]
pub struct UFnPf;

impl ParserFragment<Exp, SolverWithBound<Solver<Euf>, HashMap<Symbol, Bound<Exp>>>, EufMarker>
    for UFnPf
{
    fn handle_non_terminal(
        &self,
        f: Symbol,
        children: &mut [Exp],
        solver: &mut SolverWithBound<Solver<Euf>, HashMap<Symbol, Bound<Exp>>>,
        ctx: ExprContext<Exp>,
    ) -> PfResult<Exp> {
        use AddSexpError::*;
        true.then(|| match solver.bound.get(&f) {
            None => Err(Unbound),
            Some(Bound::Const(c)) => {
                if !children.is_empty() {
                    return Err(ExtraArgument { expected: 0 });
                }
                if let ExprContext::AssertEq(exp) = ctx {
                    if exp.sort() == c.sort() {
                        let cur = *c;
                        let _ = solver.solver.assert_eq(exp, cur);
                        return Ok(exp);
                    }
                }
                Ok(*c)
            }
            Some(Bound::Fn(def)) => {
                index_iter(children)
                    .zip(def.args())
                    .try_for_each(|(arg, sort)| {
                        arg.expect_sort(*sort)?;
                        Ok::<_, AddSexpError>(())
                    })?;
                if children.len() < def.args().len() {
                    return Err(MissingArgument {
                        actual: children.len(),
                        expected: def.args().len(),
                    });
                } else if children.len() > def.args().len() {
                    return Err(ExtraArgument {
                        expected: def.args().len(),
                    });
                }
                Ok(SolverCollapse::collapse_in_ctx(
                    &mut solver.solver,
                    UFn(f, children.iter().copied(), def.ret()),
                    ctx,
                ))
            }
        })
    }
}

pub type EufPf = (CoreOpsPf, UFnPf);
