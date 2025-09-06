use super::egraph::{children, Children, Op, SymbolLang, EQ_OP};
use super::euf::{litvec, BoolClass, EClass, Euf, Exp, FunctionInfoIter, PushInfo};
use super::explain::Justification;
use crate::collapse::{Collapse, CollapseOut, ExprContext};
use crate::core_ops::{Distinct, DistinctPf, Eq, EqPf, ItePf};
use crate::exp::Fresh;
use crate::full_theory::{FnSort, FullTheory};
use crate::intern::{DisplayInterned, InternInfo, Symbol, BOOL_SORT, DISTINCT_SYM};
use crate::outer_solver::Bound;
use crate::parser_core::SexpTerminal;
use crate::parser_fragment::{index_iter, ParserFragment, PfResult};
use crate::recorder::Recorder;
use crate::rexp::{rexp_debug, AsRexp, Namespace, NamespaceVar, Rexp};
use crate::solver::{SolverCollapse, SolverWithBound};
use crate::tseitin::{BoolOpPf, SatExplainTheoryArgT, SatTheoryArgT};
use crate::util::{pairwise_sym, HashMap};
use crate::{AddSexpError, BoolExp, Conjunction, HasSort, Solver, Sort, SubExp, SuperExp};
use core::fmt::Formatter;
use plat_egg::raw::Language;
use plat_egg::Id;
use platsat::Lit;

#[derive(Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
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

impl AsRexp for UExp {
    fn as_rexp<R>(&self, f: impl for<'a> FnOnce(Rexp<'a>) -> R) -> R {
        f(Rexp::Nv(NamespaceVar(
            Namespace::Uninterpreted,
            usize::from(self.id) as u32,
        )))
    }
}

rexp_debug!(UExp);

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

impl<R: Recorder> FullTheory<R> for Euf {
    type Exp = Exp;

    type FnSort = FnSort;
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
    fn sorted_fn_id<'a>(
        &mut self,
        f: Op,
        children: Children,
        target_sort: Sort,
        ctx: ExprContext<Exp>,
        acts: &mut impl SatTheoryArgT<'a, M = PushInfo>,
    ) -> (Id, Exp, bool) {
        let mut added = false;
        let id = self.egraph.add(f.into(), children, |id, children| {
            acts.log_def(
                UExp::new(id, target_sort),
                f.sym(),
                children.iter().map(|id| UExp::new(*id, target_sort)),
            );
            added = true;
            if target_sort == BOOL_SORT {
                let lits = if let ExprContext::AssertEq(_) = ctx {
                    litvec![]
                } else {
                    let l = Lit::new(acts.new_var_default(), true);
                    self.lit.add_id_to_lit(id, l, false);
                    acts.log_def_exp(BoolExp::unknown(l), UExp::new(id, BOOL_SORT));
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

    pub(super) fn add_eq_node<'a>(
        &mut self,
        id1: Id,
        id2: Id,
        ctx: ExprContext<BoolExp>,
        acts: &mut impl SatTheoryArgT<'a, M = PushInfo>,
    ) -> (bool, BoolExp) {
        let cid1 = self.find(id1);
        let cid2 = self.find(id2);
        if cid1 == cid2 {
            return (false, acts.collapse_const(true, ctx));
        }
        let (_, exp, added) =
            self.sorted_fn_id(EQ_OP, children![cid1, cid2], BOOL_SORT, ctx.upcast(), acts);
        let exp: BoolExp = exp.downcast().unwrap();
        if added {
            if let Ok(l) = exp.to_lit() {
                self.finish_eq_node(l, cid1, cid2, acts);
            }
        }
        (added, exp)
    }

    fn assert_eq<'a>(
        &mut self,
        e1: Exp,
        e2: Exp,
        acts: &mut impl SatTheoryArgT<'a, M = PushInfo>,
    ) -> () {
        match (e1, e2) {
            (Exp::Left(b1), Exp::Left(b2)) => match (b1.to_lit(), b2.to_lit()) {
                (Err(pol), Ok(l)) | (Ok(l), Err(pol)) => {
                    acts.propagate(l ^ !pol);
                }
                (Err(b1), Err(b2)) => {
                    if b1 != b2 {
                        acts.for_explain().clause_builder().clear();
                        acts.raise_conflict_using_builder(false)
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

    fn unify_lits<'a>(
        &mut self,
        acts: &mut impl SatTheoryArgT<'a, M = PushInfo>,
        b1: Lit,
        b2: Lit,
    ) {
        if let Some(id1) = self.check_id_for_lit(b1) {
            if let Some(id2) = self.check_id_for_lit(b2) {
                let _ = self.union(acts, id1, id2, Justification::NOOP);
            } else {
                self.lit.add_id_to_lit(id1, b2, true)
            }
        } else {
            let id = self.id_for_lit(b2, acts, true);
            self.lit.add_id_to_lit(id, b1, true);
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
        let id = self.egraph.add(fresh.name.into(), Children::new(), |_, _| {
            EClass::Uninterpreted(fresh.sort)
        });
        UExp::new(id, fresh.sort)
    }

    fn placeholder(&self, fresh: &Fresh<UExp>) -> UExp {
        UExp::new(Id::MAX, fresh.sort)
    }
}

impl<'a, 'b, A: SatTheoryArgT<'a, M = PushInfo>> Collapse<Distinct<'b, Exp>, A, EufMarker> for Euf {
    fn collapse(
        &mut self,
        Distinct(exps): Distinct<Exp>,
        acts: &mut A,
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
            let b = BoolExp::unknown(Lit::new(acts.new_var_default(), true));
            acts.log_def(b, DISTINCT_SYM, exps.iter().copied());
            b
        };
        for exp in exps {
            let id = self.id_for_exp(*exp, acts, false);
            let mut added = false;
            self.egraph
                .add(distinct_sym.into(), Children::from_slice(&[id]), |_, _| {
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

impl<'a, A: SatTheoryArgT<'a, M = PushInfo>> Collapse<Eq<Exp>, A, EufMarker> for Euf {
    fn collapse(
        &mut self,
        Eq(e1, e2): Eq<Exp>,
        acts: &mut A,
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
            let id1 = self.id_for_exp(e1, acts, false);
            let id2 = self.id_for_exp(e2, acts, false);
            let (added, res) = self.add_eq_node(id1, id2, ctx, acts);
            if added {
                if let [Some(b1), Some(b2)] = [e1, e2].map(BoolExp::from_downcast) {
                    acts.xor(b1, b2, ExprContext::AssertEq(!res));
                }
            }
            res
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

impl<'a, I: Iterator<Item = Exp>, A: SatTheoryArgT<'a, M = PushInfo>> Collapse<UFn<I>, A, EufMarker>
    for Euf
{
    fn collapse(
        &mut self,
        UFn(f, children, sort): UFn<I>,
        acts: &mut A,
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

type EufSolver<R> = SolverWithBound<Solver<Euf, R>, HashMap<Symbol, Bound<Exp, FnSort>>>;

#[derive(Default)]
pub struct UFnPf;

impl<R: Recorder> ParserFragment<Exp, EufSolver<R>, EufMarker> for UFnPf {
    fn supports(&self, _: Symbol) -> bool {
        true
    }

    fn handle_non_terminal(
        &self,
        f: Symbol,
        children: &mut [Exp],
        solver: &mut EufSolver<R>,
        ctx: ExprContext<Exp>,
    ) -> Result<Exp, AddSexpError> {
        use AddSexpError::*;
        match solver.bound.get(&f) {
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
        }
    }
}

#[derive(Default)]
pub struct EgraphPf<I>(I);

impl<R: Recorder, E: SubExp<Exp, MS> + Copy, M, MS, I: ParserFragment<E, EufSolver<R>, M>>
    ParserFragment<E, EufSolver<R>, (M, MS)> for EgraphPf<I>
{
    fn supports(&self, s: Symbol) -> bool {
        self.0.supports(s)
    }
    fn handle_terminal(
        &self,
        x: SexpTerminal,
        solver: &mut EufSolver<R>,
        ctx: ExprContext<E>,
    ) -> PfResult<E> {
        self.0.handle_terminal(x, solver, ctx)
    }

    fn handle_non_terminal(
        &self,
        f: Symbol,
        children: &mut [E],
        solver: &mut EufSolver<R>,
        ctx: ExprContext<E>,
    ) -> Result<E, AddSexpError> {
        let Some(children_ids) = solver.solver.open(
            |euf, acts| {
                let chilren_ids: Children = children
                    .iter()
                    .map(|&x| euf.id_for_exp(x.upcast(), acts, true))
                    .collect();
                Some(chilren_ids)
            },
            None,
        ) else {
            return self.0.handle_non_terminal(f, children, solver, ctx);
        };

        let mut enode = SymbolLang::new(f.into(), children_ids);

        if let Some(existing_id) = solver.solver.th.egraph.lookup(&mut enode) {
            let res: Exp = match &*solver.solver.th.egraph[existing_id] {
                EClass::Uninterpreted(s) => {
                    UExp::new(solver.solver.th.egraph.find(existing_id), *s).upcast()
                }
                EClass::Bool(BoolClass::Const(b)) => BoolExp::from_bool(*b).upcast(),
                EClass::Bool(BoolClass::Unknown(l)) => BoolExp::unknown(l[0]).upcast(),
                _ => unreachable!(),
            };
            return Ok(E::from_downcast(res).unwrap());
        }

        let ctx = match ctx {
            ExprContext::AssertEq(x) => ExprContext::AssertEq(x),
            _ => ExprContext::Exact,
        };

        let res = self.0.handle_non_terminal(f, children, solver, ctx);

        if let Ok(res) = res {
            let res: Exp = res.upcast();
            solver.solver.open(
                |euf, acts| {
                    euf.sorted_fn_id(
                        enode.op(),
                        enode.children_owned(),
                        res.sort(),
                        ExprContext::AssertEq(res),
                        acts,
                    );
                },
                (),
            );
        }
        res
    }

    fn sub_ctx(&self, f: Symbol, previous_children: &[E], ctx: ExprContext<E>) -> ExprContext<E> {
        self.0.sub_ctx(f, previous_children, ctx)
    }
}

pub type EufPf = (BoolOpPf, (EqPf, (DistinctPf, (EgraphPf<ItePf>, UFnPf))));
