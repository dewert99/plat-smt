use super::egraph::{Children, EQ_OP, Op, SymbolLang, children};
use super::euf::{EClass, Euf, EufLevelMarker, Exp, PushInfo};
use super::explain::Justification;
use crate::collapse::{BaseMarker, Collapse, CollapseOut, ExprContext, LeftMarker};
use crate::core_ops::{DefaultIte, DistinctElts, DistinctPf, Eq, EqPf, ItePf, RawDistinct};
use crate::euf::bool_euf_th::BoolClass;
use crate::euf::euf_th::{EufThBase, FullEufTh};
use crate::euf::quantifier_applier::QuantifierChecker;
use crate::exp::Fresh;
use crate::full_theory::{
    Bound, FnSort, FullTheory, FunctionAssignmentT, PrepareModelKind, QExtractor, TopLevelCollapse,
};
use crate::intern::{
    BOOL_SORT, DISTINCT_SYM, DISTINGUISHER_SYM, DisplayInterned, InternInfo, REAL_SORT, Symbol,
};
use crate::parser::{SexpTerminal, SmtlibLogic};
use crate::parser_fragment::{ParserFragment, PfResult, index_iter};
use crate::recorder::{Recorder, dep_checker};
use crate::rexp::{AsRexp, Namespace, NamespaceVar, Rexp, rexp_debug};
use crate::solver::{SolverCollapse, SolverWithBound};
use crate::theory::{Incremental, TheoryArg, TupleExtract};
use crate::tseitin::{BoolOpPf, SatTheoryArgR};
use crate::util::{HashMap, pairwise_sym};
use crate::{AddSexpError, BoolExp, Conjunction, ExpLike, HasSort, Solver, Sort, SubExp, SuperExp};
use core::fmt::Formatter;
use core::marker::PhantomData;
use core::ops::Deref;
use core::slice::Iter;
use perfect_derive::perfect_derive;
use plat_egg::Id;
use plat_egg::raw::Language;
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

pub(super) fn id_to_nv(id: Id) -> NamespaceVar {
    NamespaceVar(Namespace::Uninterpreted, usize::from(id) as u32)
}

impl AsRexp for Id {
    fn as_rexp<R>(&self, f: impl for<'a> FnOnce(Rexp<'a>) -> R) -> R {
        f(Rexp::Nv(id_to_nv(*self)))
    }
}

impl AsRexp for UExp {
    fn as_rexp<R>(&self, f: impl for<'a> FnOnce(Rexp<'a>) -> R) -> R {
        if usize::from(self.id) == 0 {
            f(Rexp::Nv(NamespaceVar(
                Namespace::SortDefault,
                self.sort.0.get(),
            )))
        } else {
            self.id.as_rexp(f)
        }
    }
}

rexp_debug!(UExp);

impl DisplayInterned for UExp {
    fn fmt(&self, i: &InternInfo, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "(as {:?} {})", self, self.sort().with_intern(i))
    }
}

impl HasSort for UExp {
    fn sort(self) -> Sort {
        self.sort
    }
    fn can_have_sort(s: Sort) -> bool {
        s != BOOL_SORT && s != REAL_SORT
    }
}
impl ExpLike for UExp {
    fn default_with_sort(s: Sort) -> Self {
        UExp::new(Id::from(0), s)
    }
}

pub struct EufQExtractor;

impl<Q, Th: EufThBase> QExtractor<Euf<Q, Th>> for EufQExtractor {
    type Target = Q;

    fn extract(t: &mut Euf<Q, Th>) -> &mut Self::Target {
        &mut t.q
    }

    fn extract_shr(t: &Euf<Q, Th>) -> &Self::Target {
        &t.q
    }
}

impl<
    R: Recorder,
    Q: Incremental + Clone + 'static,
    Th: for<'a> FullEufTh<TheoryArg<'a, EufLevelMarker<Q, Th>, R>> + Clone + 'static,
> FullTheory<R> for Euf<Q, Th>
{
    type Exp = Exp<Th::Exp>;

    type FnSort = FnSort;

    type QExtractor = EufQExtractor;
    fn prepare_model(&mut self, kind: PrepareModelKind) {
        if matches!(kind, PrepareModelKind::GetModel) {
            self.init_function_info()
        }
    }

    fn get_function_info(&self, f: Symbol) -> impl FunctionAssignmentT<Exp = Self::Exp> {
        self.get_function_info(f)
    }

    fn supported_logic(&self) -> SmtlibLogic {
        SmtlibLogic::QF_UF
    }
}

impl<Q: Incremental, Th: EufThBase> Euf<Q, Th> {
    fn model_sorted_fn<A: SatTheoryArgR>(
        &mut self,
        f: Op,
        children: Children,
        target_sort: Sort,
    ) -> (Exp<Th::Exp>, bool)
    where
        Th: FullEufTh<A>,
    {
        let node = SymbolLang::new(f, children);
        if let Some(id) = self.egraph.lookup(node) {
            (self.id_to_exp(id), false)
        } else {
            (Exp::default_with_sort(target_sort), false)
        }
    }

    fn sorted_fn<A: SatTheoryArgR<M: TupleExtract<P, PushInfo>>, P>(
        &mut self,
        f: Op,
        children: Children,
        target_sort: Sort,
        ctx: ExprContext<Exp<Th::Exp>>,
        acts: &mut A,
    ) -> (Exp<Th::Exp>, bool)
    where
        Th: FullEufTh<A>,
    {
        if acts.in_model() {
            return self.model_sorted_fn(f, children, target_sort);
        }
        let mut added = false;
        let id = self.egraph.add(f.into(), children, |id, children| {
            acts.log_def(
                UExp::new(id, target_sort),
                f.sym(),
                children.iter().map(|id| UExp::new(*id, target_sort)),
            );
            added = true;
            if Th::Exp::can_have_sort(target_sort) {
                EClass::Th(self.th.create_fresh_class_for_empty_theory(
                    acts,
                    target_sort,
                    ctx.downcast(),
                    id,
                    |lit, id| self.lit.add_id_to_lit(id, lit, false),
                ))
            } else {
                EClass::Uninterpreted(target_sort)
            }
        });

        if let ExprContext::AssertEq(exp) = ctx {
            if exp.sort() == target_sort {
                self.union_exp(exp, id, acts);
                return (exp, added);
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
        (exp, added)
    }

    pub(super) fn add_eq_node<P, A: SatTheoryArgR<M: TupleExtract<P, PushInfo>>>(
        &mut self,
        id1: Id,
        id2: Id,
        ctx: ExprContext<BoolExp>,
        acts: &mut A,
    ) -> (bool, BoolExp)
    where
        Th: FullEufTh<A>,
    {
        let cid1 = self.find(id1);
        let cid2 = self.find(id2);
        if cid1 == cid2 {
            return (false, acts.collapse_const(true, ctx));
        }
        let (exp, added) =
            self.sorted_fn(EQ_OP, children![cid1, cid2], BOOL_SORT, ctx.upcast(), acts);
        let exp: BoolExp = exp.downcast().unwrap();
        if added {
            if let Ok(l) = exp.to_lit() {
                self.finish_eq_node(l, cid1, cid2, acts);
            }
        }
        (added, exp)
    }

    fn assert_eq<P, A: SatTheoryArgR<M: TupleExtract<P, PushInfo>>>(
        &mut self,
        e1: Exp<Th::Exp>,
        e2: Exp<Th::Exp>,
        acts: &mut A,
    ) -> ()
    where
        Th: FullEufTh<A>,
    {
        match (e1, e2) {
            (Exp::Left(e1), Exp::Left(e2)) => {
                let (th, mut acts) = self.lift_th(acts);
                th.assert_exp_eq(&mut acts, e1, e2);
            }
            (Exp::Right(u1), Exp::Right(u2)) => {
                self.union(acts, u1.id, u2.id, Justification::NOOP);
            }
            _ => unreachable!(),
        }
    }
}

impl<'a, Arg, Q: QuantifierChecker<UExp, M>, Th: EufThBase, M> Collapse<UExp, Arg, BaseMarker<M>>
    for Euf<Q, Th>
{
    fn collapse(&mut self, t: UExp, _: &mut Arg, _: ExprContext<UExp>) -> UExp {
        UExp::new(self.find(t.id), t.sort)
    }

    fn placeholder(&self, t: &UExp) -> UExp {
        *t
    }
}

impl<T, Q, Th: EufThBase> DefaultIte<T> for Euf<Q, Th> {}

impl<'a, Arg, Th: EufThBase, M, Q: QuantifierChecker<UExp, M>>
    Collapse<Fresh<UExp>, Arg, BaseMarker<M>> for Euf<Q, Th>
{
    fn collapse(&mut self, fresh: Fresh<UExp>, _: &mut Arg, ctx: ExprContext<UExp>) -> UExp {
        let mut added = false;
        let id = self.egraph.add(fresh.name.into(), Children::new(), |_, _| {
            added = true;
            EClass::Uninterpreted(fresh.sort)
        });
        let res = UExp::new(if added { id } else { Id::MAX }, fresh.sort);
        if added && !matches!(ctx, ExprContext::AssertEq(_)) {
            self.q.check_new_exp(res)
        }
        res
    }

    fn placeholder(&self, fresh: &Fresh<UExp>) -> UExp {
        UExp::new(Id::MAX, fresh.sort)
    }
}

impl<
    'a,
    'b,
    Q: Incremental,
    M,
    I: DistinctElts<Exp = Exp<Th::Exp>>,
    A: SatTheoryArgR<M: TupleExtract<M, PushInfo>>,
    Th: FullEufTh<A>,
> Collapse<RawDistinct<I>, A, BaseMarker<M>> for Euf<Q, Th>
{
    fn collapse(
        &mut self,
        RawDistinct(exps): RawDistinct<I>,
        acts: &mut A,
        ctx: ExprContext<BoolExp>,
    ) -> BoolExp {
        if ctx != ExprContext::Approx(false) && ctx != ExprContext::AssertEq(BoolExp::TRUE) {
            let mut c: Conjunction = acts.new_junction();
            c.extend(
                pairwise_sym(exps)
                    .map(|(e1, e2)| !self.collapse(Eq(e1, e2), acts, ExprContext::Exact)),
            );
            return acts.collapse_bool(c, ctx);
        }

        let mut exps_iter = exps.iter();

        let Some(e0) = exps_iter.next() else {
            return acts.collapse_const(true, ctx);
        };

        let Exp::Right(_) = e0 else {
            let b0 = e0.downcast().unwrap();
            let mut bools = exps_iter.map(|exp| exp.downcast().unwrap());
            let Some(b1) = bools.next() else {
                return acts.collapse_const(true, ctx);
            };
            return if let Some(_) = bools.next() {
                return acts.collapse_const(false, ctx);
            } else {
                acts.xor(b0, b1, ctx)
            };
        };

        let distinct_sym = acts.intern_mut().symbols.gen_sym("distinguisher");
        self.distinct_gensym += 1;
        let b = if ctx == ExprContext::AssertEq(BoolExp::TRUE) {
            BoolExp::TRUE
        } else {
            let b = BoolExp::unknown(Lit::new(acts.new_var_default(), true));
            acts.log_def(b, DISTINCT_SYM, exps.iter());
            b
        };
        for exp in exps.iter() {
            let id = self.id_for_exp(exp, acts, false);
            let mut added = false;
            let id = self
                .egraph
                .add(distinct_sym.into(), Children::from_slice(&[id]), |_, _| {
                    added = true;
                    EClass::Singleton(!b)
                });
            if added {
                acts.log_def(
                    UExp::new(id, BOOL_SORT),
                    DISTINGUISHER_SYM,
                    [exp].into_iter(),
                );
            } else {
                return acts.collapse_const(false, ctx);
            }
        }
        b
    }

    fn placeholder(&self, _: &RawDistinct<I>) -> BoolExp {
        BoolExp::TRUE
    }
}

impl<'a, M, Q: Incremental, A: SatTheoryArgR<M: TupleExtract<M, PushInfo>>, Th: FullEufTh<A>>
    Collapse<Eq<Exp<Th::Exp>>, A, BaseMarker<M>> for Euf<Q, Th>
{
    fn collapse(
        &mut self,
        Eq(e1, e2): Eq<Exp<Th::Exp>>,
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

    fn placeholder(&self, _: &Eq<Exp<Th::Exp>>) -> BoolExp {
        BoolExp::TRUE
    }
}

pub struct UFn<I: Iterator>(Symbol, I, Sort);

impl<'a, I: Iterator> UFn<I> {
    pub fn new_unchecked(f: Symbol, children: I, sort: Sort) -> Self {
        UFn(f, children, sort)
    }
}

impl<I: Iterator> CollapseOut for UFn<I>
where
    I::Item: ExpLike,
{
    type Out = I::Item;
}

impl<
    M1,
    M2,
    Q: Incremental + QuantifierChecker<Exp<Th::Exp>, M1>,
    I: Iterator<Item = Exp<Th::Exp>> + Clone,
    A: SatTheoryArgR<M: TupleExtract<M2, PushInfo>>,
    Th: FullEufTh<A>,
> Collapse<UFn<I>, A, BaseMarker<(M1, M2)>> for Euf<Q, Th>
{
    fn collapse(
        &mut self,
        UFn(f, exp_children, sort): UFn<I>,
        acts: &mut A,
        ctx: ExprContext<Exp<Th::Exp>>,
    ) -> Exp<Th::Exp> {
        let children = self.resolve_children(exp_children.clone(), acts);
        let (res, added) = self.sorted_fn(f.into(), children, sort, ctx, acts);
        if added {
            let call_added = self.q.check_call(f, exp_children, res);
            if !call_added && !matches!(ctx, ExprContext::AssertEq(_)) {
                self.q.check_new_exp(res);
            }
        }
        res
    }

    fn placeholder(&self, &UFn(_, _, sort): &UFn<I>) -> Exp<Th::Exp> {
        if sort == BOOL_SORT {
            BoolExp::TRUE.upcast()
        } else {
            Exp::Right(UExp { id: Id::MAX, sort })
        }
    }
}

type FnSortSolver<Th, R> =
    SolverWithBound<Solver<Th, R>, HashMap<Symbol, Bound<<Th as FullTheory<R>>::Exp, FnSort>>>;

#[derive(Default)]
pub struct UFnPf;

impl<
    M,
    MExp,
    MEq,
    MS,
    Th: Incremental
        + FullTheory<R>
        + TopLevelCollapse<Th::Exp, MExp, R>
        + TopLevelCollapse<Eq<Th::Exp>, MEq, R>,
    R: Recorder,
> ParserFragment<Th::Exp, FnSortSolver<Th, R>, (M, MExp, MEq, MS)> for UFnPf
where
    Solver<Th, R>: for<'a> SolverCollapse<UFn<UFnIter<'a, MS, Exp, Th::Exp>>, M>,
    Th::Exp: SuperExp<Exp, MS>,
{
    fn supports(&self, _: Symbol) -> bool {
        true
    }

    fn handle_non_terminal(
        &self,
        f: Symbol,
        children: &mut [Th::Exp],
        solver: &mut FnSortSolver<Th, R>,
        ctx: ExprContext<Th::Exp>,
    ) -> Result<Th::Exp, AddSexpError> {
        use AddSexpError::*;
        solver
            .solver
            .th
            .arg
            .recorder
            .dep_checker_act(dep_checker::Reference(f));
        match solver.bound.get(&f) {
            None => Err(Unbound),
            Some(Bound::Const(c)) => {
                if !children.is_empty() {
                    return Err(ExtraArgument { expected: 0 });
                }
                if let ExprContext::AssertEq(exp) = ctx {
                    if exp.sort() == c.sort() {
                        let cur = *c;
                        let _ = solver.solver.assert_eq::<MExp, MEq, Th::Exp>(exp, cur);
                        return Ok(exp);
                    }
                }
                Ok(*c)
            }
            Some(Bound::Fn(def)) => {
                index_iter(children)
                    .zip(def.args())
                    .try_for_each(|(arg, sort)| {
                        let arg = arg.expect_sort(*sort)?;
                        let _: Exp = arg
                            .downcast()
                            .ok_or(AddSexpError::custom("invalid sort being passed in"))?;
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
                let res = SolverCollapse::<UFn<_>, M>::collapse_in_ctx(
                    &mut solver.solver,
                    UFn(f, UFnIter(children.iter(), PhantomData), def.ret()),
                    ctx.downcast(),
                );
                Ok(SuperExp::from_upcast(res))
            }
        }
    }
}

#[perfect_derive(Clone)]
struct UFnIter<'a, M, Sub, Super: SuperExp<Sub, M>>(Iter<'a, Super>, PhantomData<(M, Sub)>);

impl<'a, M, Sub, Super: SuperExp<Sub, M> + Copy> Iterator for UFnIter<'a, M, Sub, Super> {
    type Item = Sub;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|x| Sub::from_downcast(*x).unwrap())
    }
}

#[derive(Default)]
pub struct EgraphPf<I>(I);

impl<
    R: Recorder,
    E: SuperExp<Exp<Th::Exp>, MS> + ExpLike + Copy,
    Q: Incremental,
    Th: for<'a> FullEufTh<TheoryArg<'a, S::LevelMarker, R>>,
    S: TupleExtract<MS, Euf<Q, Th>>
        + FullTheory<R>
        + Incremental<LevelMarker: TupleExtract<LeftMarker<LeftMarker<MS>>, PushInfo>>,
    M,
    MS,
    I: ParserFragment<E, FnSortSolver<S, R>, M>,
> ParserFragment<E, FnSortSolver<S, R>, (M, MS, Q, Th)> for EgraphPf<I>
{
    fn supports(&self, s: Symbol) -> bool {
        self.0.supports(s)
    }
    fn handle_terminal(
        &self,
        x: SexpTerminal,
        solver: &mut FnSortSolver<S, R>,
        ctx: ExprContext<E>,
    ) -> PfResult<E> {
        self.0.handle_terminal(x, solver, ctx)
    }

    fn handle_non_terminal(
        &self,
        f: Symbol,
        children: &mut [E],
        solver: &mut FnSortSolver<S, R>,
        ctx: ExprContext<E>,
    ) -> Result<E, AddSexpError> {
        let Some(children_ids) = solver.solver.open(
            |s, acts| {
                let euf: &mut Euf<Q, Th> = s.tuple_extract_mut();
                children
                    .iter()
                    .map(|&x| Some(euf.id_for_exp(x.downcast()?, acts, true)))
                    .collect::<Option<Children>>()
            },
            None,
        ) else {
            return self.0.handle_non_terminal(f, children, solver, ctx);
        };

        let mut enode = SymbolLang::new(f.into(), children_ids);

        let euf: &Euf<Q, Th> = solver.solver.th.deref().tuple_extract();

        if let Some(existing_id) = euf.egraph.lookup(&mut enode) {
            let res: Exp<Th::Exp> = euf.id_to_exp(existing_id);
            return Ok(E::from_upcast(res));
        }

        let ctx = match ctx {
            ExprContext::AssertEq(x) => ExprContext::AssertEq(x),
            _ => ExprContext::Exact,
        };

        let res = self.0.handle_non_terminal(f, children, solver, ctx);

        if let Ok(Some(res)) = res.as_ref().map(|x| Exp::from_downcast(*x)) {
            solver.solver.open(
                |euf, acts| {
                    let euf: &mut Euf<Q, Th> = euf.tuple_extract_mut();
                    euf.sorted_fn(
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
