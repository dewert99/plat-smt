use crate::collapse::{BaseMarker, Collapse, CollapseOut, ExprContext, LeftMarker, RightMarker};
use crate::exp::{EitherExp, Fresh};
use crate::intern::{Symbol, DISTINCT_SYM, EQ_SYM, IF_SYM, ITE_SYM};
use crate::parser_fragment::{exact_args, index_iter, mandatory_args, ParserFragment};
use crate::solver::{ReuseMem, SolverCollapse};
use crate::tseitin::{andor_sub_ctx, BoolOpPf, SatTheoryArgT, TseitenMarker};
use crate::util::{extend_result, pairwise_sym};
use crate::{AddSexpError, BoolExp, Conjunction, ExpLike, SubExp, SuperExp};
use core::iter::Copied;
use core::marker::PhantomData;
use core::ops::RangeBounds;
use core::slice::Iter;
use perfect_derive::perfect_derive;

pub struct Eq<Exp>(pub(crate) Exp, pub(crate) Exp);

impl<'a, Exp: ExpLike> Eq<Exp> {
    pub fn try_new(t: Exp, e: Exp) -> Result<Self, AddSexpError> {
        if t.sort() == e.sort() {
            Ok(Eq(t, e))
        } else {
            Err(AddSexpError::SortMismatch {
                actual: e.sort(),
                expected: t.sort(),
                arg_n: 1,
            })
        }
    }

    pub fn new_unchecked(t: Exp, e: Exp) -> Self {
        Eq(t, e)
    }
}

impl<Exp> CollapseOut for Eq<Exp> {
    type Out = BoolExp;
}

pub trait DistinctElts: Copy {
    type Exp: ExpLike;
    fn index(self, x: usize) -> Self::Exp;

    fn len(self) -> usize;

    fn first(self) -> Option<Self::Exp> {
        if self.len() > 0 {
            Some(self.index(0))
        } else {
            None
        }
    }

    fn iter(self) -> impl Iterator<Item = Self::Exp> + Clone + use<Self> {
        (0..self.len()).into_iter().map(move |x| self.index(x))
    }
}

impl<'a, Exp: ExpLike> DistinctElts for &'a [Exp] {
    type Exp = Exp;
    fn index(self, x: usize) -> Self::Exp {
        self[x]
    }

    fn len(self) -> usize {
        self.len()
    }
}

#[perfect_derive(Copy, Clone)]
pub(crate) struct DowncastDistinct<Base: DistinctElts, M, Sub: SubExp<Base::Exp, M>>(
    Base,
    PhantomData<(M, Sub)>,
);

impl<Base: DistinctElts, M, Sub: SubExp<Base::Exp, M> + ExpLike> DistinctElts
    for DowncastDistinct<Base, M, Sub>
{
    type Exp = Sub;

    fn index(self, x: usize) -> Self::Exp {
        Sub::from_downcast(self.0.index(x)).unwrap()
    }

    fn len(self) -> usize {
        self.0.len()
    }
}

pub struct RawDistinct<I: DistinctElts>(pub(crate) I);
pub type Distinct<'a, Exp> = RawDistinct<&'a [Exp]>;

impl<'a, Exp: ExpLike> Distinct<'a, Exp> {
    pub fn try_new(x: &'a [Exp]) -> Result<Self, AddSexpError> {
        let mut children = index_iter(x);
        if let Some(x) = children.next() {
            let sort = x.exp().sort();
            children.try_for_each(|x| {
                x.expect_sort(sort)?;
                Ok::<_, AddSexpError>(())
            })?;
        };
        Ok(Self::new_unchecked(x))
    }

    pub fn new_unchecked(x: &'a [Exp]) -> Self {
        RawDistinct(x)
    }
}

impl<I: DistinctElts> CollapseOut for RawDistinct<I> {
    type Out = BoolExp;
}

impl<
        I: DistinctElts<Exp = EitherExp<Exp1, Exp2>>,
        Exp1: ExpLike,
        Exp2: ExpLike,
        Arg,
        M1,
        M2,
        Th1: Collapse<
            RawDistinct<DowncastDistinct<I, LeftMarker<BaseMarker>, Exp1>>,
            Arg,
            BaseMarker<M1>,
        >,
        Th2: Collapse<
            RawDistinct<DowncastDistinct<I, RightMarker<BaseMarker>, Exp2>>,
            Arg,
            BaseMarker<M2>,
        >,
    > Collapse<RawDistinct<I>, Arg, BaseMarker<(M1, M2)>> for (Th1, Th2)
{
    fn collapse(
        &mut self,
        t: RawDistinct<I>,
        acts: &mut Arg,
        ctx: ExprContext<BoolExp>,
    ) -> BoolExp {
        if t.0.len() == 0 {
            return BoolExp::FALSE;
        };
        let example = t.0.index(0);
        match example {
            EitherExp::Left(_) => {
                self.0
                    .collapse(RawDistinct(DowncastDistinct(t.0, PhantomData)), acts, ctx)
            }
            EitherExp::Right(_) => {
                self.0
                    .collapse(RawDistinct(DowncastDistinct(t.0, PhantomData)), acts, ctx)
            }
        }
    }

    fn placeholder(&self, t: &RawDistinct<I>) -> BoolExp {
        BoolExp::FALSE
    }
}

pub trait DefaultDistinct {}

impl<
        'a,
        I: DistinctElts,
        Arg: SatTheoryArgT<'a>,
        Th: Collapse<Eq<I::Exp>, Arg, BaseMarker> + DefaultDistinct,
    > Collapse<RawDistinct<I>, Arg, BaseMarker> for Th
{
    fn collapse(
        &mut self,
        t: RawDistinct<I>,
        acts: &mut Arg,
        ctx: ExprContext<BoolExp>,
    ) -> BoolExp {
        let mut conj: Conjunction = acts.new_junction();
        conj.extend(
            pairwise_sym(t.0).map(|(e0, e1)| {
                !self.collapse(Eq(e0, e1), acts, andor_sub_ctx(ctx, true).negate())
            }),
        );
        acts.collapse_bool(conj, ctx)
    }

    fn placeholder(&self, t: &RawDistinct<I>) -> BoolExp {
        BoolExp::FALSE
    }
}

pub struct Ite<Exp>(pub(crate) BoolExp, pub(crate) Exp, pub(crate) Exp);

impl<'a, Exp: ExpLike> Ite<Exp> {
    pub fn try_new(i: BoolExp, t: Exp, e: Exp) -> Result<Self, AddSexpError> {
        if t.sort() == e.sort() {
            Ok(Ite(i, t, e))
        } else {
            Err(AddSexpError::SortMismatch {
                actual: e.sort(),
                expected: t.sort(),
                arg_n: 2,
            })
        }
    }

    pub fn new_unchecked(i: BoolExp, t: Exp, e: Exp) -> Self {
        Ite(i, t, e)
    }
}

impl<Exp: ExpLike> CollapseOut for Ite<Exp> {
    type Out = Exp;
}

pub trait DefaultIte {}

pub struct IteMarker<Eq, Fresh>(Eq, Fresh);
impl<
        'a,
        Exp: ExpLike,
        A: SatTheoryArgT<'a>,
        M,
        Th: Collapse<Eq<Exp>, A, BaseMarker<M>> + Collapse<Fresh<Exp>, A, BaseMarker> + DefaultIte,
    > Collapse<Ite<Exp>, A, BaseMarker<M>> for Th
{
    fn collapse(&mut self, t: Ite<Exp>, acts: &mut A, ctx: ExprContext<Exp>) -> Exp {
        match t.0.to_lit() {
            Ok(_) => {
                let res = match ctx {
                    ExprContext::AssertEq(x) if x.sort() == t.1.sort() => x,
                    _ => {
                        let res = self.collapse(
                            Fresh::new_with_sort(
                                acts.intern_mut().symbols.gen_sym("ite"),
                                t.1.sort(),
                            )
                            .unwrap(),
                            acts,
                            ExprContext::Exact,
                        );
                        let args = [
                            EitherExp::Left(t.0),
                            EitherExp::Right(t.1),
                            EitherExp::Right(t.2),
                        ];
                        acts.log_def(res, ITE_SYM, args.iter().copied());
                        res
                    }
                };

                let eq1 = self.collapse(Eq::new_unchecked(res, t.1), acts, ExprContext::Exact);
                let eq2 = self.collapse(Eq::new_unchecked(res, t.2), acts, ExprContext::Exact);
                acts.add_clause([!t.0, eq1]);
                acts.add_clause([t.0, eq2]);
                res
            }
            Err(true) => t.1,
            Err(false) => t.2,
        }
    }

    fn placeholder(&self, t: &Ite<Exp>) -> Exp {
        t.1
    }
}

impl<
        Exp1: ExpLike,
        Exp2: ExpLike,
        Arg,
        M1,
        M2,
        Th1: Collapse<Ite<Exp1>, Arg, M1>,
        Th2: Collapse<Ite<Exp2>, Arg, M2>,
    > Collapse<Ite<EitherExp<Exp1, Exp2>>, Arg, (M1, M2)> for (Th1, Th2)
{
    fn collapse(
        &mut self,
        t: Ite<EitherExp<Exp1, Exp2>>,
        acts: &mut Arg,
        ctx: ExprContext<EitherExp<Exp1, Exp2>>,
    ) -> EitherExp<Exp1, Exp2> {
        match t {
            Ite(i, EitherExp::Left(t), EitherExp::Left(e)) => {
                EitherExp::Left(self.0.collapse(Ite(i, t, e), acts, ctx.downcast()))
            }
            Ite(i, EitherExp::Right(t), EitherExp::Right(e)) => {
                EitherExp::Right(self.1.collapse(Ite(i, t, e), acts, ctx.downcast()))
            }
            _ => unreachable!("ite branches have different types"),
        }
    }

    fn placeholder(&self, t: &Ite<EitherExp<Exp1, Exp2>>) -> EitherExp<Exp1, Exp2> {
        t.1
    }
}

#[derive(Default)]
pub struct EqPf;
impl<
        'a,
        M1,
        M2,
        Exp: ExpLike + SuperExp<BoolExp, M1>,
        S: SolverCollapse<Eq<Exp>, M2>
            + SolverCollapse<Conjunction, TseitenMarker>
            + ReuseMem<Conjunction>,
    > ParserFragment<Exp, S, (M1, M2)> for EqPf
{
    fn supports(&self, s: Symbol) -> bool {
        s == EQ_SYM
    }
    fn handle_non_terminal(
        &self,
        _: Symbol,
        children: &mut [Exp],
        solver: &mut S,
        ctx: ExprContext<Exp>,
    ) -> Result<Exp, AddSexpError> {
        let mut children = index_iter(children);
        let mut c: Conjunction = solver.reuse_mem();
        let [exp1] = mandatory_args(&mut children)?;
        let exp1 = exp1.exp();
        let inner_ctx = andor_sub_ctx(ctx.downcast(), true);
        extend_result(
            &mut c,
            children.map(|exp2| {
                Ok(solver.collapse_in_ctx(
                    Eq::new_unchecked(exp1, exp2.expect_sort(exp1.sort())?),
                    inner_ctx,
                ))
            }),
        )?;
        Ok(solver.collapse_in_ctx(c, ctx.downcast()).upcast())
    }
    fn sub_ctx(&self, _: Symbol, children: &[Exp], ctx: ExprContext<Exp>) -> ExprContext<Exp> {
        match (ctx.downcast(), &children) {
            (ExprContext::AssertEq(BoolExp::TRUE), &[child, ..]) => {
                ExprContext::AssertEq(*child).into()
            }
            _ => ExprContext::Exact.into(),
        }
    }
}

#[derive(Default)]
pub struct DistinctPf;
impl<
        'a,
        M1,
        M2,
        Exp: ExpLike + SuperExp<BoolExp, M1>,
        S: for<'b> SolverCollapse<Distinct<'b, Exp>, M2>,
    > ParserFragment<Exp, S, (M1, M2)> for DistinctPf
{
    fn supports(&self, s: Symbol) -> bool {
        s == DISTINCT_SYM
    }
    fn handle_non_terminal(
        &self,
        _: Symbol,
        children: &mut [Exp],
        solver: &mut S,
        ctx: ExprContext<Exp>,
    ) -> Result<Exp, AddSexpError> {
        Ok(solver
            .collapse_in_ctx(Distinct::try_new(children)?, ctx.downcast())
            .upcast())
    }
}

#[derive(Default)]
pub struct ItePf;
impl<'a, M1, M2, Exp: ExpLike + SuperExp<BoolExp, M1>, S: SolverCollapse<Ite<Exp>, M2>>
    ParserFragment<Exp, S, (M1, M2)> for ItePf
{
    fn supports(&self, s: Symbol) -> bool {
        s == ITE_SYM || s == IF_SYM
    }
    fn handle_non_terminal(
        &self,
        _: Symbol,
        children: &mut [Exp],
        solver: &mut S,
        ctx: ExprContext<Exp>,
    ) -> Result<Exp, AddSexpError> {
        let [i, t, e] = exact_args(&mut index_iter(children))?;
        Ok(solver.collapse_in_ctx(Ite::try_new(i.downcast()?, t.exp(), e.exp())?, ctx))
    }
}

pub trait DefaultEq {}

impl<'a, Th1: Collapse<Eq<E1>, A, M1>, Th2: Collapse<Eq<E2>, A, M2>, E1, E2, M1, M2, A>
    Collapse<Eq<EitherExp<E1, E2>>, A, (M1, M2)> for (Th1, Th2)
{
    fn collapse(
        &mut self,
        eq: Eq<EitherExp<E1, E2>>,
        acts: &mut A,
        ctx: ExprContext<BoolExp>,
    ) -> BoolExp {
        match (eq.0, eq.1) {
            (EitherExp::Left(eq0), EitherExp::Left(eq1)) => {
                self.0.collapse(Eq(eq0, eq1), acts, ctx.downcast()).upcast()
            }
            (EitherExp::Right(eq0), EitherExp::Right(eq1)) => {
                self.1.collapse(Eq(eq0, eq1), acts, ctx.downcast()).upcast()
            }
            _ => unreachable!(),
        }
    }

    fn placeholder(&self, _: &Eq<EitherExp<E1, E2>>) -> BoolExp {
        BoolExp::TRUE
    }
}

pub type CoreOpsPf = (BoolOpPf, (EqPf, (ItePf, DistinctPf)));
