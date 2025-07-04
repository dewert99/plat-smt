use crate::collapse::{CollapseOut, ExprContext};
use crate::intern::{Symbol, DISTINCT_SYM, EQ_SYM, IF_SYM, ITE_SYM};
use crate::parser_fragment::{exact_args, index_iter, mandatory_args, ParserFragment, PfResult};
use crate::solver::{ReuseMem, SolverCollapse};
use crate::tseitin::{andor_sub_ctx, BoolOpPf, TseitenMarker};
use crate::util::extend_result;
use crate::{AddSexpError, BoolExp, Conjunction, ExpLike, SubExp, SuperExp};

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

pub struct Distinct<'a, Exp>(pub(crate) &'a [Exp]);

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
        Ok(Distinct(x))
    }

    pub fn new_unchecked(x: &'a [Exp]) -> Self {
        Distinct(x)
    }
}

impl<'a, Exp> CollapseOut for Distinct<'a, Exp> {
    type Out = BoolExp;
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
    fn handle_non_terminal(
        &self,
        f: Symbol,
        children: &mut [Exp],
        solver: &mut S,
        ctx: ExprContext<Exp>,
    ) -> PfResult<Exp> {
        (f == EQ_SYM).then(|| {
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
        })
    }
    fn sub_ctx(
        &self,
        f: Symbol,
        children: &[Exp],
        ctx: ExprContext<Exp>,
    ) -> Option<ExprContext<Exp>> {
        (f == EQ_SYM).then(|| match (ctx.downcast(), &children) {
            (ExprContext::AssertEq(BoolExp::TRUE), &[child, ..]) => {
                ExprContext::AssertEq(*child).into()
            }
            _ => ExprContext::Exact.into(),
        })
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
    fn handle_non_terminal(
        &self,
        f: Symbol,
        children: &mut [Exp],
        solver: &mut S,
        ctx: ExprContext<Exp>,
    ) -> PfResult<Exp> {
        (f == DISTINCT_SYM).then(|| {
            Ok(solver
                .collapse_in_ctx(Distinct::try_new(children)?, ctx.downcast())
                .upcast())
        })
    }
}

#[derive(Default)]
pub struct ItePf;
impl<'a, M1, M2, Exp: ExpLike + SuperExp<BoolExp, M1>, S: SolverCollapse<Ite<Exp>, M2>>
    ParserFragment<Exp, S, (M1, M2)> for ItePf
{
    fn handle_non_terminal(
        &self,
        f: Symbol,
        children: &mut [Exp],
        solver: &mut S,
        ctx: ExprContext<Exp>,
    ) -> PfResult<Exp> {
        (f == IF_SYM || f == ITE_SYM).then(|| {
            let [i, t, e] = exact_args(&mut index_iter(children))?;
            Ok(solver.collapse_in_ctx(Ite::try_new(i.downcast()?, t.exp(), e.exp())?, ctx))
        })
    }
}

pub type CoreOpsPf = (BoolOpPf, (EqPf, (ItePf, DistinctPf)));
