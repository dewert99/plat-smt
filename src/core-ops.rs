use crate::collapse::{Collapse, CollapseOut, ExprContext};
use crate::exp::{EitherExp, Fresh};
use crate::intern::{Symbol, DISTINCT_SYM, EQ_SYM, IF_SYM, ITE_SYM};
use crate::parser_fragment::{exact_args, index_iter, mandatory_args, ParserFragment};
use crate::solver::{ReuseMem, SolverCollapse};
use crate::tseitin::{andor_sub_ctx, BoolOpPf, SatTheoryArgT, TseitenMarker};
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
pub struct IteMarker<Eq, Fresh>(Eq, Fresh);
impl<
        'a,
        Exp: ExpLike,
        A: SatTheoryArgT<'a>,
        EqM,
        FM,
        Th: Collapse<Eq<Exp>, A, EqM> + Collapse<Fresh<Exp>, A, FM>,
    > Collapse<Ite<Exp>, A, IteMarker<EqM, FM>> for Th
{
    fn collapse(&mut self, t: Ite<Exp>, acts: &mut A, ctx: ExprContext<Exp>) -> Exp {
        match t.0.to_lit() {
            Ok(i) => {
                let res = match ctx {
                    ExprContext::AssertEq(x) if x.sort() == t.1.sort() => x,
                    _ => {
                        let res = self.collapse(
                            Fresh::new(acts.intern_mut().symbols.gen_sym("ite"), t.1.sort())
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
                match eq1.to_lit() {
                    Ok(l) => acts.add_clause_unchecked([!i, l]),
                    Err(true) => {}
                    Err(false) => acts.add_clause_unchecked([!i]),
                }
                match eq2.to_lit() {
                    Ok(l) => acts.add_clause_unchecked([i, l]),
                    Err(true) => {}
                    Err(false) => acts.add_clause_unchecked([i]),
                }
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

pub type CoreOpsPf = (BoolOpPf, (EqPf, (ItePf, DistinctPf)));
