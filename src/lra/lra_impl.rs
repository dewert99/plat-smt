use crate::collapse::{BaseMarker, Collapse, CollapseOut, ExprContext, SpecExp};
use crate::core_ops::{DefaultDistinct, DefaultEq, DefaultIte, Eq};
use crate::exp::Fresh;
use crate::full_theory::FullTheory;
use crate::intern::{Symbol, ADD_SYM, GE_SYM, GT_SYM, LE_SYM, LT_SYM, SUB_SYM};
use crate::lra::bound::EpsilonRational;
use crate::lra::lra::Lra;
use crate::lra::tableau::{NumExp, Sum};
use crate::parser::SexpTerminal;
use crate::parser_fragment::{index_iter, mandatory_args, ParserFragment, PfResult};
use crate::recorder::Recorder;
use crate::solver::{ReuseMem, SolverCollapse};
use crate::theory::TheoryArgT;
use crate::tseitin::{andor_sub_ctx, SatTheoryArgT, TseitenMarker};
use crate::util::extend_result;
use crate::AddSexpError::CustomSexpErr;
use crate::{AddSexpError, BoolExp, Conjunction, ExpLike, Solver, SubExp, SuperExp};
use alloc::borrow::Cow;
use core::num::TryFromIntError;
use lazy_rational::Rational32;

pub struct NumSpec;

impl SpecExp<NumSpec, BaseMarker> for Lra {
    type SpecExp = NumExp;
}

impl<'a, Arg: SatTheoryArgT<'a>> Collapse<NumExp, Arg, BaseMarker> for Lra {
    fn collapse(&mut self, t: NumExp, _arg: &mut Arg, _: ExprContext<NumExp>) -> NumExp {
        if let Some(epsilon_def) = self.epsilon_def {
            let EpsilonRational { base, epsilon } = self.get_value(t);
            NumExp::from_rational(base + epsilon * epsilon_def)
        } else {
            t
        }
    }

    fn placeholder(&self, _: &NumExp) -> NumExp {
        NumExp::ZERO
    }
}

impl<'a, Arg> Collapse<Fresh<NumExp>, Arg, BaseMarker> for Lra {
    fn collapse(&mut self, _: Fresh<NumExp>, _: &mut Arg, _: ExprContext<NumExp>) -> NumExp {
        self.fresh_exp()
    }

    fn placeholder(&self, _fresh: &Fresh<NumExp>) -> NumExp {
        NumExp::ZERO
    }
}

pub struct Inequality {
    lower: NumExp,
    upper: NumExp,
    strict: bool,
}

impl Inequality {
    pub fn lt(lower: NumExp, upper: NumExp) -> Inequality {
        Inequality {
            lower,
            upper,
            strict: true,
        }
    }

    pub fn le(lower: NumExp, upper: NumExp) -> Inequality {
        Inequality {
            lower,
            upper,
            strict: false,
        }
    }

    pub fn gt(upper: NumExp, lower: NumExp) -> Inequality {
        Inequality {
            lower,
            upper,
            strict: true,
        }
    }

    pub fn ge(upper: NumExp, lower: NumExp) -> Inequality {
        Inequality {
            lower,
            upper,
            strict: false,
        }
    }
}

impl CollapseOut for Inequality {
    type Out = BoolExp;
}

impl<'a, A: SatTheoryArgT<'a>> Collapse<Inequality, A, BaseMarker> for Lra {
    fn collapse(&mut self, ineq: Inequality, acts: &mut A, _ctx: ExprContext<BoolExp>) -> BoolExp {
        if let Some(x) = ineq.lower.try_into_rational() {
            self.bind_lower_bound(ineq.upper, x, ineq.strict, acts)
        } else if let Some(x) = ineq.upper.try_into_rational() {
            !self.bind_lower_bound(ineq.lower, x, !ineq.strict, acts)
        } else {
            let diff = self.reuse_sum() + ineq.upper - ineq.lower;
            let diff = self.bind_sum(diff, acts);
            self.bind_lower_bound(diff, Rational32::ZERO, ineq.strict, acts)
        }
    }

    fn placeholder(&self, _: &Inequality) -> BoolExp {
        BoolExp::TRUE
    }
}

#[derive(Default)]
pub struct InequalityPf<const S: bool, const L: bool>;

impl<
        M1,
        M2,
        M3,
        Exp: ExpLike + SuperExp<BoolExp, M1> + SuperExp<NumExp, M2>,
        Slv: SolverCollapse<Inequality, M3>
            + SolverCollapse<Conjunction, TseitenMarker>
            + ReuseMem<Conjunction>,
        const S: bool,
        const L: bool,
    > ParserFragment<Exp, Slv, (M1, M2, M3)> for InequalityPf<S, L>
{
    fn supports(&self, s: Symbol) -> bool {
        s == match (L, S) {
            (true, true) => LT_SYM,
            (true, false) => LE_SYM,
            (false, true) => GT_SYM,
            (false, false) => GE_SYM,
        }
    }
    fn handle_non_terminal(
        &self,
        _: Symbol,
        children: &mut [Exp],
        solver: &mut Slv,
        ctx: ExprContext<Exp>,
    ) -> Result<Exp, AddSexpError> {
        let mut children = index_iter(children);
        let mut c: Conjunction = solver.reuse_mem();
        let [exp1] = mandatory_args(&mut children)?;
        let mut last_exp: NumExp = exp1.downcast()?;
        let inner_ctx = andor_sub_ctx(ctx.downcast(), true);
        extend_result(
            &mut c,
            children.map(|exp2| {
                let next_exp = exp2.downcast()?;
                let (lower, upper) = if L {
                    (last_exp, next_exp)
                } else {
                    (next_exp, last_exp)
                };
                last_exp = next_exp;
                Ok(solver.collapse_in_ctx(
                    Inequality {
                        lower,
                        upper,
                        strict: S,
                    },
                    inner_ctx,
                ))
            }),
        )?;
        Ok(solver.collapse_in_ctx(c, ctx.downcast()).upcast())
    }
}

pub type LtPf = InequalityPf<true, true>;
pub type LePf = InequalityPf<true, false>;
pub type GtPf = InequalityPf<false, true>;
pub type GePf = InequalityPf<false, false>;

impl<'a, A: SatTheoryArgT<'a>> Collapse<Eq<NumExp>, A, BaseMarker> for Lra {
    fn collapse(&mut self, eq: Eq<NumExp>, acts: &mut A, ctx: ExprContext<BoolExp>) -> BoolExp {
        let le = self.collapse(Inequality::le(eq.0, eq.1), acts, ExprContext::Exact);
        let ge = self.collapse(Inequality::ge(eq.0, eq.1), acts, ExprContext::Exact);
        let j = acts.new_junction() & le & ge;
        acts.collapse_bool(j, ctx)
    }

    fn placeholder(&self, _: &Eq<NumExp>) -> BoolExp {
        BoolExp::TRUE
    }
}

impl DefaultEq for Lra {}

impl<T, R: Recorder> ReuseMem<Sum> for Solver<(T, Lra), R>
where
    (T, Lra): FullTheory<R>,
{
    fn reuse_mem(&mut self) -> Sum {
        self.open(|th, _| th.1.reuse_sum(), Sum::default())
    }
}

impl CollapseOut for Sum {
    type Out = NumExp;
}
impl<'a, A: TheoryArgT> Collapse<Sum, A, BaseMarker> for Lra {
    fn collapse(&mut self, sum: Sum, acts: &mut A, _ctx: ExprContext<NumExp>) -> NumExp {
        self.bind_sum(sum, acts)
    }

    fn placeholder(&self, _: &Sum) -> NumExp {
        NumExp::ZERO
    }
}

#[derive(Default)]
pub struct AddPf;

impl<M1, M2, Exp: ExpLike + SuperExp<NumExp, M1>, Slv: SolverCollapse<Sum, M2> + ReuseMem<Sum>>
    ParserFragment<Exp, Slv, (M1, M2)> for AddPf
{
    fn supports(&self, s: Symbol) -> bool {
        s == ADD_SYM
    }
    fn handle_non_terminal(
        &self,
        _: Symbol,
        children: &mut [Exp],
        solver: &mut Slv,
        ctx: ExprContext<Exp>,
    ) -> Result<Exp, AddSexpError> {
        let children = index_iter(children);
        let mut sum = solver.reuse_mem();
        for child in children {
            sum += child.downcast()?;
        }
        Ok(solver.collapse_in_ctx(sum, ctx.downcast()).upcast())
    }
}

#[derive(Default)]
pub struct SubPf;

impl<M1, M2, Exp: ExpLike + SuperExp<NumExp, M1>, Slv: SolverCollapse<Sum, M2> + ReuseMem<Sum>>
    ParserFragment<Exp, Slv, (M1, M2)> for SubPf
{
    fn supports(&self, s: Symbol) -> bool {
        s == SUB_SYM
    }
    fn handle_non_terminal(
        &self,
        _: Symbol,
        children: &mut [Exp],
        solver: &mut Slv,
        ctx: ExprContext<Exp>,
    ) -> Result<Exp, AddSexpError> {
        let mut children = index_iter(children);
        let [arg] = mandatory_args(&mut children)?;
        let arg = arg.downcast()?;
        let arg2 = children.next();
        if let Some(arg2) = arg2 {
            let mut sum = solver.reuse_mem() + arg - arg2.downcast()?;
            for child in children {
                sum -= child.downcast()?;
            }
            Ok(solver.collapse_in_ctx(sum, ctx.downcast()).upcast())
        } else {
            Ok((-arg).upcast())
        }
    }
}

impl TryFrom<u128> for NumExp {
    type Error = TryFromIntError;

    fn try_from(i: u128) -> Result<NumExp, TryFromIntError> {
        Ok(NumExp::from_int(i.try_into()?))
    }
}

#[derive(Default)]
pub struct NumPf;

impl<M1, M2, Exp: ExpLike + SuperExp<Slv::SpecExp, M1>, Slv: SpecExp<NumSpec, M2>>
    ParserFragment<Exp, Slv, (M1, M2)> for NumPf
where
    Slv::SpecExp: TryFrom<u128>,
{
    fn supports(&self, _: Symbol) -> bool {
        false
    }
    fn handle_terminal(&self, x: SexpTerminal, _: &mut Slv, _: ExprContext<Exp>) -> PfResult<Exp> {
        match x {
            SexpTerminal::Number(n) => {
                if let Ok(n) = Slv::SpecExp::try_from(n) {
                    Some(Ok(n.upcast()))
                } else {
                    Some(Err(CustomSexpErr(Cow::Borrowed("too large integer"))))
                }
            }
            _ => None,
        }
    }

    fn handle_non_terminal(
        &self,
        _: Symbol,
        _: &mut [Exp],
        _: &mut Slv,
        _: ExprContext<Exp>,
    ) -> Result<Exp, AddSexpError> {
        unreachable!()
    }
}

impl DefaultIte for Lra {}

impl DefaultDistinct for Lra {}

pub type LinearOpsPf = (AddPf, SubPf);
pub type IneqsPf = (LtPf, (LePf, (GtPf, GePf)));
pub type LinearArithPf = (IneqsPf, (LinearOpsPf, NumPf));
