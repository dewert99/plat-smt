use crate::collapse::{BaseMarker, Collapse, ExprContext};
use crate::core_ops::{CoreOpsPf, DefaultIte, Distinct, DistinctElts, Eq, RawDistinct};
use crate::full_theory::{empty_fn_info, FullTheory, FunctionAssignmentT, PrepareModelKind};
use crate::intern::Symbol;
use crate::outer_solver::Bound;
use crate::parser_fragment::ParserFragment;
use crate::recorder::{dep_checker, Recorder};
use crate::solver::SolverWithBound;
use crate::theory::{Incremental, Theory};
use crate::tseitin::SatTheoryArgT;
use crate::util::HashMap;
use crate::{AddSexpError, BoolExp, Solver};
use core::convert::Infallible;
use platsat::Lit;

#[derive(Copy, Clone, Debug, Default)]
pub struct EmptyTheory;

#[derive(Copy, Clone, Debug)]
pub struct PushInfo;

impl<'a, A: SatTheoryArgT<'a>, P> Theory<A, A::Explain<'a>, P> for EmptyTheory {
    fn learn(&mut self, _: Lit, _: &mut A) -> Result<(), ()> {
        Ok(())
    }

    fn pre_decision_check(&mut self, _: &mut A) -> Result<(), ()> {
        Ok(())
    }

    fn explain_propagation(&mut self, _: Lit, _: &mut A::Explain<'a>, _: bool, _: u8) {
        unreachable!()
    }
}

impl Incremental for EmptyTheory {
    type LevelMarker = PushInfo;

    fn create_level(&self) -> Self::LevelMarker {
        PushInfo
    }

    fn pop_to_level(&mut self, _: Self::LevelMarker, _: bool) {}

    fn clear(&mut self) {}
}

impl<R: Recorder> FullTheory<R> for EmptyTheory {
    type Exp = BoolExp;

    type FnSort = Infallible;

    fn prepare_model(&mut self, _: PrepareModelKind) {}

    fn get_function_info(&self, _: Symbol) -> impl FunctionAssignmentT<Exp = BoolExp> {
        empty_fn_info()
    }
}

impl<'a, A: SatTheoryArgT<'a>> Collapse<Eq<BoolExp>, A, BaseMarker> for EmptyTheory {
    fn collapse(&mut self, t: Eq<BoolExp>, acts: &mut A, ctx: ExprContext<BoolExp>) -> BoolExp {
        !acts.xor(t.0, t.1, ctx.negate())
    }

    fn placeholder(&self, _: &Eq<BoolExp>) -> BoolExp {
        BoolExp::FALSE
    }
}

impl<'a, 'b, I: DistinctElts<Exp = BoolExp>, A: SatTheoryArgT<'a>>
    Collapse<RawDistinct<I>, A, BaseMarker> for EmptyTheory
{
    fn collapse(&mut self, t: RawDistinct<I>, acts: &mut A, ctx: ExprContext<BoolExp>) -> BoolExp {
        let mut iter = t.0.iter();
        match (iter.next(), iter.next(), iter.next()) {
            (None, _, _) | (_, None, _) => acts.collapse_const(true, ctx),
            (Some(b0), Some(b1), None) => acts.xor(b0, b1, ctx),
            _ => acts.collapse_const(false, ctx),
        }
    }

    fn placeholder(&self, _: &RawDistinct<I>) -> BoolExp {
        BoolExp::FALSE
    }
}

type ConstOnlySolver<Th, R> =
    SolverWithBound<Solver<Th, R>, HashMap<Symbol, Bound<<Th as FullTheory<R>>::Exp, Infallible>>>;

impl DefaultIte for EmptyTheory {}

#[derive(Default)]
pub struct ConstantPf;

impl<Th: FullTheory<R>, R: Recorder> ParserFragment<Th::Exp, ConstOnlySolver<Th, R>, BaseMarker>
    for ConstantPf
{
    fn supports(&self, _: Symbol) -> bool {
        true
    }

    fn handle_non_terminal(
        &self,
        f: Symbol,
        children: &mut [Th::Exp],
        solver: &mut ConstOnlySolver<Th, R>,
        _: ExprContext<Th::Exp>,
    ) -> Result<Th::Exp, AddSexpError> {
        use crate::parser_fragment::AddSexpError::*;
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
                Ok(*c)
            }
            Some(Bound::Fn(f)) => match *f {},
        }
    }
}

pub type EmptyTheoryPf = (CoreOpsPf, ConstantPf);
