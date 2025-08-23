use crate::collapse::{Collapse, ExprContext};
use crate::core_ops::{CoreOpsPf, Distinct, Eq};
use crate::full_theory::FullTheory;
use crate::intern::Symbol;
use crate::outer_solver::Bound;
use crate::parser_fragment::ParserFragment;
use crate::recorder::Recorder;
use crate::solver::SolverWithBound;
use crate::theory::{Incremental, Theory};
use crate::tseitin::SatTheoryArgT;
use crate::util::HashMap;
use crate::{AddSexpError, BoolExp, Solver};
use core::convert::Infallible;
use platsat::Lit;
use std::iter;

#[derive(Copy, Clone, Debug, Default)]
pub struct EmptyTheory;

#[derive(Copy, Clone, Debug)]
pub struct PushInfo;

pub struct EmptyTheoryMarker;

impl<'a, A: SatTheoryArgT<'a>> Theory<A, A::Explain<'a>> for EmptyTheory {
    fn learn(&mut self, _: Lit, _: &mut A) -> Result<(), ()> {
        Ok(())
    }

    fn pre_decision_check(&mut self, _: &mut A) -> Result<(), ()> {
        Ok(())
    }

    fn explain_propagation(&mut self, _: Lit, _: &mut A::Explain<'a>, _: bool) {
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

    fn init_function_info(&mut self) {}

    type FunctionInfo<'a> = iter::Empty<(iter::Empty<BoolExp>, BoolExp)>;

    fn get_function_info(&self, _: Symbol) -> Self::FunctionInfo<'_> {
        iter::empty()
    }
}

impl<'a, A: SatTheoryArgT<'a>> Collapse<Eq<BoolExp>, A, EmptyTheoryMarker> for EmptyTheory {
    fn collapse(&mut self, t: Eq<BoolExp>, acts: &mut A, ctx: ExprContext<BoolExp>) -> BoolExp {
        !acts.xor(t.0, t.1, ctx.negate())
    }

    fn placeholder(&self, _: &Eq<BoolExp>) -> BoolExp {
        BoolExp::FALSE
    }
}

impl<'a, 'b, A: SatTheoryArgT<'a>> Collapse<Distinct<'b, BoolExp>, A, EmptyTheoryMarker>
    for EmptyTheory
{
    fn collapse(
        &mut self,
        t: Distinct<'b, BoolExp>,
        acts: &mut A,
        ctx: ExprContext<BoolExp>,
    ) -> BoolExp {
        match t.0 {
            &[] | &[_] => acts.collapse_const(true, ctx),
            &[b0, b1] => acts.xor(b0, b1, ctx),
            _ => acts.collapse_const(false, ctx),
        }
    }

    fn placeholder(&self, _: &Distinct<'b, BoolExp>) -> BoolExp {
        BoolExp::FALSE
    }
}

type EmptySolver<R> =
    SolverWithBound<Solver<EmptyTheory, R>, HashMap<Symbol, Bound<BoolExp, Infallible>>>;

#[derive(Default)]
pub struct ConstantPf;

impl<R: Recorder> ParserFragment<BoolExp, EmptySolver<R>, EmptyTheoryMarker> for ConstantPf {
    fn supports(&self, _: Symbol) -> bool {
        true
    }

    fn handle_non_terminal(
        &self,
        f: Symbol,
        children: &mut [BoolExp],
        solver: &mut EmptySolver<R>,
        _: ExprContext<BoolExp>,
    ) -> Result<BoolExp, AddSexpError> {
        use crate::parser_fragment::AddSexpError::*;
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
