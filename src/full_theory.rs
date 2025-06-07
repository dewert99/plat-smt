use crate::collapse::{Collapse, CollapseOut};
use crate::exp::ExpLike;
use crate::intern::Symbol;
use crate::theory::{ExplainTheoryArg, Incremental, Theory, TheoryArg};

pub trait FullTheory:
    Incremental
    + for<'a> Theory<TheoryArg<'a, Self::LevelMarker>, ExplainTheoryArg<'a, Self::LevelMarker>>
{
    type Exp: ExpLike;

    /// Must be called before [`get_function_info`](Self::get_function_info)
    fn init_function_info(&mut self);

    type FunctionInfo<'a>: FunctionAssignmentT<Self::Exp>
    where
        Self: 'a;

    /// Gets the definition of an uninterpreted function `f` as a sequence of pairs mapping its
    /// arguments to its return value
    ///
    /// `self` must not have been mutated since the last call to
    /// [`init_function_info`](Self::init_function_info)
    fn get_function_info(&self, f: Symbol) -> Self::FunctionInfo<'_>;
}

pub trait FunctionAssignmentT<Exp>: Iterator<Item = (Self::H, Exp)> {
    type H: Iterator<Item = Exp>;
}

impl<Exp, H: Iterator<Item = Exp>, I: Iterator<Item = (H, Exp)>> FunctionAssignmentT<Exp> for I {
    type H = H;
}

pub trait TopLevelCollapse<T: CollapseOut, M>:
    Incremental + for<'a> Collapse<T, TheoryArg<'a, Self::LevelMarker>, M>
{
}

impl<
        T: CollapseOut,
        M,
        Th: Incremental + for<'a> Collapse<T, TheoryArg<'a, Th::LevelMarker>, M>,
    > TopLevelCollapse<T, M> for Th
{
}
