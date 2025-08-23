use crate::collapse::{Collapse, CollapseOut};
use crate::exp::ExpLike;
use crate::intern::Symbol;
use crate::theory::{ExplainTheoryArg, Incremental, Theory, TheoryArg};
use crate::Sort;
use core::convert::Infallible;
use smallvec::SmallVec;

pub trait FullTheory<R>: Incremental
    + for<'a> Theory<TheoryArg<'a, Self::LevelMarker, R>, ExplainTheoryArg<'a, Self::LevelMarker, R>>
{
    type Exp: ExpLike;

    type FnSort: MaybeFnSort;

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

pub trait TopLevelCollapse<T: CollapseOut, M, R>:
    Incremental + for<'a> Collapse<T, TheoryArg<'a, Self::LevelMarker, R>, M>
{
}

impl<
        T: CollapseOut,
        M,
        R,
        Th: Incremental + for<'a> Collapse<T, TheoryArg<'a, Th::LevelMarker, R>, M>,
    > TopLevelCollapse<T, M, R> for Th
{
}

#[derive(Clone)]
pub struct FnSort {
    args: SmallVec<[Sort; 5]>,
    ret: Sort,
}

impl FnSort {
    pub fn new(args: SmallVec<[Sort; 5]>, ret: Sort) -> Self {
        FnSort { args, ret }
    }
    pub fn args(&self) -> &[Sort] {
        &self.args
    }

    pub fn ret(&self) -> Sort {
        self.ret
    }
}

pub trait MaybeFnSort: Sized {
    fn try_new(f: FnSort) -> Result<Self, ()>;

    fn as_fn_sort(&self) -> &FnSort;
}

impl MaybeFnSort for FnSort {
    fn try_new(f: FnSort) -> Result<Self, ()> {
        Ok(f)
    }
    fn as_fn_sort(&self) -> &FnSort {
        self
    }
}

impl MaybeFnSort for Infallible {
    fn try_new(_: FnSort) -> Result<Self, ()> {
        Err(())
    }

    fn as_fn_sort(&self) -> &FnSort {
        match *self {}
    }
}
