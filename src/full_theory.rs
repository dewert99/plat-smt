use crate::collapse::{Collapse, CollapseOut};
use crate::exp::{EitherExp, ExpLike};
use crate::intern::Symbol;
use crate::parser::SmtlibLogic;
use crate::recorder::Recorder;
use crate::theory::{ExplainTheoryArg, Incremental, Theory, TheoryArg};
use crate::util::Either;
use crate::{Solver, Sort};
use core::convert::Infallible;
use core::marker::PhantomData;
use platsat::{lbool, Lit, SolverInterface};
use smallvec::SmallVec;
use std::iter;

#[derive(Copy, Clone, Debug)]
pub enum PrepareModelKind {
    GetModel,
    GetValues,
    Clear,
}

pub trait FullTheory<R>: Incremental
    + Clone
    + for<'a> Theory<TheoryArg<'a, Self::LevelMarker, R>, ExplainTheoryArg<'a, Self::LevelMarker, R>>
    + 'static
{
    type Exp: ExpLike;

    type FnSort: MaybeFnSort;

    /// Must be called before [`get_function_info`](Self::get_function_info)
    fn prepare_model(&mut self, kind: PrepareModelKind);

    /// Gets the definition of an uninterpreted function `f` as a sequence of pairs mapping its
    /// arguments to its return value
    ///
    /// `self` must not have been mutated since the last call to
    /// [`init_function_info`](Self::prepare_model)
    fn get_function_info<'a>(&'a self, f: Symbol)
        -> impl FunctionAssignmentT<Exp = Self::Exp> + 'a;

    fn supported_logic(&self) -> SmtlibLogic {
        SmtlibLogic::CORE
    }

    fn solve_limited_preserving_trail(solver: &mut Solver<Self, R>, assumptions: &[Lit]) -> lbool
    where
        R: Recorder,
    {
        solver
            .sat
            .solve_limited_preserving_trail_th(&mut solver.th, assumptions)
    }
}

struct InfallibleIter<T>(Infallible, PhantomData<T>);

impl<T> Iterator for InfallibleIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        match self.0 {}
    }
}

pub fn empty_fn_info<T>() -> impl FunctionAssignmentT<Exp = T> {
    iter::empty::<(InfallibleIter<_>, _)>()
}

impl<R: Recorder, T1: FullTheory<R>, T2: FullTheory<R>> FullTheory<R> for (T1, T2)
where
    T1::FnSort: FnSortComb<T2::FnSort>,
    (T1, T2): for<'a> Theory<
        TheoryArg<'a, Self::LevelMarker, R>,
        ExplainTheoryArg<'a, Self::LevelMarker, R>,
    >,
{
    type Exp = EitherExp<T1::Exp, T2::Exp>;
    type FnSort = <T1::FnSort as FnSortComb<T2::FnSort>>::Comb;

    fn prepare_model(&mut self, kind: PrepareModelKind) {
        self.0.prepare_model(kind);
        self.1.prepare_model(kind);
    }

    fn get_function_info(&self, f: Symbol) -> impl FunctionAssignmentT<Exp = Self::Exp> {
        self.0
            .get_function_info(f)
            .map(|(h, e)| (Either::Left(h.map(EitherExp::Left)), EitherExp::Left(e)))
            .chain(
                self.1
                    .get_function_info(f)
                    .map(|(h, e)| (Either::Right(h.map(EitherExp::Right)), EitherExp::Right(e))),
            )
    }

    fn supported_logic(&self) -> SmtlibLogic {
        self.0.supported_logic() | self.1.supported_logic()
    }
}

pub trait FunctionAssignmentT: Iterator<Item = (Self::H, Self::Exp)> {
    type Exp;
    type H: Iterator<Item = Self::Exp>;
}

impl<Exp, H: Iterator<Item = Exp>, I: Iterator<Item = (H, Exp)>> FunctionAssignmentT for I {
    type Exp = Exp;
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

#[doc(hidden)]
pub trait FnSortComb<Oth> {
    type Comb: MaybeFnSort;
}

impl FnSortComb<Infallible> for Infallible {
    type Comb = Infallible;
}

impl FnSortComb<FnSort> for Infallible {
    type Comb = FnSort;
}

impl<T> FnSortComb<T> for FnSort {
    type Comb = FnSort;
}
