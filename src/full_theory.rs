use crate::collapse::{Collapse, CollapseOut};
use crate::exp::{EitherExp, ExpLike};
use crate::intern::{InternInfo, Symbol};
use crate::parser::SmtlibLogic;
use crate::parser_fragment::ParserFragment;
use crate::recorder::Recorder;
use crate::solver::SolverWithBound;
use crate::theory::{ExplainTheoryArg, Incremental, Theory, TheoryArg};
use crate::util::{Either, HashMap};
use crate::{AddSexpError, BoolExp, Fresh, OuterSolver, Solver, Sort, SuperExp};
use alloc::boxed::Box;
use core::convert::Infallible;
use core::fmt;
use core::fmt::Formatter;
use core::marker::PhantomData;
use platsat::{Lit, SolverInterface, lbool};
use smallvec::SmallVec;
use std::iter;

#[derive(Copy, Clone, Debug)]
pub enum PrepareModelKind {
    GetModel,
    GetValues,
    Clear,
}

pub trait QExtractor<T> {
    type Target;
    fn extract(t: &mut T) -> &mut Self::Target;

    fn extract_shr(t: &T) -> &Self::Target;
}

impl<T> QExtractor<T> for () {
    type Target = ();
    fn extract(_: &mut T) -> &mut Self::Target {
        Box::leak(Box::new(()))
    }

    fn extract_shr(_: &T) -> &Self::Target {
        &()
    }
}

pub trait NotUnit {}

impl<T, B, E: QExtractor<B, Target = T>, B2, E2: QExtractor<B2, Target = ()>> QExtractor<(B, B2)>
    for (E, E2, T, ())
{
    type Target = E::Target;
    fn extract(t: &mut (B, B2)) -> &mut Self::Target {
        E::extract(&mut t.0)
    }

    fn extract_shr(t: &(B, B2)) -> &Self::Target {
        E::extract_shr(&t.0)
    }
}

impl<T: NotUnit, B, E: QExtractor<B, Target = T>, B2, E2: QExtractor<B2, Target = ()>>
    QExtractor<(B2, B)> for (E2, E, (), T)
{
    type Target = E::Target;
    fn extract(t: &mut (B2, B)) -> &mut Self::Target {
        E::extract(&mut t.1)
    }

    fn extract_shr(t: &(B2, B)) -> &Self::Target {
        E::extract_shr(&t.1)
    }
}

pub trait FullTheory<R>: Incremental
    + Clone
    + for<'a> Theory<TheoryArg<'a, Self::LevelMarker, R>, ExplainTheoryArg<'a, Self::LevelMarker, R>>
    + 'static
{
    type Exp: ExpLike;

    type FnSort: MaybeFnSort;

    type QExtractor: QExtractor<Self>;

    fn quantifier_applier(&mut self) -> &mut TheoryQ<Self, R> {
        Self::QExtractor::extract(self)
    }

    fn quantifier_applier_shr(&self) -> &TheoryQ<Self, R> {
        Self::QExtractor::extract_shr(self)
    }

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

type TheoryQ<Th, R> = <<Th as FullTheory<R>>::QExtractor as QExtractor<Th>>::Target;

impl<R: Recorder, T1: FullTheory<R>, T2: FullTheory<R>> FullTheory<R> for (T1, T2)
where
    T1::FnSort: FnSortComb<T2::FnSort>,
    (T1, T2): for<'a> Theory<
            TheoryArg<'a, Self::LevelMarker, R>,
            ExplainTheoryArg<'a, Self::LevelMarker, R>,
        >,
    (
        T1::QExtractor,
        T2::QExtractor,
        TheoryQ<T1, R>,
        TheoryQ<T2, R>,
    ): QExtractor<Self>,
{
    type Exp = EitherExp<T1::Exp, T2::Exp>;
    type FnSort = <T1::FnSort as FnSortComb<T2::FnSort>>::Comb;

    type QExtractor = (
        T1::QExtractor,
        T2::QExtractor,
        TheoryQ<T1, R>,
        TheoryQ<T2, R>,
    );

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

    pub fn slice_new(s: &[Sort], ret: Sort) -> Self {
        FnSort::new(SmallVec::from_slice(s), ret)
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

#[derive(Clone)]
pub enum Bound<Exp, Fn = FnSort> {
    /// An uninterpreted function with the given sort
    Fn(Fn),
    /// A constant with the given value
    Const(Exp),
}

pub type BoundL<L> = Bound<<L as Logic>::Exp, <L as Logic>::FnSort>;

pub enum QuantExp<Exp> {
    /// And expression from outside the quantifier captured in its body
    Exp(Exp),
    /// The nth variable quantified over
    QuantVar(u32),
    /// The nth let bound variable inside the quantifier
    LetVar(u32),
}

pub struct QuantContext {
    pub(crate) captures: u32,
    pub(crate) vm: u32,
    pub(crate) qvars: u32,
}

#[derive(Debug, PartialEq)]
pub enum Instruction<Exp = u32> {
    End,
    Start(Symbol),
    Var(Exp),
}

impl<Exp> Instruction<Exp> {
    pub const END: Self = Self::End;
}

pub(crate) type Trigger = Either<Symbol, Sort>;

pub trait QuantifierApplier<Exp> {
    fn run<L: Logic<Exp = Exp, Q = Self>>(
        outer: &mut OuterSolver<L>,
    ) -> Result<(), (Option<Symbol>, AddSexpError)>;
    fn clear_pending(&mut self);
    fn enabled(&self) -> bool;
    fn create_context(&self, qvars: u32) -> QuantContext;
    fn add_instruction(&mut self, ctx: &QuantContext, instruction: Instruction<QuantExp<Exp>>);
    fn bind_instructions(&mut self, ctx: &QuantContext, syms: impl Iterator<Item = Trigger>);

    fn debug_cxt(&self, ctx: &QuantContext, intern: &InternInfo, f: &mut Formatter) -> fmt::Result;
}

impl<E> QuantifierApplier<E> for () {
    fn run<L: Logic<Exp = E, Q = Self>>(
        _: &mut OuterSolver<L>,
    ) -> Result<(), (Option<Symbol>, AddSexpError)> {
        Ok(())
    }

    fn clear_pending(&mut self) {}

    fn enabled(&self) -> bool {
        false
    }

    fn create_context(&self, qvars: u32) -> QuantContext {
        QuantContext {
            qvars,
            vm: 0,
            captures: 0,
        }
    }

    fn add_instruction(&mut self, _: &QuantContext, _: Instruction<QuantExp<E>>) {}

    fn bind_instructions(&mut self, _: &QuantContext, _: impl Iterator<Item = Trigger>) {}

    fn debug_cxt(&self, _: &QuantContext, _: &InternInfo, f: &mut Formatter) -> fmt::Result {
        write!(f, "NoQuantifyApplier")
    }
}

pub trait Logic: Sized {
    type Exp: SuperExp<BoolExp, Self::EM> + ExpLike;

    type FnSort: MaybeFnSort;

    type LevelMarker: Clone;

    type Theory: FullTheory<
            Self::R,
            Exp = Self::Exp,
            FnSort = Self::FnSort,
            LevelMarker = Self::LevelMarker,
            QExtractor: QExtractor<Self::Theory, Target = Self::Q>,
        > + for<'a> Collapse<Self::Exp, TheoryArg<'a, Self::LevelMarker, Self::R>, Self::CM>
        + for<'a> Collapse<Fresh<Self::Exp>, TheoryArg<'a, Self::LevelMarker, Self::R>, Self::CM>;

    type RLevelMarker: Clone;

    type R: Recorder<LevelMarker = Self::RLevelMarker>;
    type Parser: ParserFragment<Self::Exp, WrapSolver<Self::Theory, Self::R>, Self::M>;

    type Q: QuantifierApplier<Self::Exp>;

    type EM;

    type CM;
    type M;
}

#[allow(type_alias_bounds)]
pub(crate) type WrapSolver<Th: FullTheory<R>, R> =
    SolverWithBound<Solver<Th, R>, HashMap<Symbol, Bound<Th::Exp, Th::FnSort>>>;

impl<
    R: Recorder,
    M,
    EM,
    CM,
    QE: QExtractor<Th, Target = Q>,
    Q: QuantifierApplier<Th::Exp>,
    Th: FullTheory<R, QExtractor = QE>
        + for<'a> Collapse<Th::Exp, TheoryArg<'a, Th::LevelMarker, R>, CM>
        + for<'a> Collapse<Fresh<Th::Exp>, TheoryArg<'a, Th::LevelMarker, R>, CM>,
    P: ParserFragment<Th::Exp, WrapSolver<Th, R>, M>,
> Logic for (Th, P, R, (M, EM, CM))
where
    Th::Exp: SuperExp<BoolExp, EM>,
{
    type Exp = Th::Exp;
    type FnSort = Th::FnSort;
    type LevelMarker = Th::LevelMarker;

    type Theory = Th;

    type RLevelMarker = R::LevelMarker;

    type R = R;
    type Parser = P;
    type Q = Q;
    type EM = EM;
    type CM = CM;

    type M = M;
}
