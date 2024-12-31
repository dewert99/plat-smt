use crate::intern::{Symbol, BOOL_SORT};
use crate::solver::ExpLike;
use crate::theory::{ExplainTheoryArg, Incremental, Theory, TheoryArg};
use crate::{Approx, BoolExp, Exp, HasSort, Sort};
use alloc::borrow::Cow;
use core::fmt::Debug;

pub trait EufT:
    Incremental
    + for<'a> Theory<TheoryArg<'a, Self::LevelMarker>, ExplainTheoryArg<'a, Self::LevelMarker>>
{
    type UExp: ExpLike<Self>;

    type Unsupported: Debug + Into<Cow<'static, str>>;

    /// Create a [`BoolExp`] that represents the equality of `e1` and `e2`
    ///
    /// Requires `e1` and `e2` have the same sort
    fn eq_approx(
        &mut self,
        e1: Exp<Self::UExp>,
        e2: Exp<Self::UExp>,
        approx: Approx,
        acts: &mut TheoryArg<Self::LevelMarker>,
    ) -> BoolExp;

    /// Assert that `e1` and `e2` are equal
    ///
    /// Requires `e1` and `e2` have the same sort
    fn assert_eq(
        &mut self,
        e1: Exp<Self::UExp>,
        e2: Exp<Self::UExp>,
        acts: &mut TheoryArg<Self::LevelMarker>,
    ) {
        let eq = self.eq_approx(e1, e2, Approx::Exact, acts);
        acts.assert(eq);
    }

    /// Assert that all the expressions in `exps` are distinct
    ///
    /// Requires all the expressions have the same sort
    fn assert_distinct_eq(
        &mut self,
        exps: &[Exp<Self::UExp>],
        target: BoolExp,
        acts: &mut TheoryArg<Self::LevelMarker>,
    );

    /// Create an expression representing that all expressions in `exps` are distinct
    ///
    /// Requires all the expressions have the same sort
    fn distinct_approx(
        &mut self,
        exps: &[Exp<Self::UExp>],
        approx: Approx,
        acts: &mut TheoryArg<Self::LevelMarker>,
    ) -> BoolExp;

    /// Creates a function call expression with a given name and children and return sort
    ///
    /// [`Id`]s for the children can be created with [`id`](Solver::id)
    ///
    /// This method does not check sorts of the children so callers need to ensure that functions
    /// call expressions with the same name but different return sorts do not become congruently
    /// equal (This would cause a panic when it happens)
    fn sorted_fn(
        &mut self,
        f: Symbol,
        children: impl Iterator<Item = Exp<Self::UExp>>,
        target_sort: Sort,
        acts: &mut TheoryArg<Self::LevelMarker>,
    ) -> Result<Exp<Self::UExp>, Self::Unsupported>;

    /// Assert `self.sorted_fn(f, children, target_exp.sort(), acts)` is equal to target_exp
    fn assert_fn_eq(
        &mut self,
        f: Symbol,
        children: impl Iterator<Item = Exp<Self::UExp>>,
        target_exp: Exp<Self::UExp>,
        acts: &mut TheoryArg<Self::LevelMarker>,
    ) -> Result<(), Self::Unsupported> {
        let f = self.sorted_fn(f, children, target_exp.sort(), acts)?;
        self.assert_eq(f, target_exp, acts);
        Ok(())
    }

    /// Produce an expression representing that is equivalent to `t` if `i` is true or `e` otherwise
    ///
    /// Requires `t` and `e` have the same sort
    fn ite_approx(
        &mut self,
        i: BoolExp,
        t: Exp<Self::UExp>,
        e: Exp<Self::UExp>,
        approx: Approx,
        acts: &mut TheoryArg<Self::LevelMarker>,
    ) -> Result<Exp<Self::UExp>, Self::Unsupported>;

    /// Requires `t` and `e` have the same sort
    /// Produce an expression representing that is equivalent to `t` if `i` is true or `e` otherwise
    ///
    /// If `t` and `e` have different sorts returns an error containing both sorts
    fn assert_ite_eq(
        &mut self,
        i: BoolExp,
        t: Exp<Self::UExp>,
        e: Exp<Self::UExp>,
        target: Exp<Self::UExp>,
        acts: &mut TheoryArg<Self::LevelMarker>,
    ) -> Result<(), Self::Unsupported> {
        let ite = self.ite_approx(i, t, e, Approx::Exact, acts)?;
        self.assert_eq(ite, target, acts);
        Ok(())
    }

    /// Return an arbitrary placeholder [`UExp`](EufT::UExp) that must have sort `sort`
    fn placeholder_uexp_from_sort(sort: Sort) -> Self::UExp;

    /// Return an arbitrary placeholder [`Exp`] that must have sort `sort`
    fn placeholder_exp_from_sort(sort: Sort) -> Exp<Self::UExp> {
        if sort == BOOL_SORT {
            Exp::Bool(BoolExp::TRUE)
        } else {
            Exp::Other(Self::placeholder_uexp_from_sort(sort))
        }
    }

    /// Must be called before [`get_function_info`](Self::get_function_info)
    fn init_function_info(&mut self);

    type FunctionInfo<'a>: FunctionAssignmentT<Self::UExp>
    where
        Self: 'a;

    /// Gets the definition of an uninterpreted function `f` as a sequence of pairs mapping its
    /// arguments to its return value
    ///
    /// `self` must not have been mutated since the last call to
    /// [`init_function_info`](Self::init_function_info)
    fn get_function_info(&self, f: Symbol) -> Self::FunctionInfo<'_>;
}

pub trait FunctionAssignmentT<UExp>: Iterator<Item = (Self::H, Exp<UExp>)> {
    type H: Iterator<Item = Exp<UExp>>;
}

impl<UExp, H: Iterator<Item = Exp<UExp>>, I: Iterator<Item = (H, Exp<UExp>)>>
    FunctionAssignmentT<UExp> for I
{
    type H = H;
}
