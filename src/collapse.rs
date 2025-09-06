use crate::exp::ExpLike;
use crate::intern::{DisplayInterned, InternInfo, WithIntern};
use crate::{SubExp, SuperExp};

/// Requirements on the `Exp` returned by `add_sexp`
#[derive(Copy, Clone, Debug, Default, Eq, PartialEq)]
#[non_exhaustive]
pub enum ExprContext<Exp> {
    /// Collapse the requested expression exactly
    #[default]
    Exact,
    /// Collapse the expressions knowing it is equal to another expression
    AssertEq(Exp),
    /// If `approx` is `Approx(false)` the returned boolean is assigned false whenever the expected result is assigned to false,
    /// and when the expected result is assigned to true the returned boolean is either also true or unconstrained
    ///
    /// If `approx` is `Approx(true)` the returned boolean is assigned true whenever the expected result is assigned to true,
    /// and when the expected result is assigned to false the returned boolean is either false true or unconstrained
    ///
    /// In the future this may also be used for over/under-approximating numeric expressions
    Approx(bool),
}

impl<Exp2> ExprContext<Exp2> {
    pub fn upcast<M, Exp1: SuperExp<Exp2, M>>(self) -> ExprContext<Exp1> {
        match self {
            ExprContext::Exact => ExprContext::Exact,
            ExprContext::AssertEq(x) => ExprContext::AssertEq(x.upcast()),
            ExprContext::Approx(b) => ExprContext::Approx(b),
        }
    }

    pub fn downcast<M, Exp1>(self) -> ExprContext<Exp1>
    where
        Exp2: SuperExp<Exp1, M>,
    {
        match self {
            ExprContext::Exact => ExprContext::Exact,
            ExprContext::AssertEq(x) => {
                if let Some(x) = x.downcast() {
                    ExprContext::AssertEq(x)
                } else {
                    ExprContext::Exact
                }
            }
            ExprContext::Approx(b) => ExprContext::Approx(b),
        }
    }

    pub fn with_intern(self, intern: &InternInfo) -> ExprContext<WithIntern<'_, Exp2>>
    where
        Exp2: DisplayInterned,
    {
        match self {
            ExprContext::Exact => ExprContext::Exact,
            ExprContext::AssertEq(x) => ExprContext::AssertEq(x.with_intern(intern)),
            ExprContext::Approx(b) => ExprContext::Approx(b),
        }
    }
}

/// Associated type of the [`Collapse`] trait that was extracted into its own trait since it should
/// to constrain the type parameters it is allowed to depend on
pub trait CollapseOut {
    type Out: ExpLike;
}

/// Trait for collapsing a type representing an expression into a copiable handled that can be used
/// with the solver.
///
/// See also: [`crate::Solver::collapse`].
pub trait Collapse<T: CollapseOut, Arg, Marker> {
    /// Collapse a type representing an expression into a copiable handled that can be used later.
    ///
    /// The `ctx` argument may indicate possible assumptions that may allow for additional
    /// optimizations, but an implementor may choose to ignore it
    fn collapse(&mut self, t: T, acts: &mut Arg, ctx: ExprContext<T::Out>) -> T::Out;

    /// Return a placeholder in cases where the solver is already in an unsatisfiable state.
    ///
    /// The sort of the returned expression must match the sort that would have been returned by
    /// [`Collapse::collapse`]
    fn placeholder(&self, t: &T) -> T::Out;
}
