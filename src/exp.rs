use crate::collapse::{Collapse, CollapseOut, ExprContext};
use crate::intern::{
    DisplayInterned, InternInfo, Sort, Symbol, BOOL_SORT, FALSE_SYM, NOT_SYM, TRUE_SYM,
};
use crate::rexp::{rexp_debug, AsRexp, Namespace, NamespaceVar, Rexp};
use core::fmt::{Debug, Display, Formatter};
use core::hash::Hash;
use core::marker::PhantomData;
use platsat::clause::{Lit, Var};
use std::ops::{BitXor, Not};

pub trait HasSort {
    fn sort(self) -> Sort;

    /// Static method that checks if any instance of a type can have a particular sort
    fn can_have_sort(s: Sort) -> bool;
}

pub trait ExpLike:
    Copy + Debug + DisplayInterned + AsRexp + HasSort + Eq + Hash + Ord + CollapseOut<Out = Self>
{
}

impl<
        T: Copy
            + Debug
            + DisplayInterned
            + HasSort
            + Eq
            + Hash
            + Ord
            + AsRexp
            + CollapseOut<Out = Self>,
    > ExpLike for T
{
}

pub trait StaticSort: HasSort {
    const SORT: Sort;
}

impl<X: StaticSort> HasSort for X {
    fn sort(self) -> Sort {
        Self::SORT
    }

    fn can_have_sort(s: Sort) -> bool {
        s == Self::SORT
    }
}

pub struct IdM;

pub struct Lm<M>(M);

pub struct Rm<M>(M);

pub trait SuperExp<Sub, M> {
    fn downcast(self) -> Option<Sub>;

    fn from_upcast(s: Sub) -> Self;
}

pub trait SubExp<Super, M>: Sized {
    fn upcast(self) -> Super;

    fn from_downcast(s: Super) -> Option<Self>;
}

impl<M, Sub, Super: SuperExp<Sub, M>> SubExp<Super, M> for Sub {
    fn upcast(self) -> Super {
        Super::from_upcast(self)
    }

    fn from_downcast(s: Super) -> Option<Self> {
        s.downcast()
    }
}

impl<T: ExpLike> SuperExp<T, IdM> for T {
    fn downcast(self) -> Option<T> {
        Some(self)
    }

    fn from_upcast(s: T) -> Self {
        s
    }
}

/// A dynamically sorted expression within a [`Solver`]
#[derive(Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum EitherExp<E1, E2> {
    Left(E1),
    Right(E2),
}

impl<E1: SuperExp<Sub, M>, E2, Sub, M> SuperExp<Sub, Lm<M>> for EitherExp<E1, E2> {
    fn downcast(self) -> Option<Sub> {
        match self {
            EitherExp::Left(l) => l.downcast(),
            _ => None,
        }
    }

    fn from_upcast(s: Sub) -> Self {
        EitherExp::Left(E1::from_upcast(s))
    }
}

impl<E2: SuperExp<Sub, M>, E1, Sub, M> SuperExp<Sub, Rm<M>> for EitherExp<E1, E2> {
    fn downcast(self) -> Option<Sub> {
        match self {
            EitherExp::Right(r) => r.downcast(),
            _ => None,
        }
    }

    fn from_upcast(s: Sub) -> Self {
        EitherExp::Right(E2::from_upcast(s))
    }
}

impl<E1: HasSort, E2: HasSort> HasSort for EitherExp<E1, E2> {
    fn sort(self) -> Sort {
        match self {
            EitherExp::Left(l) => l.sort(),
            EitherExp::Right(r) => r.sort(),
        }
    }

    fn can_have_sort(s: Sort) -> bool {
        E1::can_have_sort(s) || E2::can_have_sort(s)
    }
}

impl<L: crate::rexp::AsRexp, R: crate::rexp::AsRexp> crate::rexp::AsRexp for EitherExp<L, R> {
    fn as_rexp<O>(&self, f: impl for<'a> FnOnce(Rexp<'a>) -> O) -> O {
        match self {
            EitherExp::Left(l) => l.as_rexp(f),
            EitherExp::Right(r) => r.as_rexp(f),
        }
    }
}

impl<E1: Debug, E2: Debug> Debug for EitherExp<E1, E2> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            EitherExp::Left(l) => Debug::fmt(l, f),
            EitherExp::Right(r) => Debug::fmt(r, f),
        }
    }
}

impl<E1: DisplayInterned, E2: DisplayInterned> DisplayInterned for EitherExp<E1, E2> {
    fn fmt(&self, i: &InternInfo, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            EitherExp::Left(l) => DisplayInterned::fmt(l, i, f),
            EitherExp::Right(r) => DisplayInterned::fmt(r, i, f),
        }
    }
}

/// A boolean sorted expression within a [`Solver`]
///
/// It can be upcast to a dynamically sorted [`Exp`] using [`Exp::upcast`], and downcast using
/// [`Exp::downcast`].
///
/// It also implements [`BitAnd`](core::ops::BitAnd), [`BitOr`](core::ops::BitOr), and
/// [`Not`], but its [`BitAnd`](core::ops::BitAnd) and [`BitOr`](core::ops::BitOr)
/// implementations produces [`Conjunction`]s and [`Disjunction`]s respectively.
/// [`Solver::collapse_bool`] can be used to collapse these types back into [`BoolExp`]s
#[derive(Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct BoolExp(Lit);

impl BoolExp {
    pub const TRUE: BoolExp = BoolExp(Lit::UNDEF);
    pub const FALSE: BoolExp = BoolExp(Lit::ERROR);

    pub fn unknown(lit: Lit) -> Self {
        debug_assert!(lit.var() != Var::UNDEF);
        BoolExp(lit)
    }

    pub fn from_bool(b: bool) -> Self {
        BoolExp(Lit::new(Var::UNDEF, b))
    }

    /// ```
    /// use plat_smt::BoolExp;
    /// assert_eq!(BoolExp::TRUE.to_lit(), Err(true));
    /// assert_eq!(BoolExp::FALSE.to_lit(), Err(false));
    /// ```
    pub fn to_lit(self) -> Result<Lit, bool> {
        if self.0.var() == Var::UNDEF {
            Err(self.0.sign())
        } else {
            Ok(self.0)
        }
    }

    pub(crate) fn var(self) -> Var {
        self.0.var()
    }

    pub(crate) fn sign(self) -> bool {
        self.0.sign()
    }
}

impl StaticSort for BoolExp {
    const SORT: Sort = BOOL_SORT;
}

impl Not for BoolExp {
    type Output = BoolExp;

    fn not(self) -> Self::Output {
        BoolExp(!self.0)
    }
}

impl BitXor<bool> for BoolExp {
    type Output = BoolExp;

    fn bitxor(self, rhs: bool) -> Self::Output {
        BoolExp(self.0 ^ rhs)
    }
}

impl AsRexp for Var {
    fn as_rexp<R>(&self, f: impl for<'a> FnOnce(Rexp<'a>) -> R) -> R {
        f(Rexp::Nv(NamespaceVar(Namespace::Bool, self.idx() + 1)))
    }
}

impl AsRexp for BoolExp {
    fn as_rexp<R>(&self, f: impl FnOnce(Rexp<'_>) -> R) -> R {
        match self.to_lit() {
            Err(c) => f(Rexp::Call(if c { TRUE_SYM } else { FALSE_SYM }, &[])),
            Ok(l) => {
                let base = Rexp::Nv(NamespaceVar(Namespace::Bool, l.var().idx() + 1));
                if l.sign() {
                    f(base)
                } else {
                    f(Rexp::Call(NOT_SYM, &[base]))
                }
            }
        }
    }
}

rexp_debug!(BoolExp);

impl Display for BoolExp {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self.to_lit() {
            Err(c) => Debug::fmt(&c, f),
            Ok(_) => {
                write!(f, "(as {self:?} Bool)")
            }
        }
    }
}

impl<E1: ExpLike, E2: ExpLike> CollapseOut for EitherExp<E1, E2> {
    type Out = EitherExp<E1, E2>;
}

impl<E1: ExpLike, E2: ExpLike, Arg, M1, M2, Th: Collapse<E1, Arg, M1> + Collapse<E2, Arg, M2>>
    Collapse<EitherExp<E1, E2>, Arg, (M1, M2)> for Th
{
    fn collapse(
        &mut self,
        t: EitherExp<E1, E2>,
        acts: &mut Arg,
        ctx: ExprContext<EitherExp<E1, E2>>,
    ) -> EitherExp<E1, E2> {
        match t {
            EitherExp::Left(l) => EitherExp::Left(self.collapse(l, acts, ctx.downcast())),
            EitherExp::Right(r) => EitherExp::Right(self.collapse(r, acts, ctx.downcast())),
        }
    }

    fn placeholder(&self, t: &EitherExp<E1, E2>) -> EitherExp<E1, E2> {
        *t
    }
}

/// Used with [`crate::solver::SolverCollapse::collapse`] to create fresh expressions of a given sort
///
/// Invariant `E::can_have_sort(sort)`
pub struct Fresh<E> {
    pub name: Symbol,
    pub sort: Sort,
    phantom: PhantomData<E>,
}

impl<E: HasSort> Fresh<E> {
    pub fn new(name: Symbol, sort: Sort) -> Result<Self, ()> {
        if E::can_have_sort(sort) {
            Ok(Fresh {
                name,
                sort,
                phantom: PhantomData,
            })
        } else {
            Err(())
        }
    }
}

impl<E: ExpLike> CollapseOut for Fresh<E> {
    type Out = E;
}

impl<
        E1: ExpLike,
        E2: ExpLike,
        Arg,
        M1,
        M2,
        Th: Collapse<Fresh<E1>, Arg, M1> + Collapse<Fresh<E2>, Arg, M2>,
    > Collapse<Fresh<EitherExp<E1, E2>>, Arg, (M1, M2)> for Th
{
    fn collapse(
        &mut self,
        t: Fresh<EitherExp<E1, E2>>,
        acts: &mut Arg,
        ctx: ExprContext<EitherExp<E1, E2>>,
    ) -> EitherExp<E1, E2> {
        match Fresh::<E1>::new(t.name, t.sort) {
            Ok(fresh) => EitherExp::Left(self.collapse(fresh, acts, ctx.downcast())),
            _ => EitherExp::Right(self.collapse(
                Fresh::<E2> {
                    name: t.name,
                    sort: t.sort,
                    phantom: PhantomData,
                },
                acts,
                ctx.downcast(),
            )),
        }
    }

    fn placeholder(&self, t: &Fresh<EitherExp<E1, E2>>) -> EitherExp<E1, E2> {
        match Fresh::<E1>::new(t.name, t.sort) {
            Ok(fresh) => EitherExp::Left(self.placeholder(&fresh)),
            _ => EitherExp::Right(self.placeholder(&Fresh::<E2> {
                name: t.name,
                sort: t.sort,
                phantom: PhantomData,
            })),
        }
    }
}
