use core::convert::Infallible;
use core::fmt::{Debug, Display, Formatter};
use core::ops::ControlFlow;
use internal_iterator::InternalIterator;
use no_std_compat::prelude::v1::*;

pub(crate) struct DebugIter<'a, I>(pub &'a I);

impl<'a, I: Iterator + Clone> Debug for DebugIter<'a, I>
where
    I::Item: Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.debug_list().entries(self.0.clone()).finish()
    }
}

#[derive(Copy, Clone)]
pub struct DisplayFn<F: Fn(&mut Formatter) -> core::fmt::Result>(pub F);

impl<F: Fn(&mut Formatter) -> core::fmt::Result> Display for DisplayFn<F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        self.0(f)
    }
}

macro_rules! format_args2 {
    ($($xs:tt)*) => {
        $crate::util::DisplayFn(move |f: &mut ::core::fmt::Formatter| ::core::write!(f, $($xs)*))
    };
}

pub(crate) use format_args2;

pub(crate) struct Parenthesized<'a, H, I>(Option<H>, I, &'a str);
impl<'a, H: Display, I: Iterator + Clone> Display for Parenthesized<'a, H, I>
where
    I::Item: Display,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut iter = self.1.clone();
        write!(f, "(")?;
        if let Some(x) = &self.0 {
            write!(f, "{x}")?;
        } else if let Some(x) = iter.next() {
            write!(f, "{x}")?;
        }
        for x in iter {
            write!(f, "{}{x}", self.2)?;
        }
        write!(f, ")")
    }
}

pub(crate) fn parenthesized<I: IntoIterator>(
    iter: I,
    sep: &str,
) -> Parenthesized<'_, Infallible, I::IntoIter> {
    Parenthesized(None, iter.into_iter(), sep)
}

pub(crate) fn display_sexp<H, I: IntoIterator>(
    head: H,
    iter: I,
) -> Parenthesized<'static, H, I::IntoIter> {
    Parenthesized(Some(head), iter.into_iter(), " ")
}

macro_rules! display_debug {
    ($ty:ty) => {
        impl core::fmt::Display for $ty {
            fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
                core::fmt::Debug::fmt(self, f)
            }
        }
    };
}

pub(crate) use display_debug;

pub trait Bind<X> {}

impl<T, X> Bind<X> for T {}

pub(crate) fn minmax<T: Ord>(t1: T, t2: T) -> [T; 2] {
    if t1 < t2 {
        [t1, t2]
    } else {
        [t2, t1]
    }
}

pub enum Either<L, R> {
    Left(L),
    Right(R),
}

impl<L: Iterator, R: Iterator<Item = L::Item>> Iterator for Either<L, R> {
    type Item = L::Item;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Either::Left(l) => l.next(),
            Either::Right(r) => r.next(),
        }
    }

    fn fold<B, F>(self, init: B, f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        match self {
            Either::Left(l) => l.fold(init, f),
            Either::Right(r) => r.fold(init, f),
        }
    }
}

impl<L: InternalIterator, R: InternalIterator<Item = L::Item>> InternalIterator for Either<L, R> {
    type Item = L::Item;

    fn try_for_each<Res, F>(self, f: F) -> ControlFlow<Res>
    where
        F: FnMut(Self::Item) -> ControlFlow<Res>,
    {
        match self {
            Either::Left(l) => l.try_for_each(f),
            Either::Right(r) => r.try_for_each(f),
        }
    }
}

pub type DefaultHashBuilder = std::hash::BuildHasherDefault<rustc_hash::FxHasher>;

pub fn powi(mut f: f64, mut exp: u32) -> f64 {
    let mut res = 1.0;
    while exp != 0 {
        if exp & 1 != 0 {
            res *= f;
        }
        f *= f;
        exp >>= 1;
    }
    res
}

#[test]
fn test_powi() {
    debug_assert_eq!(powi(0.1, 5), 0.1f64.powi(5))
}

pub(crate) fn extend_result<T, E>(
    r: &mut impl Extend<T>,
    iter: impl Iterator<Item = Result<T, E>>,
) -> Result<(), E> {
    let mut res = Ok(());
    r.extend(iter.map_while(|x| match x {
        Ok(x) => Some(x),
        Err(e) => {
            res = Err(e);
            None
        }
    }));
    res
}

pub(crate) fn pairwise_sym<T>(slice: &[T]) -> impl Iterator<Item = (&T, &T)> {
    (0..slice.len())
        .flat_map(move |i| (i + 1..slice.len()).map(move |j| (i, j)))
        .map(|(i, j)| (&slice[i], &slice[j]))
}
