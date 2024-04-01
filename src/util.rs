use core::fmt::{Debug, Display, Formatter};

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
pub struct DisplayFn<F>(pub F);

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

pub(crate) struct Parenthesized<'a, I>(I, &'a str);
impl<'a, I: Iterator + Clone> Display for Parenthesized<'a, I>
where
    I::Item: Display,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut iter = self.0.clone();
        write!(f, "(")?;
        if let Some(x) = iter.next() {
            write!(f, "{x}")?;
        }
        for x in iter {
            write!(f, "{}{x}", self.1)?;
        }
        write!(f, ")")
    }
}

pub(crate) fn parenthesized<I: IntoIterator>(iter: I, sep: &str) -> Parenthesized<'_, I::IntoIter> {
    Parenthesized(iter.into_iter(), sep)
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
