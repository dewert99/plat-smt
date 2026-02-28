use crate::intern::{resolve_or_fail, Symbol};

use crate::util::display_sexp;
use core::fmt::{Debug, Display, Formatter};

#[non_exhaustive]
#[derive(Copy, Clone, Hash, Eq, PartialEq)]
pub enum Namespace {
    Bool,
    Uninterpreted,
    SortDefault,
    Number,
    BitVec,
    ConcreteInt,
}

impl Into<&'static str> for Namespace {
    fn into(self) -> &'static str {
        match self {
            Namespace::Bool => "b",
            Namespace::Uninterpreted => "v",
            Namespace::SortDefault => "d",
            Namespace::Number => "n",
            Namespace::BitVec => "bv",
            Namespace::ConcreteInt => "",
        }
    }
}

impl Display for Namespace {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        let x: &str = (*self).into();
        f.write_str(x)
    }
}

#[derive(Copy, Clone, Hash, Eq, PartialEq)]
pub struct NamespaceVar(pub Namespace, pub u32);

impl Display for NamespaceVar {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        if let Namespace::ConcreteInt = self.0 {
            write!(f, "{}", self.1)
        } else {
            write!(f, "@{}{}", self.0, self.1)
        }
    }
}

#[derive(Copy, Clone)]
pub enum Rexp<'a> {
    Nv(NamespaceVar),
    Call(Symbol, &'a [Rexp<'a>]),
}

impl<'a> Rexp<'a> {
    pub(crate) fn unwrap_nv(self) -> NamespaceVar {
        match self {
            Rexp::Nv(nv) => nv,
            _ => panic!("expected {self} to be a single fresh variable"),
        }
    }

    pub fn try_for_each_nv<E>(
        self,
        f: &mut impl FnMut(NamespaceVar) -> Result<(), E>,
    ) -> Result<(), E> {
        match self {
            Rexp::Nv(nv) => f(nv),
            Rexp::Call(_, children) => children.iter().try_for_each(|x| x.try_for_each_nv(f)),
        }
    }
}

impl<'a> Display for Rexp<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match *self {
            Rexp::Nv(n) => Display::fmt(&n, f),
            Rexp::Call(s, children) => {
                write!(f, "{}", display_sexp(resolve_or_fail(s), children.iter()))
            }
        }
    }
}

pub trait AsRexp: Debug {
    fn as_rexp<R>(&self, f: impl for<'a> FnOnce(Rexp<'a>) -> R) -> R;

    fn try_for_each_nv<E>(
        &self,
        mut f: impl FnMut(NamespaceVar) -> Result<(), E>,
    ) -> Result<(), E> {
        self.as_rexp(|r| r.try_for_each_nv(&mut f))
    }
}

macro_rules! rexp_debug {
    ($ty:ty) => {
        impl core::fmt::Debug for $ty {
            fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
                $crate::rexp::AsRexp::as_rexp(self, |rexp| core::fmt::Display::fmt(&rexp, f))
            }
        }
    };
}

pub(crate) use rexp_debug;
