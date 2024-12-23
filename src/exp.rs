use crate::intern::{Sort, BOOL_SORT};
use plat_egg::Id;
use platsat::clause::{Lit, Var};
use std::ops::{BitXor, Not};

pub trait HasSort {
    fn sort(self) -> Sort;
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct UExp {
    id: Id,
    sort: Sort,
}

impl UExp {
    pub fn id(self) -> Id {
        self.id
    }

    pub fn new(id: Id, sort: Sort) -> Self {
        UExp { id, sort }
    }

    pub fn with_id(self, new_id: Id) -> Self {
        UExp {
            id: new_id,
            sort: self.sort,
        }
    }
}

impl HasSort for UExp {
    fn sort(self) -> Sort {
        self.sort
    }
}

/// A boolean sorted expression within a [`Solver`]
///
/// It can be upcast to a dynamically sorted [`Exp`] using [`into`](Into::into), and downcast using
/// [`Exp::as_bool`].
///
/// It also implements [`BitAnd`](core::ops::BitAnd), [`BitOr`](core::ops::BitOr), and
/// [`Not`], but its [`BitAnd`](core::ops::BitAnd) and [`BitOr`](core::ops::BitOr)
/// implementations produces [`Conjunction`]s and [`Disjunction`]s respectively.
/// [`Solver::collapse_bool`] can be used to collapse these types back into [`BoolExp`]s
#[derive(Copy, Clone, Eq, PartialEq)]
pub struct BoolExp(Lit);

impl From<BoolExp> for Exp {
    fn from(value: BoolExp) -> Self {
        Exp::Bool(value)
    }
}

impl From<UExp> for Exp {
    fn from(value: UExp) -> Self {
        Exp::Uninterpreted(value)
    }
}

impl HasSort for Exp {
    fn sort(self) -> Sort {
        match self {
            Exp::Bool(_) => BOOL_SORT,
            Exp::Uninterpreted(u) => u.sort,
        }
    }
}

/// A dynamically sorted expression within a [`Solver`]
#[derive(Copy, Clone, Eq, PartialEq)]
pub enum Exp {
    Bool(BoolExp),
    Uninterpreted(UExp),
}

impl Exp {
    /// Try to downcast into a [`BoolExp`]
    pub fn as_bool(self) -> Option<BoolExp> {
        match self {
            Exp::Bool(b) => Some(b),
            _ => None,
        }
    }
}

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
}

impl HasSort for BoolExp {
    fn sort(self) -> Sort {
        BOOL_SORT
    }
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
