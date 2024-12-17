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
        assert_ne!(sort, BOOL_SORT);
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
        Exp {
            sort: BOOL_SORT,
            data: value.to_u32(),
        }
    }
}

impl From<UExp> for Exp {
    fn from(value: UExp) -> Self {
        let data: usize = value.id.into();
        Exp {
            sort: value.sort,
            data: data as u32,
        }
    }
}

impl HasSort for Exp {
    fn sort(self) -> Sort {
        self.sort
    }
}

#[derive(Copy, Clone)]
pub(crate) enum EExp {
    Bool(BoolExp),
    Uninterpreted(UExp),
}

impl Exp {
    pub(crate) fn expand(self) -> EExp {
        if self.sort == BOOL_SORT {
            EExp::Bool(BoolExp::from_u32(self.data))
        } else {
            EExp::Uninterpreted(UExp {
                sort: self.sort,
                id: Id::from(self.data as usize),
            })
        }
    }

    /// Try to downcast into a [`BoolExp`]
    pub fn as_bool(self) -> Option<BoolExp> {
        match self.expand() {
            EExp::Bool(b) => Some(b),
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

    fn to_u32(self) -> u32 {
        self.0.idx()
    }

    fn from_u32(n: u32) -> Self {
        BoolExp(Lit::from(n as usize))
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

/// A dynamically sorted expression within a [`Solver`]
#[derive(Copy, Clone, Eq, PartialEq)]
pub struct Exp {
    sort: Sort,
    data: u32,
}
