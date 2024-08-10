use crate::solver::BoolExp;
use core::ops::DerefMut;
use no_std_compat::prelude::v1::*;
use platsat::Lit;
use second_stack2::{with_stack_vec, StackVec};
use stackbox::StackBox;
use std::fmt::{Debug, Formatter};
use std::iter;
use std::ops::{BitAnd, BitOr};

/// Either a [`Conjunction`] or a [`Disjunction`]
#[derive(Eq, PartialEq)]
pub struct Junction<const IS_AND: bool, V = Vec<Lit>> {
    pub(crate) absorbing: bool,
    pub(crate) lits: V,
}

/// A conjunction of [`BoolExp`]s (a collection of [`BoolExp`] combined with `and`)
///
/// See [`Solver::collapse_bool`](crate::solver::Solver::collapse_bool)
/// to reduces a [`Conjunction`] to a [`BoolExp`]
pub type Conjunction<V = Vec<Lit>> = Junction<true, V>;

/// A disjunction of [`BoolExp`]s (a collection of [`BoolExp`] combined with `or`)
///
/// See [`Solver::collapse_bool`](crate::solver::Solver::collapse_bool)
/// to reduces a [`Conjunction`] to a [`BoolExp`]
pub type Disjunction<V = Vec<Lit>> = Junction<false, V>;

impl<const IS_AND: bool> Default for Junction<IS_AND> {
    fn default() -> Self {
        Junction {
            absorbing: false,
            lits: vec![],
        }
    }
}

impl<const IS_AND: bool> Debug for Junction<IS_AND> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if self.absorbing {
            Debug::fmt(&(!IS_AND), f)
        } else {
            let and_or = if IS_AND { "(and" } else { "(or" };
            f.write_str(and_or)?;
            for lit in &self.lits {
                f.write_str(" ")?;
                Debug::fmt(&lit, f)?;
            }
            f.write_str(")")
        }
    }
}

impl<const IS_AND: bool, V: Extend<Lit>> Extend<BoolExp> for Junction<IS_AND, V> {
    fn extend<T: IntoIterator<Item = BoolExp>>(&mut self, iter: T) {
        if !self.absorbing {
            self.lits.extend(
                iter.into_iter()
                    .take_while(|x| match x {
                        BoolExp::Const(x) if *x != IS_AND => {
                            self.absorbing = true;
                            false
                        }
                        _ => true,
                    })
                    .filter_map(|x| match x {
                        BoolExp::Const(_) => None,
                        BoolExp::Unknown(lit) => Some(lit),
                    }),
            );
        }
    }
}

impl<const IS_AND: bool, V: Extend<Lit>> Junction<IS_AND, V> {
    pub fn try_extend<T: IntoIterator<Item = Result<BoolExp, E>>, E>(
        &mut self,
        iter: T,
    ) -> Result<(), E> {
        let mut r = Ok(());
        self.extend(iter.into_iter().map_while(|x| match x {
            Ok(x) => Some(x),
            Err(e) => {
                r = Err(e);
                None
            }
        }));
        r?;
        Ok(())
    }

    pub fn push(&mut self, b: BoolExp) {
        self.extend(iter::once(b))
    }
}

impl<const IS_AND: bool> FromIterator<BoolExp> for Junction<IS_AND> {
    fn from_iter<T: IntoIterator<Item = BoolExp>>(iter: T) -> Self {
        let mut res = Self::default();
        res.extend(iter);
        res
    }
}

impl<const IS_AND: bool> Junction<IS_AND> {
    pub fn clear(&mut self) {
        self.lits.clear();
        self.absorbing = false;
    }
}

impl BitAnd<BoolExp> for BoolExp {
    type Output = Conjunction;

    fn bitand(self, rhs: BoolExp) -> Self::Output {
        Conjunction::from_iter([self, rhs])
    }
}

impl BitAnd<BoolExp> for Conjunction {
    type Output = Conjunction;

    fn bitand(mut self, rhs: BoolExp) -> Self::Output {
        self.push(rhs);
        self
    }
}

impl BitOr<BoolExp> for BoolExp {
    type Output = Disjunction;

    fn bitor(self, rhs: BoolExp) -> Self::Output {
        Disjunction::from_iter([self, rhs])
    }
}

impl BitOr<BoolExp> for Disjunction {
    type Output = Disjunction;

    fn bitor(mut self, rhs: BoolExp) -> Self::Output {
        self.push(rhs);
        self
    }
}

pub fn with_stack_conjunction<R>(f: impl FnOnce(Conjunction<StackVec<Lit>>) -> R) -> R {
    with_stack_vec(|lits| {
        f(Junction {
            lits,
            absorbing: false,
        })
    })
}

pub fn with_stack_disjunction<R>(f: impl FnOnce(Disjunction<StackVec<Lit>>) -> R) -> R {
    with_stack_vec(|lits| {
        f(Junction {
            lits,
            absorbing: false,
        })
    })
}

pub trait IntoSlice<T> {
    type Res: DerefMut<Target = [T]>;

    fn into_slice(self) -> Self::Res;
}

impl<T> IntoSlice<T> for Vec<T> {
    type Res = Self;

    fn into_slice(self) -> Self::Res {
        self
    }
}

impl<'a, T: 'a> IntoSlice<T> for StackVec<'a, T> {
    type Res = StackBox<'a, [T]>;

    fn into_slice(self) -> Self::Res {
        self.into_slice()
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::junction::{Conjunction, Disjunction, Junction};
    use crate::solver::BoolExp;

    fn build<const IS_AND: bool>(i: impl Copy + IntoIterator<Item = BoolExp>) -> Junction<IS_AND> {
        let v1: Junction<IS_AND> = Junction::from_iter(i);
        let mut v2: Junction<IS_AND> = Junction::default();
        v2.extend(i);
        assert_eq!(v2, v1);
        let mut v3: Junction<IS_AND> = Junction::default();
        for x in i {
            v3.push(x);
        }
        assert_eq!(v3, v1);
        v1
    }

    #[test]
    fn test() {
        let c1: Conjunction = build([BoolExp::FALSE, BoolExp::FALSE]);
        assert!(c1.absorbing);
        let c2: Conjunction = build([BoolExp::FALSE, BoolExp::TRUE]);
        assert!(c2.absorbing);
        let c3: Conjunction = build([BoolExp::TRUE, BoolExp::FALSE]);
        assert!(c3.absorbing);
        let c4: Conjunction = build([BoolExp::TRUE, BoolExp::TRUE]);
        assert_eq!(c4, Conjunction::default());
        let d1: Disjunction = build([BoolExp::FALSE, BoolExp::FALSE]);
        assert_eq!(d1, Disjunction::default());
        let d2: Disjunction = build([BoolExp::FALSE, BoolExp::TRUE]);
        assert!(d2.absorbing);
        let d3: Disjunction = build([BoolExp::TRUE, BoolExp::FALSE]);
        assert!(d3.absorbing);
        let d4: Disjunction = build([BoolExp::TRUE, BoolExp::TRUE]);
        assert!(d4.absorbing);
    }

    #[test]
    fn test_ops() {
        assert_eq!(
            BoolExp::TRUE & BoolExp::TRUE & BoolExp::TRUE,
            Conjunction::default()
        );
        assert!((BoolExp::TRUE & BoolExp::FALSE & BoolExp::TRUE).absorbing);
        assert!((BoolExp::FALSE & BoolExp::FALSE & BoolExp::FALSE).absorbing);
        assert!((BoolExp::TRUE | BoolExp::TRUE | BoolExp::TRUE).absorbing);
        assert!((BoolExp::TRUE | BoolExp::FALSE | BoolExp::TRUE).absorbing);
        assert_eq!(
            BoolExp::FALSE | BoolExp::FALSE | BoolExp::FALSE,
            Disjunction::default()
        );
    }
}
