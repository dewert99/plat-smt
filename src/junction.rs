use crate::BoolExp;
use no_std_compat::prelude::v1::*;
use platsat::Lit;
use std::fmt::{Debug, Formatter};
use std::ops::{BitAnd, BitOr};

/// Either a [`Conjunction`] or a [`Disjunction`]
#[derive(Eq, PartialEq)]
pub struct Junction<const IS_AND: bool> {
    pub(crate) absorbing: bool,
    pub(crate) lits: Vec<Lit>,
}

/// A conjunction of [`BoolExp`]s (a collection of [`BoolExp`] combined with `and`)
///
/// See [`Solver::collapse_bool`](crate::solver::Solver::collapse_bool)
/// to reduces a [`Conjunction`] to a [`BoolExp`]
pub type Conjunction = Junction<true>;

/// A disjunction of [`BoolExp`]s (a collection of [`BoolExp`] combined with `or`)
///
/// See [`Solver::collapse_bool`](crate::solver::Solver::collapse_bool)
/// to reduces a [`Conjunction`] to a [`BoolExp`]
pub type Disjunction = Junction<false>;

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

impl<const IS_AND: bool> Extend<BoolExp> for Junction<IS_AND> {
    fn extend<T: IntoIterator<Item = BoolExp>>(&mut self, iter: T) {
        if !self.absorbing {
            let mut iter = iter.into_iter();
            self.lits.extend(
                iter.by_ref()
                    .take_while(|x| match x.to_lit() {
                        Err(x) if x != IS_AND => {
                            self.absorbing = true;
                            false
                        }
                        _ => true,
                    })
                    .filter_map(|x| match x.to_lit() {
                        Err(_) => None,
                        Ok(lit) => Some(lit),
                    }),
            );
            iter.for_each(|_| ());
        }
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
    pub fn push(&mut self, b: BoolExp) {
        self.extend([b])
    }

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

#[cfg(test)]
mod test {
    use super::*;
    use crate::junction::{Conjunction, Disjunction, Junction};
    use crate::BoolExp;

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
