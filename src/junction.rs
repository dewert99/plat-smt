use crate::solver::BoolExp;
use batsat::Lit;
use std::ops::{BitAnd, BitOr};

pub struct Junction<const IS_AND: bool>(pub(super) Option<Vec<Lit>>);

pub type Conjunction = Junction<true>;

pub type Disjunction = Junction<false>;

impl<const IS_AND: bool> Default for Junction<IS_AND> {
    fn default() -> Self {
        Junction(Some(vec![]))
    }
}

impl<const IS_AND: bool> Extend<BoolExp> for Junction<IS_AND> {
    fn extend<T: IntoIterator<Item = BoolExp>>(&mut self, iter: T) {
        if let Some(v) = &mut self.0 {
            let mut mk_none = false;
            v.extend(
                iter.into_iter()
                    .take_while(|x| match x {
                        BoolExp::Const(x) if *x != IS_AND => {
                            mk_none = true;
                            false
                        }
                        _ => true,
                    })
                    .filter_map(|x| match x {
                        BoolExp::Const(_) => None,
                        BoolExp::Unknown(lit) => Some(lit),
                    }),
            );
            if mk_none {
                self.0 = None
            }
        }
    }
}

impl<const IS_AND: bool> FromIterator<BoolExp> for Junction<IS_AND> {
    fn from_iter<T: IntoIterator<Item = BoolExp>>(iter: T) -> Self {
        Junction(
            iter.into_iter()
                .filter_map(|x| match x {
                    BoolExp::Const(x) if x != IS_AND => Some(None),
                    BoolExp::Const(_) => None,
                    BoolExp::Unknown(lit) => Some(Some(lit)),
                })
                .collect(),
        )
    }
}

impl<const IS_AND: bool> Junction<IS_AND> {
    fn push(&mut self, b: BoolExp) {
        self.extend([b])
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
    use crate::junction::{Conjunction, Disjunction, Junction};
    use crate::solver::BoolExp;

    fn build<const IS_AND: bool>(i: impl Copy + IntoIterator<Item = BoolExp>) -> Junction<IS_AND> {
        let v1: Junction<IS_AND> = Junction::from_iter(i);
        let mut v2: Junction<IS_AND> = Junction::default();
        v2.extend(i);
        assert_eq!(v2.0, v1.0);
        let mut v3: Junction<IS_AND> = Junction::default();
        for x in i {
            v3.push(x);
        }
        assert_eq!(v3.0, v1.0);
        v1
    }

    #[test]
    fn test() {
        let c1: Conjunction = build([BoolExp::FALSE, BoolExp::FALSE]);
        assert_eq!(c1.0, None);
        let c2: Conjunction = build([BoolExp::FALSE, BoolExp::TRUE]);
        assert_eq!(c2.0, None);
        let c3: Conjunction = build([BoolExp::TRUE, BoolExp::FALSE]);
        assert_eq!(c3.0, None);
        let c4: Conjunction = build([BoolExp::TRUE, BoolExp::TRUE]);
        assert_eq!(c4.0, Some(vec![]));
        let d1: Disjunction = build([BoolExp::FALSE, BoolExp::FALSE]);
        assert_eq!(d1.0, Some(vec![]));
        let d2: Disjunction = build([BoolExp::FALSE, BoolExp::TRUE]);
        assert_eq!(d2.0, None);
        let d3: Disjunction = build([BoolExp::TRUE, BoolExp::FALSE]);
        assert_eq!(d3.0, None);
        let d4: Disjunction = build([BoolExp::TRUE, BoolExp::TRUE]);
        assert_eq!(d4.0, None);
    }

    #[test]
    fn test_ops() {
        assert_eq!(
            (BoolExp::TRUE & BoolExp::TRUE & BoolExp::TRUE).0,
            Some(vec![])
        );
        assert_eq!((BoolExp::TRUE & BoolExp::FALSE & BoolExp::TRUE).0, None);
        assert_eq!((BoolExp::FALSE & BoolExp::FALSE & BoolExp::FALSE).0, None);
        assert_eq!((BoolExp::TRUE | BoolExp::TRUE | BoolExp::TRUE).0, None);
        assert_eq!((BoolExp::TRUE | BoolExp::FALSE | BoolExp::TRUE).0, None);
        assert_eq!(
            (BoolExp::FALSE | BoolExp::FALSE | BoolExp::FALSE).0,
            Some(vec![])
        );
    }
}
