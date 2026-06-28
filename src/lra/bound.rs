use crate::lra::tableau::BoundDir;
use core::fmt::{Debug, Formatter};
use core::ops::{Add, Div, Mul, Sub};
use lazy_rational::Rational32;

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Default)]
pub(super) struct EpsilonRational {
    pub(super) base: Rational32,
    pub(super) epsilon: Rational32,
}

impl Debug for EpsilonRational {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        let EpsilonRational { base, epsilon } = self;
        if epsilon.is_zero() {
            write!(f, "{base:?}")
        } else {
            let (num, denom) = epsilon.parts();
            if num < 0 {
                write!(f, "{base:?} - {}ε/{denom}", -num)
            } else {
                write!(f, "{base:?} + {num}ε/{denom}")
            }
        }
    }
}

impl From<Rational32> for EpsilonRational {
    fn from(base: Rational32) -> Self {
        EpsilonRational {
            base,
            epsilon: Rational32::ZERO,
        }
    }
}

impl Mul<Rational32> for EpsilonRational {
    type Output = EpsilonRational;

    fn mul(self, rhs: Rational32) -> Self::Output {
        EpsilonRational {
            base: self.base * rhs,
            epsilon: self.epsilon * rhs,
        }
    }
}

impl Div<Rational32> for EpsilonRational {
    type Output = EpsilonRational;

    fn div(self, rhs: Rational32) -> Self::Output {
        EpsilonRational {
            base: self.base / rhs,
            epsilon: self.epsilon / rhs,
        }
    }
}

impl Add<Rational32> for EpsilonRational {
    type Output = EpsilonRational;

    fn add(self, rhs: Rational32) -> Self::Output {
        EpsilonRational {
            base: self.base + rhs,
            epsilon: self.epsilon,
        }
    }
}

impl Add<EpsilonRational> for EpsilonRational {
    type Output = EpsilonRational;

    fn add(self, rhs: EpsilonRational) -> Self::Output {
        EpsilonRational {
            base: self.base + rhs.base,
            epsilon: self.epsilon + rhs.epsilon,
        }
    }
}

impl Sub<EpsilonRational> for EpsilonRational {
    type Output = EpsilonRational;

    fn sub(self, rhs: EpsilonRational) -> Self::Output {
        EpsilonRational {
            base: self.base - rhs.base,
            epsilon: self.epsilon - rhs.epsilon,
        }
    }
}

impl EpsilonRational {
    pub fn with_epsilon_def(self, epsilon_def: Rational32) -> Rational32 {
        self.base + self.epsilon * epsilon_def
    }
}

#[derive(Copy, Clone, Default, Debug)]
pub(super) struct Bounds {
    pub(super) lower: Option<EpsilonRational>,
    pub(super) upper: Option<EpsilonRational>,
}

impl Bounds {
    /// Returns None if `self` contains `rational`
    pub(super) fn nearest_bound(&self, rational: EpsilonRational) -> Option<EpsilonRational> {
        if self.lower.is_some_and(|lower| rational < lower) {
            self.lower
        } else if self.upper.is_some_and(|upper| rational > upper) {
            self.upper
        } else {
            None
        }
    }

    /// Returns if `rational` is already at a boundary when moving in directly `dir`
    /// Only the sign of `dir` matters, `dir` cannot be zero
    pub(super) fn at_bound(&self, rational: EpsilonRational, dir: EpsilonRational) -> bool {
        let dir = if dir.base.is_zero() {
            dir.epsilon
        } else {
            dir.base
        };
        debug_assert_ne!(dir, Rational32::ZERO);
        if dir > Rational32::ZERO {
            self.upper.is_some_and(|upper| rational >= upper)
        } else {
            self.lower.is_some_and(|lower| rational <= lower)
        }
    }

    /// Returns the upper bound if dir is positive and the lower bound if it is negative
    pub(super) fn pick_bound(&self, dir: Rational32) -> (Rational32, bool, BoundDir) {
        debug_assert_ne!(dir, Rational32::ZERO);
        if dir > Rational32::ZERO {
            let upper = self.upper.unwrap();
            debug_assert!(upper.epsilon <= Rational32::ZERO);
            (upper.base, !upper.epsilon.is_zero(), BoundDir::Upper)
        } else {
            let lower = self.lower.unwrap();
            debug_assert!(lower.epsilon >= Rational32::ZERO);
            (lower.base, !lower.epsilon.is_zero(), BoundDir::Lower)
        }
    }

    pub(super) fn contains_with_epsilon_def(
        &self,
        val: EpsilonRational,
        epsilon_def: Rational32,
    ) -> bool {
        let val = val.with_epsilon_def(epsilon_def);
        self.lower
            .is_none_or(|lower| lower.with_epsilon_def(epsilon_def) <= val)
            && self
                .upper
                .is_none_or(|upper| upper.with_epsilon_def(epsilon_def) >= val)
    }
}
