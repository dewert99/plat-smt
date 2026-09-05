use crate::lra::tableau::NumVar;
use crate::util::DefaultHashBuilder;
use core::hash::{BuildHasher, Hash, Hasher};
use crypto_bigint::modular::ConstMontyForm;
use crypto_bigint::{U64, const_monty_params};
use lazy_rational::Rational32;

const_monty_params!(BigU64Mod, U64, "ffffffffffffffc5");

pub(super) type FieldElt = ConstMontyForm<BigU64Mod, 1>;

pub(super) fn rational_to_field_elt(r: Rational32) -> FieldElt {
    let (n, d) = r.parts();
    let n = if n < 0 {
        -FieldElt::new(&U64::from_u32(-n as u32))
    } else {
        FieldElt::new(&U64::from_u32(n as u32))
    };
    let d = FieldElt::new(&U64::from_u32(d)).invert_vartime().unwrap();
    n * d
}

pub(super) fn num_var_to_field_elt(n: NumVar) -> FieldElt {
    let h = DefaultHashBuilder::default();
    FieldElt::new(&U64::from_u64(h.hash_one(n)))
}

#[test]
fn test() {
    let var = num_var_to_field_elt(NumVar::ONE);
    let three_half = rational_to_field_elt(Rational32::new(2).recip() * Rational32::new(3));
    let v3a = var + var + var;
    let v3b = (var * three_half) + (var * three_half);
    let v3c = (var + var) * three_half;
    assert_eq!(v3a, v3b);
    assert_eq!(v3b, v3c);
    assert_eq!(*BigU64Mod::PARAMS.one(), U64::from_u64(0))
}

#[derive(Copy, Clone, Eq, PartialEq)]
pub(super) struct HashElt(pub(super) FieldElt);

impl Hash for HashElt {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let &[value] = self.0.as_montgomery().as_words();
        state.write_u64(value);
    }
}
