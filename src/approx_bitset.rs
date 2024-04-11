use crate::util::DefaultHashBuilder;
use egg::Id;
use hashbrown::HashSet;
use std::fmt::Debug;

type Elt = u128;
pub const BITS: usize = Elt::BITS as usize;

#[derive(Debug)]
pub(crate) struct ApproxBitSet(Elt);

pub(crate) trait IdSet: Debug {
    fn empty() -> Self;

    fn insert(&mut self, val: Id);

    fn may_contain(&self, val: Id) -> bool;

    fn might_confuse(id1: Id, id2: Id) -> bool;
}

impl IdSet for ApproxBitSet {
    fn empty() -> Self {
        ApproxBitSet(0)
    }

    fn insert(&mut self, val: Id) {
        let shift = usize::from(val) % BITS;
        self.0 |= 1 << shift
    }

    fn may_contain(&self, val: Id) -> bool {
        let shift = usize::from(val) % BITS;
        self.0 & (1 << shift) != 0
    }

    fn might_confuse(id1: Id, id2: Id) -> bool {
        usize::from(id1) % BITS == usize::from(id2) % BITS
    }
}

impl IdSet for HashSet<Id, DefaultHashBuilder> {
    fn empty() -> Self {
        HashSet::default()
    }

    fn insert(&mut self, val: Id) {
        self.insert(val);
    }

    fn may_contain(&self, val: Id) -> bool {
        self.contains(&val)
    }

    fn might_confuse(id1: Id, id2: Id) -> bool {
        id1 == id2
    }
}
