use crate::lra::tableau::NumVar;
use dary_heap::QuaternaryHeap;
use default_vec2::BitSet;
use std::cmp::Reverse;

#[derive(Clone, Default)]
pub(super) struct NumVarOrdering {
    out_of_bounds: QuaternaryHeap<Reverse<NumVar>>,
    out_of_bounds_set: BitSet<NumVar>,
}

impl NumVarOrdering {
    pub(super) fn heap_push(&mut self, var: NumVar) {
        if self.out_of_bounds_set.insert(var) {
            self.out_of_bounds.push(Reverse(var))
        }
    }

    pub(super) fn heap_pop(&mut self) -> Option<NumVar> {
        self.out_of_bounds.pop().map(|x| {
            self.out_of_bounds_set.remove(x.0);
            x.0
        })
    }
}
