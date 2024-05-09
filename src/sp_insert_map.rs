use crate::util::DefaultHashBuilder;
use core::fmt::Debug;
use core::hash::{BuildHasher, Hash};
use hashbrown::hash_table::Entry;
use hashbrown::HashTable;
use no_std_compat::prelude::v1::*;
use perfect_derive::perfect_derive;

#[perfect_derive(Default)]
pub(crate) struct SPInsertMap<K, V> {
    map: HashTable<(K, V)>,
    hasher: DefaultHashBuilder,
    pub(crate) entries: Vec<(u64, V)>,
}

impl<K: Hash + Eq + Debug, V: Hash + Ord + Copy + Debug> SPInsertMap<K, V> {
    /// Gets the value associated with `k` or calls `v` to create a new one
    /// If called `v` should return a value larger than all the values in the map
    pub(crate) fn get_or_insert(&mut self, k: K, mut v: impl FnMut() -> V) -> V {
        let hash = self.hasher.hash_one(&k);
        match self
            .map
            .entry(hash, |(k2, _)| *k2 == k, |k2| self.hasher.hash_one(k2))
        {
            Entry::Occupied(occ) => occ.into_mut().1,
            Entry::Vacant(vac) => {
                let v = v();
                if let Some((_, last_v)) = self.entries.last() {
                    debug_assert!(v >= *last_v);
                }
                self.entries.push((hash, v));
                vac.insert((k, v)).into_mut().1
            }
        }
    }

    /// Removes all values at that are at least `lowest_to_remove`
    pub(crate) fn remove_after(&mut self, lowest_to_remove: V) {
        while let Some((hash, v)) = self.entries.pop() {
            if v < lowest_to_remove {
                self.entries.push((hash, v));
                return;
            } else {
                self.map
                    .find_entry(hash, |(_, v2)| *v2 == v)
                    .unwrap()
                    .remove();
            }
        }
    }

    pub(crate) fn clear(&mut self) {
        self.entries.clear();
        self.map.clear();
    }
}
