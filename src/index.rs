use batsat::intmap::AsIndex;
use core::any::type_name;
use core::fmt::{Debug, Formatter};
use std::marker::PhantomData;

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Default)]
pub struct IndexInner<T>(u32, T);
pub type Idx<T> = IndexInner<PhantomData<T>>;

impl<T> Debug for Idx<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        let name = type_name::<T>();
        let idx = name.rfind(":").map_or(0, |x| x + 1);
        let name = &name[idx..];
        f.debug_tuple(name).field(&self.0).finish()
    }
}

impl<T> AsIndex for Idx<T> {
    fn as_index(self) -> usize {
        self.0 as usize
    }

    fn from_index(index: usize) -> Self {
        debug_assert!(index < u32::MAX as usize);
        Self::new(index as u32)
    }
}

impl<T> Idx<T> {
    pub(crate) const fn idx(self) -> u32 {
        self.0
    }

    pub(crate) const fn new(i: u32) -> Self {
        Self(i, PhantomData)
    }
}
