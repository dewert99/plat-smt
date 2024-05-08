use batsat::intmap::AsIndex;
use no_std_compat::prelude::v1::*;
use std::marker::PhantomData;

#[derive(Clone)]
pub struct SliceVec<I: AsIndex, T, S> {
    slice_data: Vec<S>,
    data: Vec<(T, u32)>,
    p: PhantomData<I>,
}

impl<I: AsIndex, T: Default, S> Default for SliceVec<I, T, S> {
    fn default() -> Self {
        SliceVec {
            slice_data: vec![],
            data: vec![(T::default(), 0)],
            p: Default::default(),
        }
    }
}

impl<I: AsIndex, T, S> SliceVec<I, T, S> {
    pub fn push<E>(&mut self, t: T, s: impl IntoIterator<Item = E>) -> I
    where
        Vec<S>: Extend<E>,
    {
        let res = I::from_index(self.data.len() - 1);
        self.slice_data.extend(s);
        if self.slice_data.len() > u32::MAX as usize {
            panic!("To much slice vec data")
        }
        self.data.push((t, self.slice_data.len() as u32));
        res
    }

    pub(crate) fn slice_data_len(&self) -> u32 {
        self.slice_data.len() as u32
    }

    pub(crate) fn range_to_slice(&self, start: u32, end: u32) -> &[S] {
        &self.slice_data[start as usize..end as usize]
    }

    pub fn lookup(&self, idx: I) -> (&T, &[S]) {
        let idx2 = idx.as_index();
        let next = idx2 + 1;
        let (data, end) = &self.data[next];
        let (_, start) = &self.data[idx2];
        (data, self.range_to_slice(*start, *end))
    }

    pub fn len(&self) -> u32 {
        self.data.len() as u32 - 1
    }

    pub fn truncate(&mut self, new_len: u32) {
        let new_len = new_len as usize;
        let slice_len = self.data[new_len].1 as usize;
        self.slice_data.truncate(slice_len);
        self.data.truncate(new_len + 1)
    }

    pub fn clear(&mut self) {
        self.data.truncate(1);
        self.slice_data.clear();
    }
}
