use crate::std::prelude::v1::vec;
use alloc::vec::Vec;
use core::marker::PhantomData;
use core::ops::{Index, IndexMut};

pub struct SliceVec<T, I = usize> {
    elements: Vec<T>,
    indices: Vec<usize>,
    phantom: PhantomData<I>,
}

impl<T, I> Default for SliceVec<T, I> {
    fn default() -> Self {
        SliceVec {
            elements: vec![],
            indices: vec![0],
            phantom: PhantomData,
        }
    }
}

impl<T, I> SliceVec<T, I> {
    pub fn push<It: IntoIterator>(&mut self, i: It)
    where
        Vec<T>: Extend<It::Item>,
    {
        self.elements.extend(i);
        self.indices.push(self.elements.len());
    }

    pub fn len(&self) -> usize {
        self.indices.len() - 1
    }

    pub fn len_idx(&self) -> I
    where
        I: From<usize>,
    {
        self.len().into()
    }

    pub fn indices(&self) -> impl DoubleEndedIterator<Item = I>
    where
        I: From<usize>,
    {
        (0usize..self.len() - 1).into_iter().map(|x| x.into())
    }

    pub fn clear(&mut self) {
        self.indices.clear();
        self.indices.push(0);
        self.elements.clear();
    }

    pub fn truncate(&mut self, new_len_idx: I)
    where
        I: Into<usize>,
    {
        self.indices.truncate(new_len_idx.into() + 1);
        self.elements.truncate(*self.indices.last().unwrap())
    }

    pub fn push_onto_last(&mut self, elt: T) {
        assert!(self.indices.len() > 1);
        self.elements.push(elt);
        *self.indices.last_mut().unwrap() += 1;
    }

    pub fn iter(&self) -> Iter<'_, T> {
        self.into_iter()
    }

    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        self.into_iter()
    }
}

macro_rules! impl_traits {
    (& $($m:ident)?, $Iter:ident, $split_off:ident) => {
        pub struct $Iter<'a, T> {
            indices: &'a [usize],
            elts: &'a $($m)? [T],
        }

        impl<'a, T> Iterator for $Iter<'a, T> {
            type Item = &'a $($m)? [T];

            fn next(&mut self) -> Option<Self::Item> {
                if self.indices.len() <= 1 {
                    None
                } else {
                    let slice_len = self.indices[1] - self.indices[0];
                    self.indices = &self.indices[1..];
                    self.elts.$split_off(..slice_len)
                }
            }

            fn size_hint(&self) -> (usize, Option<usize>) {
                let res = self.indices.len() - 1;
                (res, Some(res))
            }
        }

        impl<'a, T> DoubleEndedIterator for $Iter<'a, T> {
            fn next_back(&mut self) -> Option<Self::Item> {
                if self.indices.len() <= 1 {
                    None
                } else {
                    let indices = self.indices.len();
                    let slice_len = self.indices[indices-1] - self.indices[indices-2];
                    self.indices = &self.indices[..indices-1];
                    self.elts.$split_off(self.elts.len()-slice_len..)
                }
            }
        }

        impl<'a, T, I> IntoIterator for &'a $($m)? SliceVec<T, I> {
            type Item = &'a $($m)? [T];
            type IntoIter = $Iter<'a, T>;

            fn into_iter(self) -> Self::IntoIter {
                $Iter {
                    indices: &self.indices,
                    elts: &$($m)? self.elements,
                }
            }
        }
    };
}

impl_traits!(&, Iter, split_off);
impl_traits!(&mut, IterMut, split_off_mut);

impl<T, I: Into<usize>> Index<I> for SliceVec<T, I> {
    type Output = [T];

    fn index(&self, index: I) -> &Self::Output {
        let index = index.into();
        &self.elements[self.indices[index]..self.indices[index + 1]]
    }
}

impl<T, I: Into<usize>> IndexMut<I> for SliceVec<T, I> {
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        let index = index.into();
        &mut self.elements[self.indices[index]..self.indices[index + 1]]
    }
}
