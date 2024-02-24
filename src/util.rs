use std::fmt::{Debug, Formatter};

pub(crate) struct DebugIter<'a, I>(pub &'a I);

impl<'a, I: Iterator + Clone> Debug for DebugIter<'a, I>
where
    I::Item: Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.0.clone()).finish()
    }
}

macro_rules! display_debug {
    ($ty:ty) => {
        impl core::fmt::Display for $ty {
            fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
                core::fmt::Debug::fmt(self, f)
            }
        }
    };
}

pub(crate) use display_debug;
