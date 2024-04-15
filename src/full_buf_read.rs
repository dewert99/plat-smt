pub trait FullBufRead {
    /// Try to fill buffer, so it has at least `new_size` elements
    /// if `self.data().len() >= new_size` it does nothing
    /// if `self.data().len() < new_size` after the call it indicates an EOI
    fn fill_to(&mut self, new_size: usize);

    /// Get the data buffered so far
    fn data(&self) -> &[u8];

    /// Combine [`Self::fill_to`] and [`Self::data`]
    #[inline(always)]
    fn fill_to_data(&mut self, new_size: usize) -> &[u8] {
        self.fill_to(new_size);
        self.data()
    }
}

impl<'a> FullBufRead for &'a [u8] {
    #[inline(always)]
    fn fill_to(&mut self, _: usize) {}

    #[inline(always)]
    fn data(&self) -> &[u8] {
        self
    }
}
