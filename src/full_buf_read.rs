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

    /// Close the reader causing `fill_to` to stop working
    fn close(&mut self);
}

impl<'a> FullBufRead for &'a [u8] {
    #[inline(always)]
    fn fill_to(&mut self, _: usize) {}

    #[inline(always)]
    fn data(&self) -> &[u8] {
        self
    }

    fn close(&mut self) {}
}

impl<'a> FullBufRead for &'a str {
    #[inline(always)]
    fn fill_to(&mut self, _: usize) {}

    #[inline(always)]
    fn data(&self) -> &[u8] {
        self.as_bytes()
    }

    fn close(&mut self) {}
}

#[diagnostic::on_unimplemented(
    message = "AsyncFullBufRead can only be implemented when using the async feature, use FullBufRead instead if the implementation doesn't need to be async"
)]
pub trait Sealed {}
pub trait AsyncFullBufRead: Sealed {
    /// Try to fill buffer, so it has at least `new_size` elements
    /// if `self.data().len() >= new_size` it does nothing
    /// if `self.data().len() < new_size` after the call it indicates an EOI
    fn fill_to_async(&mut self, new_size: usize) -> impl std::future::Future<Output = ()>;

    /// Get the data buffered so far
    fn data(&self) -> &[u8];

    /// Combine [`Self::fill_to`] and [`Self::data`]
    #[inline(always)]
    fn fill_to_data_async(&mut self, new_size: usize) -> impl std::future::Future<Output = &[u8]> {
        async move {
            self.fill_to_async(new_size).await;
            self.data()
        }
    }

    /// Close the reader causing `fill_to` to stop working
    fn close(&mut self);
}

impl<T: FullBufRead> AsyncFullBufRead for T {
    async fn fill_to_async(&mut self, new_size: usize) {
        self.fill_to(new_size)
    }

    fn data(&self) -> &[u8] {
        self.data()
    }

    async fn fill_to_data_async(&mut self, new_size: usize) -> &[u8] {
        self.fill_to_data(new_size)
    }

    fn close(&mut self) {
        self.close()
    }
}

#[cfg(feature = "async")]
impl<T> Sealed for T {}

#[cfg(not(feature = "async"))]
impl<T: FullBufRead> Sealed for T {}
