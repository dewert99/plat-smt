use std::io::{Read, Result};

pub trait FullBufRead {
    /// Try to fill buffer, so it has at least `new_size` elements
    /// if `self.data().len() >= new_size` it does nothing
    /// if `self.data().len() < new_size` after the call it indicates an EOI
    fn fill_to(&mut self, new_size: usize) -> Result<()>;

    /// Get the data buffered so far
    fn data(&self) -> &[u8];

    /// Combine [`Self::fill_to`] and [`Self::data`]
    #[inline(always)]
    fn fill_to_data(&mut self, new_size: usize) -> Result<&[u8]> {
        self.fill_to(new_size)?;
        Ok(self.data())
    }
}

impl<R: AsRef<[u8]>> FullBufRead for R {
    #[inline(always)]
    fn fill_to(&mut self, _: usize) -> Result<()> {
        Ok(())
    }

    #[inline(always)]
    fn data(&self) -> &[u8] {
        self.as_ref()
    }
}

pub struct FullBufReader<R: Read> {
    buf: Vec<u8>,
    read_to: usize,
    reader: R,
}

impl<R: Read> FullBufReader<R> {
    pub fn new(reader: R, capacity: usize) -> Self {
        FullBufReader {
            reader,
            read_to: 0,
            buf: vec![0; capacity],
        }
    }

    #[inline(never)]
    fn fill_to_inner(&mut self, new_size: usize) -> Result<()> {
        self.buf.reserve(new_size.saturating_sub(self.read_to));
        while self.read_to < new_size {
            if self.read_to == self.buf.len() {
                self.buf.resize(self.read_to * 2, 0)
            }
            let read = self.reader.read(&mut self.buf[self.read_to..])?;
            if read == 0 {
                return Ok(());
            }
            self.read_to += read;
        }
        Ok(())
    }
}

impl<R: Read> FullBufRead for FullBufReader<R> {
    #[inline(always)]
    fn fill_to(&mut self, new_size: usize) -> Result<()> {
        if self.read_to < new_size {
            self.fill_to_inner(new_size)
        } else {
            Ok(())
        }
    }

    #[inline(always)]
    fn data(&self) -> &[u8] {
        &self.buf[..self.read_to]
    }
}
