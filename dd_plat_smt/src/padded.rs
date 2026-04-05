use std::fmt::{Debug, Formatter, Result, Write};

struct CountingWriter<'a, 'b>(usize, &'a mut Formatter<'b>);
impl<'a, 'b> Write for CountingWriter<'a, 'b> {
    fn write_str(&mut self, s: &str) -> Result {
        self.0 += s.len();
        self.1.write_str(s)
    }
}

pub struct Padded<T>(pub T, pub usize);

impl<T: Debug> Debug for Padded<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let mut c = CountingWriter(0, f);
        write!(c, "{:?}", self.0)?;
        let remaining = self.1.saturating_sub(c.0);
        write!(f, "{:remaining$}", "")
    }
}
