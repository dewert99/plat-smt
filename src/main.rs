#![forbid(unsafe_code)]
use plat_smt::recorder::LoggingRecorder;
use plat_smt::FullBufRead;
use std::fs::File;
use std::io::{empty, stderr, stdin, stdout, Read};

#[cfg(feature = "euf")]
use plat_smt::euf::{Euf as Th, EufPf as Pf};

#[cfg(not(feature = "euf"))]
use plat_smt::empty_theory::{EmptyTheory as Th, EmptyTheoryPf as Pf};

enum Either<L, R> {
    Left(L),
    Right(R),
}

impl<L: Read, R: Read> Read for Either<L, R> {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        match self {
            Either::Left(l) => l.read(buf),
            Either::Right(r) => r.read(buf),
        }
    }
}

pub struct FullBufReader<R: Read> {
    buf: Vec<u8>,
    read_to: usize,
    reader: Option<R>,
}

impl<R: Read> FullBufReader<R> {
    pub fn new(reader: R, init: Vec<u8>) -> Self {
        FullBufReader {
            reader: Some(reader),
            read_to: init.len(),
            buf: init,
        }
    }

    #[inline(never)]
    fn fill_to_inner(&mut self, new_size: usize) {
        let Some(reader) = &mut self.reader else {
            return;
        };
        if self.read_to >= self.buf.len() / 2 {
            self.buf.reserve(new_size.saturating_sub(self.read_to));
            self.buf.resize(self.buf.capacity(), 0);
        }
        debug_assert!(self.buf.len() >= new_size);
        while self.read_to < new_size {
            let read = reader.read(&mut self.buf[self.read_to..]).unwrap();
            if read == 0 {
                return;
            }
            self.read_to += read;
        }
    }
}

impl<R: Read> FullBufRead for FullBufReader<R> {
    #[inline(always)]
    fn fill_to(&mut self, new_size: usize) {
        if self.read_to < new_size {
            self.fill_to_inner(new_size)
        }
    }

    #[inline(always)]
    fn data(&self) -> &[u8] {
        &self.buf[..self.read_to]
    }

    fn close(&mut self) {
        self.reader = None;
    }
}

struct WrapWrite<W>(W);

impl<W: std::io::Write> std::fmt::Write for WrapWrite<W> {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        self.0.write_all(s.as_bytes()).map_err(|_| std::fmt::Error)
    }
}

fn main() {
    #[cfg(feature = "env_logger")]
    env_logger::init();
    let mut buf = Vec::new();
    let mut interactive = false;
    for arg in std::env::args().skip(1) {
        if &*arg == "-i" {
            interactive = true;
        } else {
            let Ok(mut file) = File::open(&arg) else {
                eprintln!("{arg} is not a valid file");
                continue;
            };
            file.read_to_end(&mut buf).unwrap();
        }
    }
    let reader = if interactive {
        Either::Left(stdin())
    } else {
        Either::Right(empty())
    };
    plat_smt::interp_smt2::<(Th, Pf, LoggingRecorder, _)>(
        FullBufReader::new(reader, buf),
        WrapWrite(stdout()),
        WrapWrite(stderr()),
    )
}
