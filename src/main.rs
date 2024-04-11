use bat_egg_smt::interp_smt2_with_reader;
use std::fs::File;
use std::io::{empty, stderr, stdin, stdout, Read};

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
    interp_smt2_with_reader(buf, reader, stdout(), stderr())
}
