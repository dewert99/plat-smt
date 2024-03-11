use bat_egg_smt::interp_smt2_with_reader;
use either::Either;
use std::fs::File;
use std::io::{empty, stderr, stdin, stdout, Read};

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
