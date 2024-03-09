use crate::full_buf_read::FullBufReader;
use std::fs::File;
use std::io::{stderr, stdin, stdout, Read};

mod egraph;
mod euf;
mod explain;
mod full_buf_read;
mod junction;
mod parser;
mod parser_core;
mod solver;
mod sort;
mod util;

fn main() {
    #[cfg(feature = "env_logger")]
    env_logger::init();
    let mut parser = parser::Parser::new(stdout());
    for arg in std::env::args().skip(1) {
        if &*arg == "-i" {
            parser.interp_smt2(FullBufReader::new(stdin(), 256), stderr())
        } else {
            let Ok(mut file) = File::open(&arg) else {
                eprintln!("{arg} is not a valid file");
                continue;
            };
            let mut buf: Vec<u8> = Vec::new();
            file.read_to_end(&mut buf).unwrap();
            parser::interp_smt2(&buf, stdout(), stderr())
        }
    }
}
