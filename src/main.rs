use std::fs::File;
use std::io::{stderr, stdout, Read};

mod egraph;
mod euf;
mod explain;
mod junction;
mod parser;
mod parser_core;
mod solver;
mod sort;
mod util;

fn main() {
    #[cfg(feature = "env_logger")]
    env_logger::init();
    let mut file = File::open(std::env::args().nth(1).unwrap()).unwrap();
    let mut buf: Vec<u8> = Vec::new();
    file.read_to_end(&mut buf).unwrap();
    parser::interp_smt2(&buf, stdout(), stderr())
}
