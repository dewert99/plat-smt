#![forbid(unsafe_code)]
#![no_std]

extern crate alloc;
extern crate no_std_compat as std;

mod approx_bitset;
mod ast_solver;
mod buffered_solver;
mod egraph;
mod euf;
mod explain;
mod full_buf_read;
mod index;
mod intern;
pub mod junction;
mod parser;
pub mod parser_core;
mod slice_vec;
mod solver;
mod sp_insert_map;
mod theory;
mod util;

use intern::Symbol;

pub use full_buf_read::FullBufRead;
pub use intern::Sort;
#[doc(inline)]
pub use junction::{Conjunction, Disjunction};
pub use parser::interp_smt2;
pub use solver::{BLit, BoolExp, Exp, SolveResult, Solver};
