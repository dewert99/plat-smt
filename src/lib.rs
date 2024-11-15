#![forbid(unsafe_code)]
#![no_std]

extern crate no_std_compat as std;
extern crate alloc;

mod approx_bitset;
mod buffered_solver;
mod egraph;
mod euf;
mod explain;
mod full_buf_read;
pub mod intern;
pub mod junction;
mod parser;
pub mod parser_core;
mod solver;
mod sp_insert_map;
mod theory;
mod util;
mod exp;
mod sexp_to_exp;
pub mod outer_solver;

use intern::Symbol;

pub use full_buf_read::FullBufRead;
pub use intern::Sort;
#[doc(inline)]
pub use junction::{Conjunction, Disjunction};
pub use parser::interp_smt2;
pub use solver::{BLit, SolveResult, Solver};
pub use exp::{Exp, BoolExp, HasSort};
