#![forbid(unsafe_code)]
#![no_std]

extern crate alloc;
extern crate no_std_compat as std;

mod approx_bitset;
pub mod euf;
mod exp;
mod full_buf_read;
pub mod intern;
pub mod junction;
mod local_error;
pub mod outer_solver;
mod parser;
pub mod parser_core;
mod reborrow;
mod solver;
mod sp_insert_map;
mod theory;
mod util;

use intern::Symbol;

pub use exp::{BoolExp, Exp, HasSort};
pub use full_buf_read::FullBufRead;
pub use intern::Sort;
#[doc(inline)]
pub use junction::{Conjunction, Disjunction};
pub use outer_solver::{AddSexpError, OuterSolver};
pub use parser::interp_smt2;
pub use solver::{Approx, BLit, SolveResult, Solver};
