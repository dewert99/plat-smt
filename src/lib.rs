#![forbid(unsafe_code)]
#![no_std]

extern crate alloc;
extern crate no_std_compat as std;

mod approx_bitset;
mod collapse;
pub mod euf;
mod exp;
mod full_buf_read;
pub mod intern;
pub mod junction;
pub mod outer_solver;
mod parser;
pub mod parser_core;
mod reborrow;
mod solver;
mod theory;
mod tseitin;
mod util;

#[path = "core-ops.rs"]
mod core_ops;
mod full_theory;
mod parser_fragment;

use intern::Symbol;

pub use exp::{BoolExp, ExpLike, HasSort, StaticSort, SubExp, SuperExp};
pub use full_buf_read::FullBufRead;
pub use intern::Sort;
#[doc(inline)]
pub use junction::{Conjunction, Disjunction};
pub use outer_solver::OuterSolver;
pub use parser::interp_smt2;
pub use parser_fragment::AddSexpError;
pub use solver::{Approx, BLit, SolveResult, Solver};
