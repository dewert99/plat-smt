#![forbid(unsafe_code)]
#![no_std]

extern crate alloc;
extern crate no_std_compat as std;

mod collapse;

#[cfg(feature = "euf")]
pub mod euf;
mod exp;
mod full_buf_read;
pub mod intern;
pub mod junction;
pub mod outer_solver;
pub mod parser;
mod reborrow;
mod solver;
mod theory;
mod tseitin;
mod util;

#[path = "core-ops.rs"]
mod core_ops;
pub mod empty_theory;
mod full_theory;
mod parser_fragment;
pub mod recorder;
pub mod rexp;

use intern::Symbol;

pub use exp::{BoolExp, ExpLike, HasSort, StaticSort, SubExp, SuperExp};
pub use full_buf_read::FullBufRead;
pub use intern::Sort;
#[doc(inline)]
pub use junction::{Conjunction, Disjunction};
pub use outer_solver::OuterSolver;
pub use parser::{incremental_parser::IncrementalParser, parser::interp_smt2};
pub use parser_fragment::AddSexpError;
pub use solver::{Approx, BLit, SolveResult, Solver};
