#![forbid(unsafe_code)]
#![no_std]

extern crate alloc;
extern crate no_std_compat as std;

mod collapse;

#[cfg(feature = "euf")]
pub mod euf;

#[cfg(feature = "lra")]
pub mod lra;

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
pub mod core_ops;
pub mod empty_theory;
mod full_theory;
mod parser_fragment;
pub mod recorder;
pub mod reuse_mem;
pub mod rexp;

use intern::Symbol;

pub use exp::{BoolExp, EitherExp, ExpLike, Fresh, HasSort, StaticSort, SubExp, SuperExp};
pub use full_buf_read::FullBufRead;
pub use intern::Sort;
#[doc(inline)]
pub use junction::{Conjunction, Disjunction};
pub use outer_solver::OuterSolver;
pub use parser::{incremental_parser::IncrementalParser, parser::interp_smt2};
pub use parser_fragment::AddSexpError;
pub use solver::{Approx, BLit, SolveResult, Solver, SolverCollapse};

pub mod default {
    #[cfg(feature = "euf")]
    use crate::euf::{Euf as Th0, EufPf as Pf0};

    #[cfg(not(feature = "euf"))]
    use crate::empty_theory::{EmptyTheory as Th0, EmptyTheoryPf as Pf0};

    #[cfg(feature = "interpolant")]
    pub use crate::recorder::InterpolantRecorder as DefaultRecorder;

    #[cfg(not(feature = "interpolant"))]
    pub use crate::recorder::LoggingRecorder as DefaultRecorder;

    #[cfg(not(feature = "lra"))]
    type Pf1 = Pf0;
    #[cfg(feature = "lra")]
    type Pf1 = (crate::lra::LinearArithPf, Pf0);

    #[cfg(not(feature = "lra"))]
    type Th1 = Th0;
    #[cfg(feature = "lra")]
    type Th1 = (Th0, crate::lra::Lra);

    pub type DefaultTh = Th1;
    pub type DefaultPf = Pf1;

    pub type DefaultLogic<M> = (DefaultTh, DefaultPf, DefaultRecorder, M);
}
