use crate::full_theory::FullTheory;
use crate::intern::{DisplayInterned, InternInfo, Symbol};
use crate::solver::LevelMarker;
use crate::util::{display_sexp, format_args2};
use crate::{BoolExp, Conjunction, ExpLike, Solver};
use core::convert::Infallible;
use log::{debug, info};
use platsat::theory::ClauseRef;
use platsat::Lit;

#[derive(Debug)]
pub enum ClauseKind {
    Sat,
    Added,
    TheoryExplain,
    TheoryConflict(bool),
}

pub trait Recorder: Default + 'static {
    type Interpolant<'a>;

    fn log_def<Exp: ExpLike, Exp2: ExpLike>(
        &mut self,
        val: Exp,
        f: Symbol,
        arg: impl Iterator<Item = Exp2> + Clone,
        intern: &InternInfo,
    );

    fn log_def_exp<Exp: ExpLike, Exp2: ExpLike>(
        &mut self,
        val: Exp,
        def: Exp2,
        intern: &InternInfo,
    );
    fn log_alias<Exp: ExpLike>(&mut self, alias: Symbol, exp: Exp, intern: &InternInfo);

    fn log_clause(&mut self, clause: &[Lit], kind: ClauseKind);

    fn on_gc_start(&mut self) {}

    fn on_final_lit_explanation(&mut self, _lit: Lit, _reason: ClauseRef) {}

    fn interpolant<'a, Th: FullTheory<Self>>(
        _solver: &'a mut Solver<Th, Self>,
        _pre_solve_marker: LevelMarker<Th::LevelMarker>,
        _assumptions: &Conjunction,
    ) -> Option<Self::Interpolant<'a>> {
        None
    }
}

#[derive(Default)]
pub struct LoggingRecorder;

impl Recorder for LoggingRecorder {
    type Interpolant<'a> = Infallible;

    #[inline]
    fn log_def<Exp: ExpLike, Exp2: ExpLike>(
        &mut self,
        val: Exp,
        f: Symbol,
        arg: impl Iterator<Item = Exp2> + Clone,
        intern: &InternInfo,
    ) {
        info!(
            "(define-const {val:?} {} {})",
            val.sort().with_intern(&intern),
            display_sexp(f.with_intern(intern), arg.map(|x| format_args2!("{x:?}")))
        )
    }

    #[inline(always)]
    fn log_def_exp<Exp: ExpLike, Exp2: ExpLike>(
        &mut self,
        val: Exp,
        def: Exp2,
        intern: &InternInfo,
    ) {
        info!(
            "(define-const {val:?} {} {def:?})",
            val.sort().with_intern(&intern),
        )
    }
    #[inline(always)]
    fn log_alias<Exp: ExpLike>(&mut self, alias: Symbol, exp: Exp, intern: &InternInfo) {
        info!("(assert (= {} {exp:?}))", alias.with_intern(intern))
    }
    fn log_clause(&mut self, clause: &[Lit], _: ClauseKind) {
        debug!(
            "(assert {})",
            display_sexp(
                "or",
                clause.iter().map(|x| format_args2!(
                    "{:?\
                    }",
                    BoolExp::unknown(*x)
                ))
            )
        )
    }
}
