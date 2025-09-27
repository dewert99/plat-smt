use crate::full_theory::FullTheory;
use crate::intern::{DisplayInterned, InternInfo, Symbol};
use crate::rexp::AsRexp;
use crate::solver::LevelMarker;
use crate::theory::Incremental;
use crate::util::{display_sexp, format_args2};
use crate::{BoolExp, Conjunction, ExpLike, Solver};
use core::convert::Infallible;
use core::fmt::Display;
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

pub trait Recorder: Default + Incremental + 'static {
    type Interpolant<'a>: Display;

    fn log_def<Exp: ExpLike, Exp2: AsRexp>(
        &mut self,
        val: Exp,
        f: Symbol,
        arg: impl Iterator<Item = Exp2> + Clone,
        intern: &InternInfo,
    );

    fn log_def_exp<Exp: ExpLike, Exp2: AsRexp>(&mut self, val: Exp, def: Exp2, intern: &InternInfo);
    fn log_alias<Exp: ExpLike>(&mut self, alias: Symbol, exp: Exp, intern: &InternInfo);

    fn log_clause(&mut self, clause: &[Lit], kind: ClauseKind);

    fn on_gc_start(&mut self) {}

    fn on_final_lit_explanation(&mut self, _lit: Lit, _reason: ClauseRef) {}

    fn should_explain_conflict_final(&self) -> bool {
        false
    }

    type BoolBufMarker: Copy;

    fn intern_bools(&mut self, bools: impl Iterator<Item = BoolExp>) -> Self::BoolBufMarker;

    fn try_intern_bools<E>(
        &mut self,
        mut bools: impl Iterator<Item = Result<BoolExp, E>>,
    ) -> Result<Self::BoolBufMarker, E> {
        let mut status = Ok(());
        let res = self.intern_bools(bools.by_ref().map_while(|x| match x {
            Ok(x) => Some(x),
            Err(e) => {
                status = Err(e);
                None
            }
        }));
        status?;
        bools.try_for_each(|x| x.map(|_| ()))?;
        Ok(res)
    }

    fn interpolant<'a, Th: FullTheory<Self>>(
        _solver: &'a mut Solver<Th, Self>,
        _pre_solve_marker: LevelMarker<Th::LevelMarker, Self::LevelMarker>,
        _assumptions: &Conjunction,
        _a: Self::BoolBufMarker,
        _b: Self::BoolBufMarker,
    ) -> Option<Self::Interpolant<'a>> {
        None
    }

    fn exit_solved_state(&mut self) {}
}

#[derive(Default)]
pub struct LoggingRecorder;

impl Incremental for LoggingRecorder {
    type LevelMarker = ();

    fn create_level(&self) -> Self::LevelMarker {}

    fn pop_to_level(&mut self, _: Self::LevelMarker, _: bool) {}

    fn clear(&mut self) {}
}

impl Recorder for LoggingRecorder {
    type Interpolant<'a> = Infallible;

    #[inline]
    fn log_def<Exp: ExpLike, Exp2: AsRexp>(
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
    fn log_def_exp<Exp: ExpLike, Exp2: AsRexp>(
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

    type BoolBufMarker = ();

    fn intern_bools(&mut self, _: impl Iterator<Item = BoolExp>) -> Self::BoolBufMarker {}
}
