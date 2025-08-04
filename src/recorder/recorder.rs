use crate::intern::{DisplayInterned, InternInfo, Symbol};
use crate::util::{display_sexp, format_args2};
use crate::{BoolExp, ExpLike};
use log::{debug, info};
use platsat::Lit;

pub enum ClauseKind {
    Sat,
    Added,
    TheoryExplain,
    TheoryConflict(bool),
}

pub trait Recorder: Default + 'static {
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
}

#[derive(Default)]
pub struct LoggingRecorder;

impl Recorder for LoggingRecorder {
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
