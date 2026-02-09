use crate::full_theory::FullTheory;
use crate::intern::{DisplayInterned, InternInfo, Symbol};
use crate::parser_core::SpanRange;
use crate::recorder::dep_checker::DepCheckerAction;
use crate::rexp::AsRexp;
use crate::solver::{LevelMarker, UnsatCoreConjunction};
use crate::theory::Incremental;
use crate::util::{display_sexp, format_args2};
use crate::{BoolExp, ExpLike, Solver};
use alloc::borrow::Cow;
use core::fmt::Write;
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

#[non_exhaustive]
pub enum Feature {
    Interpolant,
}

pub struct InterpolantGroup {
    pub(super) is_a: bool,
}

impl InterpolantGroup {
    pub const A: Self = InterpolantGroup { is_a: true };

    pub const B: Self = InterpolantGroup { is_a: false };
}

pub trait Recorder: Default + Incremental + 'static {
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

    fn flag_sym_for_interpolant(&mut self, _sym: Symbol, _group: &InterpolantGroup) {}

    fn write_interpolant<'a, 'b, Th: FullTheory<Self>>(
        _solver: &'a mut Solver<Th, Self>,
        _pre_solve_marker: LevelMarker<Th::LevelMarker, Self::LevelMarker>,
        _assumptions: &UnsatCoreConjunction<SpanRange>,
        _map_assumptions: impl Fn(SpanRange) -> &'b str,
        _writer: &mut impl Write,
    ) -> Result<(), Cow<'static, str>> {
        Err(Cow::Borrowed("unsupported interpolants"))
    }

    /// Return whether feature is enabled
    fn feature_enabled(&self, _feature: Feature) -> bool {
        false
    }

    /// Try to set features enabled status to enable and return if successful
    fn set_feature_enabled(&mut self, feature: Feature, enable: bool) -> bool {
        enable != self.feature_enabled(feature)
    }

    fn exit_solved_state(&mut self) {}

    fn allows_mid_search_add<Exp: AsRexp>(
        &self,
        _children: impl Iterator<Item = Exp> + Clone,
        _intern: &InternInfo,
    ) -> bool {
        true
    }

    fn dep_checker_act(&mut self, _act: impl DepCheckerAction) {}
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
}
