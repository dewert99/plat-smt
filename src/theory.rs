use crate::collapse::{BaseMarker, LeftMarker, RightMarker};
use crate::intern::{InternInfo, Symbol};
use crate::recorder::{ClauseKind, DefExp, InterpolateArg, Recorder};
use crate::rexp::AsRexp;
use crate::tseitin::SatTheoryArgT;
use crate::ExpLike;
use core::fmt::{Debug, Formatter};
use log::debug;
use no_std_compat::prelude::v1::*;
use perfect_derive::perfect_derive;
use platsat::core::ExplainTheoryArg as SatExplainTheoryArg;
use platsat::theory::{ClauseRef, Theory as SatTheory};
use platsat::{Lit, TheoryArg as SatTheoryArg};
use std::ops::{Deref, DerefMut};
pub trait Incremental: Default {
    type LevelMarker: Clone;

    /// Create a new backtracking level, and return a marker that can be used to backtrack to it
    fn create_level(&self) -> Self::LevelMarker;

    /// Pop to the level indicated by marker
    ///
    /// If `clear_lits` is true, all literals created above the level are no longer valid and must
    /// not be used anymore
    fn pop_to_level(&mut self, marker: Self::LevelMarker, clear_lits: bool);

    fn clear(&mut self);
}

impl<I1: Incremental, I2: Incremental> Incremental for (I1, I2) {
    type LevelMarker = (I1::LevelMarker, I2::LevelMarker);

    fn create_level(&self) -> Self::LevelMarker {
        (self.0.create_level(), self.1.create_level())
    }

    fn pop_to_level(&mut self, marker: Self::LevelMarker, clear_lits: bool) {
        self.0.pop_to_level(marker.0, clear_lits);
        self.1.pop_to_level(marker.1, clear_lits);
    }

    fn clear(&mut self) {
        self.0.clear();
        self.1.clear();
    }
}

#[derive(Clone, Debug)]
struct PushInfo<X> {
    th: X,
    model_len: u32,
}

#[perfect_derive(Default, Debug, Clone)]
pub struct TheoryWrapper<Th: Incremental, R> {
    th: Th,
    prev_model_len: u32,
    // whether we've handled prop_log since the last push or pop
    done_prop_log: bool,
    pub(crate) arg: IncrementalArgData<Th::LevelMarker, R>,
}

#[perfect_derive(Default, Clone)]
pub struct IncrementalArgData<M, R> {
    total_level: u32,
    push_log: Vec<PushInfo<M>>,
    pub(crate) junction_buf: Vec<Lit>,
    pub(crate) intern: InternInfo,
    pub(crate) recorder: R,
    pub(super) in_model: bool,
}

impl<M: Debug, R: Debug> Debug for IncrementalArgData<M, R> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("IncrementalArg")
            .field("decision_level", &self.total_level)
            .field("push_log", &self.push_log)
            .field("recorder", &self.recorder)
            .finish()
    }
}

pub trait Reborrow {
    type Target<'b>
    where
        Self: 'b;

    fn reborrow(&mut self) -> Self::Target<'_>;
}

impl<'a> Reborrow for SatTheoryArg<'a> {
    type Target<'b>
        = SatTheoryArg<'b>
    where
        Self: 'b;

    fn reborrow(&mut self) -> Self::Target<'_> {
        self.reborrow()
    }
}

impl<'a, T> Reborrow for &'a mut T {
    type Target<'b>
        = &'b mut T
    where
        Self: 'b;

    fn reborrow(&mut self) -> Self::Target<'_> {
        &mut *self
    }
}

pub struct TheoryArgRaw<'a, S, M, R> {
    pub(crate) sat: S,
    pub(crate) incr: &'a mut IncrementalArgData<M, R>,
    prop_marker: u8,
}

impl<'a, S, M, R> TheoryArgRaw<'a, S, M, R> {
    pub(crate) fn map<'b, S2>(
        &'b mut self,
        f: impl FnOnce(&'b mut S) -> S2,
    ) -> TheoryArgRaw<'b, S2, M, R> {
        TheoryArgRaw {
            sat: f(&mut self.sat),
            incr: &mut *self.incr,
            prop_marker: self.prop_marker,
        }
    }
}

pub type TheoryArg<'a, M, R> = TheoryArgRaw<'a, SatTheoryArg<'a>, M, R>;
pub type ExplainTheoryArg<'a, M, R> = TheoryArgRaw<'a, &'a mut SatExplainTheoryArg, M, R>;

pub trait TheoryArgT {
    type M;

    type R: Recorder;

    fn base_marker(&self) -> Option<&Self::M>;

    fn last_marker(&self) -> Option<&Self::M>;
    fn intern(&self) -> &InternInfo;

    fn intern_mut(&mut self) -> &mut InternInfo;

    fn junction_buf_mut(&mut self) -> &mut Vec<Lit>;

    fn recorder_mut(&mut self) -> (&mut InternInfo, &mut Self::R);

    fn should_explain_conflict_final(&mut self) -> bool {
        self.recorder_mut().1.should_explain_conflict_final()
    }

    fn log_def<Exp: ExpLike, Exp2: AsRexp>(
        &mut self,
        val: Exp,
        f: Symbol,
        arg: impl Iterator<Item = Exp2> + Clone,
    ) {
        let (intern, recorder) = self.recorder_mut();
        recorder.log_def(val, f, arg, intern)
    }

    fn log_def_exp<Exp: ExpLike, Exp2: AsRexp>(&mut self, val: Exp, def: Exp2) {
        let (intern, recorder) = self.recorder_mut();
        recorder.log_def_exp(val, def, intern)
    }
    fn log_alias<Exp: ExpLike>(&mut self, alias: Symbol, exp: Exp) {
        let (intern, recorder) = self.recorder_mut();
        recorder.log_alias(alias, exp, intern)
    }

    fn allows_mid_search_add<Exp: AsRexp>(
        &mut self,
        children: impl Iterator<Item = Exp> + Clone,
    ) -> bool {
        let (intern, recorder) = self.recorder_mut();
        recorder.allows_mid_search_add(children, intern)
    }

    #[doc(hidden)]
    fn prop_marker(&self) -> u8;
}

pub trait TupleExtract<P, M> {
    fn tuple_extract(&self) -> &M;

    fn tuple_extract_mut(&mut self) -> &mut M;
}

impl<X> TupleExtract<BaseMarker, X> for X {
    fn tuple_extract(&self) -> &X {
        self
    }

    fn tuple_extract_mut(&mut self) -> &mut X {
        self
    }
}
impl<P, M, T: TupleExtract<P, M>, O> TupleExtract<LeftMarker<P>, M> for (T, O) {
    fn tuple_extract(&self) -> &M {
        self.0.tuple_extract()
    }

    fn tuple_extract_mut(&mut self) -> &mut M {
        self.0.tuple_extract_mut()
    }
}

impl<P, M, T: TupleExtract<P, M>, O> TupleExtract<RightMarker<P>, M> for (O, T) {
    fn tuple_extract(&self) -> &M {
        self.1.tuple_extract()
    }

    fn tuple_extract_mut(&mut self) -> &mut M {
        self.1.tuple_extract_mut()
    }
}

trait TheoryArgMarker {
    fn marker(&mut self) -> &mut u8;
}

impl<'a, S, M, R: Recorder> TheoryArgMarker for TheoryArgRaw<'a, S, M, R> {
    #[inline]
    fn marker(&mut self) -> &mut u8 {
        &mut self.prop_marker
    }
}

impl<'a, S, M, R: Recorder> TheoryArgT for TheoryArgRaw<'a, S, M, R> {
    type M = M;
    type R = R;
    fn base_marker(&self) -> Option<&M> {
        self.incr.push_log.first().map(|x| &x.th)
    }

    fn last_marker(&self) -> Option<&M> {
        self.incr.push_log.last().map(|x| &x.th)
    }

    fn intern(&self) -> &InternInfo {
        &self.incr.intern
    }

    fn intern_mut(&mut self) -> &mut InternInfo {
        &mut self.incr.intern
    }

    fn junction_buf_mut(&mut self) -> &mut Vec<Lit> {
        &mut self.incr.junction_buf
    }

    fn recorder_mut(&mut self) -> (&mut InternInfo, &mut Self::R) {
        (&mut self.incr.intern, &mut self.incr.recorder)
    }

    fn prop_marker(&self) -> u8 {
        self.prop_marker
    }
}

impl<'a, S: Reborrow, M, R> Reborrow for TheoryArgRaw<'a, S, M, R> {
    type Target<'b>
        = TheoryArgRaw<'b, S::Target<'b>, M, R>
    where
        Self: 'b;

    fn reborrow(&mut self) -> Self::Target<'_> {
        self.map(|x| x.reborrow())
    }
}

/// Theory that parametrizes the solver and can react on events.
pub trait Theory<Arg, ExplainArg, P = BaseMarker> {
    /// Extra initialization step called with theory arg in [`Default`] implementation and after
    /// clear
    fn init(&mut self, _acts: &mut Arg) {}

    /// Pre-check called before `learn`, return `Err` if there is a conflict
    #[allow(unused_variables)]
    fn initial_check(&mut self, acts: &mut Arg) -> Result<(), ()> {
        Ok(())
    }

    /// Add a literal to the model, return `Err` if there is a conflict
    fn learn(&mut self, lit: Lit, acts: &mut Arg) -> Result<(), ()>;

    /// Check partial model before a decision is made
    ///
    /// The whole partial model so far is `acts.model()`,
    /// but all literals in the model will have already been passed to `learn`
    ///
    /// return `Err` if there is a conflict
    fn pre_decision_check(&mut self, acts: &mut Arg) -> Result<(), ()>;

    /// Final check ran before returning sat
    ///
    /// If it doesn't make any propagations or raise a conflict the solver will return sat
    fn final_check(&mut self, _acts: &mut Arg) -> Result<(), ()> {
        Ok(())
    }

    /// If the theory uses [`SatTheoryArgT::propagate`], it must implement
    /// this function to explain the propagations.
    ///
    /// It should add the negation of all literals that were used to imply `p` to
    /// `acts.clause_builder()` while leaving its current elements untouched
    ///
    ///
    /// `acts.clause_builder()` comes pre-initialized with `p` as its first element to satisfy
    /// [`BatTheory::explain_propagation_clause`]'s requirements
    ///
    ///
    fn explain_propagation(&mut self, p: Lit, acts: &mut ExplainArg, is_final: bool, marker: u8);

    fn interpolate_clause(
        &mut self,
        _acts: &mut Arg,
        _clause: impl Fn(&Arg) -> &[Lit],
        _interpolate_arg: impl Fn(&mut Arg) -> InterpolateArg,
        _marker: u8,
    ) -> DefExp {
        todo!()
    }

    #[inline]
    fn prop_types() -> u8 {
        1
    }

    #[doc(hidden)]
    fn adjusted_prop_types() -> u8 {
        Self::prop_types()
    }
}

impl<
        Arg: TheoryArgMarker,
        ExplainArg: TheoryArgMarker,
        P,
        T1: Theory<Arg, ExplainArg, LeftMarker<P>>,
        T2: Theory<Arg, ExplainArg, RightMarker<P>>,
    > Theory<Arg, ExplainArg, P> for (T1, T2)
{
    fn init(&mut self, acts: &mut Arg) {
        self.0.init(acts);
        *acts.marker() += T1::prop_types();
        self.1.init(acts);
        assert!(T1::prop_types().checked_add(T2::prop_types()).is_some());
    }

    fn initial_check(&mut self, acts: &mut Arg) -> Result<(), ()> {
        self.0.initial_check(acts)?;
        *acts.marker() += T1::adjusted_prop_types();
        self.1.initial_check(acts)
    }

    fn learn(&mut self, lit: Lit, acts: &mut Arg) -> Result<(), ()> {
        self.0.learn(lit, acts)?;
        *acts.marker() += T1::adjusted_prop_types();
        self.1.learn(lit, acts)
    }

    fn pre_decision_check(&mut self, acts: &mut Arg) -> Result<(), ()> {
        self.0.pre_decision_check(acts)?;
        *acts.marker() += T1::adjusted_prop_types();
        self.1.pre_decision_check(acts)
    }

    fn final_check(&mut self, acts: &mut Arg) -> Result<(), ()> {
        self.0.final_check(acts)?;
        *acts.marker() += T1::adjusted_prop_types();
        self.1.final_check(acts)
    }

    fn explain_propagation(&mut self, p: Lit, acts: &mut ExplainArg, is_final: bool, marker: u8) {
        if marker < T1::prop_types() {
            self.0.explain_propagation(p, acts, is_final, marker)
        } else {
            self.1
                .explain_propagation(p, acts, is_final, marker - T1::prop_types())
        }
    }

    fn interpolate_clause(
        &mut self,
        acts: &mut Arg,
        clause: impl Fn(&Arg) -> &[Lit],
        interpolate_arg: impl Fn(&mut Arg) -> InterpolateArg,
        marker: u8,
    ) -> DefExp {
        if marker < T1::prop_types() {
            self.0
                .interpolate_clause(acts, clause, interpolate_arg, marker)
        } else {
            self.1
                .interpolate_clause(acts, clause, interpolate_arg, marker - T1::prop_types())
        }
    }

    fn prop_types() -> u8 {
        T1::prop_types() + T2::prop_types()
    }

    fn adjusted_prop_types() -> u8 {
        T1::adjusted_prop_types()
    }
}

impl<
        R: Recorder,
        Th: Incremental
            + for<'a> Theory<
                TheoryArg<'a, Th::LevelMarker, R>,
                ExplainTheoryArg<'a, Th::LevelMarker, R>,
            >,
    > TheoryWrapper<Th, R>
{
    pub fn clear(&mut self) {
        self.th.clear();
        self.arg.push_log.clear();
        self.done_prop_log = false;
        self.arg.total_level = 0;
        self.prev_model_len = 0;
    }

    pub(crate) fn restore_trail_len(&mut self, len: u32) {
        self.prev_model_len = len;
    }

    pub fn open<'a, S: Reborrow>(
        &'a mut self,
        sat: &'a mut S,
    ) -> (
        &'a mut Th,
        TheoryArgRaw<'a, S::Target<'a>, Th::LevelMarker, R>,
    ) {
        (
            &mut self.th,
            TheoryArgRaw {
                sat: sat.reborrow(),
                incr: &mut self.arg,
                prop_marker: 0,
            },
        )
    }

    fn explain_propagation_clause_either<'a, 'b>(
        &mut self,
        p: Lit,
        mut acts: &'a mut SatExplainTheoryArg,
        is_final: bool,
        marker: u8,
    ) -> &'a [Lit] {
        acts.clause_builder().clear();
        acts.clause_builder().push(p);
        let (th, mut arg) = self.open(&mut acts);
        th.explain_propagation(p, &mut arg, is_final, marker);
        self.arg
            .recorder
            .log_clause(acts.clause_builder(), ClauseKind::TheoryExplain);
        acts.clause_builder()
    }
    pub fn intern(&self) -> &InternInfo {
        &self.arg.intern
    }

    pub fn intern_mut(&mut self) -> &mut InternInfo {
        &mut self.arg.intern
    }

    pub(crate) fn set_in_model(&mut self, in_model: bool) {
        self.arg.in_model = in_model;
    }
}

impl<
        R: Recorder,
        Th: Incremental
            + for<'a> Theory<
                TheoryArg<'a, Th::LevelMarker, R>,
                ExplainTheoryArg<'a, Th::LevelMarker, R>,
            >,
    > SatTheory for TheoryWrapper<Th, R>
{
    fn final_check(&mut self, acts: &mut SatTheoryArg) {
        let mut acts = TheoryArg {
            sat: acts.reborrow(),
            incr: &mut self.arg,
            prop_marker: 0,
        };
        let _ = self.th.final_check(&mut acts);
    }

    fn create_level(&mut self) {
        self.done_prop_log = false;
        let old_len = self.arg.push_log.len();
        let info = PushInfo {
            th: self.th.create_level(),
            model_len: self.prev_model_len,
        };
        self.arg.push_log.push(info);
        debug!(
            "Push ({} -> {}), internal_level ({old_len} -> {})",
            self.arg.total_level,
            self.arg.total_level + 1,
            self.arg.push_log.len()
        );
        self.arg.total_level += 1;
    }

    fn pop_levels(&mut self, n: usize) {
        let old_len = self.arg.push_log.len();
        self.done_prop_log = false;
        let target_sat_level = self.arg.total_level as usize - n;
        self.arg.total_level = target_sat_level as u32;
        self.prev_model_len = self.arg.push_log[target_sat_level].model_len;
        let target_level = target_sat_level;
        if target_level < self.arg.push_log.len() {
            self.th
                .pop_to_level(self.arg.push_log[target_level].th.clone(), false);
            self.arg.push_log.truncate(target_level);
        }
        debug!(
            "Pop ({} -> {target_sat_level}), internal_level ({old_len} -> {})",
            target_sat_level + n,
            self.arg.push_log.len()
        );
    }

    fn n_levels(&self) -> usize {
        self.arg.total_level as usize
    }

    fn partial_check(&mut self, acts: &mut SatTheoryArg) {
        debug!("Starting Theory check");
        let init_len = acts.model().len();
        let mut acts = TheoryArg {
            sat: acts.reborrow(),
            incr: &mut self.arg,
            prop_marker: 0,
        };
        let _: Result<(), ()> = (|| {
            self.th.initial_check(&mut acts)?;
            while (self.prev_model_len as usize) < acts.model().len() {
                acts.prop_marker = 0;
                self.th
                    .learn(acts.model()[self.prev_model_len as usize], &mut acts)?;
                self.prev_model_len += 1;
            }
            if acts.model().len() == init_len {
                acts.prop_marker = 0;
                self.th.pre_decision_check(&mut acts)
            } else {
                debug!("Skipping extra checks since we already made propagations");
                Ok(())
            }
        })();
    }

    #[inline]
    fn explain_propagation_clause<'a>(
        &mut self,
        p: Lit,
        acts: &'a mut SatExplainTheoryArg,
        marker: u8,
    ) -> &'a [Lit] {
        self.explain_propagation_clause_either(p, acts, false, marker)
    }

    #[inline]
    fn explain_propagation_clause_final<'a>(
        &mut self,
        p: Lit,
        acts: &'a mut SatExplainTheoryArg,
        marker: u8,
    ) -> &'a [Lit] {
        self.explain_propagation_clause_either(p, acts, true, marker)
    }

    #[inline]
    fn on_new_clause(&mut self, clause: &[Lit]) {
        self.arg.recorder.log_clause(clause, ClauseKind::Sat)
    }

    fn on_start_gc(&mut self) {
        self.arg.recorder.on_gc_start()
    }

    fn on_final_lit_explanation(&mut self, lit: Lit, reason: ClauseRef) {
        self.arg.recorder.on_final_lit_explanation(lit, reason)
    }
}

impl<Th: Incremental, R> Deref for TheoryWrapper<Th, R> {
    type Target = Th;

    fn deref(&self) -> &Self::Target {
        &self.th
    }
}

impl<Th: Incremental, R> DerefMut for TheoryWrapper<Th, R> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.th
    }
}
