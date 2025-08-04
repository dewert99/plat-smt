use crate::intern::{InternInfo, Symbol};
use crate::recorder::{ClauseKind, Recorder};
use crate::tseitin::SatTheoryArgT;
use crate::ExpLike;
use core::fmt::{Debug, Formatter};
use log::debug;
use no_std_compat::prelude::v1::*;
use perfect_derive::perfect_derive;
use platsat::core::ExplainTheoryArg as SatExplainTheoryArg;
use platsat::theory::Theory as SatTheory;
use platsat::{Lit, TheoryArg as SatTheoryArg};
use std::ops::{Deref, DerefMut};
// The implementation of push/pop is somewhat unexpected
//
// Since `platsat` uses non-chronological backtracking in can try to get EUF to pop to earlier
// assertion levels during a check-sat. To work around this EUF keeps track of the
// assertion level, and suppresses calls from `platsat` that would have it pop too far.
// Instead, it enters a state where it doesn't make any propagations or raise any conflicts,
// since it has access to information `platsat` assumes it shouldn't have access to yet.
// Since `platsat` requires proportions to be made as soon as possible
// (https://github.com/c-cube/platsat/issues/16), EUF always includes a literal representing
// the current assertion level to its explanations, which makes them appear as though the
// proportions couldn't have happened any sooner.

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

#[derive(Clone, Debug)]
struct PushInfo<X> {
    th: X,
    model_len: u32,
}

#[perfect_derive(Default, Debug)]
pub struct TheoryWrapper<Th: Incremental, R> {
    th: Th,
    prev_model_len: u32,
    // whether we've handled prop_log since the last push or pop
    done_prop_log: bool,
    pub(crate) arg: IncrementalArgData<Th::LevelMarker, R>,
}

#[perfect_derive(Default)]
pub struct IncrementalArgData<M, R> {
    total_level: u32,
    push_log: Vec<PushInfo<M>>,
    pub(crate) junction_buf: Vec<Lit>,
    intern: InternInfo,
    pub(crate) recorder: R,
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
    pub sat: S,
    pub incr: &'a mut IncrementalArgData<M, R>,
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

    fn recorder_mut(&mut self) -> (&InternInfo, &mut Self::R);

    fn log_def<Exp: ExpLike, Exp2: ExpLike>(
        &mut self,
        val: Exp,
        f: Symbol,
        arg: impl Iterator<Item = Exp2> + Clone,
    ) {
        let (intern, recorder) = self.recorder_mut();
        recorder.log_def(val, f, arg, intern)
    }

    fn log_def_exp<Exp: ExpLike, Exp2: ExpLike>(&mut self, val: Exp, def: Exp2) {
        let (intern, recorder) = self.recorder_mut();
        recorder.log_def_exp(val, def, intern)
    }
    fn log_alias<Exp: ExpLike>(&mut self, alias: Symbol, exp: Exp) {
        let (intern, recorder) = self.recorder_mut();
        recorder.log_alias(alias, exp, intern)
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

    fn recorder_mut(&mut self) -> (&InternInfo, &mut Self::R) {
        (&self.incr.intern, &mut self.incr.recorder)
    }
}

impl<'a, S: Reborrow, M, R> Reborrow for TheoryArgRaw<'a, S, M, R> {
    type Target<'b>
        = TheoryArgRaw<'b, S::Target<'b>, M, R>
    where
        Self: 'b;

    fn reborrow(&mut self) -> Self::Target<'_> {
        TheoryArgRaw {
            sat: self.sat.reborrow(),
            incr: self.incr.reborrow(),
        }
    }
}

/// Theory that parametrizes the solver and can react on events.
pub trait Theory<Arg, ExplainArg> {
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
    fn final_check(&mut self, _acts: &mut Arg) {}

    /// If the theory uses `TheoryArgument::propagate`, it must implement
    /// this function to explain the propagations.
    ///
    /// It should add the negation of all literals that were used to imply `p` to
    /// `acts.clause_builder()` while leaving its current elements untouched
    ///
    ///
    /// `acts.clause_builder()` comes pre-initialized with `p` as its first element to satisfy
    /// [`BatTheory::explain_propagation_clause`]'s requirements
    fn explain_propagation(&mut self, p: Lit, acts: &mut ExplainArg, is_final: bool);
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
            },
        )
    }

    fn explain_propagation_clause_either<'a, 'b>(
        &mut self,
        p: Lit,
        mut acts: &'a mut SatExplainTheoryArg,
        is_final: bool,
    ) -> &'a [Lit] {
        acts.clause_builder().clear();
        acts.clause_builder().push(p);
        let (th, mut arg) = self.open(&mut acts);
        th.explain_propagation(p, &mut arg, is_final);
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
        };
        self.th.final_check(&mut acts)
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
        debug!("Starting EUF check");
        let init_len = acts.model().len();
        let mut acts = TheoryArg {
            sat: acts.reborrow(),
            incr: &mut self.arg,
        };
        let _: Result<(), ()> = (|| {
            self.th.initial_check(&mut acts)?;
            while (self.prev_model_len as usize) < acts.model().len() {
                self.th
                    .learn(acts.model()[self.prev_model_len as usize], &mut acts)?;
                self.prev_model_len += 1;
            }
            if acts.model().len() == init_len {
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
    ) -> &'a [Lit] {
        self.explain_propagation_clause_either(p, acts, false)
    }

    #[inline]
    fn explain_propagation_clause_final<'a>(
        &mut self,
        p: Lit,
        acts: &'a mut SatExplainTheoryArg,
    ) -> &'a [Lit] {
        self.explain_propagation_clause_either(p, acts, true)
    }

    #[inline]
    fn on_new_clause(&mut self, clause: &[Lit]) {
        self.arg.recorder.log_clause(clause, ClauseKind::Sat)
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
