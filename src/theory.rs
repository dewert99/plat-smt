use crate::util::DefaultHashBuilder;
use hashbrown::HashMap;
use log::debug;
use no_std_compat::prelude::v1::*;
use perfect_derive::perfect_derive;
use platsat::core::ExplainTheoryArg;
use platsat::theory::Theory as BatTheory;
use platsat::{Lit, TheoryArg};
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

/// Theory that parametrizes the solver and can react on events.
pub trait Theory {
    type LevelMarker: Clone;

    /// Create a new backtracking level, and return a marker that can be used to backtrack to it
    fn create_level(&self) -> Self::LevelMarker;

    /// Pop to the level indicated by marker
    ///
    /// If `clear_lits` is true, all literals created above the level are no longer valid and must
    /// not be used anymore
    fn pop_to_level(&mut self, marker: Self::LevelMarker, clear_lits: bool);

    /// Pre-check called before `learn`, return `Err` if there is a conflict
    #[allow(unused_variables)]
    fn initial_check(
        &mut self,
        acts: &mut TheoryArg,
        iacts: &IncrementalArg<Self>,
    ) -> Result<(), ()> {
        Ok(())
    }

    /// Add a literal to the model, return `Err` if there is a conflict
    fn learn(
        &mut self,
        lit: Lit,
        acts: &mut TheoryArg,
        iacts: &IncrementalArg<Self>,
    ) -> Result<(), ()>;

    /// Check partial model before a decision is made
    ///
    /// The whole partial model so far is `acts.model()`,
    /// but all literals in the model will have already been passed to `learn`
    ///
    /// return `Err` if there is a conflict
    fn pre_decision_check(
        &mut self,
        acts: &mut TheoryArg,
        iacts: &IncrementalArg<Self>,
    ) -> Result<(), ()>;

    /// If the theory uses `TheoryArgument::propagate`, it must implement
    /// this function to explain the propagations.
    ///
    /// It should add the negation of all literals that were used to imply `p` to
    /// `acts.clause_builder()` while leaving its current elements untouched
    ///
    ///
    /// `acts.clause_builder()` comes pre-initialized with `p` as its first element to satisfy
    /// [`BatTheory::explain_propagation_clause`]'s requirements
    fn explain_propagation(
        &mut self,
        p: Lit,
        acts: &mut ExplainTheoryArg,
        iacts: &IncrementalArg<Self>,
        is_final: bool,
    );

    fn clear(&mut self);
}

#[derive(Clone)]
struct PushInfo<X> {
    th: X,
    model_len: u32,
}

#[perfect_derive(Default, Debug)]
pub struct IncrementalWrapper<Th: Theory> {
    th: Th,
    prev_len: u32,
    // explanations for lits in prop_log (always the appropriate assertion level lit)
    prop_explain: HashMap<Lit, Lit, DefaultHashBuilder>,
    // whether we've handled prop_log since the last push or pop
    done_prop_log: bool,
    arg: IncrementalArg<Th>,
}

#[perfect_derive(Default, Debug)]
pub struct IncrementalArg<Th: Theory + ?Sized> {
    decision_level: u32,
    push_log: Vec<PushInfo<Th::LevelMarker>>,
}

impl<Th: Theory> IncrementalArg<Th> {
    pub fn base_marker(&self) -> Option<&Th::LevelMarker> {
        self.push_log.first().map(|x| &x.th)
    }

    pub fn last_marker(&self) -> Option<&Th::LevelMarker> {
        self.push_log.last().map(|x| &x.th)
    }
}

impl<Th: Theory> IncrementalWrapper<Th> {
    pub fn clear(&mut self) {
        self.th.clear();
        self.arg.push_log.clear();
        self.prop_explain.clear();
        self.done_prop_log = false;
        self.arg.decision_level = 0;
        self.prev_len = 0;
    }

    pub(crate) fn restore_trail_len(&mut self, len: u32) {
        self.prev_len = len;
    }

    fn explain_propagation_clause_either<'a>(
        &mut self,
        p: Lit,
        acts: &'a mut ExplainTheoryArg,
        is_final: bool,
    ) -> &'a [Lit] {
        acts.clause_builder().clear();
        acts.clause_builder().push(p);
        self.th.explain_propagation(p, acts, &self.arg, is_final);
        acts.clause_builder()
    }

    pub fn open(&mut self) -> (&mut Th, &IncrementalArg<Th>) {
        (&mut self.th, &self.arg)
    }
}

impl<Th: Theory> BatTheory for IncrementalWrapper<Th> {
    fn final_check(&mut self, _: &mut TheoryArg) {}

    fn create_level(&mut self) {
        self.done_prop_log = false;
        let old_len = self.arg.push_log.len();
        let info = PushInfo {
            th: self.th.create_level(),
            model_len: self.prev_len,
        };
        self.arg.push_log.push(info);
        debug!(
            "Push ({} -> {}), internal_level ({old_len} -> {})",
            self.arg.decision_level,
            self.arg.decision_level + 1,
            self.arg.push_log.len()
        );
        self.arg.decision_level += 1;
    }

    fn pop_levels(&mut self, n: usize) {
        let old_len = self.arg.push_log.len();
        self.done_prop_log = false;
        let target_sat_level = self.n_levels() - n;
        self.arg.decision_level = target_sat_level as u32;
        self.prev_len = self.arg.push_log[target_sat_level].model_len;
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
        self.arg.decision_level as usize
    }

    fn partial_check(&mut self, acts: &mut TheoryArg) {
        debug!("Starting EUF check");
        let init_len = acts.model().len();
        let _ = (|| {
            self.th.initial_check(acts, &self.arg)?;
            while (self.prev_len as usize) < acts.model().len() {
                self.th
                    .learn(acts.model()[self.prev_len as usize], acts, &self.arg)?;
                self.prev_len += 1;
            }
            if acts.model().len() == init_len {
                self.th.pre_decision_check(acts, &self.arg)
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
        acts: &'a mut ExplainTheoryArg,
    ) -> &'a [Lit] {
        self.explain_propagation_clause_either(p, acts, false)
    }

    #[inline]
    fn explain_propagation_clause_final<'a>(
        &mut self,
        p: Lit,
        acts: &'a mut ExplainTheoryArg,
    ) -> &'a [Lit] {
        self.explain_propagation_clause_either(p, acts, true)
    }
}

impl<Th: Theory> Deref for IncrementalWrapper<Th> {
    type Target = Th;

    fn deref(&self) -> &Self::Target {
        &self.th
    }
}

impl<Th: Theory> DerefMut for IncrementalWrapper<Th> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.th
    }
}
