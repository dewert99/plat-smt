use batsat::theory::Theory as BatTheory;
use batsat::{Lit, TheoryArg};
use log::debug;
use perfect_derive::perfect_derive;
use std::cmp::max;
use std::ops::{Deref, DerefMut};

// The implementation of push/pop is somewhat unexpected
//
// Since `batsat` uses non-chronological backtracking in can try to get EUF to pop to earlier
// assertion levels during a check-sat. To work around this EUF keeps track of the
// assertion level, and suppresses calls from `batsat` that would have it pop too far.
// Instead, it enters a state where it doesn't make any propagations or raise any conflicts,
// since it has access to information `batsat` assumes it shouldn't have access to yet.
// Since `batsat` requires proportions to be made as soon as possible
// (https://github.com/c-cube/batsat/issues/16), EUF always includes a literal representing
// the current assertion level to its explanations, which makes them appear as though the
// proportions couldn't have happened any sooner.

/// Theory that parametrizes the solver and can react on events.
pub trait Theory {
    type LevelMarker: Clone;

    /// Create a new backtracking level, and return a marker that can be used to backtrack to it
    fn create_level(&mut self) -> Self::LevelMarker;

    /// Pop to the level indicated by marker
    fn pop_to_level(&mut self, marker: Self::LevelMarker);

    /// Add a literal to the model, return `Err` if there is a conflict
    fn learn(&mut self, lit: Lit, acts: &mut TheoryArg) -> Result<(), ()>;

    /// Check partial model before a decision is made
    ///
    /// The whole partial model so far is `acts.model()`,
    /// but all literals in the model will have already been passed to `learn`
    ///
    /// return `Err` if there is a conflict
    fn pre_decision_check(&mut self, acts: &mut TheoryArg) -> Result<(), ()>;

    /// If the theory uses `TheoryArgument::propagate`, it must implement
    /// this function to explain the propagations.
    ///
    /// `p` is the literal that has been propagated by the theory in a prefix
    /// of the current trail.
    fn explain_propagation(&mut self, p: Lit) -> &[Lit];

    /// Sets the "assertion_level_lit"
    ///
    /// This literal, if not `None`, should be included in all propagations
    /// and have its negation included in all conflicts
    fn set_assertion_level_lit(&mut self, l: Option<Lit>);

    fn clear(&mut self);
}

#[perfect_derive(Default, Debug)]
pub struct IncrementalWrapper<Th: Theory> {
    th: Th,
    prev_len: u32,
    push_log: Vec<(u32, Th::LevelMarker)>,
    sat_level: u32,
    assertion_level: u32,
}

impl<Th: Theory> IncrementalWrapper<Th> {
    /// Returns false when `self` has been popped below the assertion level
    /// In this case `self` will not produce any propagations or conflicts
    fn is_active(&self) -> bool {
        self.sat_level >= self.assertion_level
    }

    pub fn smt_push(&mut self, level_lit: Lit) {
        self.assertion_level += 1;
        self.th.set_assertion_level_lit(Some(level_lit))
    }

    pub fn smt_pop_to(&mut self, target_level: usize, level_lit: Option<Lit>) {
        debug_assert_eq!(self.n_levels(), 0);
        if target_level < self.push_log.len() {
            self.th.pop_to_level(self.push_log[target_level].clone().1);
            self.push_log.truncate(target_level);
        }
        self.assertion_level = target_level as u32;
        self.th.set_assertion_level_lit(level_lit);
    }

    pub fn assertion_level(&self) -> usize {
        self.assertion_level as usize
    }

    pub fn clear(&mut self) {
        self.th.clear();
        self.push_log.clear();
        self.sat_level = 0;
        self.prev_len = 0;
        self.assertion_level = 0;
    }
}

impl<Th: Theory> BatTheory for IncrementalWrapper<Th> {
    fn final_check(&mut self, _: &mut TheoryArg) {}

    fn create_level(&mut self) {
        if self.is_active() {
            self.push_log.push((self.prev_len, self.th.create_level()))
        } else {
            self.push_log[self.sat_level as usize].0 = self.prev_len;
        }
        self.sat_level += 1;
    }

    fn pop_levels(&mut self, n: usize) {
        let target_sat_level = self.n_levels() - n;
        self.sat_level = target_sat_level as u32;
        self.prev_len = self.push_log[target_sat_level].0;
        let target_level = max(self.assertion_level as usize, target_sat_level);
        if target_level < self.push_log.len() {
            self.th.pop_to_level(self.push_log[target_level].clone().1);
            self.push_log.truncate(target_level);
        }
    }

    fn n_levels(&self) -> usize {
        self.sat_level as usize
    }

    fn partial_check(&mut self, acts: &mut TheoryArg) {
        debug!("Starting EUF check");
        if !self.is_active() {
            return;
        }
        let _ = (|| {
            let init_len = acts.model().len();
            while (self.prev_len as usize) < acts.model().len() {
                self.th.learn(acts.model()[self.prev_len as usize], acts)?;
                self.prev_len += 1;
            }
            if acts.model().len() == init_len {
                self.th.pre_decision_check(acts)
            } else {
                debug!("Skipping extra checks since we already made propagations");
                Ok(())
            }
        })();
    }

    fn explain_propagation(&mut self, p: Lit) -> &[Lit] {
        self.th.explain_propagation(p)
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
