use crate::util::DefaultHashBuilder;
use hashbrown::HashMap;
use log::{debug, trace};
use no_std_compat::prelude::v1::*;
use perfect_derive::perfect_derive;
use platsat::theory::Theory as BatTheory;
use platsat::{Lit, TheoryArg};
use std::cmp::max;
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
pub trait Theory<Wrap: DerefMut<Target = Self>> {
    type LevelMarker: Clone;

    /// Create a new backtracking level, and return a marker that can be used to backtrack to it
    fn create_level(&mut self) -> Self::LevelMarker;

    /// Pop to the level indicated by marker
    fn pop_to_level(&mut self, marker: Self::LevelMarker);

    /// Pre-check called before `learn`, return `Err` if there is a conflict
    #[allow(unused_variables)]
    fn initial_check(this: &mut Wrap, acts: &mut TheoryArg) -> Result<(), ()> {
        Ok(())
    }

    /// Add a literal to the model, return `Err` if there is a conflict
    fn learn(this: &mut Wrap, lit: Lit, acts: &mut TheoryArg) -> Result<(), ()>;

    /// Check partial model before a decision is made
    ///
    /// The whole partial model so far is `acts.model()`,
    /// but all literals in the model will have already been passed to `learn`
    ///
    /// return `Err` if there is a conflict
    fn pre_decision_check(this: &mut Wrap, acts: &mut TheoryArg) -> Result<(), ()>;

    /// If the theory uses `TheoryArgument::propagate`, it must implement
    /// this function to explain the propagations.
    ///
    /// `p` is the literal that has been propagated by the theory in a prefix
    /// of the current trail.
    fn explain_propagation(this: &mut Wrap, p: Lit, is_final: bool) -> &[Lit];

    /// Sets the "assertion_level_lit"
    ///
    /// This literal, if not `None`, should be included in all propagations
    /// and have its negation included in all conflicts
    fn set_assertion_level_lit(&mut self, l: Option<Lit>);

    /// Return the "assertion_level_lit"
    fn assertion_level_lit(&self) -> Option<Lit>;

    fn clear(&mut self);
}

#[derive(Clone)]
struct PushInfo<X> {
    th: X,
    prop_log: u32,
    model_len: u32,
}

#[perfect_derive(Default, Debug)]
pub struct IncrementalWrapper<Th: Theory<IncrementalWrapper<Th>>> {
    th: Th,
    prev_len: u32,
    push_log: Vec<PushInfo<Th::LevelMarker>>,
    // propagations done at levels at or below the assertion level
    prop_log: Vec<Lit>,
    // explanations for lits in prop_log (always the appropriate assertion level lit)
    prop_explain: HashMap<Lit, Lit, DefaultHashBuilder>,
    // whether we've handled prop_log since the last push or pop
    done_prop_log: bool,
    sat_level: u32,
    assertion_level: u32,
}

impl<Th: Theory<IncrementalWrapper<Th>>> IncrementalWrapper<Th> {
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
            self.th.pop_to_level(self.push_log[target_level].clone().th);
            for l in self
                .prop_log
                .drain(self.push_log[target_level].prop_log as usize..)
            {
                self.prop_explain.remove(&l);
            }
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
        self.prop_log.clear();
        self.prop_explain.clear();
        self.done_prop_log = false;
        self.sat_level = 0;
        self.prev_len = 0;
        self.assertion_level = 0;
    }

    pub fn base_marker(&self) -> Option<&Th::LevelMarker> {
        self.push_log
            .get(self.assertion_level as usize)
            .map(|x| &x.th)
    }

    pub fn last_marker(&self) -> Option<&Th::LevelMarker> {
        self.push_log.last().map(|x| &x.th)
    }
}

impl<Th: Theory<IncrementalWrapper<Th>>> BatTheory for IncrementalWrapper<Th> {
    fn final_check(&mut self, _: &mut TheoryArg) {}

    fn create_level(&mut self) {
        self.done_prop_log = false;
        if self.is_active() {
            let info = PushInfo {
                th: self.th.create_level(),
                model_len: self.prev_len,
                prop_log: self.prop_log.len() as u32,
            };
            self.push_log.push(info)
        } else {
            self.push_log[self.sat_level as usize].model_len = self.prev_len;
        }
        self.sat_level += 1;
    }

    fn pop_levels(&mut self, n: usize) {
        self.done_prop_log = false;
        let target_sat_level = self.n_levels() - n;
        self.sat_level = target_sat_level as u32;
        self.prev_len = self.push_log[target_sat_level].model_len;
        let target_level = max(self.assertion_level as usize, target_sat_level);
        if target_level < self.push_log.len() {
            self.th.pop_to_level(self.push_log[target_level].th.clone());
            self.push_log.truncate(target_level);
        }
    }

    fn n_levels(&self) -> usize {
        self.sat_level as usize
    }

    fn partial_check(&mut self, acts: &mut TheoryArg) {
        debug!("Starting EUF check");
        if self.sat_level <= self.assertion_level && !self.done_prop_log && self.sat_level > 0 {
            self.done_prop_log = true;
            let start = self.push_log[self.sat_level as usize - 1].prop_log as usize;
            let end = self
                .push_log
                .get(self.sat_level as usize)
                .map_or(self.prop_log.len(), |x| x.prop_log as usize);
            for l in &self.prop_log[start..end] {
                trace!("reassert {l:?}");
                if !acts.propagate(*l) {
                    return;
                }
            }
        }
        if !self.is_active() {
            return;
        }
        let init_len = acts.model().len();
        let _ = (|| {
            Th::initial_check(self, acts)?;
            while (self.prev_len as usize) < acts.model().len() {
                Th::learn(self, acts.model()[self.prev_len as usize], acts)?;
                self.prev_len += 1;
            }
            if acts.model().len() == init_len {
                Th::pre_decision_check(self, acts)
            } else {
                debug!("Skipping extra checks since we already made propagations");
                Ok(())
            }
        })();
        if self.assertion_level == self.sat_level && self.assertion_level != 0 {
            self.prop_log.extend(&acts.model()[init_len..]);
            let all = self.th.assertion_level_lit().unwrap();
            for l in &acts.model()[init_len..] {
                self.prop_explain.insert(*l, all);
            }
        }
    }

    fn explain_propagation(&mut self, p: Lit) -> &[Lit] {
        if let Some(_x) = self.prop_explain.get(&p) {
            // todo delete if the borrow checker improves
            let x = self.prop_explain.get(&p).unwrap();
            core::slice::from_ref(x)
        } else {
            Th::explain_propagation(self, p, false)
        }
    }

    fn explain_propagation_final(&mut self, p: Lit) -> &[Lit] {
        if let Some(_x) = self.prop_explain.get(&p) {
            // todo delete if the borrow checker improves
            let x = self.prop_explain.get(&p).unwrap();
            core::slice::from_ref(x)
        } else {
            Th::explain_propagation(self, p, true)
        }
    }
}

impl<Th: Theory<IncrementalWrapper<Th>>> Deref for IncrementalWrapper<Th> {
    type Target = Th;

    fn deref(&self) -> &Self::Target {
        &self.th
    }
}

impl<Th: Theory<IncrementalWrapper<Th>>> DerefMut for IncrementalWrapper<Th> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.th
    }
}
