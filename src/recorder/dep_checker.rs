use crate::intern::Symbol;
use crate::parser_core::SpanRange;
use crate::recorder::interpolant_recorder::{BOTH, NEITHER};
use crate::theory::Incremental;
use crate::util::HashMap;
use alloc::vec::Vec;
use default_vec2::StaticFlagVec;
use smallvec::SmallVec;

#[derive(Default)]
pub struct DepChecker {
    dep_list: Vec<Symbol>,
    /// (n, Some(s)) represent that the elements of dep_list starting at `n` are used to define `s`
    /// (n, None) represent that the elements of dep_list starting at `n`  stop defining the symbol
    /// that they started defining most recently and have not yet stopped.
    /// e.g.
    /// ```smt2
    /// (assert x)
    /// (define-const b Bool (or y z)
    /// (define-const a (and b (! c :named d)))
    /// ```
    /// would be represented by
    /// ```custom
    /// dep_list = [x, y, z, b, c];
    /// instructions = [(1, None), (3, Some(b)), (3, None), (4, None), (5, Some(d)), (5, Some(a))];
    /// ```
    instructions: Vec<(u32, Option<Symbol>)>,
    shadows: HashMap<Symbol, u32>,
    assumptions: Vec<SpanRange>,
}

impl DepChecker {
    pub fn act(&mut self, action: impl DepCheckerAction) {
        action.act(self)
    }

    pub(super) fn resolve_syms_in_ab(&self, ab_syms: &mut StaticFlagVec<2, Symbol>) {
        let mut curr = self.dep_list.len();
        let mut in_ab: u8 = BOTH as u8;
        let mut scopes: SmallVec<[u8; 8]> = Default::default();
        for (next, s) in self.instructions.iter().rev() {
            for s in &self.dep_list[*next as usize..curr] {
                ab_syms.or_assign(*s, in_ab as _)
            }
            curr = *next as usize;
            if let Some(s) = *s {
                scopes.push(in_ab);
                if scopes.len() == 1 {
                    in_ab = NEITHER as u8;
                }
                ab_syms.or_assign(s, in_ab as _);
                in_ab = ab_syms.get(s) as u8;
            } else {
                in_ab = scopes.pop().unwrap();
            }
        }
        for s in &self.dep_list[..curr] {
            ab_syms.or_assign(*s, in_ab as _)
        }
    }

    pub(super) fn assumptions(&self) -> impl Iterator<Item = SpanRange> + '_ {
        self.assumptions.iter().copied()
    }
}

pub trait DepCheckerAction {
    fn act(self, checker: &mut DepChecker);
}

pub struct EnterScope;
impl DepCheckerAction for EnterScope {
    fn act(self, checker: &mut DepChecker) {
        // this None is temporary and will be replaced when ExitScope is used.
        checker
            .instructions
            .push((checker.dep_list.len() as u32, None));
    }
}

pub struct ExitScope(pub(crate) Symbol);

impl DepCheckerAction for ExitScope {
    fn act(self, checker: &mut DepChecker) {
        checker
            .instructions
            .push((checker.dep_list.len() as u32, Some(self.0)));
    }
}

pub struct Shadow(pub(crate) Symbol);

impl DepCheckerAction for Shadow {
    fn act(self, checker: &mut DepChecker) {
        *checker.shadows.entry(self.0).or_insert(0) += 1;
    }
}

pub struct Unshadow(pub(crate) Symbol);

impl DepCheckerAction for Unshadow {
    fn act(self, checker: &mut DepChecker) {
        *checker.shadows.entry(self.0).or_insert(0) -= 1;
    }
}

pub struct Reference(pub(crate) Symbol);

impl DepCheckerAction for Reference {
    fn act(self, checker: &mut DepChecker) {
        if *checker.shadows.get(&self.0).unwrap_or(&0) == 0 {
            checker.dep_list.push(self.0)
        }
    }
}

pub struct AddAssumption(pub(crate) SpanRange);

impl DepCheckerAction for AddAssumption {
    fn act(self, checker: &mut DepChecker) {
        checker.assumptions.push(self.0)
    }
}

#[derive(Copy, Clone)]
pub struct Marker {
    dep_list: u32,
    instructions: u32,
    assumptions: u32,
}

impl Incremental for DepChecker {
    type LevelMarker = Marker;
    fn create_level(&self) -> Self::LevelMarker {
        // deps, and shadows are handled by relevant DepActions
        Marker {
            dep_list: self.dep_list.len() as u32,
            instructions: self.instructions.len() as u32,
            assumptions: self.assumptions.len() as u32,
        }
    }

    fn pop_to_level(&mut self, marker: Self::LevelMarker, _: bool) {
        self.dep_list.truncate(marker.dep_list as usize);
        self.instructions.truncate(marker.instructions as usize);
        self.assumptions.truncate(marker.assumptions as usize)
    }

    fn clear(&mut self) {
        self.dep_list.clear();
        self.instructions.clear();
        self.shadows.clear();
        self.assumptions.clear();
    }
}
