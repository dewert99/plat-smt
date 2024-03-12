// https://www.cs.upc.edu/~oliveras/rta05.pdf
// 2.1 Union-find with an O(k log n) Explain operation
use batsat::Lit;
use std::fmt::Debug;
use std::ops::Deref;

use crate::approx_bitset::{ApproxBitSet, IdSet};
use batsat::LSet;
use egg::raw::RawEGraph;
use egg::{Id, Language};
use hashbrown::HashSet;
use log::trace;

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub(crate) struct Justification(Lit);

enum EJustification {
    Lit(Lit),
    Congruence,
    NoOp,
}

impl Justification {
    pub fn from_lit(l: Lit) -> Self {
        debug_assert!(l != Lit::UNDEF);
        debug_assert!(l != Lit::ERROR);
        Justification(l)
    }

    pub const CONGRUENCE: Self = Justification(Lit::ERROR);

    pub const NOOP: Self = Justification(Lit::UNDEF);

    fn expand(self) -> EJustification {
        match self.0 {
            Lit::ERROR => EJustification::Congruence,
            Lit::UNDEF => EJustification::NoOp,
            l => EJustification::Lit(l),
        }
    }
}

#[derive(Debug, Copy, Clone)]
struct UnionInfo {
    old_id: Id,
    new_id: Id,
    just: Justification,
}

#[derive(Debug, Clone, Default)]
pub struct Explain {
    union_info: Vec<UnionInfo>,
    assoc_unions: Vec<u32>, // index into union_info
}

pub(crate) struct ExplainWith<'a, X> {
    explain: &'a Explain,
    raw: X,
}

impl Explain {
    fn fresh_assoc_union(&mut self, just: Justification, old_id: Id, new_id: Id) -> u32 {
        let assoc_union = self.union_info.len() as u32;
        self.union_info.push(UnionInfo {
            just,
            old_id,
            new_id,
        });
        assoc_union
    }
    pub(crate) fn add(&mut self, set: Id) -> Id {
        debug_assert_eq!(self.assoc_unions.len(), usize::from(set));
        self.assoc_unions.push(u32::MAX);
        set
    }

    /// `old_root` is the `id` who was merged into `new_root`
    /// `old_id` is the node whose root was `old_root` before the union
    /// `new_id` is the node whose root was `new_root` before the union
    pub(crate) fn union(
        &mut self,
        old_root: Id,
        justification: Justification,
        old_id: Id,
        new_id: Id,
    ) {
        let assoc_union = self.fresh_assoc_union(justification, old_id, new_id);
        self.assoc_unions[usize::from(old_root)] = assoc_union;
    }

    pub(crate) fn with_raw_egraph<X>(&self, raw: X) -> ExplainWith<'_, X> {
        ExplainWith { explain: self, raw }
    }
}

impl<'a, X> Deref for ExplainWith<'a, X> {
    type Target = Explain;

    fn deref(&self) -> &Self::Target {
        self.explain
    }
}

impl<'x, L: Language, D> ExplainWith<'x, &'x RawEGraph<L, D, egg::raw::semi_persistent1::UndoLog>> {
    pub(crate) fn node(&self, node_id: Id) -> &L {
        self.raw.id_to_node(node_id)
    }

    // Requires `left` != `right`
    // `result.1` is true when the `old_root` from `result.0` corresponds to left
    fn max_assoc_union_gen<S: IdSet>(
        &self,
        orig_left: Id,
        orig_right: Id,
        fallback: impl FnOnce(&Self, Id, Id) -> (u32, bool),
    ) -> (u32, bool) {
        let mut seen_left = S::empty();
        let mut seen_right = S::empty();
        let mut left = orig_left;
        let mut right = orig_right;
        seen_left.insert(left);
        seen_right.insert(right);
        // base → .. → pred → ancestor
        //      other → .. -↗
        let (other_is_left, pred, ancestor, other) = loop {
            let next_left = self.raw.find_direct_parent(left);
            if seen_right.may_contain(next_left) && left != next_left {
                break (false, left, next_left, orig_right);
            }
            seen_left.insert(next_left);

            let next_right = self.raw.find_direct_parent(right);
            if seen_left.may_contain(next_right) && right != next_right {
                break (true, right, next_right, orig_left);
            }
            seen_right.insert(next_right);

            debug_assert!(next_left != left || next_right != right);
            left = next_left;
            right = next_right;
        };
        let base_path_score = self.assoc_unions[usize::from(pred)];
        debug_assert_ne!(base_path_score, u32::MAX);
        if ancestor == other {
            return (base_path_score, !other_is_left);
        } else {
            let mut curr = other;
            loop {
                if S::might_confuse(curr, ancestor) {
                    // we may have though we found the ancestor when we actually found `curr`
                    return fallback(self, orig_left, orig_right);
                }
                let next = self.raw.find_direct_parent(curr);
                if next == ancestor {
                    //   base → .. → pred → ancestor
                    // other → .. → curr -↗
                    let other_path_score = self.assoc_unions[usize::from(curr)];
                    debug_assert_ne!(other_path_score, u32::MAX);
                    return if base_path_score > other_path_score {
                        (base_path_score, !other_is_left)
                    } else {
                        (other_path_score, other_is_left)
                    };
                }
                debug_assert_ne!(next, curr);
                curr = next;
            }
        }
    }

    #[inline(never)]
    fn max_assoc_union_fallback(&self, left: Id, right: Id) -> (u32, bool) {
        self.max_assoc_union_gen::<HashSet<Id>>(left, right, |_, _, _| unreachable!())
    }

    fn max_assoc_union(&self, left: Id, right: Id) -> (u32, bool) {
        // Try with an `ApproxBitSet` and fallback to using a `HashSet` if it doesn't work
        self.max_assoc_union_gen::<ApproxBitSet>(left, right, Self::max_assoc_union_fallback)
    }

    fn handle_congruence(&self, left: Id, right: Id, res: &mut LSet, negate: bool) {
        if left == right {
            return;
        }
        trace!("{left} = {right} by congruence:");
        let current_node = self.node(left);
        let next_node = self.node(right);
        debug_assert!(current_node.matches(next_node));

        for (left_child, right_child) in current_node
            .children()
            .iter()
            .zip(next_node.children().iter())
        {
            self.explain_equivalence(*left_child, *right_child, res, negate)
        }
    }

    // `=?`: unknown equivalence
    // `===`: congruence
    // `={just}=` equivalence by `just`
    //
    // Explains: `left_congruence` === `left` =? `right`
    // Given that: `result` === `right`
    fn explain_equivalence_h(
        &self,
        left_congruence: Id,
        left: Id,
        right: Id,
        res: &mut LSet,
        negate: bool,
    ) -> Id {
        // `=?`: unknown equivalence
        // `===`: congruence
        // `={just}=` equivalence by `just`

        // left_congruence === left =? right
        if left == right {
            // left_congruence === right
            left_congruence
        } else {
            let (assoc_union, left_is_old) = self.max_assoc_union(left, right);
            let union_info = self.union_info[assoc_union as usize];
            let just = union_info.just;
            let (next_left, next_right) = if left_is_old {
                (union_info.old_id, union_info.new_id)
            } else {
                (union_info.new_id, union_info.old_id)
            };
            // left_congruence === left =? next_left ={just}= next_right =? right
            let left_congruence =
                self.explain_equivalence_h(left_congruence, left, next_left, res, negate);
            // left_congruence === next_left ={just}= next_right =? right
            let left_congruence = match just.expand() {
                EJustification::Lit(just) => {
                    self.handle_congruence(left_congruence, next_left, res, negate);
                    // next_left ={just}= next_right =? right
                    trace!("id{next_left} = id{next_right} by {just:?}");
                    res.insert(just ^ negate);
                    // next_right =? right
                    next_right
                }
                EJustification::Congruence => {
                    // left_congruence === next_left === next_right =? right
                    left_congruence
                }
                EJustification::NoOp => {
                    self.handle_congruence(left_congruence, next_left, res, negate);
                    trace!("id{next_left} = id{next_right} by assumption");
                    next_right
                }
            };
            // left_congruence === next_right =? right
            self.explain_equivalence_h(left_congruence, next_right, right, res, negate)
            // left_congruence === right
        }
    }

    pub fn explain_equivalence(&self, left: Id, right: Id, res: &mut LSet, negate: bool) {
        debug_assert_eq!(self.raw.find(left), self.raw.find(right));
        trace!("start explain id{left} = id{right}");
        let left_congruence = self.explain_equivalence_h(left, left, right, res, negate);
        self.handle_congruence(left_congruence, right, res, negate);
        trace!("end explain id{left} = id{right}");
    }
}

#[derive(Default, Clone, Debug)]
pub(crate) struct PushInfo(usize);

impl Explain {
    pub(crate) fn push(&self) -> PushInfo {
        PushInfo(self.union_info.len())
    }

    pub(crate) fn pop(&mut self, info: PushInfo, old_nodes: usize) {
        self.union_info.truncate(info.0);
        self.assoc_unions.truncate(old_nodes);
    }

    pub(crate) fn clear(&mut self) {
        self.union_info.clear();
        self.assoc_unions.clear();
    }
}
