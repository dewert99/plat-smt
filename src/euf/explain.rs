use no_std_compat::prelude::v1::*;
// https://www.cs.upc.edu/~oliveras/rta05.pdf
// 2.1 Union-find with an O(k log n) Explain operation
use platsat::Lit;
use std::fmt::{Debug, Formatter};
use std::ops::{Deref, DerefMut};

use super::egraph::{SymbolLang, EQ_OP};
use super::euf::EClass;
use crate::euf::approx_bitset::{ApproxBitSet, IdSet};
use crate::util::{minmax, DefaultHashBuilder};
use hashbrown::hash_map::Entry;
use hashbrown::{HashMap, HashSet};
use log::{debug, trace};
use perfect_derive::perfect_derive;
use plat_egg::raw::RawEGraph;
use plat_egg::{raw::Language, Id};
use smallvec::SmallVec;

// either a `Lit` that represents the equality
// or a hash an explanation of the equality
// or a marker indicating the equality was already requested
#[derive(Copy, Clone)]
struct EqIdInfo(u32);

#[derive(Debug)]
enum EEqIdInfo {
    Lit(Lit),
    Pending(u32),
    Requested,
}

impl EqIdInfo {
    // requires the lit is positive
    fn lit(l: Lit) -> Self {
        let idx = l.idx();
        debug_assert_eq!(idx & 1, 0);
        debug_assert_ne!(idx, !1);
        EqIdInfo(idx)
    }

    // requires the hash is odd
    fn pending(hash: u32) -> Self {
        debug_assert_eq!(hash & 1, 1);
        EqIdInfo(hash)
    }

    const REQUESTED: Self = EqIdInfo(!1);

    fn expand(self) -> EEqIdInfo {
        if self.0 & 1 == 1 {
            EEqIdInfo::Pending(self.0)
        } else if self.0 == !1 {
            EEqIdInfo::Requested
        } else {
            EEqIdInfo::Lit(Lit::from(self.0 as usize))
        }
    }
}

impl Debug for EqIdInfo {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.expand().fmt(f)
    }
}

#[perfect_derive(Debug, Default)]
pub(crate) struct EqIds {
    map: HashMap<[Id; 2], EqIdInfo, DefaultHashBuilder>,
    /// equalities we would like to have literals for
    pub requests: Vec<[Id; 2]>,
}

impl EqIds {
    pub fn insert(&mut self, ids: [Id; 2], l: Lit) {
        self.map.insert(ids, EqIdInfo::lit(l));
    }

    pub fn remove(&mut self, ids: &[Id; 2]) {
        self.map.remove(ids);
    }

    pub fn get_or_insert(&mut self, ids: [Id; 2], mut mk_lit: impl FnMut() -> Lit) -> Lit {
        match self.map.entry(ids) {
            Entry::Occupied(mut occ) => match occ.get().expand() {
                EEqIdInfo::Lit(lit) => lit,
                _ => {
                    let res = mk_lit();
                    occ.insert(EqIdInfo::lit(res));
                    res
                }
            },
            Entry::Vacant(vac) => {
                let res = mk_lit();
                vac.insert(EqIdInfo::lit(res));
                res
            }
        }
    }

    pub fn get(&self, ids: [Id; 2]) -> Option<Lit> {
        match self.map.get(&ids)?.expand() {
            EEqIdInfo::Lit(lit) => Some(lit),
            _ => None,
        }
    }

    pub fn clear(&mut self) {
        self.map.clear();
        self.requests.clear();
    }
}

pub fn check_node_is_eq(node: &SymbolLang) -> Option<[Id; 2]> {
    if node.op() == EQ_OP {
        match node.children() {
            &[id1, id2] => Some([id1, id2]),
            _ => unreachable!("equality without two children {node:?}",),
        }
    } else {
        None
    }
}

/// hash key to remember shape of proof tree
fn exp_hash(just: Justification) -> u32 {
    (just.0 << 1) | 1
}

#[derive(Copy, Clone, Eq, PartialEq)]
pub(crate) struct Justification(u32);

impl Debug for Justification {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.expand().fmt(f)
    }
}

mod ejust {
    use platsat::Lit;

    #[derive(Debug)]
    pub(crate) enum Justification {
        Lit(Lit),
        Congruence(bool),
        NoOp,
    }
}

use crate::exp::var_to_nv;
use crate::intern::{AND_SYM, EQ_SYM, NOT_SYM, OR_SYM};
use crate::recorder::{DefExp, InterpolateArg};
pub(crate) use ejust::Justification as EJustification;

impl Justification {
    pub fn from_lit(l: Lit) -> Self {
        debug_assert!(l != Lit::UNDEF);
        debug_assert!(l != Lit::ERROR);
        Justification(l.idx())
    }

    pub const fn congruence(flip: u32) -> Self {
        debug_assert!(flip <= 1);
        Justification((!1) ^ flip)
    }

    pub const NOOP: Self = Justification(!2u32);

    pub(crate) fn expand(self) -> EJustification {
        const C: u32 = !1;
        const N: u32 = !3;
        match self.0 & !1 {
            C => EJustification::Congruence((self.0 & 1) != 0),
            N => EJustification::NoOp,
            _ => EJustification::Lit(Lit::from(self.0 as usize)),
        }
    }
}

#[derive(Debug, Copy, Clone)]
struct UnionInfo {
    old_id: Id,
    new_id: Id,
    just: Justification,
}

#[derive(Debug, Clone, Copy)]
struct StackElem {
    next_left: Id,
    just: Justification,
    next_right: Id,
    right: Id,
}

#[derive(Debug, Clone, Default)]
pub struct Explain {
    union_info: Vec<UnionInfo>,
    /// index into union_info
    assoc_unions: Vec<u32>,
    /// stack explain equivalence
    stack: Vec<StackElem>,
    /// equalities that need to be explained as part of the current explanation
    deferred_explanations: Vec<(Id, Id)>,
    deferred_explanations_set: HashSet<(Id, Id), DefaultHashBuilder>,
}

pub(crate) struct ExplainStateInner<'a, X> {
    explain: &'a mut Explain,
    used_congruence: bool,
    raw: X,
}

pub(crate) struct ExplainState<'a, X> {
    explain: ExplainStateInner<'a, X>,
    out: &'a mut Vec<Lit>,
    // unions in union_info before base_unions are proved at the base decision level
    base_unions: u32,
    // unions in union_info before last_unions are proved at an earlier
    // decision level than the current one
    last_unions: u32,
    eq_ids: &'a mut EqIds,
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

    pub(crate) fn promote_for_interpolant<X>(&mut self, raw: X) -> ExplainStateInner<'_, X> {
        self.stack.clear();
        self.deferred_explanations.clear();
        ExplainStateInner {
            explain: self,
            raw,
            used_congruence: false,
        }
    }

    pub(crate) fn promote<'a, X>(
        &'a mut self,
        raw: X,
        out: &'a mut Vec<Lit>,
        base_unions: u32,
        last_unions: u32,
        eq_ids: &'a mut EqIds,
    ) -> ExplainState<'a, X> {
        ExplainState {
            explain: self.promote_for_interpolant(raw),
            base_unions,
            out,
            eq_ids,
            last_unions,
        }
    }
}

impl<'a, X> Deref for ExplainStateInner<'a, X> {
    type Target = Explain;

    fn deref(&self) -> &Self::Target {
        self.explain
    }
}

impl<'a, X> DerefMut for ExplainStateInner<'a, X> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.explain
    }
}

impl<'a, X> Deref for ExplainState<'a, X> {
    type Target = ExplainStateInner<'a, X>;

    fn deref(&self) -> &Self::Target {
        &self.explain
    }
}

impl<'a, X> DerefMut for ExplainState<'a, X> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.explain
    }
}

struct InterpCtx {
    right_a: bool,
    is_i: bool,
    last_shared: DefExp,
    first_shared: Option<DefExp>,
}

impl InterpCtx {
    fn new(last_shared: DefExp, left_a: bool, right_a: bool) -> Self {
        InterpCtx {
            last_shared,
            right_a,
            is_i: !left_a,
            first_shared: None,
        }
    }

    fn add_shared(&mut self, shared: DefExp) {
        self.last_shared = shared;
        if self.first_shared == None {
            self.is_i = !self.right_a;
            self.first_shared = Some(shared)
        }
    }
}

impl<'x>
    ExplainStateInner<
        'x,
        &'x RawEGraph<SymbolLang, EClass, plat_egg::raw::semi_persistent1::UndoLog>,
    >
{
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
            (base_path_score, !other_is_left)
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
        self.max_assoc_union_gen::<HashSet<Id, _>>(left, right, |_, _, _| unreachable!())
    }

    fn max_assoc_union(&self, left: Id, right: Id) -> (u32, bool) {
        // Try with an `ApproxBitSet` and fallback to using a `HashSet` if it doesn't work
        self.max_assoc_union_gen::<ApproxBitSet>(left, right, Self::max_assoc_union_fallback)
    }

    fn handle_congruence(&mut self, left: Id, right: Id, flip: &mut bool) {
        if left == right {
            debug_assert!(!*flip);
            return;
        }
        let this_flip = *flip;
        *flip = false;
        if let Some([lc0, lc1]) = check_node_is_eq(self.raw.id_to_node(left)) {
            let Some([rc0, rc1]) = check_node_is_eq(self.raw.id_to_node(right)) else {
                unreachable!("congruent nodes don't match");
            };
            // if we're trying to prove why (= x x) = (= y z) by congruence
            // we would normally prove x = y and x = z, but since all reflexive equalities are
            // true at level 0, we can instead prove why true = (= y z) which just requires
            // proving why y = z
            if lc0 == lc1 {
                trace!("id{left} = id{right} since id{rc0} = id{rc1}");
                self.deferred_explanations.push((rc0, rc1));
                return;
            } else if rc0 == rc1 {
                trace!("id{left} = id{right} since id{lc0} = id{lc1}");
                self.deferred_explanations.push((lc0, lc1));
                return;
            }
        }
        self.used_congruence = true;
        trace!("id{left} = id{right} by fused congruence {flip}");
        let current_node = self.raw.id_to_node(left);
        let next_node = self.raw.id_to_node(right);
        debug_assert!(current_node.matches(next_node));
        let left_children = current_node.children().iter().copied();
        if this_flip {
            let right_children = [next_node.children()[1], next_node.children()[0]];

            self.deferred_explanations
                .extend(left_children.zip(right_children));
        } else {
            let right_children = next_node.children().iter().copied();

            self.deferred_explanations
                .extend(left_children.zip(right_children));
        }
    }

    fn handle_interpolant_congruence(
        &mut self,
        left: Id,
        right: Id,
        flip: &mut bool,
        left_a: &mut bool,
        right_a: bool,
        congruence_start: usize,
        interp: &mut InterpolateArg,
        b_buf: &mut Vec<(DefExp, DefExp)>,
        b_buf_len: usize,
        ctx: &mut InterpCtx,
    ) {
        let congruence_mid = self.deferred_explanations.len();
        self.handle_congruence(left, right, flip);
        trace!(
            "Children: {:?}",
            &self.deferred_explanations[congruence_mid..]
        );
        if *left_a != right_a && left != right {
            for i in congruence_start..congruence_mid {
                let (left, right) = self.deferred_explanations[i];
                self.explanation_interpolant_h(left, right, interp, b_buf, *left_a, *left_a);
            }
            let mut v = SmallVec::<[DefExp; 4]>::new();
            for i in congruence_mid..self.deferred_explanations.len() {
                let (left, right) = self.deferred_explanations[i];
                let mid =
                    self.explanation_interpolant_h(left, right, interp, b_buf, *left_a, right_a);
                v.push(mid);
            }
            let f = self.raw.id_to_node(left).op().sym();
            let mut mid_intern = interp.scope();
            for id in v {
                mid_intern.add_def(id);
            }
            let mid_def = mid_intern.finish(f);
            drop(mid_intern);
            self.deferred_explanations.truncate(congruence_start);
            Self::handle_interpolant_path_inner(
                ctx.last_shared,
                mid_def,
                interp,
                ctx.is_i,
                *left_a,
                b_buf,
                b_buf_len,
            );
            *left_a = right_a;
            ctx.add_shared(mid_def);
        }
    }

    fn handle_interpolant_path(
        &mut self,
        left: DefExp,
        right: DefExp,
        interp: &mut InterpolateArg<'_>,
        is_i: bool,
        is_a: bool,
        congruence_start: usize,
        b_buf: &mut Vec<(DefExp, DefExp)>,
        b_buf_len: usize,
    ) {
        for i in congruence_start..self.deferred_explanations.len() {
            let (left, right) = self.deferred_explanations[i];
            self.explanation_interpolant_h(left, right, interp, b_buf, is_a, is_a);
        }
        self.deferred_explanations.truncate(congruence_start);
        Self::handle_interpolant_path_inner(left, right, interp, is_i, is_a, b_buf, b_buf_len);
    }

    fn handle_interpolant_path_inner(
        left: DefExp,
        right: DefExp,
        interp: &mut InterpolateArg,
        is_i: bool,
        is_a: bool,
        b_buf: &mut Vec<(DefExp, DefExp)>,
        b_buf_len: usize,
    ) {
        trace!("handle_interpolant path i:{is_i} a:{is_a}");
        match (is_i, is_a) {
            (false, false) => b_buf.push((left, right)),
            (true, true) => {
                let mut interp_j = interp.scope();
                for (i, j) in b_buf.drain(b_buf_len..) {
                    let mut interp_eq = interp_j.scope();
                    interp_eq.add_def(i);
                    interp_eq.add_def(j);
                    let eq = interp_eq.finish(EQ_SYM);
                    interp_eq.add_def(eq);
                    let neq = interp_eq.finish(NOT_SYM);
                    drop(interp_eq);
                    interp_j.add_def(neq);
                }
                let mut interp_eq = interp_j.scope();
                interp_eq.add_def(left);
                interp_eq.add_def(right);
                let eq = interp_eq.finish(EQ_SYM);
                drop(interp_eq);
                interp_j.add_def(eq);
                let j = interp_j.finish(OR_SYM);
                drop(interp_j);
                interp.add_def(j);
            }
            _ => {}
        }
    }

    // See https://arxiv.org/pdf/1111.5652 section 4.5
    // if is_i == Some(true) stores I(left, right) in interp
    // if is_i == Some(false) extends b_buf with B(left, right)
    //   and stores ^{I(s) for s in B(left, right)} in interp
    // if is_i == None, finds the first shared id, returns it, behaves like is_i == Some(!outer_left_a)
    // until that first shared id and then behaves like is_i == Some(outer_left_a)
    pub(super) fn explanation_interpolant_h(
        &mut self,
        left: Id,
        right: Id,
        interp: &mut InterpolateArg<'_>,
        b_buf: &mut Vec<(DefExp, DefExp)>,
        outer_left_a: bool,
        outer_right_a: bool,
    ) -> DefExp {
        trace!("Start explanation_interpolant_h {left}({outer_left_a}) {right}({outer_right_a})");
        let mut ctx = InterpCtx::new(interp.intern_exp(left), outer_left_a, outer_right_a);
        let old_stack_len = self.stack.len();
        debug_assert_eq!(self.raw.find(left), self.raw.find(right));
        let mut args = (left, right);
        let mut left_congruence = left;
        let mut flip = false;
        let last_congruence_len = self.deferred_explanations.len();
        let b_buf_len = b_buf.len();
        let mut was_last_a = outer_left_a;
        loop {
            let (left, right) = args;
            args = if left != right {
                let (assoc_union, left_is_old) = self.max_assoc_union(left, right);
                let union_info = self.union_info[assoc_union as usize];
                let just = union_info.just;
                let (next_left, next_right) = if left_is_old {
                    (union_info.old_id, union_info.new_id)
                } else {
                    (union_info.new_id, union_info.old_id)
                };
                // call
                self.stack.push(StackElem {
                    next_left,
                    just,
                    next_right,
                    right,
                });
                (left, next_left)
            } else {
                // return
                if self.stack.len() <= old_stack_len {
                    break;
                }

                let StackElem {
                    next_left,
                    just,
                    next_right,
                    right,
                } = self.stack.pop().unwrap();

                left_congruence = match just.expand() {
                    EJustification::Lit(l) => {
                        trace!("id{next_left} = id{next_right} by {just:?}");
                        let cur_a = interp.is_a_only(var_to_nv(l.var()));
                        self.handle_interpolant_congruence(
                            left_congruence,
                            next_left,
                            &mut flip,
                            &mut was_last_a,
                            cur_a,
                            last_congruence_len,
                            interp,
                            b_buf,
                            b_buf_len,
                            &mut ctx,
                        );
                        if was_last_a != cur_a {
                            let def = interp.intern_exp(next_left);
                            self.handle_interpolant_path(
                                ctx.last_shared,
                                def,
                                interp,
                                ctx.is_i,
                                was_last_a,
                                last_congruence_len,
                                b_buf,
                                b_buf_len,
                            );
                            // we finished a path from last shared to next_left
                            // it was an a-path if was_last_a_only
                            ctx.add_shared(def);
                        }
                        was_last_a = cur_a;
                        next_right
                    }
                    EJustification::NoOp => {
                        let was_last_a2 = was_last_a;
                        self.handle_interpolant_congruence(
                            left_congruence,
                            next_left,
                            &mut flip,
                            &mut was_last_a,
                            was_last_a2,
                            last_congruence_len,
                            interp,
                            b_buf,
                            b_buf_len,
                            &mut ctx,
                        );
                        trace!("id{next_left} = id{next_right} by {just:?}");
                        next_right
                    }
                    EJustification::Congruence(f) => {
                        trace!("id{next_left} = id{next_right} by congruence {f}");
                        flip ^= f;
                        left_congruence
                    }
                };
                // tail call
                (next_right, right)
            }
        }
        self.handle_interpolant_congruence(
            left_congruence,
            right,
            &mut flip,
            &mut was_last_a,
            outer_right_a,
            last_congruence_len,
            interp,
            b_buf,
            b_buf_len,
            &mut ctx,
        );
        self.handle_interpolant_path(
            ctx.last_shared,
            interp.intern_exp(right),
            interp,
            ctx.is_i,
            was_last_a,
            last_congruence_len,
            b_buf,
            b_buf_len,
        );
        trace!("End explanation_interpolant_h {left}({outer_left_a}) {right}({outer_right_a})");
        ctx.first_shared.unwrap_or_else(|| interp.intern_exp(right))
    }

    pub(super) fn explanation_interpolant(
        &mut self,
        left: Id,
        right: Id,
        interp: &mut InterpolateArg<'_>,
    ) -> DefExp {
        trace!("Start explanation_interpolant {left} {right}");
        let mut b_buf = Vec::new();
        self.explanation_interpolant_h(left, right, interp, &mut b_buf, false, false);
        debug_assert!(b_buf.is_empty());
        debug_assert!(self.stack.is_empty());
        interp.finish(AND_SYM)
    }
}

impl<'x>
    ExplainState<'x, &'x RawEGraph<SymbolLang, EClass, plat_egg::raw::semi_persistent1::UndoLog>>
{
    pub(crate) fn used_congruence(&self) -> bool {
        self.used_congruence
    }

    fn explain_equivalence_h(&mut self, left: Id, right: Id) {
        debug_assert!(self.stack.is_empty());
        debug_assert_eq!(self.raw.find(left), self.raw.find(right));
        let mut args = (left, right);
        let mut left_congruence = left;
        let mut flip = false;
        loop {
            let (left, right) = args;
            args = if left != right {
                let (assoc_union, left_is_old) = self.max_assoc_union(left, right);
                if assoc_union < self.base_unions {
                    trace!("id{left} = id{right} at base level");
                    self.handle_congruence(left_congruence, left, &mut flip);
                    // left = right at base level, so we can skip this subtree
                    left_congruence = right;
                    // tail call with to equal ids to force a return
                    args = (right, right);
                    continue;
                }
                let union_info = self.union_info[assoc_union as usize];
                let just = union_info.just;
                let (next_left, next_right) = if left_is_old {
                    (union_info.old_id, union_info.new_id)
                } else {
                    (union_info.new_id, union_info.old_id)
                };
                trace!("Pending {next_left} = {next_right} the {assoc_union}th union");

                let ids = minmax(left, right);
                if assoc_union < self.last_unions
                    && !matches!(self.raw.get_class(left).deref(), EClass::Bool(_))
                {
                    // avoid equalities between booleans
                    // this also prevents creating equalities about already created equalities,
                    // so we create a most n^2
                    // We would like to explain left equals right, and if we could do it in a single
                    // lit UIP would choose this lit (since assoc_union < self.last_unions).

                    // We would like to find a lit that represents (= left right)
                    match self.eq_ids.map.entry(ids) {
                        Entry::Occupied(mut occ) => match occ.get().expand() {
                            EEqIdInfo::Lit(lit) => {
                                // Yay! we found one
                                // Note: we require sat solver to use UIP to avoid explaining lit
                                // in terms of itself
                                trace!("id{left} = id{right} by found {lit:?}");
                                self.add_just(lit);
                                self.handle_congruence(left_congruence, left, &mut flip);
                                // left = right by lit, so we can skip this subtree
                                left_congruence = right;

                                // tail call with to equal ids to force a return
                                args = (right, right);
                                continue;
                            }
                            EEqIdInfo::Pending(last_info) => {
                                let curr_info = exp_hash(just);
                                if last_info != curr_info {
                                    // This is at least the second time this kind of lit would be
                                    // useful, and the other time(s) we explained the equality of
                                    // ids differently then we are going to do now
                                    // This is a good candidate for a pair of ids to assign a
                                    // literal for
                                    debug!("requesting {ids:?}");
                                    self.eq_ids.requests.push(ids);
                                    occ.insert(EqIdInfo::REQUESTED);
                                }
                            }
                            EEqIdInfo::Requested => {
                                trace!("Already requested {ids:?}");
                            }
                        },
                        Entry::Vacant(vac) => {
                            if cfg!(feature = "test_add_more_mid_search_equalities") {
                                // It should always be fine to add additional equalities, so we
                                // use this for testing
                                // Since pending requests do not get removed during `pop` we may
                                // request an equality too eagerly, so it's important this works
                                self.eq_ids.requests.push(ids);
                                vac.insert(EqIdInfo::REQUESTED);
                            } else {
                                // This is the first time this kind of explanation would be useful, so
                                // we remember how we will explain the equality in case we would want
                                // to explain it again differently later
                                let curr_info = exp_hash(just);
                                vac.insert(EqIdInfo::pending(curr_info));
                            }
                            trace!("preparing request for {ids:?}")
                        }
                    }
                }

                // call
                self.stack.push(StackElem {
                    next_left,
                    just,
                    next_right,
                    right,
                });
                (left, next_left)
            } else {
                // return
                let Some(StackElem {
                    next_left,
                    just,
                    next_right,
                    right,
                }) = self.stack.pop()
                else {
                    break;
                };
                left_congruence = match just.expand() {
                    EJustification::Lit(just) => {
                        self.handle_congruence(left_congruence, next_left, &mut flip);
                        trace!("id{next_left} = id{next_right} by {just:?}");
                        self.add_just(just);
                        next_right
                    }
                    EJustification::Congruence(f) => {
                        trace!("id{next_left} = id{next_right} by congruence {f}");
                        flip ^= f;
                        left_congruence
                    }
                    EJustification::NoOp => {
                        self.handle_congruence(left_congruence, next_left, &mut flip);
                        trace!("id{next_left} = id{next_right} by noop");
                        next_right
                    }
                };
                // tail call
                (next_right, right)
            }
        }
        self.handle_congruence(left_congruence, right, &mut flip);
    }

    fn add_just(&mut self, just: Lit) {
        self.out.push(!just)
    }

    pub fn explain_equivalence(&mut self, left: Id, right: Id) {
        debug_assert!(self.deferred_explanations.is_empty());
        debug_assert_eq!(self.raw.find(left), self.raw.find(right));
        self.deferred_explanations.push((left, right));
        while let Some((left, right)) = self.deferred_explanations.pop() {
            if self.deferred_explanations_set.insert((left, right)) {
                trace!("start explain id{left} = id{right}");
                self.explain_equivalence_h(left, right);
                trace!("end explain id{left} = id{right}");
            }
        }
        self.deferred_explanations_set.clear();
        self.deferred_explanations.clear();
    }
}

impl Explain {
    pub(crate) fn pop(&mut self, old_nodes: usize, old_unions: usize) {
        self.union_info.truncate(old_unions);
        self.assoc_unions.truncate(old_nodes);
    }

    pub(crate) fn clear(&mut self) {
        self.union_info.clear();
        self.assoc_unions.clear();
    }
}
