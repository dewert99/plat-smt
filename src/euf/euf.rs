use super::egraph::{children, Children, EGraph, Op, PushInfo as EGPushInfo, SymbolLang, EQ_OP};
use super::explain::{EqIds, Justification};
use crate::exp::{BoolExp, EitherExp};
use crate::intern::{DisplayInterned, InternInfo, Sort, BOOL_SORT, EQ_SYM, FALSE_SYM, TRUE_SYM};
use crate::theory::{Incremental, Theory};
use crate::util::{minmax, Bind, DebugIter, DisplayFn, HashMap};
use crate::{SubExp, Symbol};
use core::fmt::Display;
use default_vec2::ConstDefault;
use log::{debug, trace};
use no_std_compat::prelude::v1::*;
use perfect_derive::perfect_derive;
use plat_egg::raw::Language;
use plat_egg::Id;
use platsat::{lbool, LMap, Lit};
use std::fmt::{Debug, Formatter};
use std::mem;
use std::ops::Range;

pub type Exp = EitherExp<BoolExp, UExp>;

pub(super) type LitVec = smallvec::SmallVec<[Lit; 4]>;
use crate::collapse::ExprContext;
use crate::tseitin::{SatExplainTheoryArgT, SatTheoryArgT};
pub(super) use smallvec::smallvec as litvec;

/// A possible [`Id`] for a [`Lit`]
#[derive(Copy, Clone, Eq, PartialEq)]
struct LitId(u32);

impl LitId {
    /// No [`Id`] is associated with the lit
    const NONE: Self = LitId(u32::MAX);

    /// `id` is strongly associated with the lit.
    ///
    /// If `weak` is false: When `lit` is assigned a value `id` will be union-ed with true or false
    /// based on the assignment
    ///
    /// If `weak` is true: When `lit` is assigned a value `id` may be union-ed with true or false
    /// based on the assignment but this must not be relied upon for completeness
    ///
    /// lits must not use weak ids for explanations.
    /// If lit_a and is weakly associated with id_a, and lit_b is strongly associated with id_a,
    /// then if lit_a is learned first and then lit_b (possibly from their negations) lit_b will
    /// union id_a with true, and later when asked for the explanation of lit_a if egraph tried to
    /// use id_a for the explanation it would explain lit_a using lit_b even though lit_b was learned
    /// later
    ///
    /// lits can get away without using weak ids for explanations since lits with weak ids don't get
    /// stored in the eclass so they can never be propagated by euf
    ///
    /// converting a weak association to a strong association is acceptable as long as the lit hasn't
    /// been assigned a value which prevents the problem described earlier
    ///
    fn some(id: Id, weak: bool) -> Self {
        let x = usize::from(id) as u32;
        debug_assert!(x < u32::MAX / 2);
        LitId(x | ((weak as u32) << 31))
    }

    /// Returns `Some(id)` iff self represents and strong association to `id`.
    fn expand(self) -> Option<Id> {
        match self.0 >> 31 {
            1 => None,
            _ => Some(Id::from(self.0 as usize)),
        }
    }

    /// Returns `Some(id)` iff self represents any association to `id`.
    fn expand_weak(self) -> Option<Id> {
        match self.0 {
            u32::MAX => None,
            x => Some(Id::from((x & (u32::MAX >> 1)) as usize)),
        }
    }
}

impl Debug for LitId {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.expand().fmt(f)
    }
}

impl Default for LitId {
    fn default() -> Self {
        LitId::NONE
    }
}

impl ConstDefault for LitId {
    const DEFAULT: &'static Self = &LitId::NONE;
}

#[derive(Debug, Clone, PartialEq)]
pub(super) enum BoolClass {
    Const(bool),
    Unknown(LitVec),
}

impl BoolClass {
    fn to_exp(&self) -> BoolExp {
        match self {
            BoolClass::Const(b) => BoolExp::from_bool(*b),
            BoolClass::Unknown(v) => BoolExp::unknown(v[0]),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub(super) enum EClass {
    Uninterpreted(Sort),
    Bool(BoolClass),
    /// EClass that propagate whenever it is merged
    /// Not used for top level expressions, but used to implement `distinct`
    Singleton(BoolExp),
}

impl EClass {
    fn to_exp(&self, id: Id) -> Exp {
        match self {
            EClass::Bool(b) => b.to_exp().upcast(),
            EClass::Uninterpreted(s) => UExp::new(id, *s).upcast(),
            EClass::Singleton(_) => unreachable!(),
        }
    }

    fn to_display_exp<'a>(&'a self, id: Id, intern: &'a InternInfo) -> impl Display + 'a {
        DisplayFn(move |f| match self {
            &EClass::Uninterpreted(sort) => DisplayInterned::fmt(&UExp { id, sort }, intern, f),
            EClass::Bool(BoolClass::Const(b)) => Display::fmt(b, f),
            EClass::Bool(BoolClass::Unknown(l)) if l.len() > 0 => {
                Display::fmt(&BoolExp::unknown(l[0]), f)
            }
            EClass::Bool(BoolClass::Unknown(_)) => f.write_str("(as _ Bool)"),
            EClass::Singleton(b) => write!(f, "(Singleton {b:?})"),
        })
    }

    fn to_sort(&self) -> Sort {
        match self {
            EClass::Uninterpreted(s) => *s,
            EClass::Bool(_) => BOOL_SORT,
            _ => BOOL_SORT,
        }
    }
}

impl BoolClass {
    fn split(&mut self, info: MergeInfo) -> BoolClass {
        match (&mut *self, info) {
            (BoolClass::Const(_), MergeInfo::Both(b)) => BoolClass::Const(b),
            (BoolClass::Const(_), MergeInfo::Left(lits)) => BoolClass::Unknown(lits),
            (BoolClass::Const(b), MergeInfo::Right(lits)) => {
                let res = BoolClass::Const(*b);
                *self = BoolClass::Unknown(lits);
                res
            }
            (BoolClass::Unknown(lits), MergeInfo::Neither(rlits)) => {
                lits.truncate(lits.len() - rlits.len());
                BoolClass::Unknown(rlits)
            }
            x => unreachable!("{x:?}"),
        }
    }
}

#[derive(Debug)]
enum MergeInfo {
    Both(bool),
    Left(LitVec),
    Right(LitVec),
    Neither(LitVec),
}

#[derive(Debug, Clone)]
pub struct PushInfo {
    egraph: EGPushInfo,
    lit_log_len: u32,
    eq_id_log_len: u32,
    requests_handled: u32,
}

pub(super) fn id_for_bool(b: bool) -> Id {
    Id::from(b as usize)
}

#[derive(Debug, Default)]
pub(super) struct LitInfo {
    ids: LMap<LitId>,
    log: Vec<Lit>,
}

impl LitInfo {
    pub(super) fn strengthen_id_for_lit(&mut self, id: Id, lit: Lit) {
        debug_assert_eq!(self.ids[lit].expand_weak(), Some(id));
        self.ids[lit] = LitId::some(id, false);
    }

    pub(super) fn add_id_to_lit(&mut self, id: Id, l: Lit, weak: bool) {
        self.ids[l] = LitId::some(id, weak);
        self.log.push(l);
        debug!(
            "(as @v{id:?} Bool) is defined as {:?} (weak: {})",
            BoolExp::unknown(l),
            weak
        );
    }
}

#[derive(Debug, Default)]
pub struct Euf {
    pub(super) egraph: EGraph<EClass>,
    bool_class_history: Vec<MergeInfo>,
    pub(super) lit: LitInfo,
    pub(super) distinct_gensym: u32,
    eq_ids: EqIds,
    eq_id_log: Vec<[Id; 2]>,
    requests_handled: u32,
    function_info: FunctionInfo,
}

type Result = core::result::Result<(), ()>;

impl Incremental for Euf {
    type LevelMarker = PushInfo;

    fn create_level(&self) -> PushInfo {
        PushInfo {
            egraph: self.egraph.push(),
            lit_log_len: self.lit.log.len() as u32,
            eq_id_log_len: self.eq_id_log.len() as u32,
            requests_handled: self.requests_handled,
        }
    }

    fn pop_to_level(&mut self, info: PushInfo, clear_lits: bool) {
        debug!("Requests handled = {}", info.requests_handled);
        for lit in self.lit.log.drain(info.lit_log_len as usize..) {
            self.lit.ids[lit] = LitId::NONE;
        }
        for ids in self.eq_id_log.drain(info.eq_id_log_len as usize..) {
            self.eq_ids.remove(&ids);
        }
        if info.egraph.number_of_uncanonical_nodes() < self.egraph.number_of_uncanonical_nodes() {
            // ensure all requests contain valid ids
            // TODO use `extract_if` when it becomes stable
            let eq_ids = &mut self.eq_ids;
            for i in (info.requests_handled as usize..eq_ids.requests.len()).rev() {
                let [lower_id, higher_id] = eq_ids.requests[i];
                debug_assert!(lower_id <= higher_id);
                if usize::from(higher_id) >= info.egraph.number_of_uncanonical_nodes() {
                    trace!("Removed request {:?}", [lower_id, higher_id]);
                    eq_ids.requests.swap_remove(i);
                    eq_ids.remove(&[lower_id, higher_id]);
                }
            }
        }
        self.requests_handled = info.requests_handled;
        if clear_lits {
            for i in self.requests_handled as usize..self.eq_ids.requests.len() {
                let ids = self.eq_ids.requests[i];
                self.eq_ids.remove(&ids)
            }
        }

        self.egraph.pop(info.egraph, |class| match class {
            EClass::Uninterpreted(x) => EClass::Uninterpreted(*x),
            EClass::Bool(class) => {
                EClass::Bool(class.split(self.bool_class_history.pop().unwrap()))
            }
            EClass::Singleton(x) => EClass::Singleton(*x),
        });
        trace!("\n{:?}", self.egraph.dump_uncanonical());
        trace!("\n{:?}", self.egraph.dump_classes())
    }

    fn clear(&mut self) {
        self.egraph.clear();
        self.lit.log.clear();
        self.lit.ids.clear();
        self.bool_class_history.clear();
        self.eq_ids.clear();
    }
}

impl<'a, A: SatTheoryArgT<'a, M = PushInfo>> Theory<A, A::Explain<'a>> for Euf {
    fn init(&mut self, acts: &mut A) {
        for (b, s) in [false, true].into_iter().zip([FALSE_SYM, TRUE_SYM]) {
            let id = self.egraph.add(Op::from(s), Children::new(), |_, _| {
                EClass::Bool(BoolClass::Const(b))
            });
            debug_assert_eq!(id, id_for_bool(b));
            acts.log_def_exp(UExp::new(id, BOOL_SORT), BoolExp::from_bool(b));
        }
        let t_eq_f = self.egraph.add(
            EQ_OP,
            children![id_for_bool(false), id_for_bool(true)],
            |_, _| EClass::Bool(BoolClass::Const(false)),
        );
        self.egraph.union(
            t_eq_f,
            self.id_for_bool(false),
            Justification::NOOP,
            |d1, d2| {
                debug_assert!(matches!(d1, EClass::Bool(BoolClass::Const(false))));
                debug_assert!(matches!(d2, EClass::Bool(BoolClass::Const(false))));
            },
        )
    }
    fn initial_check(&mut self, acts: &mut A) -> Result {
        while (self.requests_handled as usize) < self.eq_ids.requests.len() {
            let [id0, id1] = self.eq_ids.requests[self.requests_handled as usize];
            self.requests_handled += 1;
            if self.find(id0) != self.find(id1) {
                let lit = self.eq_ids.get_or_insert([id0, id1], || {
                    let res = Lit::new(acts.new_var(lbool::UNDEF, false), true);
                    acts.log_def(
                        BoolExp::unknown(res),
                        EQ_SYM,
                        [
                            UExp::new(id0, self.egraph[id0].to_sort()),
                            UExp::new(id1, self.egraph[id1].to_sort()),
                        ]
                        .into_iter(),
                    );
                    res
                });
                let (id, res) = self.add_uncanonical(EQ_OP, children![id0, id1], lit, acts);
                self.lit.add_id_to_lit(id, lit, false);
                self.make_equality_true(id0, id1);
                debug!(
                    "{} is defined as (= {} {}) mid-search",
                    BoolExp::unknown(lit),
                    self.id_to_display_exp(id0, acts),
                    self.id_to_display_exp(id1, acts)
                );
                res.expect("Adding mid search shouldn't cause conflict");
            } else {
                debug_assert!(self.eq_ids.get([id0, id1]).is_none());
            }
        }
        Ok(())
    }

    fn learn(&mut self, lit: Lit, acts: &mut A) -> Result {
        debug_assert!(acts.is_ok());
        debug!("EUF learns {lit:?}");
        let just = Justification::from_lit(lit);
        let tlit = lit.apply_sign(true);
        if let Some(id) = self.lit.ids[tlit].expand() {
            if !matches!(&*self.egraph[id], EClass::Bool(_)) {
                // this is just a reminder of how to explain why a distinct node is false
                return Ok(());
            }
            // Note it is important to union the children of an equality before union-ing the lit
            // with true because of an optimization in the explanation
            let node = self.egraph.id_to_node(id);
            if let Some([id0, id1]) = self.eq_ids.check_node_is_eq(node) {
                self.union(acts, id0, id1, just)?;
            }
            let cid = self.id_for_bool(true);
            self.union(acts, cid, id, just)?;
        }
        if let Some(id) = self.lit.ids[!tlit].expand() {
            let cid = self.id_for_bool(false);
            self.union(acts, cid, id, just)?;
        }
        Ok(())
    }

    fn pre_decision_check(&mut self, acts: &mut A) -> Result {
        self.rebuild(acts)
    }

    #[cold]
    fn final_check(&mut self, acts: &mut A) {
        for i in 0..acts.model().len() {
            let l = acts.model()[i];
            for (lp, b) in [(l, true), (!l, false)] {
                if let Some(id) = self.lit.ids[lp].expand_weak() {
                    let res = self.union(acts, id, id_for_bool(b), Justification::from_lit(l));
                    debug_assert!(res.is_ok());
                }
            }
        }
    }

    fn explain_propagation(&mut self, p: Lit, acts: &mut A::Explain<'a>, is_final: bool) {
        let base_len = acts.clause_builder().len();
        if let Some(id) = self.lit.ids[p].expand() {
            let const_bool = self.id_for_bool(true);
            if self.egraph.find(id) == self.egraph.find(const_bool) {
                self.explain(id, const_bool, is_final, acts);
                let explanation = acts.clause_builder();
                if explanation.last() != Some(&!p) {
                    debug_assert!(!explanation.contains(&!p), "{explanation:?}, {p:?}");
                    debug!("EUF explains {p:?} (= {p:?} true) with clause {explanation:?}");
                    return;
                } else {
                    trace!("Skipping incorrect explanation {p:?} with clause {explanation:?}");
                    explanation.truncate(base_len)
                }
            }
        }
        if let Some(id) = self.lit.ids[!p].expand() {
            let const_bool = self.id_for_bool(false);
            if self.egraph.find(id) == self.egraph.find(const_bool) {
                self.explain(id, const_bool, is_final, acts);
                debug!(
                    "EUF explains {p:?} (= {:?} false) with clause {:?}",
                    !p,
                    acts.clause_builder()
                );
                return;
            }
        }
        if let (Some(id1), Some(id2)) = (self.lit.ids[p].expand(), self.lit.ids[!p].expand()) {
            // Explanation of lack of distinctness
            self.explain(id1, id2, is_final, acts);
            debug!(
                "EUF explains {p:?} (distinct check) with clause {:?}",
                acts.clause_builder()
            );
            return;
        }
        unreachable!("EUF couldn't explain {p:?}")
    }
}
struct MergeContext<'a, A> {
    acts: &'a mut A,
    history: &'a mut Vec<MergeInfo>,
    lit: &'a mut LitInfo,
    conflict: &'a mut Option<[Id; 2]>,
}

impl<'a, 'b, A: SatTheoryArgT<'b>> MergeContext<'a, A> {
    fn propagate(&mut self, lits: &[Lit], b: bool) {
        let lits = lits.iter().map(|l| *l ^ !b);
        debug!("EUF propagates {:?}", DebugIter(lits.clone()));
        for lit in lits {
            self.acts.propagate(lit);
        }
    }
    fn merge_bools(&mut self, lbool: &mut BoolClass, rbool: BoolClass) {
        let info = match (&mut *lbool, rbool) {
            (BoolClass::Const(b1), BoolClass::Const(b2)) => {
                if *b1 != b2 {
                    *self.conflict = Some([id_for_bool(false), id_for_bool(true)])
                }
                MergeInfo::Both(b2)
            }
            (BoolClass::Const(b), BoolClass::Unknown(lits)) => {
                self.propagate(&lits, *b);
                MergeInfo::Left(lits)
            }
            (BoolClass::Unknown(lits), BoolClass::Const(b)) => {
                self.propagate(lits, b);
                let res = MergeInfo::Right(mem::take(lits));
                *lbool = BoolClass::Const(b);
                res
            }
            (BoolClass::Unknown(lits1), BoolClass::Unknown(lits2)) => {
                lits1.extend_from_slice(&lits2);
                MergeInfo::Neither(lits2)
            }
        };
        self.history.push(info);
    }

    fn merge_fn(mut self, id1: Id, id2: Id) -> impl FnMut(&mut EClass, EClass) + Bind<&'a A> {
        move |lclass, rclass| match (lclass, rclass) {
            (EClass::Uninterpreted(sort), EClass::Uninterpreted(sort2)) if *sort == sort2 => {}
            (EClass::Bool(lbool), EClass::Bool(rbool)) => self.merge_bools(lbool, rbool),
            (EClass::Singleton(b1), EClass::Singleton(b2)) => {
                debug_assert_eq!(*b1, b2);
                match b1.to_lit() {
                    Err(false) => *self.conflict = Some([id1, id2]),
                    Err(true) => {}
                    Ok(l) => {
                        if self.acts.value_lit(l) != lbool::TRUE {
                            self.acts.propagate(l);
                            // hack only used for
                            self.lit.add_id_to_lit(id1, l, false);
                            self.lit.add_id_to_lit(id2, !l, false);
                        }
                    }
                }
            }
            (l, r) => unreachable!(
                "merging eclasses with different sorts {} {}",
                l.to_display_exp(id1, self.acts.intern()),
                r.to_display_exp(id2, self.acts.intern())
            ),
        }
    }
}
impl Euf {
    pub(super) fn find(&self, id: Id) -> Id {
        self.egraph.find(id)
    }
    pub(super) fn finish_eq_node<'a>(
        &mut self,
        l: Lit,
        cid1: Id,
        cid2: Id,
        acts: &mut impl SatTheoryArgT<'a>,
    ) {
        debug!(
            "{} is defined as (= {} {})",
            BoolExp::unknown(l),
            self.id_to_display_exp(cid1, acts),
            self.id_to_display_exp(cid2, acts)
        );
        let ids = minmax(cid1, cid2);
        self.eq_id_log.push(ids);
        self.eq_ids.insert(ids, l);
        self.make_equality_true(cid1, cid2);
    }

    // union one of (= alt_id alt_id) or (= id id) with true
    fn make_equality_true(&mut self, id: Id, alt_id: Id) {
        let candidate = SymbolLang::new(EQ_OP, children![alt_id, alt_id]);
        let eq_self = match self.egraph.lookup(candidate) {
            Some(id) => id,
            None => self.egraph.add(EQ_OP, children![id, id], |_, _| {
                EClass::Bool(BoolClass::Const(true))
            }),
        };
        let tid = self.id_for_bool(true);
        self.egraph
            .union(tid, eq_self, Justification::NOOP, |_, _| {
                self.bool_class_history.push(MergeInfo::Both(true))
            })
    }

    pub(super) fn check_id_for_lit(&self, lit: Lit) -> Option<Id> {
        self.lit.ids[lit].expand_weak()
    }

    pub(super) fn id_for_lit<'a>(
        &mut self,
        lit: Lit,
        acts: &mut impl SatTheoryArgT<'a>,
        weak: bool,
    ) -> Id {
        let val = acts.value_lit(lit);
        if val == lbool::TRUE {
            id_for_bool(true)
        } else if val == lbool::FALSE {
            id_for_bool(false)
        } else {
            match self.lit.ids[lit].expand_weak() {
                Some(id) => {
                    // If it was weak before we now need it to be strong
                    self.lit.ids[lit].0 &= !((!weak as u32) << 31);
                    id
                }
                None => {
                    let sym = acts.intern_mut().symbols.gen_sym("bool");
                    let id = self.egraph.add(sym.into(), Children::new(), |_, _| {
                        EClass::Bool(BoolClass::Unknown(litvec![]))
                    });
                    self.lit.add_id_to_lit(id, lit, weak);
                    acts.log_def_exp(UExp::new(id, BOOL_SORT), BoolExp::unknown(lit));
                    id
                }
            }
        }
    }

    pub(super) fn id_for_bool(&self, b: bool) -> Id {
        id_for_bool(b)
    }

    pub(super) fn id_for_exp<'a>(
        &mut self,
        exp: Exp,
        acts: &mut impl SatTheoryArgT<'a>,
        weak: bool,
    ) -> Id {
        match exp {
            Exp::Left(b) => match b.to_lit() {
                Err(b) => id_for_bool(b),
                Ok(lit) => self.id_for_lit(lit, acts, weak),
            },
            Exp::Right(u) => u.id(),
        }
    }

    pub(super) fn union_exp<'a>(
        &mut self,
        exp: Exp,
        id: Id,
        acts: &mut impl SatTheoryArgT<'a, M = PushInfo>,
    ) {
        debug!("Union exp {exp:?}, @v{id:?}");
        let exp_id = match exp {
            Exp::Left(b) => match acts.canonize(b).to_lit() {
                Err(b) => id_for_bool(b),
                Ok(lit) => {
                    match &mut *self.egraph[id] {
                        EClass::Bool(BoolClass::Unknown(l)) => {
                            if let Some(lit_id) = self.lit.ids[lit].expand_weak() {
                                // unifying with a lit that already has an id
                                // strengthen lit since it now represents a function
                                self.lit.strengthen_id_for_lit(lit_id, lit);
                                if *self.egraph[lit_id]
                                    == EClass::Bool(BoolClass::Unknown(litvec![]))
                                {
                                    let EClass::Bool(BoolClass::Unknown(l)) = &mut *self.egraph[id]
                                    else {
                                        unreachable!()
                                    };
                                    if l.is_empty() {
                                        // must have just created id
                                        // if lit wasn't stored in a class it will need to be now
                                        // add it to the new function so it will be removed
                                        // when this is undone
                                        l.push(lit);
                                        debug_assert_eq!(
                                            usize::from(id) + 1,
                                            self.egraph.uncanonical_ids().len()
                                        );
                                    } else {
                                        // merging these classes won't make cause lit to get
                                        // values based on the class since it wasn't storted
                                        // so we add this equality manually with an xor
                                        acts.xor(
                                            BoolExp::unknown(l[0]),
                                            BoolExp::unknown(lit),
                                            ExprContext::AssertEq(BoolExp::FALSE),
                                        );
                                    }
                                }
                                lit_id
                            } else {
                                if l.is_empty() {
                                    l.push(lit);
                                    debug_assert_eq!(
                                        usize::from(id) + 1,
                                        self.egraph.uncanonical_ids().len()
                                    );
                                } else {
                                    acts.xor(
                                        BoolExp::unknown(l[0]),
                                        BoolExp::unknown(lit),
                                        ExprContext::AssertEq(BoolExp::FALSE),
                                    );
                                }
                                self.lit.add_id_to_lit(id, lit, false);
                                return;
                            }
                        }
                        EClass::Bool(BoolClass::Const(b)) => {
                            acts.assert(BoolExp::unknown(lit ^ !*b));
                            return;
                        }
                        _ => unreachable!(),
                    }
                }
            },
            Exp::Right(u) => u.id(),
        };
        let _ = self.union(acts, id, exp_id, Justification::NOOP);
    }

    pub(super) fn resolve_children<'a>(
        &mut self,
        children: impl Iterator<Item = Exp>,
        acts: &mut impl SatTheoryArgT<'a>,
    ) -> Children {
        children.map(|x| self.id_for_exp(x, acts, false)).collect()
    }

    pub(super) fn init_function_info(&mut self) {
        let buf = &mut self.function_info;
        buf.clear();
        for (id, node) in self.egraph.uncanonical_nodes() {
            let node = node.clone().map_children(|id| self.egraph.find(id));
            buf.data.push((node, self.egraph.find(id)))
        }
        buf.data.sort_unstable_by(|x, y| x.0.cmp(&y.0));
        buf.data.dedup_by(|x, y| x.0 == y.0);
        let mut iter = buf.data.iter().map(|x| &x.0).enumerate();
        if let Some((i, x)) = iter.next() {
            let mut last_symbol = x.op();
            let mut last_idx = i;
            for (i, x) in iter {
                if x.op() != last_symbol {
                    buf.indices.insert(last_symbol.sym(), last_idx..i);
                    last_idx = i;
                    last_symbol = x.op();
                }
            }
            buf.indices
                .insert(last_symbol.sym(), last_idx..buf.data.len());
        }
    }

    pub(super) fn get_function_info(&self, s: Symbol) -> FunctionInfoIter<'_> {
        let iter = self.function_info.get(s).iter();
        FunctionInfoIter {
            pairs: iter,
            euf: &self,
        }
    }

    pub(super) fn id_to_exp(&self, id: Id) -> Exp {
        self.egraph[id].to_exp(id)
    }

    fn id_to_display_exp<'a, 'b>(
        &'a self,
        id: Id,
        acts: &'a impl SatTheoryArgT<'b>,
    ) -> impl Display + 'a {
        self.egraph[id].to_display_exp(id, acts.intern())
    }

    pub(super) fn add_uncanonical<'a, A: SatTheoryArgT<'a, M = PushInfo>>(
        &mut self,
        op: Op,
        children: Children,
        lit: Lit,
        acts: &mut A,
    ) -> (Id, Result) {
        let mut conflict = None;
        let ctx = MergeContext {
            acts,
            history: &mut self.bool_class_history,
            lit: &mut self.lit,
            conflict: &mut conflict,
        };
        // this won't be used since the new class won't be EClass::Singleton
        let dummy_id = Id::MAX;
        let id = self.egraph.add_uncanonical(
            op,
            children,
            |_| EClass::Bool(BoolClass::Unknown(litvec![lit])),
            ctx.merge_fn(dummy_id, dummy_id),
        );
        if !acts.is_ok() {
            return (id, Err(()));
        }

        if let Some([id1, id2]) = conflict {
            self.conflict(acts, id1, id2);
            return (id, Err(()));
        }
        (id, Ok(()))
    }

    /// writes an explanation clause of `id1 == id2` to `explanation`
    /// returns whether the explanation would be a useful clause
    fn explain<'a>(
        &mut self,
        id1: Id,
        id2: Id,
        is_final: bool,
        arg: &mut impl SatExplainTheoryArgT<'a, M = PushInfo>,
    ) -> bool {
        let base_unions = arg
            .base_marker()
            .map(|x| x.egraph.number_of_unions())
            .unwrap_or(usize::MAX);
        let last_unions = if is_final {
            base_unions // don't use shortcut explanations for `explain_propagation_final`
        } else {
            arg.last_marker()
                .map(|x| x.egraph.number_of_unions())
                .unwrap_or(usize::MAX)
        };
        self.egraph.explain_equivalence(
            id1,
            id2,
            arg.clause_builder(),
            base_unions,
            last_unions,
            &mut self.eq_ids,
        )
    }

    fn conflict<'a>(&mut self, acts: &mut impl SatTheoryArgT<'a, M = PushInfo>, id1: Id, id2: Id) {
        acts.for_explain().clause_builder().clear();
        let add_clause = self.explain(id1, id2, false, &mut acts.for_explain());
        acts.raise_conflict_using_builder(add_clause)
    }

    pub(super) fn rebuild<'a>(
        &mut self,
        acts: &mut impl SatTheoryArgT<'a, M = PushInfo>,
    ) -> Result {
        debug!("Rebuilding EGraph");
        EGraph::try_rebuild(
            self,
            |this| &mut this.egraph,
            |this, just, id1, id2| this.union(acts, id1, id2, just),
        )
    }

    pub(super) fn union<'a>(
        &mut self,
        acts: &mut impl SatTheoryArgT<'a, M = PushInfo>,
        id1: Id,
        id2: Id,
        just: Justification,
    ) -> Result {
        debug!(
            "EUF union @v{:?} ({}) with @v{:?} ({}) by {just:?}",
            id1,
            self.id_to_display_exp(id1, acts),
            id2,
            self.id_to_display_exp(id2, acts)
        );
        let mut conflict = None;
        let ctx = MergeContext {
            acts,
            history: &mut self.bool_class_history,
            lit: &mut self.lit,
            conflict: &mut conflict,
        };
        self.egraph.union(id1, id2, just, ctx.merge_fn(id1, id2));
        if !acts.is_ok() {
            return Err(());
        }

        if let Some([id1, id2]) = conflict {
            self.conflict(acts, id1, id2);
            return Err(());
        }
        Ok(())
    }
}

#[perfect_derive(Default, Debug)]
struct FunctionInfo {
    indices: HashMap<Symbol, Range<usize>>,
    data: Vec<(SymbolLang, Id)>,
}

impl FunctionInfo {
    fn clear(&mut self) {
        self.indices.clear();
        self.data.clear();
    }

    fn get(&self, s: Symbol) -> &[(SymbolLang, Id)] {
        self.indices.get(&s).map_or(&[], |r| &self.data[r.clone()])
    }
}

pub struct ExpIter<'a> {
    ids: core::slice::Iter<'a, Id>,
    euf: &'a Euf,
}

impl<'a> Iterator for ExpIter<'a> {
    type Item = Exp;

    fn next(&mut self) -> Option<Self::Item> {
        Some(self.euf.id_to_exp(*self.ids.next()?))
    }

    fn fold<B, F>(self, init: B, f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        self.ids.map(|&id| self.euf.id_to_exp(id)).fold(init, f)
    }
}

pub struct FunctionInfoIter<'a> {
    pairs: core::slice::Iter<'a, (SymbolLang, Id)>,
    euf: &'a Euf,
}

impl<'a> Iterator for FunctionInfoIter<'a> {
    type Item = (ExpIter<'a>, Exp);

    fn next(&mut self) -> Option<Self::Item> {
        let (node, cid) = self.pairs.next()?;
        Some((
            ExpIter {
                ids: node.children().iter(),
                euf: &self.euf,
            },
            self.euf.id_to_exp(*cid),
        ))
    }

    fn fold<B, F>(self, init: B, f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        self.pairs
            .map(|(node, cid)| {
                (
                    ExpIter {
                        ids: node.children().iter(),
                        euf: &self.euf,
                    },
                    self.euf.id_to_exp(*cid),
                )
            })
            .fold(init, f)
    }
}

use super::euf_impl::UExp;
