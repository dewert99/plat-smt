use crate::egraph::{children, Children, EGraph, Op, PushInfo as EGPushInfo, SymbolLang, EQ_OP};
use crate::explain::{EqIds, Justification};
use crate::intern::{Sort, SymbolInfo, FALSE_SYM, TRUE_SYM};
use crate::solver::{BoolExp, Exp, UExp};
use crate::theory::{IncrementalWrapper, Theory};
use crate::util::{format_args2, minmax, Bind, DebugIter};
use crate::Symbol;
use batsat::{LMap, LSet};
use batsat::{Lit, TheoryArg, Var};
use egg::{raw::Language, Id};
use hashbrown::HashMap;
use log::{debug, trace};
use perfect_derive::perfect_derive;
use std::fmt::{Debug, Formatter};
use std::mem;
use std::ops::Range;

type LitVec = smallvec::SmallVec<[Lit; 4]>;
use smallvec::smallvec as litvec;

#[derive(Copy, Clone, Eq, PartialEq)]
struct OpId(u32);

impl OpId {
    const NONE: Self = OpId(u32::MAX);

    fn some(id: Id) -> Self {
        let x = usize::from(id) as u32;
        debug_assert_ne!(x, u32::MAX);
        OpId(x)
    }

    fn expand(self) -> Option<Id> {
        match self.0 {
            u32::MAX => None,
            x => Some(Id::from(x as usize)),
        }
    }
}

impl Debug for OpId {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.expand().fmt(f)
    }
}

impl Default for OpId {
    fn default() -> Self {
        OpId::NONE
    }
}

#[derive(Debug, Clone)]
pub(crate) enum BoolClass {
    Const(bool),
    Unknown(LitVec),
}

impl BoolClass {
    fn to_exp(&self) -> BoolExp {
        match self {
            BoolClass::Const(b) => BoolExp::Const(*b),
            BoolClass::Unknown(v) => BoolExp::Unknown(v[0]),
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) enum EClass {
    Uninterpreted(Sort),
    Bool(BoolClass),
    /// EClass that creates a conflict whenever it is merged
    /// Not used for top level expressions, but used to implement `distinct`
    Singleton,
}

impl EClass {
    fn to_exp(&self, id: Id) -> Exp {
        match self {
            EClass::Bool(b) => b.to_exp().into(),
            EClass::Uninterpreted(s) => UExp { id, sort: *s }.into(),
            EClass::Singleton => unreachable!(),
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
    request_log_len: u32,
}

pub(crate) fn id_for_bool(b: bool) -> Id {
    Id::from(b as usize)
}

#[derive(Debug)]
pub struct EUFInner {
    egraph: EGraph<EClass>,
    bool_class_history: Vec<MergeInfo>,
    lit_id_log: Vec<Lit>,
    assertion_level_lit: Lit,
    explanation: LSet,
    lit_ids: LMap<OpId>,
    distinct_gensym: u32,
    eq_ids: EqIds,
    eq_id_log: Vec<[Id; 2]>,
    requests_handled: u32,
}

impl Default for EUFInner {
    fn default() -> Self {
        let mut egraph = EGraph::default();
        let fid = egraph.add(FALSE_SYM.into(), Children::new(), |_| {
            EClass::Bool(BoolClass::Const(false))
        });
        let tid = egraph.add(TRUE_SYM.into(), Children::new(), |_| {
            EClass::Bool(BoolClass::Const(true))
        });
        let mut res = EUFInner {
            egraph,
            bool_class_history: vec![],
            explanation: Default::default(),
            lit_id_log: vec![],
            lit_ids: Default::default(),
            assertion_level_lit: Lit::UNDEF,
            distinct_gensym: 0,
            eq_ids: Default::default(),
            eq_id_log: vec![],
            requests_handled: 0,
        };
        res.init();
        debug_assert_eq!(tid, id_for_bool(true));
        debug!("id{tid:?} is true");
        debug_assert_eq!(fid, id_for_bool(false));
        debug!("id{fid:?} is false");
        res
    }
}

type Result = core::result::Result<(), ()>;

pub type EUF = IncrementalWrapper<EUFInner>;
impl Theory<EUF> for EUFInner {
    type LevelMarker = PushInfo;

    fn create_level(&mut self) -> PushInfo {
        debug!("Push");
        PushInfo {
            egraph: self.egraph.push(),
            lit_log_len: self.lit_id_log.len() as u32,
            eq_id_log_len: self.eq_id_log.len() as u32,
            request_log_len: self.eq_ids.requests.len() as u32,
        }
    }

    fn pop_to_level(&mut self, info: PushInfo) {
        debug!("Pop");

        for lit in self.lit_id_log.drain(info.lit_log_len as usize..) {
            self.lit_ids[lit] = OpId::NONE;
        }
        for ids in self.eq_id_log.drain(info.eq_id_log_len as usize..) {
            self.eq_ids.remove(&ids);
        }
        if info.egraph.number_of_uncanonical_nodes() < self.egraph.number_of_uncanonical_nodes() {
            // ensure all requests contain valid ids
            // TODO use `extract_if` when it becomes stable
            let eq_ids = &mut self.eq_ids;
            for i in (info.request_log_len as usize..eq_ids.requests.len()).rev() {
                let [lower_id, higher_id] = eq_ids.requests[i];
                debug_assert!(lower_id <= higher_id);
                if usize::from(higher_id) >= info.egraph.number_of_uncanonical_nodes() {
                    trace!("Removed request {:?}", [lower_id, higher_id]);
                    eq_ids.requests.swap_remove(i);
                    eq_ids.remove(&[lower_id, higher_id]);
                }
            }
        }
        self.requests_handled = info.request_log_len;

        self.egraph.pop(info.egraph, |class| match class {
            EClass::Uninterpreted(x) => EClass::Uninterpreted(*x),
            EClass::Bool(class) => {
                EClass::Bool(class.split(self.bool_class_history.pop().unwrap()))
            }
            EClass::Singleton => EClass::Singleton,
        });
        trace!("\n{:?}", self.egraph.dump_uncanonical());
    }

    fn initial_check(this: &mut EUF, acts: &mut TheoryArg) -> Result {
        while (this.requests_handled as usize) < this.eq_ids.requests.len() {
            let [id0, id1] = this.eq_ids.requests[this.requests_handled as usize];
            this.requests_handled += 1;
            if this.find(id0) != this.find(id1) {
                let lit = this.eq_ids.get_or_insert([id0, id1], || acts.mk_new_lit());
                let (id, res) = this.add_uncanonical(EQ_OP, children![id0, id1], lit, acts);
                this.add_id_to_lit(id, lit);
                this.make_equality_true(id0, id1);
                debug!("lit{lit:?} is defined as (= {id0} {id1}) mid-search");
                res.expect("Adding mid search shouldn't cause conflict");
            } else {
                debug_assert!(this.eq_ids.get([id0, id1]).is_none());
            }
        }
        Ok(())
    }

    fn learn(this: &mut EUF, lit: Lit, acts: &mut TheoryArg) -> Result {
        debug_assert!(acts.is_ok());
        debug!("EUF learns {lit:?}");
        let just = Justification::from_lit(lit);
        let tlit = lit.apply_sign(true);
        if let Some(id) = this.lit_ids[tlit].expand() {
            // Note it is important to union the children of an equality before union-ing the lit
            // with true because of an optimization in the explanation
            let node = this.egraph.id_to_node(id);
            if let Some([id0, id1]) = this.eq_ids.check_node_is_eq(node) {
                this.union(acts, id0, id1, just)?;
            }
            let cid = this.id_for_bool(true);
            this.union(acts, cid, id, just)?;
        }
        if let Some(id) = this.lit_ids[!tlit].expand() {
            let cid = this.id_for_bool(false);
            this.union(acts, cid, id, just)?;
        }
        Ok(())
    }

    fn pre_decision_check(this: &mut EUF, acts: &mut TheoryArg) -> Result {
        this.rebuild(acts)
    }

    fn explain_propagation(this: &mut EUF, p: Lit, is_final: bool) -> &[Lit] {
        if let Some(id) = this.lit_ids[p].expand() {
            let const_bool = this.id_for_bool(true);
            if this.egraph.find(id) == this.egraph.find(const_bool) {
                let res = this.explain(id, const_bool, false, is_final);
                if !res.has(p) {
                    debug!("EUF explains {p:?} by {:?}", res.as_slice());
                    return &this.explanation;
                } else {
                    trace!(
                        "Skipping incorrect explanation {p:?} by {:?}",
                        res.as_slice()
                    );
                }
            }
        }
        if let Some(id) = this.lit_ids[!p].expand() {
            let const_bool = this.id_for_bool(false);
            let res = this.explain(id, const_bool, false, is_final);
            debug!("EUF explains {p:?} by {:?}", res.as_slice());
            return res;
        }
        unreachable!()
    }

    fn set_assertion_level_lit(&mut self, l: Option<Lit>) {
        self.assertion_level_lit = l.unwrap_or(Lit::UNDEF)
    }

    fn assertion_level_lit(&self) -> Option<Lit> {
        (self.assertion_level_lit != Lit::UNDEF).then_some(self.assertion_level_lit)
    }

    fn clear(&mut self) {
        let bools = [false, true];
        let bool_syms = bools.map(|b| self.egraph.id_to_node(self.id_for_bool(b)).op());
        self.egraph.clear();
        self.lit_id_log.clear();
        self.lit_ids.clear();
        self.bool_class_history.clear();
        self.eq_ids.clear();
        for (b, s) in bools.into_iter().zip(bool_syms) {
            let id = self
                .egraph
                .add(s, Children::new(), |_| EClass::Bool(BoolClass::Const(b)));
            debug_assert_eq!(id, id_for_bool(b))
        }
        self.init();
    }
}

pub(crate) trait SatSolver {
    fn is_ok(&self) -> bool;
    fn propagate(&mut self, p: Lit) -> bool;
    fn raise_conflict(&mut self, lits: &[Lit], costly: bool);
}

impl<'a> SatSolver for TheoryArg<'a> {
    fn is_ok(&self) -> bool {
        self.is_ok()
    }

    fn propagate(&mut self, p: Lit) -> bool {
        self.propagate(p)
    }

    fn raise_conflict(&mut self, lits: &[Lit], costly: bool) {
        self.raise_conflict(lits, costly)
    }
}

struct MergeContext<'a, S: SatSolver> {
    acts: &'a mut S,
    history: &'a mut Vec<MergeInfo>,
    conflict: &'a mut Option<[Id; 2]>,
}

impl<'a, S: 'a + SatSolver> MergeContext<'a, S> {
    fn propagate(&mut self, lits: &[Lit], b: bool) {
        let lits = lits.iter().map(|l| *l ^ !b);
        debug!("EUF propagates {:?}", DebugIter(&lits));
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
                self.propagate(&lits, b);
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

    fn merge_fn(mut self, id1: Id, id2: Id) -> impl FnMut(&mut EClass, EClass) + Bind<&'a S> {
        move |lclass, rclass| match (lclass, rclass) {
            (EClass::Uninterpreted(sort), EClass::Uninterpreted(sort2)) if *sort == sort2 => {}
            (EClass::Bool(lbool), EClass::Bool(rbool)) => self.merge_bools(lbool, rbool),
            (EClass::Singleton, EClass::Singleton) => *self.conflict = Some([id1, id2]),
            (l, r) => unreachable!("merging eclasses with different sorts {:?} {:?}", l, r),
        }
    }
}

impl EUF {
    fn explain(&mut self, id1: Id, id2: Id, negate: bool, is_final: bool) -> &LSet {
        let base_unions = self
            .base_marker()
            .map(|x| x.egraph.number_of_unions())
            .unwrap_or(usize::MAX);
        let last_unions = if is_final {
            base_unions // don't use shortcut explanations for `explain_propagation_final`
        } else {
            self.last_marker()
                .map(|x| x.egraph.number_of_unions())
                .unwrap_or(usize::MAX)
        };
        let this = &mut **self;
        this.explanation.clear();
        if this.assertion_level_lit != Lit::UNDEF {
            this.explanation.insert(this.assertion_level_lit ^ negate);
        }
        this.egraph.explain_equivalence(
            id1,
            id2,
            &mut this.explanation,
            negate,
            base_unions,
            last_unions,
            &mut this.eq_ids,
        );
        &this.explanation
    }

    fn conflict(&mut self, acts: &mut impl SatSolver, id1: Id, id2: Id) {
        self.explanation.clear();
        let res = self.explain(id1, id2, true, false);
        debug!("EUF Conflict by {:?}", res.as_slice());
        acts.raise_conflict(res, true)
    }

    pub(crate) fn rebuild(&mut self, acts: &mut impl SatSolver) -> Result {
        debug!("Rebuilding EGraph");
        EGraph::try_rebuild(
            self,
            |this| &mut this.egraph,
            |this, just, id1, id2| this.union(acts, id1, id2, just),
        )
    }

    pub(crate) fn add_uncanonical(
        &mut self,
        op: Op,
        children: Children,
        lit: Lit,
        acts: &mut impl SatSolver,
    ) -> (Id, Result) {
        let mut conflict = None;
        let this = &mut **self;
        let ctx = MergeContext {
            acts,
            history: &mut this.bool_class_history,
            conflict: &mut conflict,
        };
        // this won't be used since the new class won't be EClass::Singleton
        let dummy_id = Id::from(usize::MAX);
        let id = this.egraph.add_uncanonical(
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
        return (id, Ok(()));
    }

    pub(crate) fn union(
        &mut self,
        acts: &mut impl SatSolver,
        id1: Id,
        id2: Id,
        just: Justification,
    ) -> Result {
        debug!("EUF union id{id1:?} with id{id2:?} by {just:?}");
        let mut conflict = None;
        let this = &mut **self;
        let ctx = MergeContext {
            acts,
            history: &mut this.bool_class_history,
            conflict: &mut conflict,
        };
        this.egraph.union(id1, id2, just, ctx.merge_fn(id1, id2));
        if !acts.is_ok() {
            return Err(());
        }

        if let Some([id1, id2]) = conflict {
            self.conflict(acts, id1, id2);
            return Err(());
        }
        return Ok(());
    }
}

impl EUFInner {
    fn init(&mut self) {
        let t_eq_f = self.egraph.add(
            EQ_OP,
            children![id_for_bool(false), id_for_bool(true)],
            |_| EClass::Bool(BoolClass::Const(false)),
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
    pub(crate) fn find(&self, id: Id) -> Id {
        self.egraph.find(id)
    }

    pub fn reserve(&mut self, v: Var) {
        self.lit_ids.reserve_default(Lit::new(v, false));
    }

    fn add_id_to_lit(&mut self, id: Id, l: Lit) {
        self.reserve(l.var());
        self.lit_ids[l] = OpId::some(id);
        self.lit_id_log.push(l);
        debug!(
            "{l:?} is defined as {:?} and given id{id:?}",
            self.egraph.id_to_node(id)
        );
    }

    pub(crate) fn add_bool_node(
        &mut self,
        sym: Op,
        children: Children,
        mut fresh_lit: impl FnMut() -> Lit,
    ) -> (BoolExp, bool, Id) {
        let mut added = None;
        let id = self.egraph.add(sym.into(), children, |_| {
            let lit = fresh_lit();
            added = Some(lit);
            EClass::Bool(BoolClass::Unknown(litvec![lit]))
        });
        if let Some(l) = added {
            self.add_id_to_lit(id, l);
            (BoolExp::Unknown(l), true, id)
        } else {
            let b = match &*self.egraph[id] {
                EClass::Uninterpreted(x) => {
                    unreachable!("merging eclasses with different sorts {:?}, Bool", x)
                }
                EClass::Bool(b) => b.to_exp(),
                _ => unreachable!(),
            };
            (b, false, id)
        }
    }

    /// add a boolean node with the intention to immediately union it to another bool node
    /// returns the id and whether it is new
    pub(crate) fn add_blank_bool_node(&mut self, op: Op, children: Children) -> (Id, bool) {
        let mut added = false;
        let id = self.egraph.add(op, children, |_| {
            added = true;
            EClass::Bool(BoolClass::Unknown(litvec![]))
        });
        (id, added)
    }

    pub(crate) fn add_eq_node(
        &mut self,
        id1: Id,
        id2: Id,
        fresh_lit: impl FnMut() -> Lit,
    ) -> BoolExp {
        if self.egraph.find(id1) == self.egraph.find(id2) {
            return BoolExp::TRUE;
        }
        let (res, added, id) =
            self.add_bool_node(EQ_OP, Children::from_slice(&[id1, id2]), fresh_lit);
        if added {
            if let BoolExp::Unknown(l) = res {
                let ids = minmax(id1, id2);
                self.eq_id_log.push(ids);
                self.eq_ids.insert(ids, l);
            }

            self.make_equality_true(id1, id2);
        }
        debug!("{res:?} is defined as (= id{id1:?} id{id2:?}) and given id{id:?}");
        res
    }

    // union one of (= alt_id alt_id) or (= id id) with true
    fn make_equality_true(&mut self, id: Id, alt_id: Id) {
        let candidate = SymbolLang::new(EQ_OP, children![alt_id, alt_id]);
        let eq_self = match self.egraph.lookup(candidate) {
            Some(id) => id,
            None => self.egraph.add(EQ_OP, children![id, id], |_| {
                EClass::Bool(BoolClass::Const(true))
            }),
        };
        let tid = self.id_for_bool(true);
        self.egraph
            .union(tid, eq_self, Justification::NOOP, |_, _| {
                self.bool_class_history.push(MergeInfo::Both(true))
            })
    }

    pub(crate) fn add_uninterpreted_node(&mut self, sym: Op, children: Children, sort: Sort) -> Id {
        self.egraph
            .add(sym, children, |_| EClass::Uninterpreted(sort))
    }

    pub(crate) fn make_distinct(
        &mut self,
        ids: impl IntoIterator<Item = Id>,
        syms: &mut SymbolInfo,
    ) -> Result {
        let s = syms.gen_sym("distinct");
        self.distinct_gensym += 1;
        for id in ids {
            let mut added = false;
            self.egraph.add(s.into(), Children::from_slice(&[id]), |_| {
                added = true;
                EClass::Singleton
            });
            if !added {
                return Err(());
            }
        }
        Ok(())
    }

    pub fn id_for_lit(&mut self, lit: Lit, syms: &mut SymbolInfo) -> Id {
        match &mut self.lit_ids[lit].expand() {
            Some(id) => *id,
            None => {
                let sym = syms.gen_sym(&format_args2!("bool|lit|{lit:?}"));
                self.add_bool_node(sym.into(), Children::new(), || lit).2
            }
        }
    }
    pub fn id_for_bool(&self, b: bool) -> Id {
        id_for_bool(b)
    }

    pub fn function_info(&self, buf: &mut FunctionInfo) {
        buf.clear();
        for (id, node) in self.egraph.uncanonical_nodes() {
            let node = node.clone().map_children(|id| self.find(id));
            buf.data.push((node, id))
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

    pub fn id_to_exp(&self, id: Id) -> Exp {
        self.egraph[id].to_exp(id)
    }

    pub fn has_parents(&self, id: Id) -> bool {
        self.egraph[id].parents().len() > 0
    }
}

#[perfect_derive(Default)]
pub struct FunctionInfo<L = SymbolLang> {
    indices: HashMap<Symbol, Range<usize>>,
    data: Vec<(L, Id)>,
}

pub struct FullFunctionInfo<'a, L = SymbolLang> {
    base: &'a FunctionInfo<L>,
    euf: &'a EUFInner,
}

impl<L> FunctionInfo<L> {
    pub fn clear(&mut self) {
        self.indices.clear();
        self.data.clear();
    }

    pub fn get(&self, s: Symbol) -> &[(L, Id)] {
        self.indices.get(&s).map_or(&[], |r| &self.data[r.clone()])
    }

    pub fn with_euf<'a>(&'a self, euf: &'a EUFInner) -> FullFunctionInfo<'a, L> {
        FullFunctionInfo { base: self, euf }
    }
}

impl<'a, L: Language> FullFunctionInfo<'a, L> {
    pub fn get(
        &self,
        s: Symbol,
    ) -> impl ExactSizeIterator<Item = (impl Iterator<Item = Exp> + 'a, Exp)> {
        let iter = self.base.get(s).iter();
        let id_to_exp = |id: &Id| self.euf.id_to_exp(*id);
        iter.map(move |(node, id)| (node.children().iter().map(id_to_exp), id_to_exp(id)))
    }
}
