use crate::Symbol;
use core::num::NonZeroU32;
use core::ops::IndexMut;
use no_std_compat::prelude::v1::*;
use plat_egg::raw::reflect_const::PathCompress;
pub use plat_egg::raw::semi_persistent1::PushInfo;
use plat_egg::raw::{semi_persistent1::UndoLog, EGraphResidual, Language, RawEClass, RawEGraph};
use plat_egg::Id;
use platsat::Lit;
use smallvec::SmallVec;
use std::cmp::Ordering;
use std::fmt::{Debug, Formatter};
use std::hash::{Hash, Hasher};
use std::mem;
use std::ops::{Deref, Index};

use super::explain::{EqIds, Explain, Justification};

const N: usize = 4;
pub type Children = SmallVec<[Id; N]>;
use super::euf::EClass;
use crate::intern::EQ_SYM;
use crate::recorder::{DefExp, InterpolateArg};
pub use smallvec::smallvec as children;

const SYMMETRY_SHIFT: u32 = u32::BITS - 1;
const SYMMETRY_MASK: u32 = 1 << SYMMETRY_SHIFT;

const FLIPPED_SHIFT: u32 = u32::BITS - 2;
const FLIPPED_MASK: u32 = 1 << FLIPPED_SHIFT;

const SYMBOL_MASK: u32 = u32::MAX >> 2;

#[derive(Copy, Clone)]
pub struct Op(u32);

impl Op {
    pub const fn new(sym: Symbol, symmetric: bool) -> Self {
        let sym = sym.0.get();
        assert!(sym & SYMBOL_MASK == sym);
        Op(sym | (symmetric as u32) << SYMMETRY_SHIFT)
    }

    pub fn is_symmetric(self) -> bool {
        self.0 & SYMMETRY_MASK != 0
    }

    fn flip(&mut self) {
        debug_assert!(self.is_symmetric());
        self.0 ^= FLIPPED_MASK;
    }

    /// Returns a congruence justification that is flipped if
    /// self's flipped-ness does not match other
    fn congruence_just(self, other: Self) -> Justification {
        let f1 = self.0 & FLIPPED_MASK;
        let f2 = other.0 & FLIPPED_MASK;
        Justification::congruence((f1 ^ f2) >> FLIPPED_SHIFT)
    }

    pub fn sym(self) -> Symbol {
        Symbol(NonZeroU32::new(self.sym_u32()).unwrap())
    }

    fn sym_u32(self) -> u32 {
        self.0 & SYMBOL_MASK
    }
}

pub const EQ_OP: Op = Op::new(EQ_SYM, true);

#[test]
fn test_flip() {
    let op1 = Op::new(EQ_SYM, true);
    use super::explain::EJustification;
    assert!(matches!(
        op1.congruence_just(op1).expand(),
        EJustification::Congruence(false)
    ));
    let mut op2 = op1;
    op2.flip();
    assert!(matches!(
        op1.congruence_just(op2).expand(),
        EJustification::Congruence(true)
    ));
}

impl From<Symbol> for Op {
    fn from(value: Symbol) -> Self {
        Self::new(value, false)
    }
}

impl PartialEq for Op {
    fn eq(&self, other: &Self) -> bool {
        self.sym_u32().eq(&other.sym_u32())
    }
}

impl Eq for Op {}

impl PartialOrd<Self> for Op {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Op {
    fn cmp(&self, other: &Self) -> Ordering {
        self.sym_u32().cmp(&other.sym_u32())
    }
}

impl Hash for Op {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.sym_u32().hash(state)
    }
}

impl Debug for Op {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.sym().fmt(f)
    }
}

#[derive(Hash, Eq, PartialEq, Debug, Ord, PartialOrd)]
pub struct SymbolLang {
    op: Op,
    children: Children,
}

impl Clone for SymbolLang {
    #[inline]
    fn clone(&self) -> Self {
        SymbolLang {
            op: self.op,
            children: Children::from_slice(&self.children),
        }
    }
}

impl Language for SymbolLang {
    type Discriminant = u32;

    fn discriminant(&self) -> Self::Discriminant {
        self.op.sym_u32()
    }

    fn matches(&self, other: &Self) -> bool {
        self.discriminant() == other.discriminant()
    }

    fn children(&self) -> &[Id] {
        &self.children
    }

    fn children_mut(&mut self) -> &mut [Id] {
        unreachable!()
    }

    fn for_each_mut<F: FnMut(&mut Id)>(&mut self, f: F) {
        self.children.iter_mut().for_each(f);
        self.canonize(Op::flip);
    }
}

impl SymbolLang {
    #[inline]
    fn canonize(&mut self, flip: impl Fn(&mut Op)) {
        if self.op.is_symmetric() {
            match &mut *self.children {
                [x, y] => {
                    if x > y {
                        mem::swap(x, y);
                        flip(&mut self.op)
                    }
                }
                _ => unreachable!(),
            }
        }
    }
    pub(crate) fn new(op: Op, children: Children) -> Self {
        debug_assert_eq!(op.0 & FLIPPED_MASK, 0, "op should not be flipped");
        let mut res = SymbolLang { op, children };
        // don't flip here since we want all un-cannonical nodes to be not flipped
        res.canonize(|_| {});
        res
    }

    pub(crate) fn children_owned(self) -> Children {
        self.children
    }

    pub fn op(&self) -> Op {
        self.op
    }
}

#[derive(Debug, Clone)]
pub struct EGraph<D> {
    inner: RawEGraph<SymbolLang, D, UndoLog>,
    explain: Explain,
}

impl<D> Default for EGraph<D> {
    fn default() -> Self {
        EGraph {
            inner: Default::default(),
            explain: Default::default(),
        }
    }
}

impl<D> Deref for EGraph<D> {
    type Target = EGraphResidual<SymbolLang, PathCompress<false>>;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl EGraph<EClass> {
    pub fn add(
        &mut self,
        op: Op,
        children: Children,
        mut mk_data: impl FnMut(Id, &[Id]) -> EClass,
    ) -> Id {
        let id = RawEGraph::raw_add(
            self,
            |x| &mut x.inner,
            SymbolLang::new(op, children),
            // Note unlike the EGraph in plat_egg we only use explanations for clause learning,
            // so we do not need to distinguish between nodes that are
            // equivalent modulo ground equalities
            |_, id, _| Some(id),
            |_, _, _| unreachable!(),
            |this, id, _| {
                this.explain.add(id);
                mk_data(id, &this.id_to_node(id).children)
            },
        );
        self.inner.find_mut(id)
    }

    pub fn add_uncanonical(
        &mut self,
        op: Op,
        children: Children,
        mk_data: impl FnMut(Id) -> EClass,
        mut merge: impl FnMut(&mut EClass, EClass),
    ) -> Id {
        RawEGraph::raw_add_for_sym(
            &mut (self, mk_data),
            |(this, _)| &mut this.inner,
            SymbolLang::new(op, children),
            // Note unlike the EGraph in plat_egg we only use explanations for clause learning,
            // so we do not need to distinguish between nodes that are
            // equivalent modulo ground equalities
            |_, _, _| None,
            |node1, node2| node1.op.congruence_just(node2.op),
            |(this, mk_data), just, root_child, added_id| {
                this.explain.add(added_id);
                let class = this.inner.get_class_mut(root_child).0;
                merge(&mut *class, mk_data(added_id));
                this.explain.union(added_id, just, added_id, root_child);
            },
            |(this, mk_data), id, _| {
                this.explain.add(id);
                mk_data(id)
            },
        )
    }

    pub fn union(
        &mut self,
        id1: Id,
        id2: Id,
        justification: Justification,
        mut merge: impl FnMut(&mut EClass, EClass),
    ) {
        self.inner.raw_union(id1, id2, |info| {
            merge(info.data1, info.data2);
            let (old_id, new_id) = if info.swapped_ids {
                (id1, id2)
            } else {
                (id2, id1)
            };
            self.explain.union(info.id2, justification, old_id, new_id)
        })
    }

    pub fn try_rebuild<S, E>(
        outer: &mut S,
        get_self: impl Fn(&mut S) -> &mut Self,
        union: impl FnMut(&mut S, Justification, Id, Id) -> Result<(), E>,
    ) -> Result<(), E> {
        RawEGraph::try_raw_rebuild_for_sym(
            outer,
            |this| &mut get_self(this).inner,
            |n1, n2| n1.op.congruence_just(n2.op),
            union,
            |_, _, _| {},
        )
    }

    pub fn push(&self) -> PushInfo {
        self.inner.push1()
    }

    pub fn pop(&mut self, info: PushInfo, mut split: impl FnMut(&mut EClass) -> EClass) {
        self.explain
            .pop(info.number_of_uncanonical_nodes(), info.number_of_unions());
        self.inner.raw_pop1(info, |data, _, _| split(data))
    }

    pub fn clear(&mut self) {
        self.explain.clear();
        self.inner.clear();
    }

    /// Returns whether the explanation used congruence
    pub fn explain_equivalence(
        &mut self,
        id1: Id,
        id2: Id,
        res: &mut Vec<Lit>,
        base_unions: usize,
        last_unions: usize,
        eq_ids: &mut EqIds,
    ) -> bool {
        let mut explain = self.explain.promote(
            &self.inner,
            res,
            base_unions as u32,
            last_unions as u32,
            eq_ids,
        );
        explain.explain_equivalence(id1, id2);
        explain.used_congruence()
    }

    pub(crate) fn explanation_interpolant(
        &mut self,
        id0: Id,
        id1: Id,
        mut interp: InterpolateArg<'_>,
    ) -> DefExp {
        let mut explain = self.explain.promote_for_interpolant(&self.inner);
        explain.explanation_interpolant(id0, id1, &mut interp)
    }

    pub fn dump_classes(&self) -> impl Debug + '_ {
        self.inner.dump_classes()
    }
}

impl<D> Index<Id> for EGraph<D> {
    type Output = RawEClass<D>;

    fn index(&self, id: Id) -> &Self::Output {
        self.inner.get_class(id)
    }
}

impl<D> IndexMut<Id> for EGraph<D> {
    fn index_mut(&mut self, id: Id) -> &mut Self::Output {
        self.inner.get_class_mut(id).0
    }
}
