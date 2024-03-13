use batsat::LSet;
use egg::raw::{self, semi_persistent1::UndoLog, EGraphResidual, RawEGraph};
use egg::{Id, Language, Symbol};
use smallvec::SmallVec;
use std::ops::{Deref, Index};

use crate::explain;
use crate::explain::{Explain, Justification};

const N: usize = 4;
pub type Children = SmallVec<[Id; N]>;

#[derive(Hash, Eq, PartialEq, Debug, Ord, PartialOrd)]
pub struct SymbolLang {
    pub(crate) op: Symbol,
    pub(crate) children: Children,
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
    type Discriminant = Symbol;

    fn discriminant(&self) -> Self::Discriminant {
        self.op
    }

    fn matches(&self, other: &Self) -> bool {
        self.op == other.op
    }

    fn children(&self) -> &[Id] {
        &self.children
    }

    fn children_mut(&mut self) -> &mut [Id] {
        &mut self.children
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
pub type PushInfo = (raw::semi_persistent1::PushInfo, explain::PushInfo);

impl<D> Deref for EGraph<D> {
    type Target = EGraphResidual<SymbolLang>;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<D> EGraph<D> {
    pub fn add(
        &mut self,
        name: Symbol,
        children: Children,
        mut mk_data: impl FnMut(Id) -> D,
    ) -> Id {
        RawEGraph::raw_add(
            self,
            |x| &mut x.inner,
            SymbolLang { op: name, children },
            // Note unlike the EGraph in egg we only use explanations for clause learning,
            // so we do not need to distinguish between nodes that are
            // equivalent modulo ground equalities
            |_, id, _| Some(id),
            |this, existing_id, new_id| {
                this.explain
                    .union(existing_id, Justification::CONGRUENCE, existing_id, new_id)
            },
            |this, id, _| {
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
        mut merge: impl FnMut(&mut D, D),
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
        union: impl FnMut(&mut S, Id, Id) -> Result<(), E>,
    ) -> Result<(), E> {
        RawEGraph::try_raw_rebuild(outer, |this| &mut get_self(this).inner, union, |_, _, _| {})
    }

    pub fn push(&self) -> PushInfo {
        (self.inner.push1(), self.explain.push())
    }

    pub fn pop(&mut self, info: PushInfo, mut split: impl FnMut(&mut D) -> D) {
        self.explain
            .pop(info.1, info.0.number_of_uncanonical_nodes());
        self.inner.raw_pop1(info.0, |data, _, _| split(data))
    }

    pub fn clear(&mut self) {
        self.explain.clear();
        self.inner.clear();
    }

    pub fn explain_equivalence(&self, id1: Id, id2: Id, res: &mut LSet, negate: bool) {
        self.explain
            .promote(&self.inner, res, negate)
            .explain_equivalence(id1, id2)
    }

    pub fn is_clean(&self) -> bool {
        self.inner.is_clean()
    }
}

impl<D> Index<Id> for EGraph<D> {
    type Output = D;

    fn index(&self, id: Id) -> &Self::Output {
        self.inner.get_class(id)
    }
}
