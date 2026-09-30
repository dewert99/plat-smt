use crate::collapse::ExprContext;
use crate::empty_theory::EmptyTheory;
use crate::euf::UExp;
use crate::euf::egraph::EClassT;
use crate::euf::euf::{EClass, LitVec, id_for_bool, litvec};
use crate::euf::euf_th::{EufTh, EufThBase, EufTheoryArg, EufTheoryArgT, ParentEufTh};
use crate::euf::explain::Justification;
use crate::intern::{BOOL_SORT, DisplayInterned, InternInfo};
use crate::theory::TheoryArgT;
use crate::tseitin::{SatExplainTheoryArgT, SatTheoryArgT};
use crate::util::DebugIter;
use crate::{BoolExp, EitherExp, Sort, SubExp, SuperExp};
use core::fmt::{Display, Formatter};
use core::{iter, mem};
use log::debug;
use plat_egg::Id;
use platsat::{Lit, lbool};
use std::fmt;

#[derive(Debug, Clone, PartialEq)]
pub enum BoolClass {
    Const(bool),
    Unknown(LitVec),
}

impl BoolClass {
    pub(super) fn to_exp(&self) -> BoolExp {
        match self {
            BoolClass::Const(b) => BoolExp::from_bool(*b),
            BoolClass::Unknown(v) => BoolExp::unknown(v[0]),
        }
    }
}

#[derive(Debug, Clone)]
pub enum MergeInfo {
    Both(bool),
    Left(LitVec),
    Right(LitVec),
    Neither(LitVec),
}

impl DisplayInterned for BoolClass {
    fn fmt(&self, _: &InternInfo, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            BoolClass::Const(b) => Display::fmt(b, f),
            BoolClass::Unknown(l) if l.len() > 0 => Display::fmt(&BoolExp::unknown(l[0]), f),
            BoolClass::Unknown(_) => f.write_str("(as _ Bool)"),
        }
    }
}

impl EClassT for BoolClass {
    type MergeInfo = MergeInfo;
    fn allows_fresh_equalities(&self) -> bool {
        false
    }

    fn split(&mut self, mut info: impl Iterator<Item = MergeInfo>) -> BoolClass {
        match (&mut *self, info.next().unwrap()) {
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

impl EufThBase for EmptyTheory {
    type EClass = BoolClass;

    type Exp = BoolExp;

    fn eclass_to_exp(&self, b: &Self::EClass) -> EitherExp<Self::Exp, UExp> {
        b.to_exp().upcast()
    }

    fn merge_classes(
        &mut self,
        l: &mut Self::EClass,
        r: Self::EClass,
        acts: &mut impl SatTheoryArgT,
    ) -> (impl Iterator<Item = MergeInfo>, Option<[Id; 2]>) {
        let mut conf = None;
        let info = match (&mut *l, r) {
            (BoolClass::Const(b1), BoolClass::Const(b2)) => {
                if *b1 != b2 {
                    conf = Some([id_for_bool(false), id_for_bool(true)])
                }
                MergeInfo::Both(b2)
            }
            (BoolClass::Const(b), BoolClass::Unknown(lits)) => {
                propagate(acts, &lits, *b);
                MergeInfo::Left(lits)
            }
            (BoolClass::Unknown(lits), BoolClass::Const(b)) => {
                propagate(acts, lits, b);
                let res = MergeInfo::Right(mem::take(lits));
                *l = BoolClass::Const(b);
                res
            }
            (BoolClass::Unknown(lits1), BoolClass::Unknown(lits2)) => {
                lits1.extend_from_slice(&lits2);
                MergeInfo::Neither(lits2)
            }
        };
        (iter::once(info), conf)
    }

    fn create_fresh_class_for_empty_theory(
        &mut self,
        acts: &mut impl SatTheoryArgT,
        _: Sort,
        ctx: ExprContext<Self::Exp>,
        id: Id,
        add_id_to_lit: impl FnOnce(Lit, Id) -> (),
    ) -> BoolClass {
        let lits = if let ExprContext::AssertEq(_) = ctx {
            litvec![]
        } else {
            let l = Lit::new(acts.new_var_default(), true);
            add_id_to_lit(l, id);
            acts.log_def_exp(BoolExp::unknown(l), UExp::new(id, BOOL_SORT));
            litvec![l]
        };

        BoolClass::Unknown(lits)
    }

    fn create_fresh_class(
        &mut self,
        _: &mut impl SatTheoryArgT,
        _: Sort,
        _: ExprContext<Self::Exp>,
        _: Id,
    ) -> Self::EClass {
        unreachable!("create_fresh_class must not be called directly")
    }
}

impl<'a, A: SatTheoryArgT, M, Th: ParentEufTh<Self, M>> EufTh<M, EufTheoryArg<'_, A, Th>>
    for EmptyTheory
{
    fn id_for_exp(&mut self, acts: &mut EufTheoryArg<'_, A, Th>, e: Self::Exp, weak: bool) -> Id {
        let lit = match e.to_lit() {
            Ok(l) => l,
            Err(b) => return id_for_bool(b),
        };
        let val = acts.value_lit(lit);
        if val == lbool::TRUE {
            id_for_bool(true)
        } else if val == lbool::FALSE {
            id_for_bool(false)
        } else {
            match acts.lit.get_weak(lit) {
                Some(id) => {
                    // If it was weak before we now need it to be strong
                    acts.lit.strengthen_if_needed(lit, weak);
                    id
                }
                None => {
                    let sym = acts.intern_mut().symbols.gen_sym("bool");
                    let id = acts.add(sym, || BoolClass::Unknown(litvec![]));
                    acts.lit.add_id_to_lit(id, lit, weak);
                    acts.log_def_exp(UExp::new(id, BOOL_SORT), BoolExp::unknown(lit));
                    id
                }
            }
        }
    }

    fn id_for_eq_exp(
        &mut self,
        acts: &mut EufTheoryArg<'_, A, Th>,
        e: Self::Exp,
        id: Id,
    ) -> Option<Id> {
        match acts.canonize(e).to_lit() {
            Err(b) => Some(id_for_bool(b)),
            Ok(lit) => {
                let EClass::Th(c) = &mut *acts.egraph[id] else {
                    unreachable!()
                };
                let c = c.downcast_mut().unwrap();
                match c {
                    BoolClass::Unknown(l) => {
                        if let Some(lit_id) = acts.lit.get_weak(lit) {
                            // unifying with a lit that already has an id
                            // strengthen lit since it now represents a function
                            acts.lit.strengthen_id_for_lit(lit_id, lit);
                            if let Some(BoolClass::Unknown(empt)) = acts.resolve(lit_id)
                                && empt.is_empty()
                            {
                                let EClass::Th(c) = &mut *acts.egraph[id] else {
                                    unreachable!()
                                };
                                let c = c.downcast_mut().unwrap();
                                let BoolClass::Unknown(l) = c else {
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
                                        acts.egraph.uncanonical_ids().len()
                                    );
                                } else {
                                    let l0 = l[0];
                                    // merging these classes won't make cause lit to get
                                    // values based on the class since it wasn't storted
                                    // so we add this equality manually with an xor
                                    acts.xor(
                                        BoolExp::unknown(l0),
                                        BoolExp::unknown(lit),
                                        ExprContext::AssertEq(BoolExp::FALSE),
                                    );
                                }
                            }
                            Some(lit_id)
                        } else {
                            if l.is_empty() {
                                l.push(lit);
                                debug_assert_eq!(
                                    usize::from(id) + 1,
                                    acts.egraph.uncanonical_ids().len()
                                );
                            } else {
                                let l0 = l[0];
                                acts.xor(
                                    BoolExp::unknown(l0),
                                    BoolExp::unknown(lit),
                                    ExprContext::AssertEq(BoolExp::FALSE),
                                );
                            }
                            acts.lit.add_id_to_lit(id, lit, false);
                            None
                        }
                    }
                    &mut BoolClass::Const(b) => {
                        acts.assert(BoolExp::unknown(lit ^ !b));
                        None
                    }
                }
            }
        }
    }

    fn assert_exp_eq(&mut self, acts: &mut EufTheoryArg<'_, A, Th>, b1: Self::Exp, b2: Self::Exp) {
        match (b1.to_lit(), b2.to_lit()) {
            (Err(pol), Ok(l)) | (Ok(l), Err(pol)) => {
                acts.assert(BoolExp::unknown(l ^ !pol));
            }
            (Err(b1), Err(b2)) => {
                if b1 != b2 {
                    acts.for_explain().clause_builder().clear();
                    acts.raise_conflict_using_builder(false)
                }
            }
            (Ok(b1), Ok(b2)) => {
                acts.xor(
                    BoolExp::unknown(b1),
                    BoolExp::unknown(b2),
                    ExprContext::AssertEq(BoolExp::FALSE),
                );
                unify_lits(acts, b1, b2);
                unify_lits(acts, !b1, !b2);
            }
        }
    }
}

fn unify_lits<A: SatTheoryArgT, M, Th: ParentEufTh<EmptyTheory, M>>(
    acts: &mut EufTheoryArg<'_, A, Th>,
    b1: Lit,
    b2: Lit,
) {
    if let Some(id1) = acts.lit.get_weak(b1) {
        if let Some(id2) = acts.lit.get_weak(b2) {
            let mut conflict = None;
            acts.egraph
                .union(id1, id2, Justification::NOOP, |lclass, rclass| {
                    match (lclass, rclass) {
                        (EClass::Th(lth), EClass::Th(rth)) => {
                            let lth = lth.downcast_mut().unwrap();
                            let rth = rth.downcast().unwrap();
                            let mut th = EmptyTheory;
                            let (iter, conf) = th.merge_classes(lth, rth, &mut acts.arg);
                            acts.history.extend(iter.map(SubExp::upcast));
                            conflict = conf;
                        }
                        (l, r) => unreachable!(
                            "invalid eclasses merge in unify lits {} {}",
                            l.to_display_exp(id1, acts.arg.intern()),
                            r.to_display_exp(id2, acts.arg.intern())
                        ),
                    }
                });
        } else {
            acts.lit.add_id_to_lit(id1, b2, true)
        }
    } else {
        let id = EmptyTheory.id_for_exp(acts, BoolExp::unknown(b2), true);
        acts.lit.add_id_to_lit(id, b1, true);
    }
}

fn propagate(acts: &mut impl SatTheoryArgT, lits: &[Lit], b: bool) {
    let lits = lits.iter().map(|l| *l ^ !b);
    debug!("EUF propagates {:?}", DebugIter(lits.clone()));
    for lit in lits {
        acts.propagate(lit);
    }
}
