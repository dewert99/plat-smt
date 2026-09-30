use crate::collapse::{AppendLeftMarker, AppendRightMarker, BaseMarker, ExprContext, MarkerAppend};
use crate::empty_theory::EmptyTheory;
use crate::euf::UExp;
use crate::euf::bool_euf_th::{BoolClass, MergeInfo};
use crate::euf::egraph::{Children, EClassT, EGraph};
use crate::euf::euf::{EClass, LitInfo};
use crate::intern::{DisplayInterned, InternInfo};
use crate::recorder::Recorder;
use crate::rexp::AsRexp;
use crate::theory::ambassador_impl_TheoryArgT;
use crate::theory::{Incremental, NeverTheoryArg, Reborrow, TheoryArgT};
use crate::tseitin::{SatExplainTheoryArgT, SatTheoryArgT};
use crate::tseitin::{SatTheoryArgR, ambassador_impl_SatExplainTheoryArgT};
use crate::util::{Either, InfallibleIter};
use crate::{BoolExp, EitherExp, ExpLike, SubExp, SuperExp};
use crate::{HasSort, Sort, Symbol};
use alloc::vec::Vec;
use ambassador::Delegate;
use core::fmt::{Debug, Formatter};
use plat_egg::Id;
use platsat::{Lit, TheoryArg as SatTheoryArg};
use std::fmt;

pub trait EufTheoryArgT<M, C>: SatTheoryArgT {
    fn resolve(&self, id: Id) -> Option<&C>;

    fn union(&mut self, id0: Id, id1: Id);

    fn add(&mut self, s: Symbol, class: impl FnOnce() -> C) -> Id;
}

#[derive(Delegate)]
#[delegate(TheoryArgT, target = "arg")]
#[delegate(SatExplainTheoryArgT, target = "arg")]
pub struct EufTheoryArg<'a, A, Th: EufThBase> {
    pub(super) arg: A,
    pub(super) egraph: &'a mut EGraph<EClass<Th>>,
    pub(super) history: &'a mut Vec<<Th::EClass as EClassT>::MergeInfo>,
    pub(super) lit: &'a mut LitInfo,
}

impl<'a, A: Reborrow, Th: EufThBase> Reborrow for EufTheoryArg<'a, A, Th> {
    type Target<'b>
        = EufTheoryArg<'b, A::Target<'b>, Th>
    where
        Self: 'b;

    fn reborrow(&mut self) -> Self::Target<'_> {
        EufTheoryArg {
            arg: self.arg.reborrow(),
            egraph: &mut *self.egraph,
            lit: &mut self.lit,
            history: &mut *self.history,
        }
    }
}

impl<'a, A: SatTheoryArgT, Th: EufThBase> SatTheoryArgT for EufTheoryArg<'a, A, Th> {
    type Explain<'b>
        = EufTheoryArg<'b, A::Explain<'b>, Th>
    where
        Self: 'b;

    fn sat_mut(&mut self) -> (SatTheoryArg<'_>, &mut Self::R) {
        self.arg.sat_mut()
    }

    fn sat(&self) -> &SatTheoryArg<'_> {
        self.arg.sat()
    }

    fn in_model(&self) -> bool {
        self.arg.in_model()
    }

    fn for_explain(&mut self) -> Self::Explain<'_> {
        EufTheoryArg {
            arg: self.arg.for_explain(),
            egraph: &mut *self.egraph,
            lit: &mut *self.lit,
            history: &mut *self.history,
        }
    }
}

impl<'a, A: SatTheoryArgT, Th: EufThBase, M, C: SubExp<Th::EClass, M>> EufTheoryArgT<M, C>
    for EufTheoryArg<'a, A, Th>
{
    fn resolve(&self, id: Id) -> Option<&C> {
        match &*self.egraph[id] {
            EClass::Th(x) => C::from_downcast_ref(x),
            _ => None,
        }
    }

    fn union(&mut self, id0: Id, id1: Id) {
        self.egraph
            .union(id0, id1, todo!(), |c0, c1| match (c0, c1) {
                (EClass::Th(c0), EClass::Th(c1)) => self
                    .history
                    .extend(Th::merge_classes_in_theory_union(c0, c1, &mut self.arg)),
                (EClass::Uninterpreted(s0), EClass::Uninterpreted(s1)) if *s0 == s1 => {}
                (l, r) => unreachable!(
                    "merging eclasses with different sorts {} {}",
                    l.to_display_exp(id0, self.arg.intern()),
                    r.to_display_exp(id1, self.arg.intern())
                ),
            })
    }

    fn add(&mut self, s: Symbol, class: impl FnOnce() -> C) -> Id {
        self.egraph.add(s.into(), Children::new(), |_, _| {
            EClass::Th(class().upcast())
        })
    }
}

impl<M, R: Recorder, E, M2, C> EufTheoryArgT<M2, C> for NeverTheoryArg<M, R, E> {
    fn resolve(&self, _: Id) -> Option<&C> {
        self.diverge()
    }

    fn union(&mut self, _: Id, _: Id) {
        self.diverge()
    }

    fn add(&mut self, _: Symbol, _: impl FnOnce() -> C) -> Id {
        self.diverge()
    }
}

pub trait EufThBase: Incremental {
    type EClass: EClassT + DisplayInterned;

    type Exp: ExpLike;

    fn eclass_to_exp(&self, c: &Self::EClass) -> EitherExp<Self::Exp, UExp>;

    fn display_eclass(c: &Self::EClass, f: &mut Formatter, _: &InternInfo) -> fmt::Result {
        Debug::fmt(c, f)
    }

    fn merge_classes(
        &mut self,
        l: &mut Self::EClass,
        r: Self::EClass,
        acts: &mut impl SatTheoryArgT,
    ) -> (
        impl Iterator<Item = <Self::EClass as EClassT>::MergeInfo>,
        Option<[Id; 2]>,
    );

    fn merge_classes_in_theory_union(
        l: &mut Self::EClass,
        r: Self::EClass,
        acts: &mut impl SatTheoryArgT,
    ) -> impl Iterator<Item = <Self::EClass as EClassT>::MergeInfo> {
        #[expect(unreachable_code)]
        InfallibleIter::new(panic!(
            "Unioning {} and {:?} is unsupported",
            l.ref_with_intern(acts.intern()),
            r.with_intern(acts.intern())
        ))
    }

    #[doc(hidden)]
    fn create_fresh_class_for_empty_theory(
        &mut self,
        acts: &mut impl SatTheoryArgT,
        target_sort: Sort,
        ctx: ExprContext<Self::Exp>,
        id: Id,
        _add_id_to_lit: impl FnOnce(Lit, Id) -> (),
    ) -> Self::EClass {
        self.create_fresh_class(acts, target_sort, ctx, id)
    }

    fn create_fresh_class(
        &mut self,
        acts: &mut impl SatTheoryArgT,
        target_sort: Sort,
        ctx: ExprContext<Self::Exp>,
        id: Id,
    ) -> Self::EClass;
}

pub trait EufTh<M, Arg>: EufThBase {
    fn id_for_exp(&mut self, acts: &mut Arg, e: Self::Exp, weak: bool) -> Id;

    fn id_for_eq_exp(&mut self, acts: &mut Arg, e: Self::Exp, _id: Id) -> Option<Id> {
        Some(self.id_for_exp(acts, e, true))
    }

    fn assert_exp_eq(&mut self, acts: &mut Arg, e1: Self::Exp, e2: Self::Exp);
}

pub trait FullEufTh<A: SatTheoryArgR>:
    EufThBase<
        Exp: SuperExp<BoolExp, Self::BoolMarker>,
        EClass: SuperExp<BoolClass, Self::BoolMarker>
                    + EClassT<MergeInfo: SuperExp<MergeInfo, Self::BoolMarker>>,
    > + for<'a> EufTh<BaseMarker, EufTheoryArg<'a, A::Target<'a>, Self>>
{
    type BoolMarker;
}

impl<A: SatTheoryArgR> FullEufTh<A> for EmptyTheory {
    type BoolMarker = BaseMarker;
}

pub trait ParentEufTh<Th: EufThBase, M>:
    EufThBase<
        Exp: SuperExp<Th::Exp, M>,
        EClass: SuperExp<Th::EClass, M>
                    + EClassT<MergeInfo: SuperExp<<Th::EClass as EClassT>::MergeInfo, M>>,
    >
{
}

impl<
    Th: EufThBase,
    M,
    T: EufThBase<
            Exp: SuperExp<Th::Exp, M>,
            EClass: SuperExp<Th::EClass, M>
                        + EClassT<MergeInfo: SuperExp<<Th::EClass as EClassT>::MergeInfo, M>>,
        >,
> ParentEufTh<Th, M> for T
{
}

impl<C1: EClassT, C2: EClassT> EClassT for EitherExp<C1, C2> {
    type MergeInfo = EitherExp<C1::MergeInfo, C2::MergeInfo>;

    fn split(&mut self, info: impl Iterator<Item = Self::MergeInfo>) -> Self {
        match self {
            EitherExp::Left(l) => EitherExp::Left(l.split(info.map(|x| x.downcast().unwrap()))),
            EitherExp::Right(r) => EitherExp::Right(r.split(info.map(|x| x.downcast().unwrap()))),
        }
    }
}

impl<Th1: EufThBase, Th2: EufThBase> EufThBase for (Th1, Th2) {
    type Exp = EitherExp<Th1::Exp, Th2::Exp>;

    type EClass = EitherExp<Th1::EClass, Th2::EClass>;

    fn eclass_to_exp(&self, c: &Self::EClass) -> EitherExp<Self::Exp, UExp> {
        match c {
            EitherExp::Left(c) => match self.0.eclass_to_exp(c) {
                EitherExp::Left(e) => EitherExp::Left(EitherExp::Left(e)),
                EitherExp::Right(e) => EitherExp::Right(e),
            },
            EitherExp::Right(c) => match self.1.eclass_to_exp(c) {
                EitherExp::Left(e) => EitherExp::Left(EitherExp::Right(e)),
                EitherExp::Right(e) => EitherExp::Right(e),
            },
        }
    }

    fn merge_classes(
        &mut self,
        l: &mut Self::EClass,
        r: Self::EClass,
        acts: &mut impl SatTheoryArgT,
    ) -> (
        impl Iterator<Item = <Self::EClass as EClassT>::MergeInfo>,
        Option<[Id; 2]>,
    ) {
        match (l, r) {
            (EitherExp::Left(l), EitherExp::Left(r)) => {
                let (iter, conf) = self.0.merge_classes(l, r, acts);
                (Either::Left(iter.map(EitherExp::Left)), conf)
            }
            (EitherExp::Right(l), EitherExp::Right(r)) => {
                let (iter, conf) = self.1.merge_classes(l, r, acts);
                (Either::Right(iter.map(EitherExp::Right)), conf)
            }
            (l, r) => panic!(
                "Unioning {} and {:?} is unsupported",
                l.ref_with_intern(acts.intern()),
                r.with_intern(acts.intern())
            ),
        }
    }

    fn merge_classes_in_theory_union(
        l: &mut Self::EClass,
        r: Self::EClass,
        acts: &mut impl SatTheoryArgT,
    ) -> impl Iterator<Item = <Self::EClass as EClassT>::MergeInfo> {
        match (l, r) {
            (EitherExp::Left(l), EitherExp::Left(r)) => {
                let iter = Th1::merge_classes_in_theory_union(l, r, acts);
                Either::Left(iter.map(EitherExp::Left))
            }
            (EitherExp::Right(l), EitherExp::Right(r)) => {
                let iter = Th2::merge_classes_in_theory_union(l, r, acts);
                Either::Right(iter.map(EitherExp::Right))
            }
            (l, r) => panic!(
                "Unioning {} and {:?} is unsupported",
                l.ref_with_intern(acts.intern()),
                r.with_intern(acts.intern())
            ),
        }
    }

    fn create_fresh_class_for_empty_theory(
        &mut self,
        acts: &mut impl SatTheoryArgT,
        target_sort: Sort,
        ctx: ExprContext<Self::Exp>,
        id: Id,
        add_id_to_lit: impl FnOnce(Lit, Id) -> (),
    ) -> Self::EClass {
        if Th1::Exp::can_have_sort(target_sort) {
            EitherExp::Left(self.0.create_fresh_class_for_empty_theory(
                acts,
                target_sort,
                ctx.downcast(),
                id,
                add_id_to_lit,
            ))
        } else {
            EitherExp::Right(self.1.create_fresh_class_for_empty_theory(
                acts,
                target_sort,
                ctx.downcast(),
                id,
                add_id_to_lit,
            ))
        }
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

impl<
    M: MarkerAppend,
    A: SatTheoryArgT,
    Th1: EufTh<AppendLeftMarker<M>, A>,
    Th2: EufTh<AppendRightMarker<M>, A>,
> EufTh<M, A> for (Th1, Th2)
{
    fn id_for_exp(&mut self, acts: &mut A, e: Self::Exp, weak: bool) -> Id {
        match e {
            EitherExp::Left(e) => self.0.id_for_exp(acts, e, weak),
            EitherExp::Right(e) => self.1.id_for_exp(acts, e, weak),
        }
    }

    fn id_for_eq_exp(&mut self, acts: &mut A, e: Self::Exp, id: Id) -> Option<Id> {
        match e {
            EitherExp::Left(e) => self.0.id_for_eq_exp(acts, e, id),
            EitherExp::Right(e) => self.1.id_for_eq_exp(acts, e, id),
        }
    }

    fn assert_exp_eq(&mut self, acts: &mut A, e1: Self::Exp, e2: Self::Exp) {
        match (e1, e2) {
            (EitherExp::Left(e1), EitherExp::Left(e2)) => self.0.assert_exp_eq(acts, e1, e2),
            (EitherExp::Right(e1), EitherExp::Right(e2)) => self.1.assert_exp_eq(acts, e1, e2),
            (e1, e2) => panic!(
                "Unioning {} and {:?} is unsupported",
                e1.with_intern(acts.intern()),
                e2.with_intern(acts.intern())
            ),
        }
    }
}
