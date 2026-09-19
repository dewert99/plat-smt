use crate::collapse::BaseMarker;
use crate::empty_theory::EmptyTheory;
use crate::euf::UExp;
use crate::euf::egraph::EClassT;
use crate::euf::euf::{LitVec, id_for_bool};
use crate::intern::{DisplayInterned, InternInfo};
use crate::recorder::Recorder;
use crate::theory::{Incremental, NeverTheoryArg};
use crate::tseitin::SatTheoryArgT;
use crate::util::DebugIter;
use crate::{BoolExp, EitherExp, ExpLike, SubExp, SuperExp};
use core::fmt::{Display, Formatter};
use log::debug;
use plat_egg::Id;
use platsat::Lit;
use std::{fmt, iter, mem};

pub trait EufTheoryArgT: SatTheoryArgT {
    type Exp;
    fn resolve(&self, id: Id) -> Option<Self::Exp>;

    fn union(&mut self, id0: Id, id1: Id) -> Result<(), ()>;
}

impl<M, R: Recorder, Exp, E> EufTheoryArgT for NeverTheoryArg<M, R, (Exp, E)> {
    type Exp = Exp;

    fn resolve(&self, _: Id) -> Option<Self::Exp> {
        self.diverge()
    }

    fn union(&mut self, _: Id, _: Id) -> Result<(), ()> {
        self.diverge()
    }
}

pub trait EufTh: Incremental {
    type EClass: EClassT;

    type Exp: ExpLike;

    fn eclass_to_exp(&self, c: &Self::EClass) -> EitherExp<Self::Exp, UExp>;

    fn display_eclass(
        &self,
        c: &Self::EClass,
        f: &mut Formatter,
        intern: &InternInfo,
    ) -> fmt::Result {
        self.eclass_to_exp(c).fmt(intern, f)
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
}

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

impl EufTh for EmptyTheory {
    type EClass = BoolClass;

    type Exp = BoolExp;

    fn eclass_to_exp(&self, b: &Self::EClass) -> EitherExp<Self::Exp, UExp> {
        b.to_exp().upcast()
    }
    fn display_eclass(&self, c: &Self::EClass, f: &mut Formatter, _: &InternInfo) -> fmt::Result {
        match c {
            BoolClass::Const(b) => Display::fmt(b, f),
            BoolClass::Unknown(l) if l.len() > 0 => Display::fmt(&BoolExp::unknown(l[0]), f),
            BoolClass::Unknown(_) => f.write_str("(as _ Bool)"),
        }
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
}

fn propagate(acts: &mut impl SatTheoryArgT, lits: &[Lit], b: bool) {
    let lits = lits.iter().map(|l| *l ^ !b);
    debug!("EUF propagates {:?}", DebugIter(lits.clone()));
    for lit in lits {
        acts.propagate(lit);
    }
}

pub trait FullEufTh:
    EufTh<Exp: SuperExp<BoolExp, Self::BoolMarker>, EClass: SuperExp<BoolClass, Self::BoolMarker>>
{
    type BoolMarker;
}

impl FullEufTh for EmptyTheory {
    type BoolMarker = BaseMarker;
}
