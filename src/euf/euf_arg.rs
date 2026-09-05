use crate::recorder::Recorder;
use crate::theory::NeverTheoryArg;
use crate::tseitin::SatTheoryArgT;
use plat_egg::Id;

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
