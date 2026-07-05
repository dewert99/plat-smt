use crate::collapse::{BaseMarker, LeftMarker, RightMarker};
use crate::full_theory::FullTheory;
use crate::junction::Junction;
use crate::solver::SolverWithBound;
use crate::Solver;

pub trait ReuseMem<T, M = BaseMarker> {
    fn reuse_mem(&mut self) -> T;
}

pub struct Lift<T>(T);
impl<T, M, Th: FullTheory<R> + ReuseMem<T, M>, R> ReuseMem<T, Lift<M>> for Solver<Th, R> {
    fn reuse_mem(&mut self) -> T {
        self.th.reuse_mem()
    }
}

impl<T, M, Th: ReuseMem<T, M>, O> ReuseMem<T, LeftMarker<M>> for (Th, O) {
    fn reuse_mem(&mut self) -> T {
        self.0.reuse_mem()
    }
}

impl<T, M, Th: ReuseMem<T, M>, O> ReuseMem<T, RightMarker<M>> for (O, Th) {
    fn reuse_mem(&mut self) -> T {
        self.1.reuse_mem()
    }
}

impl<Th: FullTheory<R>, R, const B: bool> ReuseMem<Junction<B>> for Solver<Th, R> {
    fn reuse_mem(&mut self) -> Junction<B> {
        self.th.new_junction()
    }
}

impl<T, M, S: ReuseMem<T, M>, B> ReuseMem<T, M> for SolverWithBound<S, B> {
    fn reuse_mem(&mut self) -> T {
        self.solver.reuse_mem()
    }
}
