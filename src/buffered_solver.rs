use no_std_compat::prelude::v1::*;
use platsat::{Lit, SolverInterface};
use std::ops::{Deref, DerefMut};

#[derive(Default)]
pub struct BufferedSolver<S> {
    solver: S,
    buffer: Vec<Lit>,
}

impl<S> Deref for BufferedSolver<S> {
    type Target = S;

    fn deref(&self) -> &Self::Target {
        &self.solver
    }
}

impl<S> DerefMut for BufferedSolver<S> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.solver
    }
}

impl<S: SolverInterface> BufferedSolver<S> {
    pub fn add_clause(&mut self, clause: impl IntoIterator<Item = Lit>) {
        self.buffer.clear();
        self.buffer.extend(clause);
        self.buffer
            .extend(self.solver.assumptions().last().map(|x| !*x));
        self.solver.add_clause_reuse(&mut self.buffer);
    }
}
