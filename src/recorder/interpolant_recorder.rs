use crate::full_theory::FullTheory;
use crate::intern::{InternInfo, Symbol};
use crate::recorder::slice_vec::SliceVec;
use crate::recorder::{ClauseKind, LoggingRecorder, Recorder};
use crate::solver::LevelMarker;
use crate::util::{DebugIter, HashMap};
use crate::{Conjunction, ExpLike, Solver};
use alloc::vec::Vec;
use bytemuck::must_cast;
use core::fmt::{Debug, Formatter};
use log::{debug, trace};
use platsat::theory::ClauseRef;
use platsat::{lbool, Lit};

#[derive(Copy, Clone, Default, Eq, PartialEq, Debug)]
enum State {
    #[default]
    Solving,
    Proving,
    Final,
}

#[derive(Copy, Clone)]
struct ClauseProofElement {
    pivot: Lit,
    /// This represents a [`ClauseRef`] in [`State::Proving`] and an index in [`State::Final`]
    /// The indexes first index into `clause_proofs` and if they are more than `clause_proofs.len()`
    /// they instead index into `tseiten_clauses`, the proof of each index only depends on the
    /// proofs of larger indexes
    clause: u32,
}

impl ClauseProofElement {
    fn new(pivot: Lit, clause: ClauseRef) -> Self {
        ClauseProofElement {
            pivot,
            clause: must_cast(clause),
        }
    }

    fn clause_ref(&self) -> ClauseRef {
        must_cast(self.clause)
    }
}

impl Debug for ClauseProofElement {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(f, "{:?} (pivot {:?})", self.clause_ref(), self.pivot)
    }
}

#[derive(Default)]
pub struct InterpolantRecorder {
    state: State,
    clauses: SliceVec<Lit>,
    // maps clause refs to their proof index (see ClauseProofElement) or MAX if that hasn't been
    // resolved yet
    clause_refs: HashMap<ClauseRef, u32>,
    tseiten_clauses: Vec<ClauseRef>,
    clause_proofs: SliceVec<ClauseProofElement>,
}

impl InterpolantRecorder {
    fn start_new_clause_proof(&mut self, clause: ClauseRef) -> Option<()> {
        let r = self.clause_refs.get_mut(&clause)?;
        *r = self.clause_proofs.len() as u32;
        self.clause_proofs.push(&[]);
        Some(())
    }
}

impl Recorder for InterpolantRecorder {
    type Interpolant<'a> = ();

    fn log_def<Exp: ExpLike, Exp2: ExpLike>(
        &mut self,
        val: Exp,
        f: Symbol,
        arg: impl Iterator<Item = Exp2> + Clone,
        intern: &InternInfo,
    ) {
        LoggingRecorder.log_def(val, f, arg, intern)
    }

    fn log_def_exp<Exp: ExpLike, Exp2: ExpLike>(
        &mut self,
        val: Exp,
        def: Exp2,
        intern: &InternInfo,
    ) {
        LoggingRecorder.log_def_exp(val, def, intern)
    }

    fn log_alias<Exp: ExpLike>(&mut self, alias: Symbol, exp: Exp, intern: &InternInfo) {
        LoggingRecorder.log_alias(alias, exp, intern)
    }

    fn log_clause(&mut self, clause: &[Lit], kind: ClauseKind) {
        trace!("Adding clause {:?} {:?} in {:?}", clause, kind, self.state);
        match (self.state, kind) {
            (State::Solving, ClauseKind::Sat) => self.clauses.push(clause),
            _ => {}
        }
    }

    fn on_gc_start(&mut self) {
        if let State::Proving = self.state {
            unreachable!()
        }
    }

    fn on_final_lit_explanation(&mut self, lit: Lit, reason: ClauseRef) {
        if let State::Proving = self.state {
            if reason != ClauseRef::UNDEF {
                self.clause_proofs
                    .push_onto_last(ClauseProofElement::new(lit, reason));
                self.clause_refs.insert(reason, u32::MAX);
            }
        };
    }

    fn interpolant<'a, Th: FullTheory<Self>>(
        solver: &'a mut Solver<Th, Self>,
        pre_solve_marker: LevelMarker<Th::LevelMarker>,
        assumptions: &Conjunction,
    ) -> Option<Self::Interpolant<'a>> {
        if State::Final != solver.th.arg.recorder.state {
            solver.th.arg.recorder.state = State::Proving;
            solver.pop_model();
            // reset solver to before original solve
            solver.pop_to_level(pre_solve_marker.clone());
            let mut levels = Vec::with_capacity(solver.th.arg.recorder.clauses.len());
            solver.open(
                |_, acts| {
                    for &l in &assumptions.lits {
                        acts.sat.add_clause_unchecked([l]);
                    }
                },
                (),
            );
            for i in 0..solver.th.arg.recorder.clauses.len() {
                let level = solver.create_level();
                if !solver.is_ok() {
                    break;
                }
                levels.push(level);
                solver
                    .sat
                    .add_exact_clause(solver.th.arg.recorder.clauses[i].iter().copied());
            }

            // Add all learned clauses back to the solver

            // analyze final conflict
            solver.th.arg.recorder.clause_proofs.push(&[]);
            solver.simplify();
            solver.analyze_final_conflict();
            debug!(
                "final: {:?} by {:?}",
                DebugIter(&assumptions.lits.iter().map(|&x| !x)),
                solver
                    .th
                    .arg
                    .recorder
                    .clause_proofs
                    .iter()
                    .next_back()
                    .unwrap()
            );

            // analyze each learned clause
            for (i, level) in levels.into_iter().enumerate().rev() {
                let _ = analyze_clause(solver, i, level);
            }

            solver.pop_to_level(pre_solve_marker);
            solver.open(
                |_, acts| {
                    let recorder = &mut acts.incr.recorder;
                    let sat = &acts.sat;
                    for (k, v) in &mut recorder.clause_refs {
                        if *v == u32::MAX {
                            *v = (recorder.tseiten_clauses.len() + recorder.clause_proofs.len())
                                as u32;
                            recorder.tseiten_clauses.push(*k);
                            debug!("{k:?}: {:?} by tseiten", sat.resolve_clause_ref(*k))
                        }
                    }
                    for proof_elt in recorder.clause_proofs.iter_mut().flatten() {
                        proof_elt.clause =
                            *recorder.clause_refs.get(&proof_elt.clause_ref()).unwrap();
                    }
                    recorder.state = State::Final;
                },
                (),
            );
        };
        // create interpolant
        None
    }
}

fn analyze_clause<Th: FullTheory<InterpolantRecorder>>(
    solver: &mut Solver<Th, InterpolantRecorder>,
    i: usize,
    level_before: LevelMarker<Th::LevelMarker>,
) -> Option<()> {
    let cr = solver.clauses().last().unwrap();
    solver.th.arg.recorder.start_new_clause_proof(cr)?;
    solver.pop_to_level(level_before);
    solver.open(
        |_, acts| {
            for l in acts.incr.recorder.clauses[i].iter().copied() {
                let l = !l;
                if acts.sat.value_lit(l) == lbool::UNDEF {
                    acts.sat.add_clause_unchecked([l]);
                } else {
                    debug_assert_eq!(acts.sat.value_lit(l), lbool::TRUE)
                }
            }
        },
        (),
    );
    solver.simplify();
    solver.analyze_final_conflict();
    let c = &solver.th.arg.recorder.clauses[i];
    let proof = solver
        .th
        .arg
        .recorder
        .clause_proofs
        .iter()
        .next_back()
        .unwrap();
    debug!("{cr:?}: {c:?} by {proof:?}");
    Some(())
}
