use crate::full_theory::FullTheory;
use crate::intern::{InternInfo, Symbol, AND_SYM, OR_SYM};
use crate::recorder::definition_recorder::{
    DefExp, DefinitionRecorder, DisplayStandAloneDefExp, FALSE_DEF_EXP, TRUE_DEF_EXP,
};
use crate::recorder::slice_vec::SliceVec;
use crate::recorder::{ClauseKind, Recorder};
use crate::solver::LevelMarker as SolverMarker;
use crate::theory::Incremental;
use crate::util::{display_sexp, DebugIter, DisplayFn, HashMap};
use crate::{BoolExp, Conjunction, ExpLike, Solver};
use alloc::vec::Vec;
use bytemuck::must_cast;
use core::fmt::Debug;
use default_vec2::BitSet;
use log::{debug, info, trace};
use platsat::theory::ClauseRef;
use platsat::{lbool, Lit, SolverInterface, TheoryArg};

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

#[derive(Copy, Clone)]
pub struct LevelMarker {
    def_marker: <DefinitionRecorder as Incremental>::LevelMarker,
    clause_len: u32,
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
    defs: DefinitionRecorder,
    lit_buf: Vec<Lit>,
    a_only_defs: BitSet<DefExp>,
    visited: BitSet<DefExp>,
    def_stack: Vec<DefExp>,
}

#[derive(Copy, Clone)]
enum ClauseProofResolveState {
    True,
    False,
    Single,
    And,
    Or,
}

impl ClauseProofResolveState {
    fn init(def: DefExp, stack: &mut Vec<DefExp>) -> ClauseProofResolveState {
        if def == TRUE_DEF_EXP {
            ClauseProofResolveState::True
        } else if def == FALSE_DEF_EXP {
            ClauseProofResolveState::False
        } else {
            stack.push(def);
            ClauseProofResolveState::Single
        }
    }

    fn add_on(
        &mut self,
        def: DefExp,
        is_and: bool,
        stack: &mut Vec<DefExp>,
        defs: &mut DefinitionRecorder,
        stack_len: usize,
    ) {
        match (*self, is_and) {
            (ClauseProofResolveState::True, false) | (ClauseProofResolveState::False, true) => {}
            (_, false) if def == TRUE_DEF_EXP => {
                stack.truncate(stack_len);
                *self = ClauseProofResolveState::True;
            }
            (_, true) if def == FALSE_DEF_EXP => {
                stack.truncate(stack_len);
                *self = ClauseProofResolveState::False;
            }
            (_, false) if def == FALSE_DEF_EXP => {}
            (_, true) if def == TRUE_DEF_EXP => {}
            (ClauseProofResolveState::True, true) | (ClauseProofResolveState::False, false) => {
                stack.push(def);
                *self = ClauseProofResolveState::Single;
            }
            (ClauseProofResolveState::Single, _) => {
                stack.push(def);
                *self = if is_and {
                    ClauseProofResolveState::And
                } else {
                    ClauseProofResolveState::Or
                };
            }
            (ClauseProofResolveState::And, true) | (ClauseProofResolveState::Or, false) => {
                stack.push(def);
            }
            (ClauseProofResolveState::And, false) | (ClauseProofResolveState::Or, true) => {
                let old_op = if is_and { OR_SYM } else { AND_SYM };
                let children = &stack[stack_len..];
                let combined = defs.intern_call(old_op, children);
                stack.truncate(stack_len);
                stack.push(combined);
                stack.push(def);
                *self = if is_and {
                    ClauseProofResolveState::And
                } else {
                    ClauseProofResolveState::Or
                };
            }
        }
        debug_assert!(match *self {
            ClauseProofResolveState::True | ClauseProofResolveState::False =>
                stack.len() == stack_len,
            ClauseProofResolveState::Single => stack.len() == stack_len + 1,
            ClauseProofResolveState::And | ClauseProofResolveState::Or =>
                stack.len() > stack_len + 1,
        });
    }

    fn finish(
        self,
        stack: &mut Vec<DefExp>,
        defs: &mut DefinitionRecorder,
        stack_len: usize,
    ) -> DefExp {
        match self {
            ClauseProofResolveState::True => TRUE_DEF_EXP,
            ClauseProofResolveState::False => FALSE_DEF_EXP,
            ClauseProofResolveState::Single => stack.pop().unwrap(),
            ClauseProofResolveState::And | ClauseProofResolveState::Or => {
                let old_op = match self {
                    ClauseProofResolveState::And => AND_SYM,
                    _ => OR_SYM,
                };
                let children = &stack[stack_len..];
                let combined = defs.intern_call(old_op, children);
                stack.truncate(stack_len);
                combined
            }
        }
    }
}

impl InterpolantRecorder {
    fn start_new_clause_proof(&mut self, clause: ClauseRef) -> Option<()> {
        let r = self.clause_refs.get_mut(&clause)?;
        *r = self.clause_proofs.len() as u32;
        self.clause_proofs.push(&[]);
        Some(())
    }

    fn display_last_proof<'a>(&'a self, intern: &'a InternInfo) -> impl Debug + use<'a> {
        let proof = self.clause_proofs.iter().last().unwrap();
        DebugIter(proof.iter().map(move |x| {
            DisplayFn(|f| {
                if x.pivot != Lit::UNDEF {
                    write!(
                        f,
                        "{:?} (pivot {})",
                        x.clause_ref(),
                        self.defs.display_exp(BoolExp::unknown(x.pivot), intern)
                    )
                } else {
                    Debug::fmt(&x.clause_ref(), f)
                }
            })
        }))
    }

    fn set_def_exps_in_a(&mut self, (start, end): (usize, usize), in_a: bool, intern: &InternInfo) {
        self.def_stack.clear();
        self.visited.clear();
        self.def_stack.extend(
            self.lit_buf[start..end]
                .iter()
                .map(|l| self.defs.intern_exp(l.var())),
        );
        while let Some(x) = self.def_stack.pop() {
            if !self.visited.contains_mut(x) {
                trace!(
                    "setting {} in a to be {}",
                    self.defs.display_def(x, intern),
                    in_a
                );
                self.visited.set(x, true);
                self.a_only_defs.set(x, in_a);
                self.def_stack.extend_from_slice(self.defs.resolve(x).1)
            }
        }
    }

    fn find_interpolant(&mut self, sat: &TheoryArg, intern: &InternInfo) -> DefExp {
        self.def_stack.clear();
        let max_idx = self.tseiten_clauses.len() + self.clause_proofs.len() - 1;
        for tseiten in self.tseiten_clauses.iter().rev() {
            let tseiten = sat.resolve_clause_ref(*tseiten);
            let def_len = self.def_stack.len();
            for &l in tseiten {
                if !self.a_only_defs.contains(self.defs.intern_exp(l.var())) {
                    self.def_stack
                        .push(self.defs.intern_exp(BoolExp::unknown(l)));
                }
            }
            let added = &self.def_stack[def_len..];
            let partial_interpolant = if added.len() == tseiten.len() {
                TRUE_DEF_EXP
            } else if let &[] = added {
                FALSE_DEF_EXP
            } else if let &[l] = added {
                l
            } else {
                self.defs.intern_call(OR_SYM, added)
            };
            self.def_stack.truncate(def_len);
            self.def_stack.push(partial_interpolant);
        }
        for proof in self.clause_proofs.iter().rev() {
            let def_len = self.def_stack.len();
            let (first, rest) = proof.split_first().unwrap();
            let def = self.def_stack[max_idx - first.clause as usize];
            let mut state = ClauseProofResolveState::init(def, &mut self.def_stack);
            for elt in rest {
                let pivot_def = self.defs.intern_exp(elt.pivot.var());
                let is_and = !self.a_only_defs.contains(pivot_def);
                let def = self.def_stack[max_idx - elt.clause as usize];
                state.add_on(def, is_and, &mut self.def_stack, &mut self.defs, def_len);
            }
            let res = state.finish(&mut self.def_stack, &mut self.defs, def_len);
            debug_assert_eq!(self.def_stack.len(), def_len);
            self.def_stack.push(res);
        }
        debug!(
            "partial interpolants: {}",
            display_sexp(
                "",
                self.def_stack
                    .iter()
                    .map(|&d| self.defs.display_def(d, intern))
            )
        );
        self.def_stack.pop().unwrap()
    }
}

impl Incremental for InterpolantRecorder {
    type LevelMarker = LevelMarker;

    fn create_level(&self) -> Self::LevelMarker {
        LevelMarker {
            def_marker: self.defs.create_level(),
            clause_len: self.clauses.len_idx() as u32,
        }
    }

    fn pop_to_level(&mut self, marker: Self::LevelMarker, clear_lits: bool) {
        match self.state {
            State::Solving => {
                self.defs.pop_to_level(marker.def_marker, clear_lits);
                self.clauses.truncate(marker.clause_len as usize);
            }
            _ => {}
        }
    }

    fn clear(&mut self) {
        debug_assert!(matches!(self.state, State::Solving));
        self.defs.clear();
        self.clauses.clear();
    }
}

impl Recorder for InterpolantRecorder {
    type Interpolant<'a> = DisplayStandAloneDefExp<'a>;

    fn log_def<Exp: ExpLike, Exp2: ExpLike>(
        &mut self,
        val: Exp,
        f: Symbol,
        arg: impl Iterator<Item = Exp2> + Clone,
        intern: &InternInfo,
    ) {
        self.defs.log_def(val, f, arg, intern)
    }

    fn log_def_exp<Exp: ExpLike, Exp2: ExpLike>(
        &mut self,
        val: Exp,
        def: Exp2,
        intern: &InternInfo,
    ) {
        self.defs.log_def_exp(val, def, intern);
    }

    fn log_alias<Exp: ExpLike>(&mut self, alias: Symbol, exp: Exp, intern: &InternInfo) {
        self.defs.log_alias(alias, exp, intern)
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

    type BoolBufMarker = (usize, usize);

    fn intern_bools(&mut self, bools: impl Iterator<Item = BoolExp>) -> Self::BoolBufMarker {
        let start_len = self.lit_buf.len();
        self.lit_buf.extend(bools.filter_map(|x| x.to_lit().ok()));
        (start_len, self.lit_buf.len())
    }

    fn interpolant<'a, Th: FullTheory<Self>>(
        solver: &'a mut Solver<Th, Self>,
        pre_solve_marker: SolverMarker<Th::LevelMarker, LevelMarker>,
        assumptions: &Conjunction,
        a: Self::BoolBufMarker,
        b: Self::BoolBufMarker,
    ) -> Option<Self::Interpolant<'a>> {
        if State::Final != solver.th.arg.recorder.state {
            solver.th.arg.recorder.state = State::Proving;
            solver.sat.pop_model(&mut solver.th);
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
            info!(
                "\n{}",
                solver
                    .th
                    .arg
                    .recorder
                    .defs
                    .dump_global_defs(&solver.th.arg.intern)
            );
            info!(
                "final: {} by {:?}",
                solver
                    .th
                    .arg
                    .recorder
                    .defs
                    .display_clause(assumptions.lits.iter().map(|&x| !x), solver.intern()),
                solver.th.arg.recorder.display_last_proof(solver.intern())
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
                            let c = sat.resolve_clause_ref(*k);
                            info!(
                                "{k:?}: {} by tseiten",
                                recorder
                                    .defs
                                    .display_clause(c.iter().copied(), &acts.incr.intern)
                            );
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
        solver.th.arg.recorder.a_only_defs.clear();
        solver
            .th
            .arg
            .recorder
            .set_def_exps_in_a(a, true, &solver.th.arg.intern);
        solver
            .th
            .arg
            .recorder
            .set_def_exps_in_a(b, false, &solver.th.arg.intern);
        let res = solver.open(
            |_, arg| {
                arg.incr
                    .recorder
                    .find_interpolant(&arg.sat, &arg.incr.intern)
            },
            FALSE_DEF_EXP,
        );
        Some(
            solver
                .th
                .arg
                .recorder
                .defs
                .display_stand_alone_def(res, &solver.th.arg.intern),
        )
    }

    fn exit_solved_state(&mut self) {
        self.state = State::Solving;
        self.tseiten_clauses.clear();
        self.clause_proofs.clear();
    }
}

fn analyze_clause<Th: FullTheory<InterpolantRecorder>>(
    solver: &mut Solver<Th, InterpolantRecorder>,
    i: usize,
    level_before: SolverMarker<Th::LevelMarker, LevelMarker>,
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
    let proof = solver.th.arg.recorder.display_last_proof(solver.intern());
    info!(
        "{cr:?}: {} by {proof:?}",
        solver
            .th
            .arg
            .recorder
            .defs
            .display_clause(c.iter().copied(), solver.intern())
    );
    Some(())
}
