use crate::full_theory::FullTheory;
use crate::intern::{InternInfo, Symbol, AND_SYM, EQ_SYM, NOT_SYM, OR_SYM};
use crate::recorder::definition_recorder::{
    DefExp, DefinitionRecorder, DisplayStandAloneDefExp, FALSE_DEF_EXP, TRUE_DEF_EXP,
};
use crate::recorder::slice_vec::SliceVec;
use crate::recorder::{ClauseKind, Recorder};
use crate::rexp::{AsRexp, NamespaceVar};
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

#[derive(Copy, Clone, Debug)]
struct ClauseProofElement {
    pivot: Lit,
    /// Represents a [`ClauseRef`] in [`State::Proving`], and an index in [`State::Final`].
    /// The indexes index into `clause_proofs ++ tseiten_clauses ++ clauses[clause_boundary..]`
    /// Where `clause_proofs` represent clauses produced by resolution, `tseiten_clause` represent
    /// clauses produce by the tseiten transformation, and `clauses[clause_boundary..]` represent
    /// theory lemmas
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
    // Cleared in `clear`
    /// Stores clauses found during search before clause boundary, and theory clauses after
    /// clause_boundary
    clauses: SliceVec<Lit>,
    defs: DefinitionRecorder,
    // Cleared in `exit_solved_state`
    tseiten_clauses: Vec<ClauseRef>,
    clause_proofs: SliceVec<ClauseProofElement>,
    lit_buf: Vec<Lit>,
    clause_boundary: usize,
    /// Maps clause refs to their proof index (see ClauseProofElement) or MAX if it was not
    /// resolved yet.
    clause_refs: HashMap<ClauseRef, u32>,
    // Cleared at the start of `find_interpolant`
    a_only_defs: BitSet<DefExp>,
    def_stack: Vec<DefExp>,
    // cleared and only used in `set_def_exps_in_a`
    visited: BitSet<DefExp>,
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

    fn tseiten_partial_interpolate(&mut self, sat: &TheoryArg) {
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
    }

    fn resolution_partial_interpolate(&mut self) {
        let theory_clauses = self.clauses.len() - self.clause_boundary;
        let max_idx = self.tseiten_clauses.len() + self.clause_proofs.len() + theory_clauses - 1;
        for proof in self.clause_proofs.iter().rev() {
            let (first, rest) = proof.split_first().unwrap();
            let def = self.def_stack[max_idx - first.clause as usize];
            let def_stack_len = self.def_stack.len();
            let mut interp = InterpolateArg {
                a_only: &self.a_only_defs,
                defs: &mut self.defs,
                def_stack: &mut self.def_stack,
                def_stack_len,
            };
            interp.add_def(def);
            let mut is_and = true;
            for elt in rest {
                let pivot_def = interp.intern_exp(elt.pivot.var());
                let def_is_and = !interp.a_only.contains(pivot_def);
                let def = interp.def_stack[max_idx - elt.clause as usize];
                if def_is_and != is_and {
                    let so_far = interp.finish(if is_and { AND_SYM } else { OR_SYM });
                    interp.add_def(so_far);
                    is_and = def_is_and;
                }
                interp.add_def(def);
            }
            let res = interp.finish(if is_and { AND_SYM } else { OR_SYM });
            drop(interp);
            self.def_stack.push(res);
        }
    }

    fn initialize_tseiten_clauses(&mut self, sat: &TheoryArg, intern: &InternInfo) {
        let clause_proofs = self.clause_proofs.len();
        for (k, v) in &mut self.clause_refs {
            if *v == u32::MAX && *k != ClauseRef::SPECIAL {
                *v = (self.tseiten_clauses.len() + clause_proofs) as u32;
                self.tseiten_clauses.push(*k);
                let c = sat.resolve_clause_ref(*k);
                info!(
                    "{k:?}: {} by tseiten",
                    self.defs.display_clause(c.iter().copied(), intern)
                );
            }
        }
    }

    fn finalize_clause_proofs(&mut self, intern: &InternInfo) {
        let mut theory_lemma_idx = (self.clause_proofs.len() + self.tseiten_clauses.len()) as u32;
        let mut clause_idx = self.clause_boundary;
        for proof_elt in self.clause_proofs.iter_mut().flatten() {
            let cr = proof_elt.clause_ref();
            proof_elt.clause = if cr == ClauseRef::SPECIAL {
                info!(
                    "{cr:?}: {} by theory",
                    self.defs
                        .display_clause(self.clauses[clause_idx].iter().copied(), intern)
                );
                clause_idx += 1;
                theory_lemma_idx += 1;
                theory_lemma_idx - 1
            } else {
                *self.clause_refs.get(&proof_elt.clause_ref()).unwrap()
            }
        }
    }

    fn arg(&mut self) -> InterpolateArg<'_> {
        let def_stack_len = self.def_stack.len();
        InterpolateArg {
            a_only: &self.a_only_defs,
            defs: &mut self.defs,
            def_stack: &mut self.def_stack,
            def_stack_len,
        }
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

    fn log_def<Exp: ExpLike, Exp2: AsRexp>(
        &mut self,
        val: Exp,
        f: Symbol,
        arg: impl Iterator<Item = Exp2> + Clone,
        intern: &InternInfo,
    ) {
        self.defs.log_def(val, f, arg, intern)
    }

    fn log_def_exp<Exp: ExpLike, Exp2: AsRexp>(
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
            (State::Solving, ClauseKind::Sat)
            | (State::Proving, ClauseKind::TheoryExplain | ClauseKind::TheoryConflict(_)) => {
                self.clauses.push(clause)
            }
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

    fn should_explain_conflict_final(&self) -> bool {
        matches!(self.state, State::Proving)
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
            initialize_interpolant_info(solver, pre_solve_marker, &assumptions);
        };
        let res = find_interpolant(solver, a, b);
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
        self.lit_buf.clear();
        self.clause_refs.clear();
        self.def_stack.clear();
        self.clause_boundary = 0;
    }
}

fn analyze_final_clause<Th: FullTheory<InterpolantRecorder>>(
    solver: &mut Solver<Th, InterpolantRecorder>,
    assumptions: &Conjunction,
) {
    solver.th.arg.recorder.clause_proofs.push(&[]);
    solver.simplify();
    solver.analyze_final_conflict();
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
}

fn initialize_interpolant_info<Th: FullTheory<InterpolantRecorder>>(
    solver: &mut Solver<Th, InterpolantRecorder>,
    pre_solve_marker: SolverMarker<Th::LevelMarker, LevelMarker>,
    assumptions: &Conjunction,
) {
    solver.th.arg.recorder.clause_boundary = solver.th.arg.recorder.clauses.len();
    solver.th.arg.recorder.state = State::Proving;
    solver.sat.pop_model(&mut solver.th);
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

    info!(
        "\n{}",
        solver
            .th
            .arg
            .recorder
            .defs
            .dump_global_defs(&solver.th.arg.intern)
    );
    analyze_final_clause(solver, assumptions);

    // analyze each learned clause
    for (i, level) in levels.into_iter().enumerate().rev() {
        let _ = analyze_clause(solver, i, level);
    }

    solver.pop_to_level(pre_solve_marker);
    solver.open(
        |_, acts| {
            let recorder = &mut acts.incr.recorder;
            let sat = &acts.sat;
            let intern = &acts.incr.intern;
            recorder.initialize_tseiten_clauses(sat, intern);
            recorder.finalize_clause_proofs(intern);
            recorder.state = State::Final;
        },
        (),
    );
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

fn theory_partial_interpolate<Th: FullTheory<InterpolantRecorder>>(
    solver: &mut Solver<Th, InterpolantRecorder>,
) {
    let marker = solver.create_level();
    for i in (solver.th.arg.recorder.clause_boundary..solver.th.arg.recorder.clauses.len())
        .into_iter()
        .rev()
    {
        let interpolant = solver.open(
            |th, arg| {
                th.interpolate_clause(
                    arg,
                    |arg| &arg.incr.recorder.clauses[i],
                    |arg| arg.incr.recorder.arg(),
                )
            },
            FALSE_DEF_EXP,
        );
        solver.th.arg.recorder.def_stack.push(interpolant);
        solver.pop_to_level(marker.clone());
    }
}

fn find_interpolant<Th: FullTheory<InterpolantRecorder>>(
    solver: &mut Solver<Th, InterpolantRecorder>,
    a: (usize, usize),
    b: (usize, usize),
) -> DefExp {
    solver.th.arg.recorder.a_only_defs.clear();
    solver.th.arg.recorder.def_stack.clear();
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
    theory_partial_interpolate(solver);
    solver.open(
        |_, arg| arg.incr.recorder.tseiten_partial_interpolate(&arg.sat),
        (),
    );
    solver.th.arg.recorder.resolution_partial_interpolate();
    debug!(
        "partial interpolants: {}",
        display_sexp(
            "",
            solver.th.arg.recorder.def_stack.iter().map(|&d| solver
                .th
                .arg
                .recorder
                .defs
                .display_def(d, &solver.th.arg.intern))
        )
    );
    solver.th.arg.recorder.def_stack.pop().unwrap()
}

/// Allows building [`DefExp`]s
pub struct InterpolateArg<'a> {
    a_only: &'a BitSet<DefExp>,
    defs: &'a mut DefinitionRecorder,
    def_stack: &'a mut Vec<DefExp>,
    def_stack_len: usize,
}

impl<'a> InterpolateArg<'a> {
    /// Check if `d` is only in "a" when interpolating "a" and "b"
    pub fn is_a_only(&self, v: NamespaceVar) -> bool {
        self.a_only.contains(self.defs.resolve_nv(v))
    }

    /// Adds `d` to the [`DefExp`] being built
    pub fn add_def(&mut self, d: DefExp) {
        self.def_stack.push(d)
    }

    pub fn intern_exp(&mut self, e: impl AsRexp) -> DefExp {
        self.defs.intern_exp(e)
    }

    pub fn add_exp(&mut self, e: impl AsRexp) {
        let d = self.defs.intern_exp(e);
        self.add_def(d);
    }

    /// Returns the [`DefExp`] being build and resets the internal state.
    pub fn finish(&mut self, s: Symbol) -> DefExp {
        self.finish_from(s, self.def_stack_len)
    }

    /// Similar to [`Self::finish`] but only includes elements after `from`
    /// and leaves the rest behind for future calls
    pub fn finish_from(&mut self, s: Symbol, from: usize) -> DefExp {
        debug_assert!(from >= self.def_stack_len);
        let res = match (s, &mut self.def_stack[from..]) {
            (AND_SYM | OR_SYM, defs) => {
                match (s == AND_SYM, optimize_junction(defs, s == AND_SYM)) {
                    (true, Some(0)) | (false, None) => TRUE_DEF_EXP,
                    (false, Some(0)) | (true, None) => FALSE_DEF_EXP,
                    (_, Some(1)) => defs[0],
                    (_, Some(j)) => self.defs.intern_call(s, &defs[..j]),
                }
            }
            (NOT_SYM, &mut [FALSE_DEF_EXP]) => TRUE_DEF_EXP,
            (NOT_SYM, &mut [TRUE_DEF_EXP]) => FALSE_DEF_EXP,
            (NOT_SYM, &mut [def]) if self.defs.resolve(def).0 == NOT_SYM => {
                self.defs.resolve(def).1[0]
            }
            (EQ_SYM, &mut [d1, d2]) if d1 == d2 => TRUE_DEF_EXP,
            (EQ_SYM, &mut [TRUE_DEF_EXP, FALSE_DEF_EXP] | &mut [FALSE_DEF_EXP, TRUE_DEF_EXP]) => {
                FALSE_DEF_EXP
            }
            (EQ_SYM, &mut [TRUE_DEF_EXP, d] | &mut [d, TRUE_DEF_EXP]) => d,
            (EQ_SYM, &mut [FALSE_DEF_EXP, d] | &mut [d, FALSE_DEF_EXP]) => {
                if self.defs.resolve(d).0 == NOT_SYM {
                    self.defs.resolve(d).1[0]
                } else {
                    self.defs.intern_call(NOT_SYM, &[d])
                }
            }
            _ => self.defs.intern_call(s, &self.def_stack[from..]),
        };
        self.def_stack.truncate(from);
        res
    }

    /// Creates a new [`InterpolateArg`] that can be used without disrupting the current one
    pub fn scope(&mut self) -> InterpolateArg<'_> {
        let def_stack_len = self.def_stack.len();
        InterpolateArg {
            a_only: &self.a_only,
            defs: &mut self.defs,
            def_stack: &mut self.def_stack,
            def_stack_len,
        }
    }
}

impl<'a> Drop for InterpolateArg<'a> {
    fn drop(&mut self) {
        self.def_stack.truncate(self.def_stack_len)
    }
}

pub(crate) fn optimize_junction(defs: &mut [DefExp], is_and: bool) -> Option<usize> {
    defs.sort_unstable();

    let mut last_def = None;
    let mut j = 0;
    // remove duplicates, true literals, etc.
    for i in 0..defs.len() {
        let def_i = defs[i];
        if def_i == (if is_and { FALSE_DEF_EXP } else { TRUE_DEF_EXP }) {
            return None;
        } else if def_i != (if is_and { TRUE_DEF_EXP } else { FALSE_DEF_EXP })
            && Some(def_i) != last_def
        {
            // not a duplicate
            last_def = Some(def_i);
            defs[j] = def_i;
            j += 1;
        }
    }
    Some(j)
}
