use crate::full_theory::FullTheory;
use crate::intern::{InternInfo, RecInfoArg, Symbol, AND_SYM, EQ_SYM, NOT_SYM, OR_SYM};
use crate::recorder::definition_recorder::{
    DefExp, DefinitionRecorder, FALSE_DEF_EXP, TRUE_DEF_EXP,
};
use crate::recorder::dep_checker::{DepChecker, DepCheckerAction};
use crate::recorder::slice_vec::SliceVec;
use crate::recorder::{dep_checker, ClauseKind, Recorder};
use crate::rexp::{AsRexp, NamespaceVar};
use crate::solver::LevelMarker as SolverMarker;
use crate::theory::Incremental;
use crate::util::{display_sexp, DebugIter, DisplayFn, HashMap};
use crate::{BoolExp, Conjunction, ExpLike, Solver};
use alloc::borrow::Cow;
use alloc::string::String;
use alloc::vec::Vec;
use bytemuck::must_cast;
use core::fmt::Debug;
use core::fmt::Write;
use core::num::NonZeroU32;
use default_vec2::StaticFlagVec;
use log::{debug, info, trace, warn};
use platsat::theory::ClauseRef;
use platsat::{lbool, Lit, SolverInterface, TheoryArg};
use std::mem;

pub(super) const NEITHER: u32 = 0b00;
pub(super) const A_ONLY: u32 = 0b01;
pub(super) const B_ONLY: u32 = 0b10;
pub(super) const BOTH: u32 = 0b11;

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
    deps_marker: dep_checker::Marker,
}

#[derive(Debug)]
enum ErrorReason {
    MixedTerm,
    MissedAssumption,
}
use crate::recorder::recorder::Feature;
use ErrorReason::*;

#[derive(Default)]
pub struct InterpolantRecorder {
    // Cleared in `clear`
    /// Stores clauses found during search before clause boundary, and theory clauses after
    /// clause_boundary
    clauses: SliceVec<Lit>,
    defs: DefinitionRecorder,
    disabled: bool,

    // Cleared in `exit_solved_state`
    state: State,
    tseiten_clauses: Vec<ClauseRef>,
    clause_proofs: SliceVec<ClauseProofElement>,
    /// Maps clause refs to their proof index (see ClauseProofElement) or MAX if it was not
    /// resolved yet.
    clause_refs: HashMap<ClauseRef, u32>,
    def_stack: Vec<DefExp>,
    sym_buf: Vec<Symbol>,
    clause_boundary: usize,

    // Cleared at the end of `find_interpolant`
    ab_defs: StaticFlagVec<2, DefExp>,
    ab_syms: StaticFlagVec<2, Symbol>,

    defs_marker_after_solve: u32,

    dep_checker: DepChecker,
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

    fn set_def_exps_status(
        &mut self,
        a: (usize, usize),
        b: (usize, usize),
        assumptions: &Conjunction,
        intern: &InternInfo,
    ) -> Result<(), (DefExp, ErrorReason)> {
        for &a_sym in &self.sym_buf[a.0..a.1] {
            self.ab_syms.or_assign(a_sym, A_ONLY)
        }
        for &b_sym in &self.sym_buf[b.0..b.1] {
            self.ab_syms.or_assign(b_sym, B_ONLY)
        }

        for &a in &assumptions.lits {
            let def = self.defs.intern_exp(BoolExp::unknown(a));
            let Some(sym) = self.defs.get_alias(def) else {
                return Err((def, MissedAssumption));
            };
            if self.ab_syms.get(sym) == NEITHER {
                return Err((def, MissedAssumption));
            }
        }

        self.dep_checker.resolve_syms_in_ab(&mut self.ab_syms);

        self.set_def_status_from_syms(intern)
    }

    fn set_def_status_from_syms(
        &mut self,
        intern: &InternInfo,
    ) -> Result<(), (DefExp, ErrorReason)> {
        for def in (1..self.defs_marker_after_solve)
            .into_iter()
            .map(|x| DefExp::new(NonZeroU32::new(x).unwrap()))
        {
            let (sym, children) = self.defs.resolve(def);
            let mut in_ab = if sym.is_builtin() {
                BOTH
            } else {
                self.ab_syms.get(sym)
            };
            for &child in children {
                let child_in_ab = self.ab_defs.get(child);
                in_ab &= child_in_ab;
                if in_ab == NEITHER {
                    warn!(
                        "{} is a possible mixed term which currently isn't supported",
                        self.defs.display_stand_alone_def(def, intern)
                    );
                    return Err((def, MixedTerm));
                }
            }
            debug!(
                "{} is in {}",
                self.defs.display_stand_alone_def(def, intern),
                match in_ab {
                    NEITHER => "neither",
                    A_ONLY => "a",
                    B_ONLY => "b",
                    BOTH => "both",
                    _ => "???",
                }
            );
            self.ab_defs.set(def, in_ab);
        }
        Ok(())
    }

    fn is_a_only(&self, def: DefExp) -> bool {
        self.ab_defs.get(def) == A_ONLY
    }

    fn tseiten_partial_interpolate(&mut self, sat: &TheoryArg) {
        for tseiten in self.tseiten_clauses.iter().rev() {
            let tseiten = sat.resolve_clause_ref(*tseiten);
            let def_len = self.def_stack.len();
            for &l in tseiten {
                let def = self.defs.intern_exp(l.var());
                if !self.is_a_only(def) {
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
                ab: &self.ab_defs,
                defs: &mut self.defs,
                def_stack: &mut self.def_stack,
                def_stack_len,
            };
            interp.add_def(def);
            let mut is_and = true;
            for elt in rest {
                let pivot_def = interp.intern_exp(elt.pivot.var());
                let def_is_and = !interp.is_def_a_only(pivot_def);
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

    fn finalize_interplant(&mut self, assumptions: &Conjunction, intern: &InternInfo) -> DefExp {
        info!(
            "partial interpolants: {}",
            display_sexp(
                "",
                self.def_stack
                    .iter()
                    .map(|&d| self.defs.display_def(d, &intern))
            )
        );
        let base = self.def_stack.pop().unwrap();
        let ab_syms = mem::take(&mut self.ab_syms);
        let mut arg = self.arg();
        arg.add_def(base);
        for &a in &assumptions.lits {
            let def = arg.intern_exp(BoolExp::unknown(a));
            if arg.ab.get(def) == BOTH {
                let sym = arg.defs.get_alias(def).unwrap();
                if ab_syms.get(sym) == A_ONLY {
                    debug!(
                        "{} is only in a but uses only shared symbols",
                        arg.defs.display_stand_alone_def(def, intern)
                    );
                    arg.add_def(def)
                }
            }
        }
        let res = arg.finish(AND_SYM);
        drop(arg);
        self.ab_syms = ab_syms;
        self.ab_defs.clear();
        self.ab_syms.clear();
        res
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
            ab: &self.ab_defs,
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
            deps_marker: self.dep_checker.create_level(),
        }
    }

    fn pop_to_level(&mut self, marker: Self::LevelMarker, clear_lits: bool) {
        match self.state {
            State::Solving => {
                self.defs.pop_to_level(marker.def_marker, clear_lits);
                self.clauses.truncate(marker.clause_len as usize);
                self.dep_checker
                    .pop_to_level(marker.deps_marker, clear_lits);
            }
            _ => {
                debug_assert_eq!(clear_lits, false)
            }
        }
    }

    fn clear(&mut self) {
        debug_assert!(matches!(self.state, State::Solving));
        self.defs.clear();
        self.clauses.clear();
        self.dep_checker.clear();
    }
}

impl Recorder for InterpolantRecorder {
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

    type SymBufMarker = (usize, usize);

    fn intern_syms(&mut self, syms: impl Iterator<Item = Symbol>) -> Self::SymBufMarker {
        let start_len = self.sym_buf.len();
        self.sym_buf.extend(syms);
        (start_len, self.sym_buf.len())
    }

    fn write_interpolant<'a, Th: FullTheory<Self>>(
        solver: &'a mut Solver<Th, Self>,
        pre_solve_marker: SolverMarker<Th::LevelMarker, LevelMarker>,
        assumptions: &Conjunction,
        a: Self::SymBufMarker,
        b: Self::SymBufMarker,
        writer: &mut impl Write,
    ) -> Result<(), Cow<'static, str>> {
        let pre_solve_recorder_marker = pre_solve_marker.recorder.def_marker.def_maker;
        if State::Final != solver.th.arg.recorder.state {
            initialize_interpolant_info(solver, pre_solve_marker.clone(), &assumptions);
        };

        let res = match find_interpolant(solver, a, b, assumptions) {
            Ok(res) => res,
            Err((def, MixedTerm)) if usize::from(def) >= pre_solve_recorder_marker as usize => {
                let lit_buf = mem::take(&mut solver.th.arg.recorder.sym_buf);
                solver.th.arg.recorder.exit_solved_state();
                solver.th.arg.recorder.sym_buf = lit_buf;
                solver.pop_to_level(pre_solve_marker.clone());
                solver.check_sat_assuming_preserving_trail(assumptions);
                initialize_interpolant_info(solver, pre_solve_marker, &assumptions);
                find_interpolant(solver, a, b, assumptions).unwrap()
            }
            Err((def, reason)) => {
                let mut s = String::new();
                s.push_str("Can't produce interpolant because of ");
                s.push_str(match reason {
                    MixedTerm => "term containing a-only and b-only constants: ",
                    MissedAssumption => "term in check-sat-assuming in neither a nor b: ",
                });
                write!(
                    &mut s,
                    "{}",
                    solver
                        .th
                        .arg
                        .recorder
                        .defs
                        .display_stand_alone_def(def, &solver.th.arg.intern)
                )
                .unwrap();
                solver.th.arg.recorder.ab_defs.clear();
                solver.th.arg.recorder.ab_syms.clear();
                return Err(Cow::Owned(s));
            }
        };
        let interpolant = solver
            .th
            .arg
            .recorder
            .defs
            .display_stand_alone_def(res, &solver.th.arg.intern);
        write!(writer, "{interpolant}").unwrap();
        Ok(())
    }

    fn feature_enabled(&self, feature: Feature) -> bool {
        if matches!(feature, Feature::Interpolant) {
            !self.disabled
        } else {
            false
        }
    }

    fn set_feature_enabled(&mut self, feature: Feature, enable: bool) -> bool {
        if matches!(feature, Feature::Interpolant) {
            self.disabled = !enable;
            true
        } else {
            enable
        }
    }

    fn exit_solved_state(&mut self) {
        self.state = State::Solving;
        self.tseiten_clauses.clear();
        self.clause_proofs.clear();
        self.clause_refs.clear();
        self.def_stack.clear();
        self.sym_buf.clear();
        self.clause_boundary = 0;
    }

    fn allows_mid_search_add<Exp: AsRexp>(
        &self,
        children: impl Iterator<Item = Exp> + Clone,
        intern: &InternInfo,
    ) -> bool {
        let mut is_ab = BOTH;
        let res = children
            .clone()
            .try_for_each(|child| {
                child.try_for_each_nv(|nv| {
                    is_ab &= self.ab_defs.get(self.defs.resolve_nv(nv));
                    if is_ab == NEITHER {
                        Err(())
                    } else {
                        Ok(())
                    }
                })
            })
            .is_ok();
        trace!(
            "Adding {} is{} allowed",
            display_sexp("?", children.map(|x| self.defs.display_exp(x, intern))),
            if res { "" } else { " not" }
        );
        res
    }

    fn dep_checker_act(&mut self, act: impl DepCheckerAction) {
        self.dep_checker.act(act)
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
    solver.th.arg.recorder.defs_marker_after_solve =
        solver.th.arg.recorder.defs.create_level().def_maker;
    solver.th.arg.recorder.clause_boundary = solver.th.arg.recorder.clauses.len();
    solver.th.arg.recorder.state = State::Proving;
    solver.th.arg.recorder.defs_marker_after_solve =
        solver.th.arg.recorder.defs.create_level().def_maker;
    solver.sat.pop_model(&mut solver.th);
    solver.pop_to_level_keep_lits(pre_solve_marker.clone());
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

    solver.pop_to_level_keep_lits(pre_solve_marker);
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
    solver.pop_to_level_keep_lits(level_before);
    solver.th.arg.recorder.start_new_clause_proof(cr)?;
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
        solver.pop_to_level_keep_lits(marker.clone());
    }
}

fn find_interpolant<Th: FullTheory<InterpolantRecorder>>(
    solver: &mut Solver<Th, InterpolantRecorder>,
    a: (usize, usize),
    b: (usize, usize),
    assumptions: &Conjunction,
) -> Result<DefExp, (DefExp, ErrorReason)> {
    solver.th.arg.recorder.def_stack.clear();
    solver
        .th
        .arg
        .recorder
        .set_def_exps_status(a, b, assumptions, &solver.th.arg.intern)?;
    theory_partial_interpolate(solver);
    solver.open(
        |_, arg| arg.incr.recorder.tseiten_partial_interpolate(&arg.sat),
        (),
    );
    solver.th.arg.recorder.resolution_partial_interpolate();
    Ok(solver
        .th
        .arg
        .recorder
        .finalize_interplant(assumptions, &solver.th.arg.intern))
}

/// Allows building [`DefExp`]s
pub struct InterpolateArg<'a> {
    ab: &'a StaticFlagVec<2, DefExp>,
    defs: &'a mut DefinitionRecorder,
    def_stack: &'a mut Vec<DefExp>,
    def_stack_len: usize,
}

impl<'a> InterpolateArg<'a> {
    /// Check if `d` is only in "a" when interpolating "a" and "b"
    pub fn is_a_only(&self, v: NamespaceVar) -> bool {
        self.is_def_a_only(self.defs.resolve_nv(v))
    }

    /// Check if `d` is only in "a" when interpolating "a" and "b"
    fn is_def_a_only(&self, def: DefExp) -> bool {
        self.ab.get(def) == A_ONLY
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
            ab: &self.ab,
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
