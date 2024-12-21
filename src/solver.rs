use crate::egraph::Children;
use crate::euf::{Euf, FullFunctionInfo, FunctionInfo};
use crate::exp::*;
use crate::explain::Justification;
use crate::intern::*;
use crate::junction::*;
use crate::sp_insert_map::SPInsertMap;
use crate::theory::Theory as _;
use crate::util::{display_debug, format_args2, DefaultHashBuilder, Either};
use crate::{euf, Symbol};
use core::cmp::Ordering;
use core::ops::Deref;
use hashbrown::HashMap;
use internal_iterator::{InternalIterator, IteratorExt};
use log::debug;
use no_std_compat::prelude::v1::*;
use perfect_derive::perfect_derive;
use plat_egg::Id;
use platsat::{lbool, Callbacks, Lit, SolverInterface, SolverOpts, Var};
use std::fmt::{Debug, Formatter};
use std::mem;

#[derive(Default)]
struct NoCb;
impl Callbacks for NoCb {}
type BatSolver = platsat::Solver<NoCb>;

/// The main solver structure including the sat solver and egraph.
///
/// It allows constructing and asserting expressions [`Exp`] within the solver
#[perfect_derive(Default)]
pub struct Solver {
    euf: Euf,
    pending_equalities: Vec<(Id, Id)>,
    sat: BatSolver,
    function_info_buf: FunctionInfo,
    ifs: SPInsertMap<(Lit, Id, Id), Id>,
    pub intern: InternInfo,
    junction_buf: Vec<Lit>,
}

impl DisplayInterned for UExp {
    fn fmt(&self, i: &InternInfo, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "(as @v{:?} {})", self.id(), self.sort().with_intern(i))
    }
}

impl Debug for BoolExp {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self.to_lit() {
            Err(c) => Debug::fmt(&c, f),
            Ok(l) => {
                if l.sign() {
                    write!(f, "(as @b{:?} Bool)", l.var())
                } else {
                    write!(f, "(as (not @b{:?}) Bool)", l.var())
                }
            }
        }
    }
}

display_debug!(BoolExp);

impl Debug for Exp {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self.expand() {
            EExp::Bool(b) => Debug::fmt(&b, f),
            EExp::Uninterpreted(u) => Debug::fmt(&u, f),
        }
    }
}

impl DisplayInterned for Exp {
    fn fmt(&self, i: &InternInfo, f: &mut Formatter<'_>) -> std::fmt::Result {
        match &self.expand() {
            EExp::Bool(b) => DisplayInterned::fmt(b, i, f),
            EExp::Uninterpreted(u) => DisplayInterned::fmt(u, i, f),
        }
    }
}

pub trait ExpLike: Into<Exp> + Copy + Debug + DisplayInterned + HasSort + Eq {
    fn canonize(self, solver: &Solver) -> Self;
}

impl ExpLike for BoolExp {
    fn canonize(self, solver: &Solver) -> Self {
        match self.to_lit() {
            Ok(x) => {
                let val = solver.sat.raw_value_lit(x);
                if val == lbool::TRUE {
                    BoolExp::TRUE
                } else if val == lbool::FALSE {
                    BoolExp::FALSE
                } else {
                    self
                }
            }
            _ => self,
        }
    }
}

impl ExpLike for UExp {
    fn canonize(self, solver: &Solver) -> Self {
        self.with_id(solver.euf.find(self.id()))
    }
}

impl ExpLike for Exp {
    fn canonize(self, solver: &Solver) -> Self {
        match self.expand() {
            EExp::Bool(b) => b.canonize(solver).into(),
            EExp::Uninterpreted(u) => u.canonize(solver).into(),
        }
    }
}

pub type BLit = Lit;

#[derive(Debug, Copy, Clone)]
/// Result of calling [`Solver::check_sat_assuming`]
pub enum SolveResult {
    Sat,
    Unsat,
    Unknown,
}

impl SolveResult {
    pub fn valid_when_expecting(self, oth: SolveResult) -> bool {
        matches!(
            (self, oth),
            (SolveResult::Sat, SolveResult::Sat)
                | (SolveResult::Unsat, SolveResult::Unsat)
                | (_, SolveResult::Unknown)
        )
    }

    pub fn as_lower_str(self) -> &'static str {
        match self {
            SolveResult::Sat => "sat",
            SolveResult::Unsat => "unsat",
            SolveResult::Unknown => "unknown",
        }
    }
}

impl Solver {
    pub fn is_ok(&self) -> bool {
        self.sat.is_ok()
    }
    fn fresh(&mut self) -> Var {
        let fresh = self.sat.new_var_default();
        fresh
    }

    /// Generate a fresh boolean variable
    pub fn fresh_bool(&mut self) -> BoolExp {
        BoolExp::unknown(Lit::new(self.fresh(), true))
    }

    #[inline]
    fn andor_reuse(&mut self, exps: &mut Vec<BLit>, is_and: bool, approx: Option<bool>) -> BoolExp {
        exps.sort_unstable();

        let mut last_lit = Lit::UNDEF;
        let mut j = 0;
        // remove duplicates, true literals, etc.
        for i in 0..exps.len() {
            let lit_i = exps[i];
            let value = self.sat.raw_value_lit(lit_i);
            if (value == lbool::TRUE ^ is_and) || lit_i == !last_lit {
                return BoolExp::from_bool(!is_and);
            } else if !(value ^ is_and == lbool::FALSE) && lit_i != last_lit {
                // not a duplicate
                last_lit = lit_i;
                exps[j] = lit_i;
                j += 1;
            }
        }
        exps.truncate(j);

        if let [exp] = &**exps {
            return BoolExp::unknown(*exp);
        }
        let fresh = self.fresh();
        let res = Lit::new(fresh, true);
        for lit in &mut *exps {
            if approx != Some(is_and) {
                self.sat.add_clause_unchecked(
                    [*lit ^ !is_and, Lit::new(fresh, !is_and)].iter().copied(),
                );
            }
            *lit ^= is_and;
        }
        if approx != Some(!is_and) {
            exps.push(Lit::new(fresh, is_and));
            self.sat.add_clause_unchecked(exps.iter().copied());
        }
        BoolExp::unknown(res)
    }

    /// Collapse a [`Conjunction`] or [`Disjunction`] into a [`BoolExp`]
    ///
    /// To reuse memory you can pass mutable reference instead of an owned value
    /// Doing this will leave `j` in an unspecified state, so it should be
    /// [`clear`](Junction::clear)ed before it is used again
    pub fn collapse_bool<const IS_AND: bool>(&mut self, j: Junction<IS_AND>) -> BoolExp {
        self.collapse_bool_approx(j, None)
    }

    /// Similar to [`collapse_bool`](Self::collapse_bool), but returns a boolean that approximates `j`
    ///
    /// If `approx` is `None` the returned boolean exactly matches `j` (same behaviour as  [`collapse_bool`](Self::collapse_bool))
    ///
    /// If `approx` is `Some(false)` the returned boolean is assigned false whenever `j` is assigned to false,
    /// and when `j` is assigned to true the returned boolean is either also true or unconstrained
    ///
    /// If `approx` is `Some(true)` the returned boolean is assigned true whenever `j` is assigned to true,
    /// and when `j` is assigned to false the returned boolean is either also false or unconstrained
    ///
    /// ## Example
    /// ```
    /// use plat_smt::Solver;
    /// use plat_smt::SolveResult;
    /// let mut s = Solver::default();
    /// let a = s.fresh_bool();
    /// let b = s.fresh_bool();
    /// let ab = s.collapse_bool_approx(a | b, Some(false));
    /// s.assert(!a);
    /// s.assert(!b);
    /// s.assert(ab);
    /// assert!(matches!(s.check_sat(), SolveResult::Unsat))
    /// ```
    pub fn collapse_bool_approx<const IS_AND: bool>(
        &mut self,
        mut j: Junction<IS_AND>,
        approx: Option<bool>,
    ) -> BoolExp {
        debug!("{j:?} (approx: {approx:?}) was collapsed to ...");
        let res = match j.absorbing {
            true => BoolExp::from_bool(!IS_AND),
            false if j.lits.is_empty() => BoolExp::from_bool(IS_AND),
            false => self.andor_reuse(&mut j.lits, IS_AND, approx),
        };
        self.junction_buf = j.lits;
        debug!("... {res}");
        res
    }

    /// Returns an empty [`Conjunction`] or [`Disjunction`]  which reuses memory from the last call
    /// to [`collapse_bool`](Self::collapse_bool)
    pub fn new_junction<const IS_AND: bool>(&mut self) -> Junction<IS_AND> {
        self.junction_buf.clear();
        Junction {
            absorbing: false,
            lits: mem::take(&mut self.junction_buf),
        }
    }

    pub fn xor(&mut self, b1: BoolExp, b2: BoolExp) -> BoolExp {
        let b1 = self.canonize(b1);
        let b2 = self.canonize(b2);
        let res = match (b1.to_lit(), b2.to_lit()) {
            (_, Err(b2)) => b1 ^ b2,
            (Err(b1), _) => b2 ^ b1,
            (Ok(l1), Ok(l2)) => {
                let (l1, l2) = match l1.var().cmp(&l2.var()) {
                    Ordering::Less => (l1, l2),
                    Ordering::Equal if l1 == l2 => return BoolExp::FALSE,
                    Ordering::Equal => return BoolExp::TRUE,
                    Ordering::Greater => (l2, l1),
                };
                let fresh = self.fresh();
                let fresh = Lit::new(fresh, true);
                self.sat
                    .add_clause_unchecked([l1, l2, !fresh].iter().copied());
                self.sat
                    .add_clause_unchecked([!l1, l2, fresh].iter().copied());
                self.sat
                    .add_clause_unchecked([l1, !l2, fresh].iter().copied());
                self.sat
                    .add_clause_unchecked([!l1, !l2, !fresh].iter().copied());
                BoolExp::unknown(fresh)
            }
        };
        debug!("{res} = (xor {b1} {b2})");
        res
    }

    pub(crate) fn raw_eq(&mut self, id1: Id, id2: Id) -> BoolExp {
        let res = self
            .euf
            .add_eq_node(id1, id2, || Lit::new(self.sat.new_var_default(), true));
        debug!("{res:?} is defined as (= id{id1:?} id{id2:?})");
        res
    }

    pub(crate) fn assert_raw_eq(&mut self, id1: Id, id2: Id) {
        if !self.is_ok() {
            return;
        }
        if !self.euf.has_parents(id1) || !self.euf.has_parents(id2) {
            let (euf, arg) = self.euf.open();
            self.sat.with_theory_arg(|acts| {
                let _ = euf.union(acts, arg, id1, id2, Justification::NOOP);
            });
        } else {
            self.pending_equalities.push((id1, id2));
        }
    }

    /// Produce a boolean expression representing the equality of the two expressions
    ///
    /// If the two expressions have different sorts returns an error containing both sorts
    pub fn eq(&mut self, exp1: Exp, exp2: Exp) -> Result<BoolExp, (Sort, Sort)> {
        let id1 = self.id(exp1);
        let id2 = self.id(exp2);
        if exp1.sort() != exp2.sort() {
            Err((exp1.sort(), exp2.sort()))
        } else {
            Ok(self.raw_eq(id1, id2))
        }
    }

    /// Equivalent to `self.`[`assert`](Self::assert)`(self.`[`eq`](Self::eq)`(exp1, exp2)?)` but
    /// more efficient
    pub fn assert_eq(&mut self, exp1: Exp, exp2: Exp) -> Result<(), (Sort, Sort)> {
        let id1 = self.id(exp1);
        let id2 = self.id(exp2);
        if exp1.sort() != exp2.sort() {
            Err((exp1.sort(), exp2.sort()))
        } else {
            self.assert_raw_eq(id1, id2);
            Ok(())
        }
    }

    /// Assert that no pair of `Id`s from `ids` are equal to each other
    pub fn assert_distinct(&mut self, ids: impl IntoIterator<Item = Id>) {
        if let Err(()) = self.euf.make_distinct(ids, &mut self.intern.symbols) {
            self.sat.add_clause_unchecked([]);
        }
    }

    /// Equivalent to `self.`[`assert`](Self::assert)`(self.`[`bool_fn`](Self::bool_fn)`(f, children) ^ negate)`
    /// but more efficient
    pub fn assert_bool_fn(&mut self, f: Symbol, children: Children, negate: bool) {
        if !self.is_ok() {
            return;
        }
        let (id1, _) = self.euf.add_blank_bool_node(f.into(), children);
        let id2 = self.euf.id_for_bool(!negate);
        self.assert_raw_eq(id1, id2);
    }

    pub fn assert_inv(&self) {
        if let Some((_, id)) = self.ifs.entries.last() {
            assert!(*id < self.euf.len_id())
        }
    }

    fn raw_ite(&mut self, i: Lit, t: Id, e: Id, s: Sort) -> Exp {
        let mut ifs = mem::take(&mut self.ifs);
        let id = ifs.get_or_insert((i, t, e), || {
            let sym = self
                .intern
                .symbols
                .gen_sym(&format_args2!("if|{i:?}|id{t}|id{e}"));
            let fresh = self.sorted_fn(sym, Children::new(), s);
            let fresh_id = self.id(fresh);
            let eqt = self.raw_eq(fresh_id, t);
            let Ok(eqt) = eqt.to_lit() else {
                unreachable!()
            };
            let eqe = self.raw_eq(fresh_id, e);
            let Ok(eqe) = eqe.to_lit() else {
                unreachable!()
            };
            self.sat.add_clause_unchecked([!i, eqt].iter().copied());
            self.sat.add_clause_unchecked([i, eqe].iter().copied());
            fresh_id
        });
        self.ifs = ifs;
        self.euf.id_to_exp(id)
    }

    /// Produce an expression representing that is equivalent to `t` if `i` is true or `e` otherwise
    ///
    /// If `t` and `e` have different sorts returns an error containing both sorts
    pub fn ite(&mut self, i: BoolExp, t: Exp, e: Exp) -> Result<Exp, (Sort, Sort)> {
        let tsort = t.sort();
        let esort = e.sort();
        if tsort != esort {
            return Err((tsort, esort));
        }
        let res = match self.canonize(i).to_lit() {
            Err(true) => t,
            Err(false) => e,
            Ok(u) => {
                let t = self.canonize(t);
                let e = self.canonize(e);
                if t == e {
                    t
                } else {
                    let tid = self.id(t);
                    let eid = self.id(e);
                    self.raw_ite(u, tid, eid, tsort)
                }
            }
        };
        debug!("{res:?} is bound to (ite {i:?} {t:?} {e:?})");
        Ok(res)
    }

    /// Creates a function call expression with a given name and children and return sort
    ///
    /// [`Id`]s for the children can be created with [`id`](Solver::id)
    ///
    /// This method does not check sorts of the children so callers need to ensure that functions
    /// call expressions with the same name but different return sorts do not become congruently
    /// equal (This would cause a panic when it happens)
    pub fn sorted_fn(&mut self, fn_name: Symbol, children: Children, sort: Sort) -> Exp {
        if sort == BOOL_SORT {
            self.bool_fn(fn_name, children).into()
        } else {
            let id = self
                .euf
                .add_uninterpreted_node(fn_name.into(), children, sort);
            UExp::new(id, sort).into()
        }
    }

    /// Similar to calling [`sorted_fn`](Solver::sorted_fn) with the boolean sort, but returns
    /// a [`BoolExp`] instead of an [`Exp`]
    pub fn bool_fn(&mut self, fn_name: Symbol, children: Children) -> BoolExp {
        if !self.is_ok() {
            return BoolExp::FALSE;
        }
        self.euf
            .add_bool_node(fn_name.into(), children, || {
                Lit::new(self.sat.new_var_default(), true)
            })
            .0
    }

    /// Assert that `b` is true
    pub fn assert(&mut self, b: BoolExp) {
        debug!("assert {b}");
        match self.canonize(b).to_lit() {
            Err(true) => {}
            Ok(l) => {
                self.sat.add_clause_unchecked([l]);
            }
            Err(false) => {
                self.sat.add_clause_unchecked([]);
            }
        }
    }

    fn flush_pending(&mut self) {
        let _ = self.pending_equalities.iter().try_for_each(|&(id1, id2)| {
            let (euf, arg) = self.euf.open();
            let mut res = Ok(());
            self.sat
                .with_theory_arg(|acts| res = euf.union(acts, arg, id1, id2, Justification::NOOP));
            res
        });
        self.pending_equalities.clear();
    }

    /// Check if the current assertions are satisfiable
    pub fn check_sat(&mut self) -> SolveResult {
        self.check_sat_assuming(&Default::default())
    }

    /// Check if the current assertions combined with the assertions in `c` are satisfiable
    /// Leave the solver in a state representing the model
    pub fn check_sat_assuming_preserving_trail(&mut self, c: &Conjunction) -> SolveResult {
        self.flush_pending();
        let res = match c.absorbing {
            true => lbool::FALSE,
            false => self
                .sat
                .solve_limited_preserving_trail_th(&mut self.euf, &c.lits),
        };
        if res == lbool::FALSE {
            debug!("check-sat {c:?} returned unsat",);
            SolveResult::Unsat
        } else if res == lbool::TRUE {
            debug!(
                "check-sat {c:?} returned sat, model:\n{:?}",
                self.sat.raw_model()
            );
            SolveResult::Sat
        } else {
            SolveResult::Unknown
        }
    }

    /// Check if the current assertions combined with the assertions in `c` are satisfiable
    pub fn check_sat_assuming(&mut self, c: &Conjunction) -> SolveResult {
        let res = self.check_sat_assuming_preserving_trail(c);
        self.pop_model();
        res
    }

    /// Restores the state after calling `raw_check_sat_assuming`
    pub fn pop_model(&mut self) {
        self.sat.pop_model(&mut self.euf);
    }

    pub fn push(&mut self) {
        debug!(
            "Push ({} -> {})",
            self.euf.assertion_level(),
            self.euf.assertion_level() + 1
        );
        self.flush_pending();
        self.sat.push_th(&mut self.euf);
        self.euf.smt_push()
    }

    pub fn pop(&mut self, n: usize) {
        debug!(
            "Pop ({} -> {})",
            self.euf.assertion_level(),
            self.euf.assertion_level() - n
        );
        if n > self.euf.assertion_level() {
            self.clear();
        } else if n > 0 {
            self.sat.pop_n_th(&mut self.euf, n as u32);
            self.euf.smt_pop_to(self.euf.assertion_level() - n);
            self.ifs.remove_after(self.euf.len_id());
        }
    }

    pub fn clear(&mut self) {
        self.sat.reset();
        self.euf.clear();
        self.ifs.clear();
    }

    pub fn simplify(&mut self) {
        self.flush_pending();
        self.sat.simplify_th(&mut self.euf);
    }

    /// Like [`check_sat_assuming`](Solver::check_sat_assuming) but takes in an
    /// [`UnsatCoreConjunction`] which associates its elements values and returns an iterator
    /// over the values associated with the elements of the unsat core if the result is unsat
    pub fn check_sat_assuming_for_core<'a, T>(
        &'a mut self,
        c: &'a UnsatCoreConjunction<T>,
    ) -> Option<impl InternalIterator<Item = &'a T>> {
        let (conj, info) = c.parts();
        match self.check_sat_assuming(conj) {
            SolveResult::Unsat => Some(info.core(self.last_unsat_core())),
            _ => None,
        }
    }

    /// Returns the id of an `exp`
    ///
    /// See [`sorted_fn`](Solver::sorted_fn) and  [`bool_fn`](Solver::bool_fn)
    pub fn id(&mut self, exp: Exp) -> Id {
        match exp.expand() {
            EExp::Bool(b) => match self.canonize(b).to_lit() {
                Err(b) => self.euf.id_for_bool(b),
                Ok(lit) => self.euf.id_for_lit(lit, &mut self.intern.symbols),
            },
            EExp::Uninterpreted(u) => u.id(),
        }
    }

    /// Returns the boolean sort
    pub fn bool_sort(&self) -> Sort {
        BOOL_SORT
    }

    /// Simplifies `t` based on the current assertions
    pub fn canonize<T: ExpLike>(&self, t: T) -> T {
        let res = t.canonize(self);
        debug!(
            "{} canonized to {}",
            t.with_intern(&self.intern),
            res.with_intern(&self.intern)
        );
        res
    }

    pub(crate) fn last_unsat_core(&mut self) -> impl InternalIterator<Item = Lit> + '_ {
        self.sat.unsat_core(&mut self.euf)
    }

    pub fn function_info(&mut self) -> (FullFunctionInfo<'_>, &Self) {
        self.euf.function_info(&mut self.function_info_buf);
        (self.function_info_buf.with_euf(&self.euf), &*self)
    }
    pub fn sat_options(&self) -> SolverOpts {
        self.sat.options()
    }

    pub fn set_sat_options(&mut self, options: SolverOpts) -> Result<(), ()> {
        self.sat.set_options(options)
    }

    pub fn assertion_level(&self) -> u32 {
        self.euf.assertion_level() as u32
    }
}

#[derive(Clone)]
pub struct CheckPoint {
    sat: platsat::core::CheckPoint,
    euf: Option<euf::PushInfo>,
}

impl Solver {
    pub fn checkpoint(&self) -> CheckPoint {
        CheckPoint {
            sat: self.sat.checkpoint(),
            euf: self.is_ok().then(|| self.euf.deref().create_level()),
        }
    }

    pub fn restore_checkpoint(&mut self, checkpoint: CheckPoint) {
        self.sat.restore_checkpoint(checkpoint.sat);
        if let Some(x) = checkpoint.euf {
            self.euf.pop_to_level(x, true)
        }
    }
}

#[perfect_derive(Default)]
pub(crate) struct UnsatCoreInfo<T> {
    false_by: Option<T>,
    data: HashMap<Lit, T, DefaultHashBuilder>,
}

impl<T> UnsatCoreInfo<T> {
    fn add(&mut self, bool_exp: BoolExp, t: T) {
        match bool_exp.to_lit() {
            Err(false) => {
                if self.false_by.is_none() {
                    self.false_by = Some(t)
                }
            }
            Err(true) => {}
            Ok(l) => {
                if self.false_by.is_none() {
                    self.data.insert(!l, t);
                }
            }
        }
    }

    pub(crate) fn core(
        &self,
        lits: impl InternalIterator<Item = Lit>,
    ) -> impl InternalIterator<Item = &T> {
        match &self.false_by {
            Some(x) => Either::Right(core::iter::once(x).into_internal()),
            None => Either::Left(lits.filter_map(|x| self.data.get(&x))),
        }
    }
}

#[perfect_derive(Default)]
pub struct UnsatCoreConjunction<T> {
    conj: Conjunction,
    info: UnsatCoreInfo<T>,
}

impl<T> FromIterator<(BoolExp, T)> for UnsatCoreConjunction<T> {
    fn from_iter<I: IntoIterator<Item = (BoolExp, T)>>(iter: I) -> Self {
        let mut info = UnsatCoreInfo::default();
        let conj = iter
            .into_iter()
            .map(|(b, t)| {
                info.add(b, t);
                b
            })
            .collect();
        UnsatCoreConjunction { info, conj }
    }
}

impl<T> Extend<(BoolExp, T)> for UnsatCoreConjunction<T> {
    fn extend<I: IntoIterator<Item = (BoolExp, T)>>(&mut self, iter: I) {
        let conj = iter.into_iter().map(|(b, t)| {
            self.info.add(b, t);
            b
        });
        self.conj.extend(conj);
    }
}

impl<T> UnsatCoreConjunction<T> {
    pub(crate) fn parts(&self) -> (&Conjunction, &UnsatCoreInfo<T>) {
        (&self.conj, &self.info)
    }

    pub(crate) fn push(&self) -> u32 {
        if self.conj.absorbing {
            u32::MAX
        } else {
            self.conj.lits.len() as u32
        }
    }

    pub(crate) fn pop_to(&mut self, push_info: u32) {
        if push_info != u32::MAX {
            self.conj.absorbing = false;
            self.info.false_by = None;
            for l in self.conj.lits.drain(push_info as usize..) {
                self.info.data.remove(&!l);
            }
        }
    }
}
