use crate::AddSexpError::{AsSortMismatch, Unbound};
use crate::collapse::ExprContext;
use crate::exp::Fresh;
pub use crate::full_theory::{FnSort, MaybeFnSort};
use crate::full_theory::{
    FullTheory, FunctionAssignmentT, Instruction, PrepareModelKind, QuantContext, QuantExp,
    QuantifierApplier, WrapSolver,
};
use crate::intern::*;
use crate::parser::SexpTerminal;
use crate::parser_fragment::{ParserFragment, PfResult};
use crate::recorder::dep_checker::DepCheckerAction;
use crate::recorder::{Recorder, dep_checker};
use crate::solver::SolverCollapse;
use crate::theory::TheoryArgT;
use crate::util::{DebugIter, Either};
use crate::{AddSexpError, BoolExp, HasSort, Solver, Sort, SubExp, full_theory, util};
use alloc::vec::Vec;
use core::fmt::{Debug, Formatter};
use core::ops::{Deref, DerefMut};
pub use full_theory::{Bound, BoundL, Logic};
use hashbrown::hash_map::Entry;
use log::info;
use std::{iter, mem};

#[derive(Debug, Copy, Clone)]
struct Inner;
/// Requirements on the `Exp` created
#[derive(Debug, Copy, Clone)]
pub enum StartExpCtx {
    /// Must be equivalent
    Exact,
    /// Will be asserted (only available when starting a new expression)
    Assert,
    /// Optimize to satisfy parent constraints (only available when continuing an existing expression)
    Opt,
    #[doc(hidden)]
    AssertOrOpt(#[expect(private_interfaces)] Inner),
}

impl StartExpCtx {
    pub(crate) const ASSERT_OR_OPT: Self = StartExpCtx::AssertOrOpt(Inner);
}

// If `f` is `LET_SYM` then `stack_len` refers to let_bound_stack instead of exp_stack
struct Frame<UExp> {
    ctx: ExprContext<UExp>,
    f: Symbol,
    expected: Option<Sort>,
    stack_len: u32,
}

pub enum DefineError<L: Logic> {
    Exists(BoundL<L>),
    Unsupported,
}

/// Wrapper around solver more conducive to building up expressions such as from parsing or compiling
///
/// ## Examples
///
/// ### `(assert (not (= true false)))`
/// ```
/// use plat_smt::recorder::recorder::LoggingRecorder;
/// use plat_smt::intern::{EQ_SYM, FALSE_SYM, NOT_SYM, TRUE_SYM};
/// use plat_smt::outer_solver::{StartExpCtx::*, OuterSolver};
/// use plat_smt::euf::{Euf, EufPf};
/// let mut solver = OuterSolver::<(Euf, EufPf, LoggingRecorder, _)>::default();
/// // Use Assert to start since this is an assertion
/// solver.start_exp(NOT_SYM, None, Assert);
/// // Afterwards we use Opt to optimize sub expressions by knowing their position in the whole expression
/// solver.start_exp(EQ_SYM, None, Opt);
/// solver.start_exp(TRUE_SYM, None, Opt);
///  // Use false for independent since this is meant to be a child of the parent expression `=`
/// solver.end_exp().unwrap();
/// solver.start_exp(FALSE_SYM, None, Opt);
/// solver.end_exp().unwrap();
/// solver.end_exp().unwrap();
/// solver.end_exp_take().unwrap();
/// ```
///
/// ### `(declare-fun f (Bool, Bool) Bool)`
/// ```
/// # use plat_smt::recorder::recorder::LoggingRecorder;
/// # use plat_smt::euf::{Euf, EufPf};
/// use plat_smt::intern::{BOOL_SORT, EQ_SYM, FALSE_SYM, NOT_SYM, TRUE_SYM};
/// # use plat_smt::outer_solver::{StartExpCtx::*, OuterSolver, Bound, FnSort };
/// # let mut solver = OuterSolver::<(Euf, EufPf, LoggingRecorder, _)>::default();
/// let f_sym = solver.intern_mut().symbols.intern("f");
/// solver.define(f_sym, Bound::Fn(FnSort::new([BOOL_SORT, BOOL_SORT].into_iter().collect(), BOOL_SORT))).ok().unwrap();
/// ```
///
/// ### `(assert (not (let ((x (f true false))) (f x x))))`
/// ```
/// # use plat_smt::recorder::recorder::LoggingRecorder;
/// # use plat_smt::euf::{Euf, EufPf};
/// use plat_smt::intern::{BOOL_SORT, EQ_SYM, FALSE_SYM, NOT_SYM, TRUE_SYM};
/// # use plat_smt::outer_solver::{StartExpCtx::*, OuterSolver, Bound, FnSort};
/// # let mut solver = OuterSolver::<(Euf, EufPf, LoggingRecorder, _)>::default();
/// # let f_sym = solver.intern_mut().symbols.intern("f");
/// # solver.define(f_sym, Bound::Fn(FnSort::new([BOOL_SORT, BOOL_SORT].into_iter().collect(), BOOL_SORT))).ok().unwrap();
/// let x_sym = solver.intern_mut().symbols.intern("x");
/// solver.start_exp(NOT_SYM, None, Assert);
/// // this is an independent expression not a child of `not` so we need it to be exact
/// solver.start_exp(f_sym, None, Exact);
/// // this is a child of `f` so we can use `Opt` here
/// solver.start_exp(TRUE_SYM, None, Opt);
/// solver.end_exp().unwrap(); // true
/// solver.start_exp(FALSE_SYM, None, Opt);
/// solver.end_exp().unwrap(); // false
/// // we don't want (f true false) to get added as a child of not
/// let ftf = solver.end_exp_take().unwrap(); // (f true false)
/// solver.with_defined(x_sym, ftf, |solver| {
///    solver.start_exp(f_sym, None, Opt);
///    solver.start_exp(x_sym, None, Opt);
///    solver.end_exp().unwrap(); // x
///    solver.start_exp(x_sym, None, Opt);
///    solver.end_exp().unwrap(); // x
///    solver.end_exp().unwrap(); // (f x x)
/// });
/// solver.end_exp_take().unwrap(); // (not (f x x))
/// ```
///
/// ### `(assert (not (f (! (f true false) :named x) x)))`
/// ```
/// # use plat_smt::recorder::recorder::LoggingRecorder;
/// # use plat_smt::euf::{Euf, EufPf};
/// use plat_smt::intern::{BOOL_SORT, EQ_SYM, FALSE_SYM, NOT_SYM, TRUE_SYM};
/// # use plat_smt::outer_solver::{StartExpCtx::*, OuterSolver, Bound, FnSort};
/// # let mut solver = OuterSolver::<(Euf, EufPf, LoggingRecorder, _)>::default();
/// # let f_sym = solver.intern_mut().symbols.intern("f");
/// # solver.define(f_sym, Bound::Fn(FnSort::new([BOOL_SORT, BOOL_SORT].into_iter().collect(), BOOL_SORT))).ok().unwrap();
/// let x_sym = solver.intern_mut().symbols.intern("x");
/// solver.start_exp(NOT_SYM, None, Assert);
/// solver.start_exp(f_sym, None, Opt);
/// // even though this is a child of f, it may be used in other places so we use Exact
/// solver.start_exp(f_sym, None, Exact);
/// solver.start_exp(TRUE_SYM, None, Opt);
/// solver.end_exp().unwrap(); // true
/// solver.start_exp(FALSE_SYM, None, Opt);
/// solver.end_exp().unwrap(); // false
/// let ftf = solver.end_exp_take().unwrap(); // (f true false)
/// // // we do want (f true false) to get added as a child of `f` so we re-inject it
/// solver.inject_exp(ftf);
/// solver.define(x_sym, Bound::Const(ftf)).ok().unwrap();
/// solver.start_exp(x_sym, None, Opt);
/// solver.end_exp().unwrap(); // x
/// solver.end_exp().unwrap(); // (f (f true false) x)
/// solver.end_exp_take().unwrap(); // (not (f (f true false) x))
/// ```
pub struct OuterSolver<L: Logic> {
    inner: WrapSolver<L::Theory, L::R>,
    parser: L::Parser,
    stack: Vec<Frame<L::Exp>>,
    /// List of let bound variable with the old value they are shadowing
    let_bound_stack: Vec<(Symbol, Option<BoundL<L>>)>,
    exp_stack: Vec<L::Exp>,
}

impl<L: Logic> Default for OuterSolver<L> {
    fn default() -> Self {
        let mut res = OuterSolver {
            inner: Default::default(),
            parser: Default::default(),
            stack: Default::default(),
            exp_stack: Default::default(),
            let_bound_stack: Default::default(),
        };
        res.inner
            .bound
            .insert(TRUE_SYM, Bound::Const(BoolExp::TRUE.upcast()));
        res.inner
            .bound
            .insert(FALSE_SYM, Bound::Const(BoolExp::FALSE.upcast()));
        res
    }
}

impl<L: Logic> OuterSolver<L> {
    pub fn dep_checker_act(&mut self, act: impl DepCheckerAction) {
        self.solver_mut().th.arg.recorder.dep_checker_act(act)
    }
    fn optimize_binding(&mut self, name: Symbol, b: Bound<L::Exp>) -> Result<BoundL<L>, ()> {
        match b {
            Bound::Fn(f) => {
                if f.args().is_empty() {
                    match Fresh::<L::Exp>::new_with_sort(name, f.as_fn_sort().ret()) {
                        Ok(fresh) => {
                            let exp = SolverCollapse::<Fresh<L::Exp>, _>::collapse(
                                &mut self.inner,
                                fresh,
                            );
                            self.solver_mut().open(
                                |_, acts| acts.log_def(exp, name, iter::empty::<L::Exp>()),
                                (),
                            );
                            return Ok(Bound::Const(exp));
                        }
                        _ => {}
                    };
                }
                Ok(Bound::Fn(L::FnSort::try_new(f)?))
            }
            Bound::Const(c) => Ok(Bound::Const(c)),
        }
    }

    /// Defines `symbol` to be `bound`,
    /// if it is already defined the old definition replaced is returned
    ///
    /// ## Waring
    /// Defining a symbol as an uninterpreted function and later redefining it as a different
    /// uninterpreted function may lead to unexpected behaviour
    pub fn raw_define(&mut self, symbol: Symbol, bound: Option<BoundL<L>>) -> Option<BoundL<L>> {
        if let Some(bound) = bound {
            self.inner.bound.insert(symbol, bound)
        } else {
            self.inner.bound.remove(&symbol)
        }
    }

    /// Defines `symbol` to be `bound`,
    /// if it is already defined the old definition kept and Err(`bound`)
    pub fn define(&mut self, symbol: Symbol, bound: Bound<L::Exp>) -> Result<(), DefineError<L>> {
        let bound = self
            .optimize_binding(symbol, bound)
            .map_err(|()| DefineError::Unsupported)?;
        let entry = self.inner.bound.entry(symbol);
        match entry {
            Entry::Occupied(_) => Err(DefineError::Exists(bound)),
            Entry::Vacant(vac) => {
                if let Bound::Const(e) = bound {
                    self.inner
                        .solver
                        .open(|_, acts| acts.log_alias(symbol, e), ());
                }
                vac.insert(bound);
                Ok(())
            }
        }
    }

    /// Temporally defines `symbol` to be `bound` for the call to `f`
    /// May shadow a previous definition if one exists
    pub fn with_defined<O>(
        &mut self,
        symbol: Symbol,
        value: L::Exp,
        f: impl FnOnce(&mut Self) -> O,
    ) -> O {
        let old = self.raw_define(symbol, Some(Bound::Const(value)));
        let res = f(self);
        self.raw_define(symbol, old);
        res
    }

    fn defined_symbols(&self) -> impl Iterator<Item = Symbol> + '_ {
        self.inner
            .bound
            .keys()
            .copied()
            .filter(|&k| k != TRUE_SYM && k != FALSE_SYM)
    }

    pub fn definition(&self, sym: Symbol) -> Option<&BoundL<L>> {
        self.inner.bound.get(&sym)
    }

    fn child_context(&self, frame: &Frame<L::Exp>) -> ExprContext<<L as Logic>::Exp> {
        let parent = frame.ctx;
        let f = frame.f;
        if f == LET_SYM {
            return frame.ctx;
        }
        let previous_children = &self.exp_stack[frame.stack_len as usize..];
        self.parser
            .try_sub_ctx(f, previous_children, parent)
            .unwrap_or_default()
    }

    pub fn let_bindings_len(&self) -> u32 {
        self.let_bound_stack.len() as u32
    }
    pub fn add_let_binding(&mut self, name: Symbol, value: L::Exp) {
        self.dep_checker_act(dep_checker::Shadow(name));
        let old = self.raw_define(name, Some(Bound::Const(value)));
        self.let_bound_stack.push((name, old));
    }

    pub(crate) fn pre_add_let_binding(&mut self, name: Symbol, value: L::Exp) {
        self.let_bound_stack.push((name, Some(Bound::Const(value))))
    }

    pub(crate) fn finish_let_bindings_since(&mut self, old_len: u32) {
        let mut let_bound_stack = mem::take(&mut self.let_bound_stack);
        for (name, bound) in &mut let_bound_stack[old_len as usize..] {
            self.dep_checker_act(dep_checker::Shadow(*name));
            *bound = self.raw_define(*name, bound.take())
        }
        self.let_bound_stack = let_bound_stack;
    }

    pub(crate) fn truncate_let_bindings(&mut self, old_len: u32) {
        self.let_bound_stack.truncate(old_len as usize);
    }

    /// Removes let bindings after [`let_bindings_len`] returned `old_len`
    pub fn undo_let_bindings(&mut self, old_len: u32) {
        let mut let_bound_stack = mem::take(&mut self.let_bound_stack);
        for (name, bound) in let_bound_stack.drain(old_len as usize..).rev() {
            self.dep_checker_act(dep_checker::Unshadow(name));
            self.raw_define(name, bound);
        }
        self.let_bound_stack = let_bound_stack;
    }

    pub fn reset_working_exp(&mut self) {
        self.exp_stack.clear();
        self.stack.clear();
        self.undo_let_bindings(0);
        self.quantifier_applier().clear_pending();
    }

    /// Enter a context where the next [`end_exp_take`] will call `undo_let_bindings(old_len)`
    pub fn start_let(&mut self, ctx: StartExpCtx) {
        let stack_len = self.let_bindings_len();
        let ctx = self.resolve_ctx(ctx);
        self.stack.push(Frame {
            ctx,
            f: LET_SYM,
            expected: None,
            stack_len,
        })
    }

    fn resolve_ctx(&self, ctx: StartExpCtx) -> ExprContext<L::Exp> {
        match (ctx, self.stack.last()) {
            (StartExpCtx::Assert | StartExpCtx::AssertOrOpt(_), None) => {
                ExprContext::AssertEq(BoolExp::TRUE.upcast()).into()
            }
            (StartExpCtx::Exact, _) => ExprContext::Exact.into(),
            (StartExpCtx::Opt | StartExpCtx::AssertOrOpt(_), Some(x)) => self.child_context(x),
            (ctx, last) => {
                let not = if last.is_some() { "" } else { " not" };
                panic!("Invalid ctx {ctx:?} when{not} building existing expression")
            }
        }
    }

    /// Starts an expression
    ///
    /// see [`OuterSolver`] documentation for more details
    pub fn start_exp(&mut self, f: Symbol, expected: Option<Sort>, ctx: StartExpCtx) {
        let ctx = self.resolve_ctx(ctx);
        self.stack.push(Frame {
            ctx,
            f,
            expected,
            stack_len: self.exp_stack.len() as u32,
        })
    }

    fn end_exp_inner(
        &mut self,
        f: Symbol,
        ctx: ExprContext<<L as Logic>::Exp>,
        expected: Option<Sort>,
        stack_len: u32,
    ) -> Result<L::Exp, AddSexpError> {
        let children_slice = &mut self.exp_stack[stack_len as usize..];
        let res = self
            .parser
            .try_handle_non_terminal(f, children_slice, &mut self.inner, ctx)
            .unwrap_or(Err(Unbound))?;
        if let Some(expected) = expected {
            if res.sort() != expected {
                return Err(AsSortMismatch {
                    actual: res.sort(),
                    expected,
                });
            }
        }
        Ok(res)
    }

    pub fn try_handle_terminal(
        &mut self,
        terminal: SexpTerminal,
        ctx: StartExpCtx,
    ) -> PfResult<L::Exp> {
        let ctx = self.resolve_ctx(ctx);
        self.parser.handle_terminal(terminal, &mut self.inner, ctx)
    }

    /// Ends an expression
    ///
    /// see [`OuterSolver`] documentation for more details
    pub fn end_exp_take(&mut self) -> Result<L::Exp, (Symbol, AddSexpError)> {
        let Frame {
            ctx,
            f,
            expected,
            stack_len,
        } = self.stack.pop().unwrap();
        if f == LET_SYM {
            self.undo_let_bindings(stack_len);
            return Ok(self.exp_stack.pop().unwrap());
        }
        self.end_exp_take_inner(ctx, f, expected, stack_len)
    }

    #[inline]
    pub(crate) fn end_exp_take_q(&mut self) -> Result<Option<L::Exp>, (Symbol, AddSexpError)> {
        let Frame {
            ctx,
            f,
            expected,
            stack_len,
        } = self.stack.pop().unwrap();
        if f == LET_STAR_SYM {
            self.exp_stack.truncate(stack_len as usize);
            return Ok(None);
        }
        self.end_exp_take_inner(ctx, f, expected, stack_len)
            .map(Some)
    }

    pub(crate) fn in_q_let(&self) -> bool {
        self.stack.last().is_some_and(|x| x.f == LET_STAR_SYM)
    }

    fn end_exp_take_inner(
        &mut self,
        ctx: ExprContext<L::Exp>,
        f: Symbol,
        expected: Option<Sort>,
        stack_len: u32,
    ) -> Result<L::Exp, (Symbol, AddSexpError)> {
        match self.end_exp_inner(f, ctx, expected, stack_len) {
            Ok(x) => {
                info!(
                    "{} => {} in ctx {:?}",
                    util::display_sexp(
                        f.with_intern(self.intern()),
                        self.exp_stack[stack_len as usize..]
                            .iter()
                            .map(|x| x.with_intern(self.intern())),
                    ),
                    x.with_intern(self.intern()),
                    ctx.with_intern(self.intern())
                );
                self.exp_stack.truncate(stack_len as usize);
                Ok(x)
            }
            Err(x) => Err((f, x)),
        }
    }

    /// Adds a child to the current expression
    pub fn inject_exp(&mut self, exp: L::Exp) {
        debug_assert!(!self.stack.is_empty());
        self.exp_stack.push(exp)
    }

    /// Ends and expressions and adds it as a child of the parent expression
    pub fn end_exp(&mut self) -> Result<(), (Symbol, AddSexpError)> {
        let exp = self.end_exp_take()?;
        self.inject_exp(exp);
        Ok(())
    }

    /// Returns an iterator over the values associated with each definition along with the interner
    ///
    /// The definitions are sorted alphabetically by name
    pub fn get_definition_values<'a>(&'a mut self) -> impl BoundDefinitions<Exp = L::Exp> + 'a
    where
        L::Theory: 'static,
        L::R: 'static,
    {
        BoundDefinitionsImpl(self, L::Theory::get_function_info)
    }

    /// Like [`clear`](Solver::clear) but also clears defintions
    pub fn full_clear(&mut self) {
        self.inner.solver.clear();
        self.inner.bound.clear();
        self.reset_working_exp();
        self.inner
            .bound
            .insert(TRUE_SYM, Bound::Const(BoolExp::TRUE.upcast()));
        self.inner
            .bound
            .insert(FALSE_SYM, Bound::Const(BoolExp::FALSE.upcast()));
    }

    pub fn prepare_get_values(&mut self) {
        self.inner
            .solver
            .th
            .prepare_model(PrepareModelKind::GetValues)
    }

    pub fn solver(&self) -> &Solver<L::Theory, L::R> {
        &self.inner.solver
    }

    pub fn solver_mut(&mut self) -> &mut Solver<L::Theory, L::R> {
        &mut self.inner.solver
    }

    pub fn recorder_mut(&mut self) -> &mut L::R {
        &mut self.solver_mut().th.arg.recorder
    }

    pub fn solver_mut_with_def<'a>(
        &'a mut self,
    ) -> (
        &'a mut Solver<L::Theory, L::R>,
        impl Fn(Symbol) -> Option<&'a BoundL<L>>,
    ) {
        let definition = |x| self.inner.bound.get(&x);
        (&mut self.inner.solver, definition)
    }

    pub fn intern(&self) -> &InternInfo {
        self.inner.solver.intern()
    }

    pub fn intern_mut(&mut self) -> &mut InternInfo {
        self.inner.solver.intern_mut()
    }

    pub(crate) fn quantifier_applier(&mut self) -> &mut L::Q {
        self.inner.solver.th.quantifier_applier()
    }

    pub(crate) fn quantifier_builder(&mut self, qvars: u32) -> QuantifierBuilder<'_, L> {
        let ctx = self.quantifier_applier().create_context(qvars);
        QuantifierBuilder { solver: self, ctx }
    }
}

pub struct QuantifierBuilder<'a, L: Logic> {
    solver: &'a mut OuterSolver<L>,
    ctx: QuantContext,
}

impl<'a, L: Logic> Deref for QuantifierBuilder<'a, L> {
    type Target = OuterSolver<L>;
    fn deref(&self) -> &Self::Target {
        &self.solver
    }
}

impl<'a, L: Logic> DerefMut for QuantifierBuilder<'a, L> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.solver
    }
}

impl<'a, L: Logic> QuantifierBuilder<'a, L> {
    ///
    /// Let
    /// * `(<s>` denote `Instruction::Start(s)` e.g. `(and` for `Instruction::Start(AND_SYM)`
    /// * `)` denotes `Instruction::End`
    /// * `@c{<e>}` denote `Instruction::Var(QuantExp::Exp(e))`
    /// * `q!<v>` denote `Instruction::Var(QuantExp::QuantVar(v))`
    /// * `l!<v>` denote `Instruction::Var(QuantExp::LetVar(v))`
    ///
    /// When translating `let` the special `Instruction::Start(LET_STAR)`/`(let*` instruction is used
    /// It is not counted as argument to its parent and its children are incrementally bound for `LetVar` instructions
    ///
    /// `(forall ((x Int) (y Int)) (let ((z (max x y))) (and (>= z x) (>= z y))))` would translate to
    /// `(let*`, `(max`, `q!0`, `q!1`, `)`, `)`, `(and`, `(>=`, `l!0`, `q!0`, `)`, `(>=`, `l!0`, `q!1`, `)`, `)`
    ///
    /// `(forall ((x Int) (y Int)) (not (let ((z (max x y))) (or (< z x) (< z y)))))` would translate to
    /// (leaving out commas) `(not (let* (max q!0 q!1)) (and (< l!0 q!0 ) (< l!0 q!1)))`
    pub fn add_instruction(&mut self, instruction: Instruction<QuantExp<L::Exp>>) {
        self.solver
            .quantifier_applier()
            .add_instruction(&self.ctx, instruction);
    }

    pub fn bind(self, syms: impl Iterator<Item = Symbol> + Clone, block: bool) {
        #[cfg(debug_assertions)]
        syms.clone().for_each(|x| {
            let intern = self.solver.intern();
            if let Some(Bound::Fn(f)) = self.solver.inner.bound.get(&x) {
                debug_assert_eq!(
                    self.ctx.qvars as usize,
                    f.as_fn_sort().args().len(),
                    "Symbol {} has incorrect number of args",
                    x.with_intern(intern)
                )
            } else {
                debug_assert!(
                    false,
                    "Symbol {} bound to quantifier is not a function",
                    x.with_intern(intern)
                )
            }
        });
        info!(
            "Adding quantifier to {:?}:{self:?}",
            DebugIter(syms.clone().map(|x| x.with_intern(self.solver.intern())))
        );

        self.solver.quantifier_applier().bind_instructions(
            &self.ctx,
            syms.map(Either::Left),
            block,
        );
    }

    pub fn bind_to_sort(self, sort: Sort) {
        debug_assert_eq!(self.ctx.qvars, 1);
        info!(
            "Adding quantifier to sort {}:{self:?}",
            sort.with_intern(self.solver.intern())
        );
        self.solver.quantifier_applier().bind_instructions(
            &self.ctx,
            [Either::Right(sort)].into_iter(),
            false,
        );
    }
}

impl<'a, L: Logic> Debug for QuantifierBuilder<'a, L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        let q = self.solver.inner.solver.th.quantifier_applier_shr();
        q.debug_cxt(&self.ctx, self.solver.inner.solver.intern(), f)
    }
}

pub enum BoundDefinition<'a, F, UExp> {
    Const(UExp),
    Fn(&'a FnSort, F),
}

pub trait BoundDefinitions {
    type Exp;
    type FunctionInfo<'a>: FunctionAssignmentT<Exp = Self::Exp>;

    fn for_each(
        &mut self,
        f: impl FnMut(Symbol, BoundDefinition<Self::FunctionInfo<'_>, Self::Exp>, &InternInfo),
    );
}

struct BoundDefinitionsImpl<'a, L: Logic, Id>(&'a mut OuterSolver<L>, Id);

trait FnAssoc<In> {
    type Out;

    fn apply(&self, x: In, s: Symbol) -> Self::Out;
}

impl<I, O, F: Fn(I, Symbol) -> O> FnAssoc<I> for F {
    type Out = O;

    fn apply(&self, x: I, s: Symbol) -> Self::Out {
        self(x, s)
    }
}

impl<'b, L: Logic, F: for<'a> FnAssoc<&'a L::Theory, Out: FunctionAssignmentT<Exp = L::Exp>>>
    BoundDefinitions for BoundDefinitionsImpl<'b, L, F>
where
    L::Theory: 'static,
{
    type Exp = L::Exp;
    type FunctionInfo<'a> = <F as FnAssoc<&'a L::Theory>>::Out;

    fn for_each(
        &mut self,
        mut f: impl FnMut(Symbol, BoundDefinition<Self::FunctionInfo<'_>, Self::Exp>, &InternInfo),
    ) {
        let mut syms: Vec<_> = self.0.defined_symbols().collect();
        syms.sort_unstable_by_key(|sym| self.0.intern().symbols.resolve(*sym));
        let solver = &mut self.0.inner.solver;
        solver.th.prepare_model(PrepareModelKind::GetModel);
        let bound = &self.0.inner.bound;
        syms.into_iter().for_each(|sym| {
            let val = bound.get(&sym).unwrap();
            match val {
                Bound::Const(exp) => f(
                    sym,
                    BoundDefinition::Const(SolverCollapse::<L::Exp, _>::collapse(
                        &mut *solver,
                        *exp,
                    )),
                    solver.intern(),
                ),
                Bound::Fn(s) => f(
                    sym,
                    BoundDefinition::Fn(s.as_fn_sort(), self.1.apply(&solver.th, sym)),
                    solver.intern(),
                ),
            }
        })
    }
}
