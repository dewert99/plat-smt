use crate::collapse::ExprContext;
use crate::exp::Fresh;
use crate::full_theory::{FullTheory, FunctionAssignmentT, PrepareModelKind};
use crate::intern::*;
use crate::parser_fragment::{ParserFragment, PfResult};
use crate::recorder::Recorder;
use crate::solver::{SolverCollapse, SolverWithBound};
use crate::theory::{TheoryArg, TheoryArgT};
use crate::util::HashMap;
use crate::AddSexpError::{AsSortMismatch, Unbound};
use crate::{
    collapse, util, AddSexpError, BoolExp, ExpLike, HasSort, Solver, Sort, SubExp, SuperExp,
};
use alloc::vec::Vec;
use hashbrown::hash_map::Entry;
use log::info;
use std::iter;

pub use crate::full_theory::{FnSort, MaybeFnSort};
use crate::parser::SexpTerminal;
use crate::recorder::dep_checker::DepCheckerAction;

#[allow(type_alias_bounds)]
type WrapSolver<L: Logic> = SolverWithBound<Solver<L::Theory, L::R>, HashMap<Symbol, BoundL<L>>>;

pub trait Logic: Sized {
    type Exp: SuperExp<BoolExp, Self::EM> + ExpLike;

    type FnSort: MaybeFnSort;

    type LevelMarker: Clone;

    type Theory: FullTheory<Self::R, Exp = Self::Exp, FnSort = Self::FnSort, LevelMarker = Self::LevelMarker>
        + for<'a> collapse::Collapse<Self::Exp, TheoryArg<'a, Self::LevelMarker, Self::R>, Self::CM>
        + for<'a> collapse::Collapse<
            Fresh<Self::Exp>,
            TheoryArg<'a, Self::LevelMarker, Self::R>,
            Self::CM,
        >;

    type RLevelMarker: Clone;

    type R: Recorder<LevelMarker = Self::RLevelMarker>;
    type Parser: ParserFragment<Self::Exp, WrapSolver<Self>, Self::M>;

    type EM;

    type CM;
    type M;
}

impl<
        R: Recorder,
        M,
        EM,
        CM,
        Th: FullTheory<R>
            + for<'a> collapse::Collapse<Th::Exp, TheoryArg<'a, Th::LevelMarker, R>, CM>
            + for<'a> collapse::Collapse<Fresh<Th::Exp>, TheoryArg<'a, Th::LevelMarker, R>, CM>,
        P: ParserFragment<
            Th::Exp,
            SolverWithBound<Solver<Th, R>, HashMap<Symbol, Bound<Th::Exp, Th::FnSort>>>,
            M,
        >,
    > Logic for (Th, P, R, (M, EM, CM))
where
    Th::Exp: SuperExp<BoolExp, EM>,
{
    type Exp = Th::Exp;
    type FnSort = Th::FnSort;
    type LevelMarker = Th::LevelMarker;

    type Theory = Th;

    type RLevelMarker = R::LevelMarker;
    type R = R;
    type Parser = P;
    type EM = EM;
    type CM = CM;

    type M = M;
}

#[derive(Clone)]
pub enum Bound<Exp, Fn = FnSort> {
    /// An uninterpreted function with the given sort
    Fn(Fn),
    /// A constant with the given value
    Const(Exp),
}

pub type BoundL<L> = Bound<<L as Logic>::Exp, <L as Logic>::FnSort>;

/// Requirements on the `Exp` created
#[derive(Debug, Copy, Clone)]
pub enum StartExpCtx {
    /// Must be equivalent
    Exact,
    /// Will be asserted (only available when starting a new expression)
    Assert,
    /// Optimize to satisfy parent constraints (only available when continuing an existing expression)
    Opt,
}
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
    inner: WrapSolver<L>,
    parser: L::Parser,
    stack: Vec<Frame<L::Exp>>,
    exp_stack: Vec<L::Exp>,
}

impl<L: Logic> Default for OuterSolver<L> {
    fn default() -> Self {
        let mut res = OuterSolver {
            inner: Default::default(),
            parser: Default::default(),
            stack: Default::default(),
            exp_stack: Default::default(),
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
        let previous_children = &self.exp_stack[frame.stack_len as usize..];
        self.parser
            .try_sub_ctx(f, previous_children, parent)
            .unwrap_or_default()
    }

    pub fn reset_working_exp(&mut self) {
        self.exp_stack.clear();
        self.stack.clear();
    }

    fn resolve_ctx(&self, ctx: StartExpCtx) -> ExprContext<L::Exp> {
        match (ctx, self.stack.last()) {
            (StartExpCtx::Assert, None) => ExprContext::AssertEq(BoolExp::TRUE.upcast()).into(),
            (StartExpCtx::Exact, _) => ExprContext::Exact.into(),
            (StartExpCtx::Opt, Some(x)) => self.child_context(x),
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
