use crate::egraph::Children;
use crate::intern::*;
use crate::util::{extend_result, pairwise_sym, DefaultHashBuilder};
use crate::{util, BoolExp, Conjunction, Disjunction, Exp, HasSort, Solver, Sort};
use alloc::vec::Vec;
use hashbrown::hash_map::{Entry, HashMap};
use log::{debug, info};
use plat_egg::Id;
use smallvec::SmallVec;
use std::{iter, mem};

#[derive(Clone)]
pub struct FnSort {
    args: SmallVec<[Sort; 5]>,
    ret: Sort,
}

impl FnSort {
    pub fn new(args: SmallVec<[Sort; 5]>, ret: Sort) -> Self {
        FnSort { args, ret }
    }

    pub fn try_new<E>(args: impl Iterator<Item = Result<Sort, E>>, ret: Sort) -> Result<Self, E> {
        Ok(FnSort {
            args: args.collect::<Result<_, E>>()?,
            ret,
        })
    }

    pub fn args(&self) -> &[Sort] {
        &self.args
    }

    pub fn ret(&self) -> Sort {
        self.ret
    }
}

#[derive(Clone)]
pub enum Bound {
    /// An uninterpreted function with the given sort
    Fn(FnSort),
    /// A constant with the given value
    Const(Exp),
}

/// Requirements on the `Exp` returned by `add_sexp`
#[derive(Copy, Clone, Debug, Default)]
enum ExprContext {
    /// the `Exp` must be equivalent to the s-expression
    #[default]
    Exact,
    /// assert the s-expression xor negate (the returned `Exp` will be !negate) `
    Assert {
        negate: bool,
    },
    Approx(bool),
}

impl ExprContext {
    fn to_approx(self) -> Option<bool> {
        match self {
            ExprContext::Assert { negate: a } | ExprContext::Approx(a) => Some(a),
            _ => None,
        }
    }
}

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
struct Frame {
    ctx: ExprContext,
    f: Symbol,
    expected: Option<Sort>,
    stack_len: u32,
}

/// Wrapper around solver more conducive to building up expressions such as from parsing or compiling
///
/// ## Examples
///
/// ### `(assert (not (= true false)))`
/// ```
/// use plat_smt::intern::{EQ_SYM, FALSE_SYM, NOT_SYM, TRUE_SYM};
/// use plat_smt::outer_solver::{StartExpCtx::*, OuterSolver};
/// let mut solver = OuterSolver::default();
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
/// # use plat_smt::intern::{BOOL_SORT, EQ_SYM, FALSE_SYM, NOT_SYM, TRUE_SYM};
/// # use plat_smt::outer_solver::{StartExpCtx::*, OuterSolver, Bound, FnSort};
/// # let mut solver = OuterSolver::default();
/// let f_sym = solver.intern_mut().symbols.intern("f");
/// solver.define(f_sym, Bound::Fn(FnSort::new([BOOL_SORT, BOOL_SORT].into_iter().collect(), BOOL_SORT))).ok().unwrap();
/// ```
///
/// ### `(assert (not (let ((x (f true false))) (f x x))))`
/// ```
/// # use plat_smt::intern::{BOOL_SORT, EQ_SYM, FALSE_SYM, NOT_SYM, TRUE_SYM};
/// # use plat_smt::outer_solver::{StartExpCtx::*, OuterSolver, Bound, FnSort};
/// # let mut solver = OuterSolver::default();
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
/// # use plat_smt::intern::{BOOL_SORT, EQ_SYM, FALSE_SYM, NOT_SYM, TRUE_SYM};
/// # use plat_smt::outer_solver::{StartExpCtx::*, OuterSolver, Bound, FnSort};
/// # let mut solver = OuterSolver::default();
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
pub struct OuterSolver {
    inner: Solver,
    bound: HashMap<Symbol, Bound, DefaultHashBuilder>,
    id_buf: Vec<Id>,
    stack: Vec<Frame>,
    exp_stack: Vec<Exp>,
}

impl Default for OuterSolver {
    fn default() -> Self {
        let mut bound = HashMap::default();
        bound.insert(TRUE_SYM, Bound::Const(BoolExp::TRUE.into()));
        bound.insert(FALSE_SYM, Bound::Const(BoolExp::FALSE.into()));
        OuterSolver {
            inner: Solver::default(),
            bound,
            id_buf: Default::default(),
            stack: Default::default(),
            exp_stack: Default::default(),
        }
    }
}

impl OuterSolver {
    fn optimize_binding(&mut self, name: Symbol, b: Bound) -> Bound {
        match b {
            Bound::Fn(FnSort { args, ret }) if args.is_empty() => {
                let exp = if ret == BOOL_SORT {
                    self.inner.fresh_bool().into()
                } else {
                    self.inner.sorted_fn(name, Children::new(), ret)
                };
                debug!(
                    "{} is bound to {}",
                    name.with_intern(self.intern()),
                    exp.with_intern(self.intern())
                );
                Bound::Const(exp)
            }
            _ => b,
        }
    }

    /// Defines `symbol` to be `bound`,
    /// if it is already defined the old definition replaced is returned
    ///
    /// ## Waring
    /// Defining a symbol as an uninterpreted function and later redefining it as a different
    /// uninterpreted function may lead to unexpected behaviour
    pub fn raw_define(&mut self, symbol: Symbol, bound: Option<Bound>) -> Option<Bound> {
        if let Some(bound) = bound {
            self.bound.insert(symbol, bound)
        } else {
            self.bound.remove(&symbol)
        }
    }

    /// Defines `symbol` to be `bound`,
    /// if it is already defined the old definition kept and Err(`bound`)
    pub fn define(&mut self, symbol: Symbol, bound: Bound) -> Result<(), Bound> {
        let bound = self.optimize_binding(symbol, bound);
        let entry = self.bound.entry(symbol);
        match entry {
            Entry::Occupied(_) => Err(bound),
            Entry::Vacant(vac) => {
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
        value: Exp,
        f: impl FnOnce(&mut Self) -> O,
    ) -> O {
        let old = self.raw_define(symbol, Some(Bound::Const(value)));
        let res = f(self);
        self.raw_define(symbol, old);
        res
    }

    fn defined_symbols(&self) -> impl Iterator<Item = Symbol> + '_ {
        self.bound
            .keys()
            .copied()
            .filter(|&k| k != TRUE_SYM && k != FALSE_SYM)
    }

    pub fn definition(&self, sym: Symbol) -> Option<&Bound> {
        self.bound.get(&sym)
    }

    fn child_context(&self, parent: ExprContext, f: Symbol) -> ExprContext {
        use ExprContext::*;
        match (parent, f) {
            (Assert { negate }, NOT_SYM) => Assert { negate: !negate },
            (Approx(a), NOT_SYM) => Approx(!a),
            (Assert { negate: false }, AND_SYM) => Assert { negate: false },
            (Assert { negate: true }, OR_SYM) => Assert { negate: true },
            (Assert { negate: a } | Approx(a), AND_SYM | OR_SYM) => Approx(a),
            _ => Exact,
        }
    }

    pub fn reset_working_exp(&mut self) {
        self.exp_stack.clear();
        self.stack.clear();
    }

    /// Starts an expression
    ///
    /// see [`OuterSolver`] documentation for more details
    pub fn start_exp(&mut self, f: Symbol, expected: Option<Sort>, ctx: StartExpCtx) {
        let ctx = match (ctx, self.stack.last()) {
            (StartExpCtx::Assert, None) => ExprContext::Assert { negate: false },
            (StartExpCtx::Exact, _) => ExprContext::Exact,
            (StartExpCtx::Opt, Some(x)) => self.child_context(x.ctx, x.f),
            (ctx, last) => {
                let not = if last.is_some() { "" } else { " not" };
                panic!("Invalid ctx {ctx:?} when{not} building existing expression")
            }
        };
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
        ctx: ExprContext,
        expected: Option<Sort>,
        stack_len: u32,
    ) -> Result<Exp, AddSexpError> {
        let mut base_children = self.exp_stack[stack_len as usize..]
            .iter()
            .copied()
            .enumerate()
            .map(IndexExp);
        let children = &mut base_children;
        let res: Exp = match f {
            AND_SYM => {
                if matches!(ctx, ExprContext::Assert { negate: false }) {
                    children
                        .map(|x| {
                            self.inner.assert(x.as_bool()?);
                            Ok(())
                        })
                        .collect::<Result<(), AddSexpError>>()?;
                    BoolExp::TRUE.into()
                } else {
                    let mut c: Conjunction = self.inner.new_junction();
                    extend_result(&mut c, children.map(|x| x.as_bool()))?;
                    self.inner.collapse_bool_approx(c, ctx.to_approx()).into()
                }
            }
            OR_SYM => {
                if matches!(ctx, ExprContext::Assert { negate: true }) {
                    children
                        .map(|x| {
                            self.inner.assert(!x.as_bool()?);
                            Ok(())
                        })
                        .collect::<Result<(), AddSexpError>>()?;
                    BoolExp::FALSE.into()
                } else {
                    let mut d: Disjunction = self.inner.new_junction();
                    extend_result(&mut d, children.map(|x| x.as_bool()))?;
                    self.inner.collapse_bool_approx(d, ctx.to_approx()).into()
                }
            }
            NOT_SYM => {
                let [arg] = mandatory_args(children)?;
                (!arg.as_bool()?).into()
            }
            IMP_SYM => {
                let mut d: Disjunction = self.inner.new_junction();
                let [arg] = mandatory_args(children)?;
                let mut last = arg.as_bool()?;
                let other = children.map(|x| Ok(!mem::replace(&mut last, x.as_bool()?)));
                extend_result(&mut d, other)?;
                d.push(last);
                self.inner.collapse_bool(d).into()
            }
            XOR_SYM => children
                .map(|x| x.as_bool())
                .fold(Ok(BoolExp::FALSE), |b1, b2| Ok(self.inner.xor(b1?, b2?)))?
                .into(),
            EQ_SYM => {
                let mut c: Conjunction = self.inner.new_junction();
                let [exp1] = mandatory_args(children)?;
                let id1 = self.inner.id(exp1.exp());
                let sort = exp1.exp().sort();
                extend_result(
                    &mut c,
                    children.map(|x| {
                        let id2 = self.inner.id(x.expect_sort(sort)?);
                        match ctx {
                            ExprContext::Assert { negate: false } => {
                                self.inner.assert_raw_eq(id1, id2);
                                Ok(BoolExp::TRUE.into())
                            }
                            _ => Ok(self.inner.raw_eq(id1, id2)),
                        }
                    }),
                )?;
                self.inner.collapse_bool(c).into()
            }
            DISTINCT_SYM => {
                let [exp1] = mandatory_args(children)?;
                let sort = exp1.exp().sort();
                let children =
                    iter::once(Ok(exp1.exp())).chain(children.map(|x| x.expect_sort(sort)));
                let mut ids = mem::take(&mut self.id_buf);
                ids.clear();
                extend_result(&mut ids, children.map(|child| Ok(self.inner.id(child?))))?;
                let res = match ctx {
                    ExprContext::Assert { negate: false } => {
                        self.inner.assert_distinct(ids.iter().copied());
                        BoolExp::TRUE.into()
                    }
                    _ => {
                        let mut c: Conjunction = self.inner.new_junction();
                        c.extend(
                            pairwise_sym(&ids).map(|(id1, id2)| !self.inner.raw_eq(*id1, *id2)),
                        );
                        self.inner.collapse_bool(c).into()
                    }
                };
                self.id_buf = ids;
                res
            }
            ITE_SYM | IF_SYM => {
                let [i, t, e] = mandatory_args(children)?;

                self.inner
                    .ite(i.as_bool()?, t.exp(), e.exp())
                    .map_err(|(expected, actual)| SortMismatch {
                        actual,
                        expected,
                        arg_n: 2,
                    })?
            }
            sym => match self.bound.get(&sym) {
                None => return Err(Unbound),
                Some(Bound::Const(c)) => {
                    if let (ExprContext::Assert { negate }, Some(b)) = (ctx, c.as_bool()) {
                        self.inner.assert(b ^ negate);
                        BoolExp::from_bool(!negate).into()
                    } else {
                        self.inner.canonize(*c)
                    }
                }
                Some(Bound::Fn(f)) => {
                    let children: Children = children
                        .zip(&f.args)
                        .map(|(arg, sort)| Ok(self.inner.id(arg.expect_sort(*sort)?)))
                        .collect::<Result<_, AddSexpError>>()?;
                    if children.len() < f.args.len() {
                        return Err(MissingArgument {
                            actual: children.len(),
                            expected: f.args.len(),
                        });
                    }
                    if let (ExprContext::Assert { negate }, BOOL_SORT) = (ctx, f.ret) {
                        self.inner.assert_bool_fn(sym, children, negate);
                        BoolExp::from_bool(!negate).into()
                    } else {
                        self.inner.sorted_fn(sym, children, f.ret)
                    }
                }
            },
        };
        finish_iter(base_children)?;
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

    /// Ends an expression
    ///
    /// see [`OuterSolver`] documentation for more details
    pub fn end_exp_take(&mut self) -> Result<Exp, (Symbol, AddSexpError)> {
        let Frame {
            ctx,
            f,
            expected,
            stack_len,
        } = self.stack.pop().unwrap();
        match self.end_exp_inner(f, ctx, expected, stack_len) {
            Ok(x) => {
                info!(
                    "{} => {} in ctx {ctx:?}",
                    util::display_sexp(
                        f.with_intern(&self.intern()),
                        self.exp_stack[stack_len as usize..]
                            .iter()
                            .map(|x| x.with_intern(&self.intern())),
                    ),
                    x.with_intern(&self.intern())
                );
                self.exp_stack.truncate(stack_len as usize);
                Ok(x)
            }
            Err(x) => Err((f, x)),
        }
    }

    /// Adds a child to the current expression
    pub fn inject_exp(&mut self, exp: Exp) {
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
    pub fn get_definition_values(
        &mut self,
    ) -> (
        &InternInfo,
        impl Iterator<Item = (Symbol, BoundDefinition<FunctionAssignment!['_]>)>,
    ) {
        let mut syms: Vec<_> = self.defined_symbols().collect();
        syms.sort_unstable_by_key(|sym| self.intern().symbols.resolve(*sym));
        let (function_info, inner) = self.inner.function_info();
        let bound = &self.bound;
        let iter = syms.into_iter().map(move |sym| {
            let val = bound.get(&sym).unwrap();
            match val {
                Bound::Const(exp) => (sym, BoundDefinition::Const(inner.canonize(*exp))),
                Bound::Fn(f) => (sym, BoundDefinition::Fn(f, function_info.get(sym))),
            }
        });
        (&inner.intern, iter)
    }

    /// Like [`clear`](Solver::clear) but also clears defintions
    pub fn full_clear(&mut self) {
        self.inner.clear();
        self.bound.clear();
        self.reset_working_exp();
        self.bound
            .insert(TRUE_SYM, Bound::Const(BoolExp::TRUE.into()));
        self.bound
            .insert(FALSE_SYM, Bound::Const(BoolExp::FALSE.into()));
    }

    pub fn solver(&self) -> &Solver {
        &self.inner
    }

    pub fn solver_mut(&mut self) -> &mut Solver {
        &mut self.inner
    }

    pub fn intern(&self) -> &InternInfo {
        &self.inner.intern
    }

    pub fn intern_mut(&mut self) -> &mut InternInfo {
        &mut self.inner.intern
    }
}

pub enum BoundDefinition<'a, F> {
    Const(Exp),
    Fn(&'a FnSort, F),
}

#[derive(Debug)]
pub enum AddSexpError {
    SortMismatch {
        arg_n: usize,
        actual: Sort,
        expected: Sort,
    },
    AsSortMismatch {
        actual: Sort,
        expected: Sort,
    },
    MissingArgument {
        actual: usize,
        expected: usize,
    },
    ExtraArgument {
        expected: usize,
    },
    Unbound,
}
use crate::euf::FunctionAssignment;
use AddSexpError::*;

#[derive(Copy, Clone)]
pub(crate) struct IndexExp(pub(crate) (usize, Exp));

impl IndexExp {
    pub(crate) fn exp(self) -> Exp {
        self.0 .1
    }

    pub(crate) fn sort_mismatch(self, expected: Sort) -> AddSexpError {
        SortMismatch {
            arg_n: self.0 .0,
            actual: self.exp().sort(),
            expected,
        }
    }

    pub(crate) fn expect_sort(self, expected: Sort) -> Result<Exp, AddSexpError> {
        if self.exp().sort() != expected {
            Err(self.sort_mismatch(expected))
        } else {
            Ok(self.exp())
        }
    }

    pub(crate) fn as_bool(self) -> Result<BoolExp, AddSexpError> {
        self.exp().as_bool().ok_or(self.sort_mismatch(BOOL_SORT))
    }
}

pub(crate) fn mandatory_args<const N: usize>(
    iter: &mut impl Iterator<Item = IndexExp>,
) -> Result<[IndexExp; N], AddSexpError> {
    let mut res = Ok(());

    let arr = core::array::from_fn(|i| match iter.next() {
        Some(x) => x,
        None => {
            res = Err(MissingArgument {
                expected: N,
                actual: i,
            });
            IndexExp((0, BoolExp::TRUE.into()))
        }
    });
    res?;
    Ok(arr)
}

pub(crate) fn finish_iter(mut iter: impl Iterator<Item = IndexExp>) -> Result<(), AddSexpError> {
    match iter.next() {
        Some(x) => Err(ExtraArgument { expected: x.0 .0 }),
        None => Ok(()),
    }
}
