use crate::intern::*;
use crate::util::{extend_result, DefaultHashBuilder};
use crate::{util, Approx, BoolExp, Conjunction, Disjunction, Exp, HasSort, Solver, Sort};
use alloc::borrow::Cow;
use alloc::vec::Vec;
use hashbrown::hash_map::{Entry, HashMap};
use log::{debug, info};
use smallvec::SmallVec;
use std::mem;

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
pub enum Bound<UExp> {
    /// An uninterpreted function with the given sort
    Fn(FnSort),
    /// A constant with the given value
    Const(Exp<UExp>),
}

/// Requirements on the `Exp` returned by `add_sexp`
#[derive(Copy, Clone, Debug, Default)]
enum ExprContext<UExp> {
    /// the `Exp` must be equivalent to the s-expression
    #[default]
    Exact,
    AssertEq(Exp<UExp>, bool),
    Approx(bool),
}

impl<UExp> ExprContext<UExp> {
    fn to_approx(self) -> Approx {
        match self {
            ExprContext::Approx(a) => Approx::Approx(a),
            ExprContext::AssertEq(Exp::Bool(BoolExp::TRUE), _) => Approx::Approx(false),
            ExprContext::AssertEq(Exp::Bool(BoolExp::FALSE), _) => Approx::Approx(true),
            _ => Approx::Exact,
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
struct Frame<UExp> {
    ctx: ExprContext<UExp>,
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
/// use plat_smt::euf::Euf;
/// let mut solver = OuterSolver::<Euf>::default();
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
/// # use plat_smt::euf::Euf;
/// use plat_smt::intern::{BOOL_SORT, EQ_SYM, FALSE_SYM, NOT_SYM, TRUE_SYM};
/// # use plat_smt::outer_solver::{StartExpCtx::*, OuterSolver, Bound, FnSort};
/// # let mut solver = OuterSolver::<Euf>::default();
/// let f_sym = solver.intern_mut().symbols.intern("f");
/// solver.define(f_sym, Bound::Fn(FnSort::new([BOOL_SORT, BOOL_SORT].into_iter().collect(), BOOL_SORT))).ok().unwrap();
/// ```
///
/// ### `(assert (not (let ((x (f true false))) (f x x))))`
/// ```
/// # use plat_smt::euf::Euf;
/// use plat_smt::intern::{BOOL_SORT, EQ_SYM, FALSE_SYM, NOT_SYM, TRUE_SYM};
/// # use plat_smt::outer_solver::{StartExpCtx::*, OuterSolver, Bound, FnSort};
/// # let mut solver = OuterSolver::<Euf>::default();
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
/// # use plat_smt::euf::Euf;
/// use plat_smt::intern::{BOOL_SORT, EQ_SYM, FALSE_SYM, NOT_SYM, TRUE_SYM};
/// # use plat_smt::outer_solver::{StartExpCtx::*, OuterSolver, Bound, FnSort};
/// # let mut solver = OuterSolver::<Euf>::default();
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
pub struct OuterSolver<Euf: EufT> {
    inner: Solver<Euf>,
    bound: HashMap<Symbol, Bound<Euf::UExp>, DefaultHashBuilder>,
    stack: Vec<Frame<Euf::UExp>>,
    exp_stack: Vec<Exp<Euf::UExp>>,
}

impl<Euf: EufT> Default for OuterSolver<Euf> {
    fn default() -> Self {
        let mut bound = HashMap::default();
        bound.insert(TRUE_SYM, Bound::Const(BoolExp::TRUE.into()));
        bound.insert(FALSE_SYM, Bound::Const(BoolExp::FALSE.into()));
        OuterSolver {
            inner: Solver::default(),
            bound,
            stack: Default::default(),
            exp_stack: Default::default(),
        }
    }
}

impl<Euf: EufT> OuterSolver<Euf> {
    fn optimize_binding(&mut self, name: Symbol, b: Bound<Euf::UExp>) -> Bound<Euf::UExp> {
        match &b {
            Bound::Fn(FnSort { args, ret }) if args.is_empty() => {
                let exp = if *ret == BOOL_SORT {
                    self.inner.fresh_bool().into()
                } else {
                    match self.inner.sorted_fn(name, [], *ret) {
                        Ok(x) => x,
                        Err(_) => return b,
                    }
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
    pub fn raw_define(
        &mut self,
        symbol: Symbol,
        bound: Option<Bound<Euf::UExp>>,
    ) -> Option<Bound<Euf::UExp>> {
        if let Some(bound) = bound {
            self.bound.insert(symbol, bound)
        } else {
            self.bound.remove(&symbol)
        }
    }

    /// Defines `symbol` to be `bound`,
    /// if it is already defined the old definition kept and Err(`bound`)
    pub fn define(
        &mut self,
        symbol: Symbol,
        bound: Bound<Euf::UExp>,
    ) -> Result<(), Bound<Euf::UExp>> {
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
        value: Exp<Euf::UExp>,
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

    pub fn definition(&self, sym: Symbol) -> Option<&Bound<Euf::UExp>> {
        self.bound.get(&sym)
    }

    fn child_context(&self, frame: &Frame<Euf::UExp>) -> ExprContext<Euf::UExp> {
        use ExprContext::*;
        let parent = frame.ctx;
        let f = frame.f;
        match (parent, f) {
            (AssertEq(Exp::Bool(b), negated), NOT_SYM) => AssertEq(Exp::Bool(!b), !negated),
            (Approx(a), NOT_SYM) => Approx(!a),
            (AssertEq(Exp::Bool(BoolExp::TRUE), _), AND_SYM) => {
                AssertEq(Exp::Bool(BoolExp::TRUE), false)
            }
            (AssertEq(Exp::Bool(BoolExp::FALSE), _), OR_SYM) => {
                AssertEq(Exp::Bool(BoolExp::FALSE), false)
            }
            (AssertEq(Exp::Bool(BoolExp::TRUE), _), EQ_SYM) => {
                match self.exp_stack.get(frame.stack_len as usize) {
                    None => Exact,
                    Some(in_eq) => AssertEq(self.inner.canonize(*in_eq), false),
                }
            }
            (parent, AND_SYM | OR_SYM) => match parent.to_approx() {
                crate::Approx::Exact => Exact,
                crate::Approx::Approx(b) => Approx(b),
            },
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
            (StartExpCtx::Assert, None) => ExprContext::AssertEq(Exp::Bool(BoolExp::TRUE), false),
            (StartExpCtx::Exact, _) => ExprContext::Exact,
            (StartExpCtx::Opt, Some(x)) => self.child_context(x),
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
        ctx: ExprContext<Euf::UExp>,
        expected: Option<Sort>,
        stack_len: u32,
    ) -> Result<Exp<Euf::UExp>, AddSexpError> {
        let children_slice = &mut self.exp_stack[stack_len as usize..];
        let mut base_children = children_slice
            .iter()
            .copied()
            .enumerate()
            .map(IndexExp::<Euf::UExp>);
        let children = &mut base_children;
        let res: Exp<Euf::UExp> = match f {
            AND_SYM => {
                let mut c: Conjunction = self.inner.new_junction();
                extend_result(&mut c, children.map(|x| x.as_bool()))?;
                if let ExprContext::AssertEq(Exp::Bool(b), _) = ctx {
                    self.inner.assert_junction_eq(c, b);
                    b.into()
                } else {
                    self.inner.collapse_bool_approx(c, ctx.to_approx()).into()
                }
            }
            OR_SYM => {
                let mut d: Disjunction = self.inner.new_junction();
                extend_result(&mut d, children.map(|x| x.as_bool()))?;
                if let ExprContext::AssertEq(Exp::Bool(b), _) = ctx {
                    self.inner.assert_junction_eq(d, b);
                    b.into()
                } else {
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
                let other =
                    children.map(|x| Ok::<_, AddSexpError>(!mem::replace(&mut last, x.as_bool()?)));
                extend_result(&mut d, other)?;
                d.push(last);
                self.inner.collapse_bool_approx(d, ctx.to_approx()).into()
            }
            XOR_SYM => {
                let child_len = children.len();
                let first_res = if child_len == 0 {
                    BoolExp::FALSE
                } else {
                    let mut first_children = children.by_ref().take(child_len - 1);
                    first_children.try_fold(BoolExp::FALSE, |b1, b2| {
                        Ok::<_, AddSexpError>(self.inner.xor_approx(
                            b1,
                            b2.as_bool()?,
                            Approx::Exact,
                        ))
                    })?
                };
                let last_child = if let Some(last_child) = children.next() {
                    last_child.as_bool()?
                } else {
                    BoolExp::FALSE
                };
                if let ExprContext::AssertEq(Exp::Bool(target), ..) = ctx {
                    self.inner.assert_xor_eq(first_res, last_child, target);
                    target.into()
                } else {
                    self.inner
                        .xor_approx(first_res, last_child, ctx.to_approx())
                        .into()
                }
            }
            EQ_SYM => {
                let mut c: Conjunction = self.inner.new_junction();
                let [exp1] = mandatory_args(children)?;
                let exp1 = exp1.exp();
                extend_result(
                    &mut c,
                    children.map(|exp2| match ctx {
                        ExprContext::AssertEq(Exp::Bool(BoolExp::TRUE), _) => {
                            self.inner.assert_eq(exp1, exp2.expect_sort(exp1.sort())?);
                            Ok(BoolExp::TRUE)
                        }
                        _ => Ok(self.inner.eq(exp1, exp2.expect_sort(exp1.sort())?)),
                    }),
                )?;
                self.inner.collapse_bool(c).into()
            }
            DISTINCT_SYM => {
                if let Some(x) = children.next() {
                    let sort = x.exp().sort();
                    children.try_for_each(|x| {
                        x.expect_sort(sort)?;
                        Ok::<_, AddSexpError>(())
                    })?;
                }
                match ctx {
                    ExprContext::AssertEq(Exp::Bool(b), _) => {
                        self.inner.assert_distinct_eq(children_slice, b);
                        b.into()
                    }
                    _ => self
                        .inner
                        .distinct_approx(children_slice, ctx.to_approx())
                        .into(),
                }
            }
            ITE_SYM | IF_SYM => {
                let [i, t, e] = mandatory_args(children)?;
                let (i, t, e) = (i.as_bool()?, t.exp(), e.expect_sort(t.exp().sort())?);

                match ctx {
                    ExprContext::AssertEq(target, _) if t.sort() == target.sort() => {
                        self.inner
                            .assert_ite_eq(i, t, e, target)
                            .map_err(unsupported)?;
                        target
                    }
                    _ => self.inner.ite(i, t, e).map_err(unsupported)?,
                }
            }
            sym => match self.bound.get(&sym) {
                None => return Err(Unbound),
                Some(Bound::Const(c)) => {
                    if let ExprContext::AssertEq(mut exp, negate) = ctx {
                        if exp.sort() == c.sort() {
                            let mut cur = *c;
                            if let (true, Some(exp_b), Some(cur_b)) =
                                (negate, exp.as_bool(), cur.as_bool())
                            {
                                exp = (!exp_b).into();
                                cur = (!cur_b).into();
                            }
                            // ignore error since we will type check at a higher level
                            let _ = self.inner.assert_eq(exp, cur);
                        }
                    }
                    *c
                }
                Some(Bound::Fn(f)) => {
                    children.zip(&f.args).try_for_each(|(arg, sort)| {
                        arg.expect_sort(*sort)?;
                        Ok::<_, AddSexpError>(())
                    })?;
                    if children_slice.len() < f.args.len() {
                        return Err(MissingArgument {
                            actual: children_slice.len(),
                            expected: f.args.len(),
                        });
                    }
                    match (ctx, f.ret) {
                        (ExprContext::AssertEq(e @ Exp::Bool(b), negate), BOOL_SORT)
                            if !negate || b.to_lit().is_err() =>
                        {
                            self.inner
                                .assert_fn_eq(sym, children_slice.iter().copied(), e)
                                .map_err(unsupported)?;
                            e
                        }
                        _ => self
                            .inner
                            .sorted_fn(sym, children_slice.iter().copied(), f.ret)
                            .map_err(unsupported)?,
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
    pub fn end_exp_take(&mut self) -> Result<Exp<Euf::UExp>, (Symbol, AddSexpError)> {
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
                        f.with_intern(self.intern()),
                        self.exp_stack[stack_len as usize..]
                            .iter()
                            .map(|x| x.with_intern(self.intern())),
                    ),
                    x.with_intern(self.intern())
                );
                self.exp_stack.truncate(stack_len as usize);
                Ok(x)
            }
            Err(x) => Err((f, x)),
        }
    }

    /// Adds a child to the current expression
    pub fn inject_exp(&mut self, exp: Exp<Euf::UExp>) {
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
        impl Iterator<
            Item = (
                Symbol,
                BoundDefinition<Euf::FunctionInfo<'_>, Exp<Euf::UExp>>,
            ),
        >,
    ) {
        let mut syms: Vec<_> = self.defined_symbols().collect();
        syms.sort_unstable_by_key(|sym| self.intern().symbols.resolve(*sym));
        let (function_info, inner) = self.inner.function_info();
        let bound = &self.bound;
        let iter = syms.into_iter().map(move |sym| {
            let val = bound.get(&sym).unwrap();
            match val {
                Bound::Const(exp) => (sym, BoundDefinition::Const(inner.canonize(*exp))),
                Bound::Fn(f) => (sym, BoundDefinition::Fn(f, function_info(sym))),
            }
        });
        (inner.intern(), iter)
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

    pub fn solver(&self) -> &Solver<Euf> {
        &self.inner
    }

    pub fn solver_mut(&mut self) -> &mut Solver<Euf> {
        &mut self.inner
    }

    pub fn intern(&self) -> &InternInfo {
        self.inner.intern()
    }

    pub fn intern_mut(&mut self) -> &mut InternInfo {
        self.inner.intern_mut()
    }
}

pub enum BoundDefinition<'a, F, UExp> {
    Const(UExp),
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
    Unsupported(Cow<'static, str>),
}

use crate::euf::EufT;
use AddSexpError::*;

#[derive(Copy, Clone)]
pub(crate) struct IndexExp<Euf>(pub(crate) (usize, Exp<Euf>));

impl<UExp: HasSort + Copy> IndexExp<UExp> {
    pub(crate) fn exp(self) -> Exp<UExp> {
        self.0 .1
    }

    pub(crate) fn sort_mismatch(self, expected: Sort) -> AddSexpError {
        SortMismatch {
            arg_n: self.0 .0,
            actual: self.exp().sort(),
            expected,
        }
    }

    pub(crate) fn expect_sort(self, expected: Sort) -> Result<Exp<UExp>, AddSexpError> {
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

pub(crate) fn mandatory_args<const N: usize, UExp>(
    iter: &mut impl Iterator<Item = IndexExp<UExp>>,
) -> Result<[IndexExp<UExp>; N], AddSexpError> {
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

pub(crate) fn finish_iter<UExp>(
    mut iter: impl Iterator<Item = IndexExp<UExp>>,
) -> Result<(), AddSexpError> {
    match iter.next() {
        Some(x) => Err(ExtraArgument { expected: x.0 .0 }),
        None => Ok(()),
    }
}

fn unsupported<U: Into<Cow<'static, str>>>(u: U) -> AddSexpError {
    Unsupported(u.into())
}
