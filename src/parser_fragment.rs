use crate::collapse::ExprContext;
use crate::intern::Symbol;
use crate::parser_core::SexpTerminal;
use crate::{BoolExp, ExpLike, Sort, StaticSort, SubExp, SuperExp};
use alloc::borrow::Cow;
use AddSexpError::*;

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

#[derive(Copy, Clone)]
pub(crate) struct IndexExp<Exp>(pub(crate) (usize, Exp));

impl<Exp: ExpLike> IndexExp<Exp> {
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
}

impl<Exp: ExpLike> IndexExp<Exp> {
    pub(crate) fn downcast<Sub: StaticSort + SubExp<Exp, M>, M>(self) -> Result<Sub, AddSexpError> {
        Sub::from_downcast(self.exp()).ok_or(self.sort_mismatch(Sub::SORT))
    }
}

pub(crate) fn index_iter<Exp: Copy>(i: &[Exp]) -> impl Iterator<Item = IndexExp<Exp>> + '_ {
    i.iter().copied().enumerate().map(IndexExp)
}

// TODO use std version when it becomes stable
fn try_from_fn<const N: usize, T: Copy, E>(
    mut f: impl FnMut(usize) -> Result<T, E>,
) -> Result<[T; N], E> {
    if N == 0 {
        Ok(core::array::from_fn(|_| unreachable!()))
    } else {
        let x0 = f(0)?;
        let mut res = Ok(());
        let arr = core::array::from_fn(|i| {
            if i == 0 {
                x0
            } else {
                let f_res = f(i);
                match f_res {
                    Ok(x) => x,
                    Err(e) => {
                        res = Err(e);
                        x0
                    }
                }
            }
        });
        res?;
        Ok(arr)
    }
}

pub fn mandatory_args<const N: usize, Exp: Copy>(
    iter: &mut impl Iterator<Item = Exp>,
) -> Result<[Exp; N], AddSexpError> {
    try_from_fn(|i| match iter.next() {
        Some(x) => Ok(x),
        None => Err(MissingArgument {
            expected: N,
            actual: i,
        }),
    })
}

pub fn exact_args<const N: usize, Exp: Copy>(
    iter: &mut impl Iterator<Item = Exp>,
) -> Result<[Exp; N], AddSexpError> {
    let res = mandatory_args(iter)?;
    if iter.next().is_some() {
        return Err(ExtraArgument { expected: N });
    }
    Ok(res)
}

impl<Exp> ExprContext<Exp> {
    pub fn negate<M>(self) -> Self
    where
        Exp: SuperExp<BoolExp, M>,
    {
        let ctx = match self.downcast() {
            ExprContext::Approx(a) => ExprContext::Approx(!a),
            ExprContext::AssertEq(b) => ExprContext::AssertEq(!b),
            _ => ExprContext::Exact,
        };
        ctx.upcast()
    }
}

pub type PfResult<Exp> = Option<Result<Exp, AddSexpError>>;

#[allow(unused_variables)]
pub trait ParserFragment<Exp, S, M>: Default {
    fn supports(&self, s: Symbol) -> bool;
    fn handle_terminal(
        &self,
        x: SexpTerminal,
        solver: &mut S,
        ctx: ExprContext<Exp>,
    ) -> PfResult<Exp> {
        None
    }

    /// Requires that `self.`[`supports`](Self::supports)`(f)`
    fn handle_non_terminal(
        &self,
        f: Symbol,
        children: &mut [Exp],
        solver: &mut S,
        ctx: ExprContext<Exp>,
    ) -> Result<Exp, AddSexpError>;

    fn try_handle_non_terminal(
        &self,
        f: Symbol,
        children: &mut [Exp],
        solver: &mut S,
        ctx: ExprContext<Exp>,
    ) -> PfResult<Exp> {
        self.supports(f)
            .then(|| self.handle_non_terminal(f, children, solver, ctx))
    }

    fn sub_ctx(
        &self,
        f: Symbol,
        previous_children: &[Exp],
        ctx: ExprContext<Exp>,
    ) -> ExprContext<Exp> {
        ExprContext::Exact
    }

    fn try_sub_ctx(
        &self,
        f: Symbol,
        previous_children: &[Exp],
        ctx: ExprContext<Exp>,
    ) -> Option<ExprContext<Exp>> {
        self.supports(f)
            .then(|| self.sub_ctx(f, previous_children, ctx))
    }
}

impl<Exp: ExpLike, S, M1, M2, P1: ParserFragment<Exp, S, M1>, P2: ParserFragment<Exp, S, M2>>
    ParserFragment<Exp, S, (M1, M2)> for (P1, P2)
{
    fn supports(&self, s: Symbol) -> bool {
        self.0.supports(s) || self.1.supports(s)
    }

    fn handle_terminal(
        &self,
        x: SexpTerminal,
        solver: &mut S,
        ctx: ExprContext<Exp>,
    ) -> PfResult<Exp> {
        match self.0.handle_terminal(x, solver, ctx) {
            Some(res) => Some(res),
            None => self.1.handle_terminal(x, solver, ctx),
        }
    }

    fn handle_non_terminal(
        &self,
        f: Symbol,
        children: &mut [Exp],
        solver: &mut S,
        ctx: ExprContext<Exp>,
    ) -> Result<Exp, AddSexpError> {
        match self.0.try_handle_non_terminal(f, children, solver, ctx) {
            Some(res) => res,
            None => self.1.handle_non_terminal(f, children, solver, ctx),
        }
    }

    fn try_handle_non_terminal(
        &self,
        f: Symbol,
        children: &mut [Exp],
        solver: &mut S,
        ctx: ExprContext<Exp>,
    ) -> PfResult<Exp> {
        match self.0.try_handle_non_terminal(f, children, solver, ctx) {
            Some(res) => Some(res),
            None => self.1.try_handle_non_terminal(f, children, solver, ctx),
        }
    }

    fn sub_ctx(
        &self,
        f: Symbol,
        previous_children: &[Exp],
        ctx: ExprContext<Exp>,
    ) -> ExprContext<Exp> {
        match self.0.try_sub_ctx(f, previous_children, ctx) {
            Some(res) => res,
            None => self.1.sub_ctx(f, previous_children, ctx),
        }
    }

    fn try_sub_ctx(
        &self,
        f: Symbol,
        previous_children: &[Exp],
        ctx: ExprContext<Exp>,
    ) -> Option<ExprContext<Exp>> {
        match self.0.try_sub_ctx(f, previous_children, ctx) {
            Some(res) => Some(res),
            None => self.1.try_sub_ctx(f, previous_children, ctx),
        }
    }
}
