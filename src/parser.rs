use crate::egraph::Children;
use crate::euf::FullFunctionInfo;
use crate::full_buf_read::{FullBufRead, FullBufReader};
use crate::junction::{Conjunction, Disjunction};
use crate::parser::Error::*;
use crate::parser_core::{ParseError, SexpParser, SexpToken, SpanRange};
use crate::solver::{BoolExp, Exp, SolveResult, Solver, UnsatCoreConjunction, UnsatCoreInfo};
use crate::sort::{BaseSort, Sort};
use crate::util::{format_args2, parenthesized};
use egg::{Id, Symbol};
use hashbrown::HashMap;
use internment::Intern;
use log::debug;
use std::fmt::Formatter;
use std::io::{Read, Write};
use std::iter;
use thiserror::Error;

#[derive(Error, Debug)]
enum Error {
    #[error("the {arg_n}th argument of the function {f} has sort {actual} but should have sort {expected}")]
    SortMismatch {
        f: &'static str,
        arg_n: usize,
        actual: Sort,
        expected: Sort,
    },
    #[error(
        "the function {f} has return sort {actual} but should have sort {expected} because of as"
    )]
    AsSortMismatch {
        f: &'static str,
        actual: Sort,
        expected: Sort,
    },
    #[error("the left side of the equality has sort {left} but the right side has sort {right}")]
    EqSortMismatch { left: Sort, right: Sort },
    #[error(
        "the left side of the ite expression has sort {left} but the right side has sort {right}"
    )]
    IteSortMismatch { left: Sort, right: Sort },
    #[error("the definition had the incorrect sort {0:?}")]
    BindSortMismatch(Sort),
    #[error("the function `{f}` expects {expected} arguments but got {actual}")]
    ArgumentMismatch {
        f: &'static str,
        actual: usize,
        expected: usize,
    },
    #[error("unknown identifier `{0}`")]
    Unbound(Symbol),
    #[error("unknown sort `{0}`")]
    UnboundSort(Symbol),
    #[error("the identifier `{0}` shadows a global constant")]
    Shadow(Symbol),
    #[error("unexpected token when parsing sort")]
    InvalidSort,
    #[error("unexpected token when parsing expression")]
    InvalidExp,
    #[error("unexpected token when parsing command")]
    InvalidCommand,
    #[error("`define-fun` does not support functions with arguments")]
    InvalidDefineFun,
    #[error("unexpected token when parsing binding")]
    InvalidBinding,
    #[error("unexpected token when parsing let expression")]
    InvalidLet,
    #[error("(check-sat) returned {actual:?} but should have returned {expected:?} based on last (set-info :status)")]
    CheckSatStatusMismatch {
        actual: SolveResult,
        expected: SolveResult,
    },
    #[error("The last command was not `check-sat-assuming` that returned `Unsat`")]
    NoCore,
    #[error("The last command was not `check-sat-assuming` that returned `Sat`")]
    NoModel,
    #[error("unsupported {0}")]
    Unsupported(&'static str),
    #[error(transparent)]
    Parser(#[from] ParseError),
}

type Result<T> = core::result::Result<T, Error>;

#[derive(Copy, Clone)]
struct FnSort {
    args: Intern<[Sort]>,
    ret: Sort,
}

impl FnSort {
    fn mismatch(&self, name: Symbol, actual: usize) -> Error {
        ArgumentMismatch {
            f: name.as_str(),
            expected: self.args.len(),
            actual,
        }
    }
}
#[derive(Copy, Clone)]
enum Bound {
    Fn(FnSort),
    Const(Exp),
}

macro_rules! enum_str {
    ($name:ident {$($s:literal => $var:ident,)*}) => {
        #[derive(Copy, Clone)]
        enum $name {
            $($var,)*
            Unknown,
        }

        impl $name {
            fn from_str(s: &str) -> Self {
                match s {
                    $($s => Self::$var,)*
                    _ => Self::Unknown,
                }
            }

            fn to_str(self) -> &'static str {
                 match self {
                    $(Self::$var => $s,)*
                    Self::Unknown => "???",
                }
            }
        }

        impl ::core::fmt::Debug for $name {
            fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
                f.write_str(self.to_str())
            }
        }
    };
}

enum_str!(Smt2Command{
    "declare-sort" => DeclareSort,
    "declare-fun" => DeclareFn,
    "declare-const" => DeclareConst,
    "define-const" => DefineConst,
    "define-fun" => DefineFn,
    "get-unsat-core" => GetUnsatCore,
    "get-value" => GetValue,
    "get-model" => GetModel,
    "assert" => Assert,
    "check-sat" => CheckSat,
    "check-sat-assuming" => CheckSatAssuming,
    "push" => Push,
    "pop" => Pop,
    "reset" => Reset,
    "set-logic" => SetLogic,
    "set-info" => SetInfo,
    "exit" => Exit,
});

macro_rules! sym_struct {
    ($name:ident {$($var:ident = $l:literal,)*}) => {
        #[derive(Copy, Clone)]
        struct $name {
            $($var: ::egg::Symbol,)*
        }

        impl ::core::default::Default for $name {
            fn default() -> Self {
                $name{
                    $($var: ::egg::Symbol::new($l),)*
                }
            }
        }
    };
}

sym_struct! {Syms{
    and = "and",
    or = "or",
    not = "not",
    imp = "=>",
    xor = "xor",
    eq = "=",
    distinct = "distinct",
    let_ = "let",
    ite = "ite",
    if_ = "if",
}}

#[derive(Default)]
enum State {
    Unsat(UnsatCoreInfo<SpanRange>),
    Model,
    #[default]
    Base,
}

struct PushInfo {
    sort: usize,
    bound: usize,
}
#[derive(Default)]
struct Parser<W: Write> {
    bound: HashMap<Symbol, Bound>,
    bound_stack: Vec<(Symbol, Option<Bound>)>,
    declared_sorts: HashMap<Symbol, u32>,
    sort_stack: Vec<Symbol>,
    push_info: Vec<PushInfo>,
    core: Solver,
    syms: Syms,
    writer: W,
    state: State,
    last_status_info: Option<SolveResult>,
}

struct CountingParser<'a, R: FullBufRead> {
    p: SexpParser<'a, R>,
    name: &'static str,
    actual: usize,
    expected: usize,
}

type InfoToken<'a, R> = (SexpToken<'a, R>, usize, &'static str);

impl<'a, R: FullBufRead> CountingParser<'a, R> {
    fn new(p: SexpParser<'a, R>, name: &'static str, expected: usize) -> Self {
        CountingParser {
            p,
            name,
            actual: 0,
            expected,
        }
    }

    fn try_next(&mut self) -> Result<Option<SexpToken<'_, R>>> {
        debug_assert!(self.actual < self.expected);
        self.actual += 1;
        match self.p.next() {
            None => Ok(None),
            Some(x) => Ok(Some(x?)),
        }
    }

    fn next_full(&mut self) -> Result<(SexpToken<'_, R>, usize, &'static str)> {
        let actual = self.actual;
        let err = ArgumentMismatch {
            f: self.name,
            actual,
            expected: self.expected,
        };
        debug_assert!(self.actual < self.expected);
        self.actual += 1;
        Ok((self.p.next().ok_or(err)??, actual, self.name))
    }
    fn next(&mut self) -> Result<SexpToken<'_, R>> {
        Ok(self.next_full()?.0)
    }

    fn finish(mut self) -> Result<()> {
        debug_assert_eq!(self.actual, self.expected);
        if self.p.next().is_some() {
            Err(ArgumentMismatch {
                f: self.name,
                actual: self.expected + 1,
                expected: self.expected,
            })
        } else {
            Ok(())
        }
    }
}

fn cross<I1: IntoIterator, I2: IntoIterator + Clone>(
    iter1: I1,
    iter2: I2,
) -> impl Iterator<Item = (I1::Item, I2::Item)>
where
    I1::Item: Copy,
{
    iter1
        .into_iter()
        .flat_map(move |x1| iter2.clone().into_iter().map(move |x2| (x1, x2)))
}

fn pairwise<T>(slice: &[T]) -> impl Iterator<Item = (&T, &T)> {
    cross(0..slice.len(), 0..slice.len())
        .filter(|&(i, j)| i != j)
        .map(|(i, j)| (&slice[i], &slice[j]))
}

impl<W: Write> Parser<W> {
    fn new(writer: W) -> Self {
        let mut res = Parser {
            bound: Default::default(),
            bound_stack: Default::default(),
            push_info: vec![],
            declared_sorts: Default::default(),
            core: Default::default(),
            syms: Default::default(),
            writer,
            state: State::Base,
            sort_stack: vec![],
            last_status_info: None,
        };
        res.declared_sorts.insert(res.core.bool_sort().name, 0);
        let true_sym = Symbol::new("true");
        let false_sym = Symbol::new("false");
        res.bound
            .insert(true_sym, Bound::Const(BoolExp::TRUE.into()));
        res.bound
            .insert(false_sym, Bound::Const(BoolExp::FALSE.into()));
        res
    }

    fn handle_as<R: FullBufRead>(&mut self, rest: SexpParser<R>) -> Result<(Symbol, Sort)> {
        let mut rest = CountingParser::new(rest, "as", 2);
        let SexpToken::Symbol(s) = rest.next()? else {
            return Err(InvalidExp);
        };
        let s = Symbol::new(s);
        let sort = self.parse_sort(rest.next()?)?;
        rest.finish()?;
        Ok((s, sort))
    }

    fn parse_exp<R: FullBufRead>(&mut self, token: SexpToken<R>) -> Result<Exp> {
        match token {
            SexpToken::Symbol(s) => {
                SexpParser::with_empty(|p| self.parse_fn_exp(Symbol::new(s), p, None))
            }
            SexpToken::String(_) => Err(Unsupported("strings")),
            SexpToken::Number(_) => Err(Unsupported("arithmetic")),
            SexpToken::Decimal(_, _) => Err(Unsupported("decimal")),
            SexpToken::BitVec { .. } => Err(Unsupported("bitvec")),
            SexpToken::List(mut l) => {
                let status = match l.next().ok_or(InvalidExp)?? {
                    SexpToken::Symbol("as") => None,
                    SexpToken::Symbol(s) => Some((Symbol::new(s), None)),
                    SexpToken::List(mut l2) => {
                        if matches!(l2.next().ok_or(InvalidExp)??, SexpToken::Symbol("as")) {
                            let (s, sort) = self.handle_as(l2)?;
                            Some((s, Some(sort)))
                        } else {
                            return Err(InvalidExp);
                        }
                    }
                    _ => return Err(InvalidExp),
                };
                if let Some((s, sort)) = status {
                    self.parse_fn_exp(s, l, sort)
                } else {
                    let (s, sort) = self.handle_as(l)?;
                    SexpParser::with_empty(|p| self.parse_fn_exp(s, p, Some(sort)))
                }
            }
            SexpToken::Keyword(_) => Err(InvalidExp),
        }
    }

    fn parse_bool<R: FullBufRead>(&mut self, (token, arg_n, f): InfoToken<R>) -> Result<BoolExp> {
        let exp = self.parse_exp(token)?;
        exp.as_bool().ok_or_else(|| SortMismatch {
            f,
            arg_n,
            actual: self.core.id_sort(exp).1,
            expected: self.core.bool_sort(),
        })
    }

    fn parse_id<R: FullBufRead>(
        &mut self,
        f: Symbol,
        arg_n: usize,
        expected: Sort,
        token: SexpToken<R>,
    ) -> Result<Id> {
        let exp = self.parse_exp(token)?;
        let (id, actual) = self.core.id_sort(exp);
        if actual != expected {
            Err(SortMismatch {
                f: f.into(),
                arg_n,
                actual,
                expected,
            })
        } else {
            Ok(id)
        }
    }

    fn parse_binding<R: FullBufRead>(&mut self, token: SexpToken<R>) -> Result<(Symbol, Exp)> {
        match token {
            SexpToken::List(mut l) => {
                let sym = match l.next().ok_or(InvalidBinding)?? {
                    SexpToken::Symbol(s) => Symbol::new(s),
                    _ => return Err(InvalidBinding),
                };
                let exp = self.parse_exp(l.next().ok_or(InvalidBinding)??)?;
                Ok((sym, exp))
            }
            _ => Err(InvalidBinding),
        }
    }

    fn undo_bindings(&mut self, old_len: usize) {
        for (name, bound) in self.bound_stack.drain(old_len..).rev() {
            match bound {
                None => self.bound.remove(&name),
                Some(x) => self.bound.insert(name, x),
            };
        }
    }

    fn parse_fn_exp<R: FullBufRead>(
        &mut self,
        f: Symbol,
        mut rest: SexpParser<R>,
        expect_res: Option<Sort>,
    ) -> Result<Exp> {
        let res = match f {
            not if not == self.syms.not => {
                let mut rest = CountingParser::new(rest, "not", 1);
                let token = rest.next_full()?;
                let x = self.parse_bool(token)?;
                rest.finish()?;
                (!x).into()
            }
            and if and == self.syms.and => {
                let conj = rest
                    .zip_map(0.., |token, i| self.parse_bool((token?, i, "and")))
                    .collect::<Result<Conjunction>>()?;
                self.core.collapse_bool(conj).into()
            }
            or if or == self.syms.or => {
                let disj = rest
                    .zip_map(0.., |token, i| self.parse_bool((token?, i, "or")))
                    .collect::<Result<Disjunction>>()?;
                self.core.collapse_bool(disj).into()
            }
            imp if imp == self.syms.imp => {
                let mut iter = rest.zip_map(0.., |token, i| self.parse_bool((token?, i, "=>")));
                let mut last = iter.next().ok_or(ArgumentMismatch {
                    actual: 0,
                    expected: 1,
                    f: "=>",
                })??;
                let not_last = iter.map(|item| Ok(!std::mem::replace(&mut last, item?)));
                let res = not_last.collect::<Result<Disjunction>>()? | last;
                self.core.collapse_bool(res).into()
            }
            xor if xor == self.syms.xor => {
                let mut res = BoolExp::FALSE;
                rest.zip_map(0.., |token, i| {
                    let parsed = self.parse_bool((token?, i, "xor"))?;
                    res = self.core.xor(res, parsed);
                    Ok(())
                })
                .collect::<Result<()>>()?;
                res.into()
            }
            eq if eq == self.syms.eq => {
                let mut rest = CountingParser::new(rest, "=", 1);
                let exp1 = self.parse_exp(rest.next()?)?;
                let (id1, sort1) = self.core.id_sort(exp1);
                let conj = rest
                    .p
                    .map(|x| {
                        let parsed = self.parse_exp(x?)?;
                        let (id2, sort2) = self.core.id_sort(parsed);
                        if sort1 != sort2 {
                            return Err(EqSortMismatch {
                                left: sort1,
                                right: sort2,
                            });
                        } else {
                            Ok(self.core.raw_eq(id1, id2))
                        }
                    })
                    .collect::<Result<Conjunction>>()?;
                self.core.collapse_bool(conj).into()
            }
            distinct if distinct == self.syms.distinct => {
                let mut rest = CountingParser::new(rest, "distinct", 1);
                let exp1 = self.parse_exp(rest.next()?)?;
                let (id1, sort1) = self.core.id_sort(exp1);
                let iter = rest.p.map(|x| {
                    let parsed = self.parse_exp(x?)?;
                    let (id2, sort2) = self.core.id_sort(parsed);
                    if sort1 != sort2 {
                        return Err(EqSortMismatch {
                            left: sort1,
                            right: sort2,
                        });
                    } else {
                        Ok(id2)
                    }
                });
                let ids = [Ok(id1)]
                    .into_iter()
                    .chain(iter)
                    .collect::<Result<Vec<Id>>>()?;
                let conj: Conjunction = pairwise(&ids)
                    .map(|(&id1, &id2)| !self.core.raw_eq(id1, id2))
                    .collect();
                self.core.collapse_bool(conj).into()
            }
            let_ if let_ == self.syms.let_ => {
                let mut rest = CountingParser::new(rest, "let", 2);
                let old_len = self.bound_stack.len();
                match rest.next()? {
                    SexpToken::List(mut l) => l
                        .map(|token| {
                            let (name, exp) = self.parse_binding(token?)?;
                            self.bound_stack.push((name, Some(Bound::Const(exp))));
                            Ok(())
                        })
                        .collect::<Result<()>>()?,
                    _ => return Err(InvalidLet),
                }
                let body = rest.next()?;
                for (name, bound) in &mut self.bound_stack[old_len..] {
                    *bound = self.bound.insert(*name, bound.unwrap())
                }
                let exp = self.parse_exp(body)?;
                rest.finish()?;
                self.undo_bindings(old_len);
                exp
            }
            ite if ite == self.syms.ite || ite == self.syms.if_ => {
                let mut rest = CountingParser::new(rest, ite.as_str(), 3);
                let i = self.parse_bool(rest.next_full()?)?;
                let t = self.parse_exp(rest.next()?)?;
                let e = self.parse_exp(rest.next()?)?;
                rest.finish()?;
                let err_m = |(left, right)| IteSortMismatch { left, right };
                self.core.ite(i, t, e).map_err(err_m)?
            }
            f => {
                // Uninterpreted function
                let sig = *self.bound.get(&f).ok_or(Unbound(f))?;
                match sig {
                    Bound::Fn(sig) => {
                        let arg_iter = sig.args.iter().copied().enumerate();
                        let children = rest
                            .zip_map(arg_iter, |token, (i, expect)| {
                                self.parse_id(f, i, expect, token?)
                            })
                            .collect::<Result<Children>>()?;
                        if rest.next().is_some() {
                            return Err(sig.mismatch(f, sig.args.len() + 1));
                        }
                        if children.len() < sig.args.len() {
                            return Err(sig.mismatch(f, children.len()));
                        }
                        self.core.sorted_fn(f, children, sig.ret)
                    }
                    Bound::Const(c) => {
                        if rest.next().is_some() {
                            return Err(ArgumentMismatch {
                                f: f.as_str(),
                                actual: 1,
                                expected: 0,
                            });
                        }
                        self.core.canonize(c)
                    }
                }
            }
        };
        if let Some(expected) = expect_res {
            let actual = self.core.sort(res);
            if actual != expected {
                return Err(AsSortMismatch {
                    f: f.as_str(),
                    actual,
                    expected,
                });
            }
        };
        return Ok(res);
    }

    fn parse_sort<R: FullBufRead>(&self, token: SexpToken<R>) -> Result<Sort> {
        let res = match token {
            SexpToken::Symbol(s) => BaseSort {
                name: Symbol::new(s),
                params: Box::new([]),
            },
            SexpToken::List(mut l) => {
                let name = match l.next().ok_or(InvalidSort)?? {
                    SexpToken::Symbol(s) => Symbol::new(s),
                    _ => return Err(InvalidSort),
                };
                let params = l.map(|x| self.parse_sort(x?)).collect::<Result<_>>()?;
                BaseSort { name, params }
            }
            _ => return Err(InvalidSort),
        };
        let len = res.params.len();
        match self.declared_sorts.get(&res.name) {
            None => Err(UnboundSort(res.name)),
            Some(x) if *x as usize != len => Err(ArgumentMismatch {
                f: res.name.into(),
                expected: *x as usize,
                actual: len,
            }),
            _ => Ok(Sort::new(res)),
        }
    }

    fn reset_state(&mut self) {
        if matches!(self.state, State::Model) {
            self.core.pop_model();
        }
        self.state = State::Base;
    }

    fn parse_command<R: FullBufRead>(
        &mut self,
        name: Smt2Command,
        rest: SexpParser<R>,
    ) -> Result<()> {
        match name {
            Smt2Command::DeclareSort => {
                let mut rest = CountingParser::new(rest, name.to_str(), 2);
                let SexpToken::Symbol(name) = rest.next()? else {
                    return Err(InvalidCommand);
                };
                let name = Symbol::new(name);
                if self.declared_sorts.contains_key(&name) {
                    return Err(Shadow(name));
                }
                let args = match rest.try_next()? {
                    None => 0,
                    Some(SexpToken::Number(n)) => n,
                    Some(_) => return Err(InvalidCommand),
                };
                rest.finish()?;
                self.sort_stack.push(name);
                self.declared_sorts
                    .insert(name, args.try_into().map_err(|_| ParseError::Overflow)?);
            }
            Smt2Command::GetUnsatCore => {
                let State::Unsat(info) = &self.state else {
                    return Err(NoCore);
                };
                write!(self.writer, "(").unwrap();
                let mut iter = info
                    .core(self.core.last_unsat_core())
                    .map(|x| rest.lookup_range(*x));
                if let Some(x) = iter.next() {
                    write!(self.writer, "{x}").unwrap();
                }
                for x in iter {
                    write!(self.writer, " {x}").unwrap();
                }
                writeln!(self.writer, ")").unwrap();
                CountingParser::new(rest, name.to_str(), 0).finish()?;
            }
            Smt2Command::GetValue => {
                let mut rest = CountingParser::new(rest, name.to_str(), 1);
                if !matches!(self.state, State::Model) {
                    return Err(NoModel);
                }
                let SexpToken::List(mut l) = rest.next()? else {
                    return Err(InvalidCommand);
                };
                let values = l
                    .zip_map_full(iter::repeat(()), |x, ()| self.parse_exp(x?))
                    .collect::<Result<Vec<_>>>()?;
                drop(l);
                write!(self.writer, "(").unwrap();
                let mut iter = values.into_iter();
                if let Some((x, span)) = iter.next() {
                    write!(self.writer, "({} {x})", rest.p.lookup_range(span)).unwrap();
                }
                for (x, span) in iter {
                    write!(self.writer, "\n ({} {x})", rest.p.lookup_range(span)).unwrap();
                }
                writeln!(self.writer, ")").unwrap();
                rest.finish()?;
            }
            Smt2Command::GetModel => {
                CountingParser::new(rest, name.to_str(), 0).finish()?;
                if !matches!(self.state, State::Model) {
                    return Err(NoModel);
                }
                let (funs, core) = self.core.function_info();
                writeln!(self.writer, "(").unwrap();
                let mut bound: Vec<_> = self
                    .bound
                    .keys()
                    .copied()
                    .filter(|k| !matches!(k.as_str(), "true" | "false"))
                    .collect();
                bound.sort_unstable_by_key(|x| x.as_str());
                for k in bound {
                    match &self.bound[&k] {
                        Bound::Const(x) => {
                            if matches!(k.as_str(), "true" | "false") {
                                continue;
                            }
                            let x = core.canonize(*x);
                            let sort = core.sort(x);
                            writeln!(self.writer, " (define-fun {k} () {sort} {x})").unwrap();
                        }
                        Bound::Fn(f) => {
                            let args = f
                                .args
                                .iter()
                                .enumerate()
                                .map(|(i, s)| format_args2!("(x!{i} {s})"));
                            let args = parenthesized(args, " ");
                            writeln!(self.writer, " (define-fun {k} {args} {}", f.ret).unwrap();
                            write_body(&mut self.writer, &funs, k);
                        }
                    }
                }
                writeln!(self.writer, ")").unwrap();
            }
            Smt2Command::SetLogic => {
                let mut rest = CountingParser::new(rest, name.to_str(), 1);
                match rest.next()? {
                    SexpToken::Symbol("QF_UF") => {}
                    SexpToken::Symbol(_) => return Err(Unsupported("logic")),
                    _ => return Err(InvalidCommand),
                }
                rest.finish()?;
            }
            Smt2Command::SetInfo => {
                let mut rest = CountingParser::new(rest, name.to_str(), 2);
                let SexpToken::Keyword(key) = rest.next()? else {
                    return Err(InvalidCommand);
                };
                let info_was_status = key == "status";
                let body = rest.next()?;
                if info_was_status {
                    self.last_status_info = match body {
                        SexpToken::Symbol("sat") => Some(SolveResult::Sat),
                        SexpToken::Symbol("unsat") => Some(SolveResult::Unsat),
                        SexpToken::Symbol("unknown") => Some(SolveResult::Unknown),
                        _ => return Err(InvalidCommand),
                    }
                }
            }
            _ => return self.parse_destructive_command(name, rest),
        }
        Ok(())
    }

    fn set_state(&mut self, res: SolveResult, info: UnsatCoreInfo<SpanRange>) -> Result<()> {
        self.state = if let SolveResult::Unsat = res {
            self.core.pop_model();
            State::Unsat(info)
        } else {
            State::Model
        };
        if let Some(expected) = self.last_status_info.take() {
            if !res.valid_when_expecting(expected) {
                return Err(CheckSatStatusMismatch {
                    actual: res,
                    expected,
                });
            }
        }
        Ok(())
    }

    fn parse_fresh_binder<R: FullBufRead>(&self, token: SexpToken<R>) -> Result<Symbol> {
        let SexpToken::Symbol(name) = token else {
            return Err(InvalidCommand);
        };
        let name = Symbol::new(name);
        if self.bound.contains_key(&name) {
            return Err(Shadow(name));
        }
        Ok(name)
    }

    fn clear(&mut self) {
        self.push_info.clear();
        self.bound_stack.clear();
        self.bound.clear();
        self.core.clear();
        self.declared_sorts.clear();
        self.sort_stack.clear();
        self.declared_sorts.insert(self.core.bool_sort().name, 0);
        self.bound
            .insert(Symbol::new("true"), Bound::Const(BoolExp::TRUE.into()));
        self.bound
            .insert(Symbol::new("false"), Bound::Const(BoolExp::FALSE.into()));
    }

    fn parse_destructive_command<R: FullBufRead>(
        &mut self,
        name: Smt2Command,
        rest: SexpParser<R>,
    ) -> Result<()> {
        self.reset_state();
        match name {
            Smt2Command::DeclareFn => {
                let mut rest = CountingParser::new(rest, name.to_str(), 3);
                let name = self.parse_fresh_binder(rest.next()?)?;
                let SexpToken::List(mut l) = rest.next()? else {
                    return Err(InvalidCommand);
                };
                let args = l
                    .map(|t| self.parse_sort(t?))
                    .collect::<Result<Box<[_]>>>()?;
                drop(l);
                let ret = self.parse_sort(rest.next()?)?;
                rest.finish()?;
                if args.is_empty() {
                    self.declare_const(name, ret);
                } else {
                    let fn_sort = FnSort {
                        args: Intern::from(args),
                        ret,
                    };
                    self.insert_bound(name, Bound::Fn(fn_sort));
                }
            }
            Smt2Command::DeclareConst => {
                let mut rest = CountingParser::new(rest, name.to_str(), 2);
                let name = self.parse_fresh_binder(rest.next()?)?;
                let ret = self.parse_sort(rest.next()?)?;
                rest.finish()?;
                self.declare_const(name, ret);
            }
            Smt2Command::DefineConst => {
                let mut rest = CountingParser::new(rest, name.to_str(), 3);
                let name = self.parse_fresh_binder(rest.next()?)?;
                let sort = self.parse_sort(rest.next()?)?;
                let ret = self.parse_exp(rest.next()?)?;
                if sort != self.core.sort(ret) {
                    return Err(BindSortMismatch(self.core.sort(ret)));
                }
                rest.finish()?;
                self.insert_bound(name, Bound::Const(ret));
            }
            Smt2Command::DefineFn => {
                let mut rest = CountingParser::new(rest, name.to_str(), 4);
                let name = self.parse_fresh_binder(rest.next()?)?;
                let SexpToken::List(mut args) = rest.next()? else {
                    return Err(InvalidCommand);
                };
                if args.next().is_some() {
                    return Err(InvalidDefineFun);
                }
                drop(args);
                let sort = self.parse_sort(rest.next()?)?;
                let ret = self.parse_exp(rest.next()?)?;
                if sort != self.core.sort(ret) {
                    return Err(BindSortMismatch(self.core.sort(ret)));
                }
                rest.finish()?;
                self.insert_bound(name, Bound::Const(ret));
            }
            Smt2Command::Assert => {
                let mut rest = CountingParser::new(rest, name.to_str(), 1);
                let b = self.parse_bool(rest.next_full()?)?;
                self.core.assert(b);
                rest.finish()?;
            }
            Smt2Command::CheckSat => {
                CountingParser::new(rest, name.to_str(), 0).finish()?;
                let res = self
                    .core
                    .check_sat_assuming_preserving_trail(&Default::default());
                self.set_state(res, Default::default())?;
                writeln!(self.writer, "{}", res.as_lower_str()).unwrap()
            }
            Smt2Command::CheckSatAssuming => {
                let mut rest = CountingParser::new(rest, name.to_str(), 1);
                let SexpToken::List(mut l) = rest.next()? else {
                    return Err(InvalidCommand);
                };
                let conj = l
                    .zip_map_full(0.., |token, i| self.parse_bool((token?, i, name.to_str())))
                    .collect::<Result<UnsatCoreConjunction<SpanRange>>>()?;
                drop(l);
                rest.finish()?;
                let res = self
                    .core
                    .check_sat_assuming_preserving_trail(conj.parts().0);
                self.set_state(res, conj.take_core())?;
                writeln!(self.writer, "{}", res.as_lower_str()).unwrap()
            }
            Smt2Command::Push => {
                let mut rest = CountingParser::new(rest, name.to_str(), 1);
                let n = match rest.try_next()? {
                    None => 1,
                    Some(SexpToken::Number(x)) => {
                        usize::try_from(x).map_err(|_| ParseError::Overflow)?
                    }
                    Some(_) => return Err(InvalidCommand),
                };
                for _ in 0..n {
                    self.core.push();
                    let info = PushInfo {
                        bound: self.bound_stack.len(),
                        sort: self.sort_stack.len(),
                    };
                    self.push_info.push(info);
                }
            }
            Smt2Command::Pop => {
                let mut rest = CountingParser::new(rest, name.to_str(), 1);
                let n = match rest.try_next()? {
                    None => 1,
                    Some(SexpToken::Number(x)) => {
                        usize::try_from(x).map_err(|_| ParseError::Overflow)?
                    }
                    Some(_) => return Err(InvalidCommand),
                };
                if n > self.push_info.len() {
                    self.clear()
                } else if n > 0 {
                    self.core.pop(n);
                    let mut info = None;
                    for _ in 0..n {
                        info = self.push_info.pop();
                    }
                    let info = info.unwrap();
                    self.undo_bindings(info.bound);

                    for s in self.sort_stack.drain(info.sort..).rev() {
                        self.declared_sorts.remove(&s);
                    }
                }
            }
            Smt2Command::Reset => self.clear(),
            Smt2Command::Exit => {}
            _ => return Err(InvalidCommand),
        }
        Ok(())
    }

    fn insert_bound(&mut self, name: Symbol, val: Bound) {
        self.bound_stack.push((name, self.bound.insert(name, val)))
    }

    fn declare_const(&mut self, name: Symbol, ret: Sort) {
        let exp = if ret == self.core.bool_sort() {
            self.core.fresh_bool().into()
        } else {
            self.core.sorted_fn(name, Children::new(), ret)
        };
        debug!("{name} is bound to {exp}");
        self.insert_bound(name, Bound::Const(exp));
    }

    fn parse_command_token<R: FullBufRead>(&mut self, t: SexpToken<R>) -> Result<()> {
        match t {
            SexpToken::List(mut l) => {
                let s = match l.next().ok_or(InvalidCommand)?? {
                    SexpToken::Symbol(s) => Smt2Command::from_str(s),
                    _ => return Err(InvalidCommand),
                };
                self.parse_command(s, l)
            }
            _ => Err(InvalidCommand),
        }
    }

    fn interp_smt2(&mut self, data: impl FullBufRead, mut err: impl Write) {
        SexpParser::parse_stream_keep_going(
            data,
            |t| self.parse_command_token(t?),
            |e| writeln!(err, "{e}").unwrap(),
        );
    }
}

fn write_body<W: Write>(writer: &mut W, info: &FullFunctionInfo, name: Symbol) {
    let cases = info.get(name);
    let len = cases.len();
    for (case, res) in cases {
        let mut case = case
            .enumerate()
            .map(|(i, x)| format_args2!("(= x!{i} {x})"));
        write!(writer, "  (ite ").unwrap();
        let c1 = case.next().unwrap();
        match case.next() {
            None => write!(writer, "{c1}").unwrap(),
            Some(c2) => {
                write!(writer, "(and {c1} {c2}").unwrap();
                for c in case {
                    write!(writer, " {c}").unwrap();
                }
                write!(writer, ")").unwrap();
            }
        }
        writeln!(writer, " {res}").unwrap();
    }
    writeln!(writer, "   {name}!default{:)<len$})", "").unwrap()
}

/// Evaluate `data`, the bytes of an `smt2` file, reporting results to `stdout` and errors to
/// `stderr`
pub fn interp_smt2(data: &[u8], out: impl Write, err: impl Write) {
    let mut p = Parser::new(out);
    p.interp_smt2(data, err)
}

/// Similar to [`interp_smt2`] but evaluates the bytes read from `reader` after init_data
pub fn interp_smt2_with_reader(
    init_data: Vec<u8>,
    reader: impl Read,
    out: impl Write,
    err: impl Write,
) {
    let mut p = Parser::new(out);
    p.interp_smt2(FullBufReader::new(reader, init_data), err)
}
