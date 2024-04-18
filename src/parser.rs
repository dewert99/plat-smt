use crate::egraph::Children;
use crate::euf::FullFunctionInfo;
use crate::full_buf_read::FullBufRead;
use crate::intern::{DisplayInterned, InternInfo, Sort, Symbol, BOOL_SYM, FALSE_SYM, TRUE_SYM};
use crate::junction::{Conjunction, Disjunction};
use crate::parser::Error::*;
use crate::parser_core::{ParseError, SexpParser, SexpToken, SpanRange};
use crate::solver::{BoolExp, Exp, SolveResult, Solver, UnsatCoreConjunction, UnsatCoreInfo};
use crate::util::{format_args2, parenthesized, powi, Bind, DefaultHashBuilder};
use egg::Id;
use hashbrown::HashMap;
use log::debug;
use no_std_compat::prelude::v1::*;
use smallvec::SmallVec;
use std::fmt::Formatter;
use std::fmt::Write;
use std::iter;

#[derive(Copy, Clone)]
enum StrSym {
    Str(&'static str),
    Sym(Symbol),
}

impl From<Symbol> for StrSym {
    fn from(value: Symbol) -> Self {
        StrSym::Sym(value)
    }
}

impl DisplayInterned for StrSym {
    fn fmt(&self, i: &InternInfo, f: &mut Formatter<'_>) -> std::fmt::Result {
        let str = match *self {
            StrSym::Sym(s) => i.symbols.resolve(s),
            StrSym::Str(s) => s,
        };
        f.write_str(str)
    }
}

enum Error {
    SortMismatch {
        f: StrSym,
        arg_n: usize,
        actual: Sort,
        expected: Sort,
    },
    AsSortMismatch {
        f: ExpKind,
        actual: Sort,
        expected: Sort,
    },
    IteSortMismatch {
        left: Sort,
        right: Sort,
    },
    BindSortMismatch(Sort),
    MissingArgument {
        f: StrSym,
        actual: usize,
        expected: usize,
    },
    ExtraArgument {
        f: StrSym,
        expected: usize,
    },
    Unbound(Symbol),
    UnboundSort(Symbol),
    Shadow(Symbol),
    NamedShadow(Symbol),
    InvalidSort,
    InvalidExp,
    InvalidCommand,
    InvalidOption,
    InvalidDefineFun,
    InvalidBinding,
    InvalidLet,
    InvalidAnnot,
    InvalidAnnotAttr(Symbol),
    InvalidInt,
    InvalidFloat,
    InvalidBool,
    CheckSatStatusMismatch {
        actual: SolveResult,
        expected: SolveResult,
    },
    NoCore,
    NoModel,
    Unsupported(&'static str),
    Parser(ParseError),
}

impl DisplayInterned for Error {
    fn fmt(&self, i: &InternInfo, fmt: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            SortMismatch {
                f,
                arg_n,
                actual,
                expected,
            } => write!(fmt, "the {arg_n}th argument of the function {} has sort {} but should have sort {}", f.with_intern(i), actual.with_intern(i), expected.with_intern(i)),
            AsSortMismatch {
                f,
                actual,
                expected
            } => write!(fmt, "the function {} has return sort {} but should have sort {} because of as", f.with_intern(i), actual.with_intern(i), expected.with_intern(i)),
            IteSortMismatch {
                left,
                right,
            } => write!(fmt, "the left side of the ite expression has sort {} but the right side has sort {}", left.with_intern(i), right.with_intern(i)),
            BindSortMismatch(s) => write!(fmt, "the definition had the incorrect sort {}", s.with_intern(i)),
            MissingArgument {
                f,
                actual,
                expected,
            } => write!(fmt, "the function `{}` expects at least {expected} arguments but only got {actual}", f.with_intern(i)),
            ExtraArgument {
                f,
                expected,
            } => write!(fmt, "the function `{}` expects at most {expected} arguments", f.with_intern(i)),
            Unbound(s) => write!(fmt, "unknown identifier `{}`", s.with_intern(i)),
            UnboundSort(s) => write!(fmt, "unknown sort `{}`", s.with_intern(i)),
            Shadow(s) => write!(fmt, "the identifier `{}` shadows a global constant", s.with_intern(i)),
            NamedShadow(s) => write!(fmt, "the :named identifier `{}` is already in scope", s.with_intern(i)),
            InvalidSort => write!(fmt, "unexpected token when parsing sort"),
            InvalidExp => write!(fmt, "unexpected token when parsing expression"),
            InvalidCommand => write!(fmt, "unexpected token when parsing command"),
            InvalidOption => write!(fmt, "unexpected token when parsing option"),
            InvalidDefineFun => write!(fmt, "`define-fun` does not support functions with arguments"),
            InvalidBinding => write!(fmt, "unexpected token when parsing binding"),
            InvalidLet => write!(fmt, "unexpected token when parsing let expression"),
            InvalidAnnot => write!(fmt, "unexpected token when parsing annotation"),
            InvalidAnnotAttr(s) => write!(fmt, "invalid attribute :{}", s.with_intern(i)),
            InvalidInt => write!(fmt, "expected integer token"),
            InvalidFloat => write!(fmt, "expected decimal token"),
            InvalidBool => write!(fmt, "expected boolean token"),
            CheckSatStatusMismatch {
                actual,
                expected,
            } => write!(fmt, "(check-sat) returned {actual:?} but should have returned {expected:?} based on last (set-info :status)"),
            NoCore => write!(fmt, "The last command was not `check-sat-assuming` that returned `unsat`"),
            NoModel => write!(fmt, "The last command was not `check-sat-assuming` that returned `sat`"),
            Unsupported(s) => write!(fmt, "unsupported {s}"),
            Parser(err) => write!(fmt, "{err}"),
        }
    }
}

impl From<ParseError> for Error {
    fn from(value: ParseError) -> Self {
        Error::Parser(value)
    }
}

type Result<T> = core::result::Result<T, Error>;

trait FromSexp: Sized {
    fn from_sexp<R: FullBufRead>(sexp_token: SexpToken<R>) -> Result<Self>;
}

trait IntFromSexp: TryFrom<u128> {}

impl<I: IntFromSexp> FromSexp for I {
    fn from_sexp<R: FullBufRead>(sexp_token: SexpToken<R>) -> Result<Self> {
        match sexp_token {
            SexpToken::Number(n) => Ok(n.try_into().map_err(|_| ParseError::Overflow)?),
            _ => Err(InvalidInt),
        }
    }
}

impl IntFromSexp for u32 {}
impl IntFromSexp for usize {}
impl IntFromSexp for i32 {}

impl FromSexp for f64 {
    fn from_sexp<R: FullBufRead>(sexp_token: SexpToken<R>) -> Result<Self> {
        match sexp_token {
            SexpToken::Number(n) => Ok(n as f64),
            SexpToken::Decimal(n, shift) => Ok(n as f64 * powi(0.1, shift as u32)),
            _ => Err(InvalidFloat),
        }
    }
}

impl FromSexp for f32 {
    fn from_sexp<R: FullBufRead>(sexp_token: SexpToken<R>) -> Result<Self> {
        f64::from_sexp(sexp_token).map(|x| x as f32)
    }
}

impl FromSexp for bool {
    fn from_sexp<R: FullBufRead>(sexp_token: SexpToken<R>) -> Result<Self> {
        match sexp_token {
            SexpToken::Symbol("true") => Ok(true),
            SexpToken::Symbol("false") => Ok(false),
            _ => Err(InvalidBool),
        }
    }
}

#[derive(Clone)]
struct FnSort {
    args: SmallVec<[Sort; 5]>,
    ret: Sort,
}
#[derive(Clone)]
enum Bound {
    Fn(FnSort),
    Const(Exp),
}

macro_rules! enum_str {
    ($name:ident {$($s:literal => $var:ident($min_args:literal),)*}) => {
        #[derive(Copy, Clone)]
        enum $name {
            $($var,)*
            Unknown(Symbol),
        }

        impl $name {
            fn from_str(s: &str, i: &mut InternInfo) -> Self {
                match s {
                    $($s => Self::$var,)*
                    _ => Self::Unknown(i.symbols.intern(s)),
                }
            }

            fn minimum_arguments(self) -> usize {
                match self {
                    $(Self::$var => $min_args,)*
                    Self::Unknown(_) => 0,
                }
            }

            fn to_str_sym(self) -> StrSym {
                match self {
                    $(Self::$var => StrSym::Str($s),)*
                    Self::Unknown(s) => StrSym::Sym(s),
                }
            }

            fn bind<'a, R: FullBufRead>(self, p: SexpParser<'a, R>) -> CountingParser<'a, R> {
                CountingParser::new(p, self.to_str_sym(), self.minimum_arguments())
            }
        }

        impl DisplayInterned for $name {
            fn fmt(&self, i: &InternInfo, f: &mut Formatter<'_>) -> std::fmt::Result {
                self.to_str_sym().fmt(i, f)
            }
        }
    };
}

enum_str! {Smt2Command{
    "declare-sort" => DeclareSort(1),
    "declare-fun" => DeclareFn(3),
    "declare-const" => DeclareConst(2),
    "define-const" => DefineConst(3),
    "define-fun" => DefineFn(4),
    "get-unsat-core" => GetUnsatCore(0),
    "get-value" => GetValue(1),
    "get-model" => GetModel(0),
    "assert" => Assert(1),
    "check-sat" => CheckSat(1),
    "check-sat-assuming" => CheckSatAssuming(1),
    "push" => Push(0),
    "pop" => Pop(0),
    "reset" => Reset(0),
    "set-logic" => SetLogic(1),
    "set-info" => SetInfo(2),
    "set-option" => SetOption(2),
    "exit" => Exit(0),
}}

enum_str! {ExpKind{
    "and" => And(0),
    "or" => Or(0),
    "not" => Not(1),
    "=>" => Imp(1),
    "xor" => Xor(0),
    "=" => Eq(1),
    "distinct" => Distinct(1),
    "let" => Let(2),
    "if" => If(3),
    "ite" => Ite(3),
    "!" => Annot(3),
}}

macro_rules! enum_option {
    ($name:ident {$($s:literal => $var:ident($ty:ty),)*}) => {
        #[derive(Copy, Clone, Debug)]
        enum $name {
            $($var($ty),)*
        }

        impl $name {
            fn from_parser<R: FullBufRead>(mut rest: CountingParser<R>) -> Result<Self> {
                enum Tmp {
                    $($var,)*
                }

                let tmp = match rest.next()? {
                    SexpToken::Keyword(s) => match s {
                        $($s => Tmp::$var,)*
                        _ => return Err(InvalidOption)
                    }
                    _ => return Err(InvalidOption),
                };
                let res = match tmp {
                    $(Tmp::$var => Self::$var(rest.next_parse()?),)*
                };
                rest.finish()?;
                Ok(res)
            }
        }
    };
}

enum_option! {SetOption{
    "sat.var_decay" => VarDecay(f32),
    "sat.clause_decay" => ClauseDecay(f64),
    "sat.random_var_freq" => RandomVarFreq(f64),
    "sat.random_seed" => RandomSeed(f64),
    "sat.luby_restart" => LubyRestart(bool),
    "sat.ccmin_mode" => CcminMode(i32),
    "sat.phase_saving" => PhaseSaving(i32),
    "sat.rnd_pol" => RndPol(bool),
    "sat.rnd_init_act" => RndInitAct(bool),
    "sat.garbage_frac" => GarbageFrac(f64),
    "sat.min_learnts_lim" => MinLearntsLim(i32),
    "sat.restart_first" => RestartFirst(i32),
    "sat.restart_inc" => RestartInc(f64),
    "sat.learntsize_factor" => LearntsizeFactor(f64),
    "sat.learntsize_inc" => LearntsizeInc(f64),
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
    bound: HashMap<Symbol, Bound, DefaultHashBuilder>,
    /// List of global variables in the order defined
    /// Used to remove global variable during `(pop)`
    global_stack: Vec<Symbol>,
    /// List of let bound variable with the old value they are shadowing
    let_bound_stack: Vec<(Symbol, Option<Bound>)>,
    /// A symbol we are currently defining (it cannot be used with :named even though it's not bound
    /// yet
    currently_defining: Option<Symbol>,
    declared_sorts: HashMap<Symbol, u32, DefaultHashBuilder>,
    sort_stack: Vec<Symbol>,
    push_info: Vec<PushInfo>,
    core: Solver,
    writer: W,
    state: State,
    last_status_info: Option<SolveResult>,
}

struct CountingParser<'a, R: FullBufRead> {
    p: SexpParser<'a, R>,
    name: StrSym,
    actual: usize,
    minimum_expected: usize,
}

type InfoToken<'a, R> = (SexpToken<'a, R>, usize, StrSym);

impl<'a, R: FullBufRead> CountingParser<'a, R> {
    fn new(p: SexpParser<'a, R>, name: StrSym, minimum_expected: usize) -> Self {
        CountingParser {
            p,
            name,
            actual: 0,
            minimum_expected,
        }
    }

    fn try_next_full(&mut self) -> Option<Result<InfoToken<'_, R>>> {
        debug_assert!(self.actual >= self.minimum_expected);
        let actual = self.actual;
        self.actual += 1;
        self.p.next().map(|x| Ok((x?, actual, self.name)))
    }

    fn map_full<U, F: FnMut(Result<InfoToken<'_, R>>) -> U>(
        mut self,
        mut f: F,
    ) -> impl Iterator<Item = U> + Bind<(F, Self)> {
        iter::from_fn(move || Some(f(self.try_next_full()?)))
    }

    fn next_full(&mut self) -> Result<InfoToken<'_, R>> {
        let actual = self.actual;
        let err = MissingArgument {
            f: self.name.into(),
            actual,
            expected: self.minimum_expected,
        };
        debug_assert!(self.actual < self.minimum_expected);
        self.actual += 1;
        Ok((self.p.next().ok_or(err)??, actual, self.name))
    }

    fn next(&mut self) -> Result<SexpToken<'_, R>> {
        Ok(self.next_full()?.0)
    }

    fn next_parse<N: FromSexp>(&mut self) -> Result<N> {
        Ok(N::from_sexp(self.next()?)?)
    }

    fn try_next_parse<N: FromSexp>(&mut self) -> Result<Option<N>> {
        match self.try_next_full() {
            None => Ok(None),
            Some(x) => N::from_sexp(x?.0).map(Some),
        }
    }

    fn finish(mut self) -> Result<()> {
        debug_assert!(self.actual >= self.minimum_expected);
        if self.p.next().is_some() {
            Err(ExtraArgument {
                f: self.name.into(),
                expected: self.actual,
            })
        } else {
            Ok(())
        }
    }

    /// Set the minimum expected arguments if it is only known dynamically
    fn set_minimum_expected(&mut self, minimum_expected: usize) {
        self.minimum_expected = minimum_expected
    }
}

fn pairwise_sym<T>(slice: &[T]) -> impl Iterator<Item = (&T, &T)> {
    (0..slice.len())
        .flat_map(move |i| (i + 1..slice.len()).map(move |j| (i, j)))
        .map(|(i, j)| (&slice[i], &slice[j]))
}

trait ExpParser {
    type Out;

    fn sort<W: Write>(&self, out: &Self::Out, p: &Parser<W>) -> Sort;

    fn parse<W: Write, R: FullBufRead>(
        &self,
        p: &mut Parser<W>,
        f: ExpKind,
        rest: CountingParser<R>,
    ) -> Result<Self::Out>;
}

struct BaseExpParser;

impl ExpParser for BaseExpParser {
    type Out = Exp;

    fn sort<W: Write>(&self, out: &Exp, p: &Parser<W>) -> Sort {
        p.core.sort(*out)
    }
    fn parse<W: Write, R: FullBufRead>(
        &self,
        p: &mut Parser<W>,
        f: ExpKind,
        mut rest: CountingParser<R>,
    ) -> Result<Exp> {
        let res = match f {
            ExpKind::Let => unreachable!(),
            ExpKind::Not => {
                let x = p.parse_bool(rest.next_full()?)?;
                rest.finish()?;
                (!x).into()
            }
            ExpKind::And => {
                let conj = rest
                    .map_full(|token| p.parse_bool(token?))
                    .collect::<Result<Conjunction>>()?;
                p.core.collapse_bool(conj).into()
            }
            ExpKind::Or => {
                let disj = rest
                    .map_full(|token| p.parse_bool(token?))
                    .collect::<Result<Disjunction>>()?;
                p.core.collapse_bool(disj).into()
            }
            ExpKind::Imp => {
                let mut last = p.parse_bool(rest.next_full()?)?;
                let not_last = rest.map_full(|token| {
                    let item = p.parse_bool(token?)?;
                    Ok(!std::mem::replace(&mut last, item))
                });
                let res = not_last.collect::<Result<Disjunction>>()? | last;
                p.core.collapse_bool(res).into()
            }
            ExpKind::Xor => {
                let mut res = BoolExp::FALSE;
                rest.map_full(|token| {
                    let parsed = p.parse_bool(token?)?;
                    res = p.core.xor(res, parsed);
                    Ok(())
                })
                .collect::<Result<()>>()?;
                res.into()
            }
            ExpKind::Eq => {
                let exp1 = p.parse_exp(rest.next()?)?;
                let (id1, sort1) = p.core.id_sort(exp1);
                let conj = rest
                    .map_full(|x| {
                        let id2 = p.parse_id(x?, sort1)?;
                        Ok(p.core.raw_eq(id1, id2))
                    })
                    .collect::<Result<Conjunction>>()?;
                p.core.collapse_bool(conj).into()
            }
            ExpKind::Distinct => {
                let exp1 = p.parse_exp(rest.next()?)?;
                let (id1, sort1) = p.core.id_sort(exp1);
                let iter = rest.map_full(|x| p.parse_id(x?, sort1));
                let ids = [Ok(id1)]
                    .into_iter()
                    .chain(iter)
                    .collect::<Result<Vec<Id>>>()?;
                let conj: Conjunction = pairwise_sym(&ids)
                    .map(|(&id1, &id2)| !p.core.raw_eq(id1, id2))
                    .collect();
                p.core.collapse_bool(conj).into()
            }
            ExpKind::Ite | ExpKind::If => {
                let i = p.parse_bool(rest.next_full()?)?;
                let t = p.parse_exp(rest.next()?)?;
                let e = p.parse_exp(rest.next()?)?;
                rest.finish()?;
                let err_m = |(left, right)| IteSortMismatch { left, right };
                p.core.ite(i, t, e).map_err(err_m)?
            }
            ExpKind::Annot => {
                let exp = p.parse_exp(rest.next()?)?;
                let SexpToken::Keyword(k) = rest.next()? else {
                    return Err(InvalidAnnot);
                };
                if k != "named" {
                    return Err(InvalidAnnotAttr(p.core.intern.symbols.intern(k)));
                }
                let SexpToken::Symbol(s) = rest.next()? else {
                    return Err(InvalidAnnot);
                };
                let s = p.core.intern.symbols.intern(s);
                if p.bound.contains_key(&s) || p.currently_defining == Some(s) {
                    return Err(NamedShadow(s));
                }
                // we now know that `s` isn't bound anywhere, so we can insert it without shadowing
                // a let bound variable that should have higher priority
                p.insert_bound(s, Bound::Const(exp));
                exp
            }
            ExpKind::Unknown(f) => {
                // Uninterpreted function
                let sig = p.bound.get(&f).ok_or(Unbound(f))?.clone();
                match sig {
                    Bound::Fn(sig) => {
                        rest.set_minimum_expected(sig.args.len());
                        let mut children = Children::new();
                        for sort in sig.args.iter().copied() {
                            children.push(p.parse_id(rest.next_full()?, sort)?)
                        }
                        rest.finish()?;
                        p.core.sorted_fn(f, children, sig.ret)
                    }
                    Bound::Const(c) => {
                        rest.finish()?;
                        p.core.canonize(c)
                    }
                }
            }
        };
        Ok(res)
    }
}

struct AssertExpParser {
    // assert (exp ^ self.negate)
    negate: bool,
}

impl ExpParser for AssertExpParser {
    type Out = core::result::Result<(), Sort>;

    fn sort<W: Write>(&self, out: &Self::Out, p: &Parser<W>) -> Sort {
        match out {
            Ok(()) => p.core.bool_sort(),
            Err(s) => *s,
        }
    }
    fn parse<W: Write, R: FullBufRead>(
        &self,
        p: &mut Parser<W>,
        f: ExpKind,
        mut rest: CountingParser<R>,
    ) -> Result<Self::Out> {
        match (f, self.negate) {
            (ExpKind::And, neg @ false) | (ExpKind::Or, neg @ true) => {
                rest.map_full(|token| p.parse_assert(token?, neg))
                    .collect::<Result<()>>()?;
            }
            (ExpKind::Not, neg) => {
                p.parse_assert(rest.next_full()?, !neg)?;
            }
            (ExpKind::Eq, false) => {
                let exp1 = p.parse_exp(rest.next()?)?;
                let (id1, sort1) = p.core.id_sort(exp1);
                rest.map_full(|x| {
                    let id2 = p.parse_id(x?, sort1)?;
                    Ok(p.core.assert_raw_eq(id1, id2))
                })
                .collect::<Result<()>>()?;
            }
            (ExpKind::Distinct, false) => {
                let exp1 = p.parse_exp(rest.next()?)?;
                let (id1, sort1) = p.core.id_sort(exp1);
                let iter = rest.map_full(|x| p.parse_id(x?, sort1));
                let ids = [Ok(id1)]
                    .into_iter()
                    .chain(iter)
                    .collect::<Result<Vec<Id>>>()?;
                p.core.assert_distinct(ids)
            }
            (ExpKind::Unknown(f), neg) => {
                let sig = p.bound.get(&f).ok_or(Unbound(f))?.clone();
                match sig {
                    Bound::Fn(sig) => {
                        rest.set_minimum_expected(sig.args.len());
                        let mut children = Children::new();
                        for sort in sig.args.iter().copied() {
                            children.push(p.parse_id(rest.next_full()?, sort)?)
                        }
                        rest.finish()?;
                        if sig.ret != p.core.bool_sort() {
                            return Ok(Err(sig.ret));
                        }
                        p.core.assert_bool_fn(f, children, neg);
                    }
                    Bound::Const(exp) => {
                        rest.finish()?;
                        match exp.as_bool() {
                            None => return Ok(Err(p.core.sort(exp))),
                            Some(b) => p.core.assert(b ^ neg),
                        }
                    }
                }
            }
            (_, neg) => {
                let exp = BaseExpParser.parse(p, f, rest)?;
                match exp.as_bool() {
                    None => return Ok(Err(p.core.sort(exp))),
                    Some(b) => p.core.assert(b ^ neg),
                }
            }
        };
        Ok(Ok(()))
    }
}

impl<W: Write> Parser<W> {
    fn new(writer: W) -> Self {
        let mut res = Parser {
            bound: Default::default(),
            global_stack: Default::default(),
            let_bound_stack: Default::default(),
            push_info: vec![],
            declared_sorts: Default::default(),
            core: Default::default(),
            writer,
            state: State::Base,
            sort_stack: vec![],
            last_status_info: None,
            currently_defining: None,
        };
        res.declared_sorts.insert(BOOL_SYM, 0);
        res.bound
            .insert(TRUE_SYM, Bound::Const(BoolExp::TRUE.into()));
        res.bound
            .insert(FALSE_SYM, Bound::Const(BoolExp::FALSE.into()));
        res
    }

    fn handle_as<R: FullBufRead>(&mut self, rest: SexpParser<R>) -> Result<(ExpKind, Sort)> {
        let mut rest = CountingParser::new(rest, StrSym::Str("as"), 2);
        let SexpToken::Symbol(s) = rest.next()? else {
            return Err(InvalidExp);
        };
        let s = ExpKind::from_str(s, &mut self.core.intern);
        let sort = self.parse_sort(rest.next()?)?;
        rest.finish()?;
        Ok((s, sort))
    }

    fn parse_exp_gen<R: FullBufRead, P: ExpParser>(
        &mut self,
        token: SexpToken<R>,
        p: &P,
    ) -> Result<P::Out> {
        match token {
            SexpToken::Symbol(s) => {
                let exp = ExpKind::from_str(s, &mut self.core.intern);
                SexpParser::with_empty(|l| self.parse_fn_exp_gen(exp, l, None, p))
            }
            SexpToken::String(_) => Err(Unsupported("strings")),
            SexpToken::Number(_) => Err(Unsupported("arithmetic")),
            SexpToken::Decimal(_, _) => Err(Unsupported("decimal")),
            SexpToken::BitVec { .. } => Err(Unsupported("bitvec")),
            SexpToken::List(mut l) => {
                let status = match l.next().ok_or(InvalidExp)?? {
                    SexpToken::Symbol("as") => None,
                    SexpToken::Symbol(s) => {
                        Some((ExpKind::from_str(s, &mut self.core.intern), None))
                    }
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
                    self.parse_fn_exp_gen(s, l, sort, p)
                } else {
                    let (s, sort) = self.handle_as(l)?;
                    SexpParser::with_empty(|l| self.parse_fn_exp_gen(s, l, Some(sort), p))
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

    // assert token ^ negate
    fn parse_assert<R: FullBufRead>(
        &mut self,
        (token, arg_n, f): InfoToken<R>,
        negate: bool,
    ) -> Result<()> {
        let exp = self.parse_exp_gen(token, &AssertExpParser { negate })?;
        exp.map_err(|actual| SortMismatch {
            f,
            arg_n,
            actual,
            expected: self.core.bool_sort(),
        })
    }

    fn parse_id<R: FullBufRead>(
        &mut self,
        (token, arg_n, f): InfoToken<R>,
        expected: Sort,
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
                    SexpToken::Symbol(s) => self.core.intern.symbols.intern(s),
                    _ => return Err(InvalidBinding),
                };
                let exp = self.parse_exp(l.next().ok_or(InvalidBinding)??)?;
                Ok((sym, exp))
            }
            _ => Err(InvalidBinding),
        }
    }

    fn undo_let_bindings(&mut self, old_len: usize) {
        for (name, bound) in self.let_bound_stack.drain(old_len..).rev() {
            match bound {
                None => self.bound.remove(&name),
                Some(x) => self.bound.insert(name, x),
            };
        }
    }
    fn undo_base_bindings(&mut self, old_len: usize) {
        for name in self.global_stack.drain(old_len..).rev() {
            self.bound.remove(&name);
        }
    }

    fn parse_fn_exp_gen<R: FullBufRead, P: ExpParser>(
        &mut self,
        f: ExpKind,
        rest: SexpParser<R>,
        expect_res: Option<Sort>,
        p: &P,
    ) -> Result<P::Out> {
        let mut rest = f.bind(rest);
        let res = match f {
            ExpKind::Let => {
                let old_len = self.let_bound_stack.len();
                match rest.next()? {
                    SexpToken::List(mut l) => l
                        .map(|token| {
                            let (name, exp) = self.parse_binding(token?)?;
                            self.let_bound_stack.push((name, Some(Bound::Const(exp))));
                            Ok(())
                        })
                        .collect::<Result<()>>()?,
                    _ => return Err(InvalidLet),
                }
                let body = rest.next()?;
                for (name, bound) in &mut self.let_bound_stack[old_len..] {
                    *bound = self.bound.insert(*name, bound.take().unwrap())
                }
                let exp = self.parse_exp_gen(body, p)?;
                rest.finish()?;
                self.undo_let_bindings(old_len);
                exp
            }
            _ => p.parse(self, f, rest)?,
        };
        if let Some(expected) = expect_res {
            let actual = p.sort(&res, &self);
            if actual != expected {
                return Err(AsSortMismatch {
                    f,
                    actual,
                    expected,
                });
            }
        };
        return Ok(res);
    }

    fn parse_exp<R: FullBufRead>(&mut self, token: SexpToken<R>) -> Result<Exp> {
        self.parse_exp_gen(token, &BaseExpParser)
    }

    fn create_sort(&mut self, name: Symbol, params: &[Sort]) -> Result<Sort> {
        let len = params.len();
        match self.declared_sorts.get(&name) {
            None => Err(UnboundSort(name)),
            Some(x) if (*x as usize) < len => Err(MissingArgument {
                f: name.into(),
                expected: *x as usize,
                actual: len,
            }),
            Some(x) if *x as usize > len => Err(ExtraArgument {
                f: name.into(),
                expected: *x as usize,
            }),
            _ => Ok(self.core.intern.sorts.intern(name, params)),
        }
    }

    fn parse_sort<R: FullBufRead>(&mut self, token: SexpToken<R>) -> Result<Sort> {
        match token {
            SexpToken::Symbol(s) => {
                let s = self.core.intern.symbols.intern(s);
                self.create_sort(s, &[])
            }
            SexpToken::List(mut l) => {
                let name = match l.next().ok_or(InvalidSort)?? {
                    SexpToken::Symbol(s) => self.core.intern.symbols.intern(s),
                    _ => return Err(InvalidSort),
                };
                let params = l.map(|x| self.parse_sort(x?)).collect::<Result<Vec<_>>>()?;
                self.create_sort(name, &params)
            }
            _ => return Err(InvalidSort),
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
        let old_len = self.global_stack.len();
        match self.parse_command_h(name, rest) {
            Ok(()) => Ok(()),
            Err(err) => {
                self.undo_base_bindings(old_len);
                Err(err)
            }
        }
    }

    fn parse_command_h<R: FullBufRead>(
        &mut self,
        name: Smt2Command,
        rest: SexpParser<R>,
    ) -> Result<()> {
        let mut rest = name.bind(rest);
        match name {
            Smt2Command::DeclareSort => {
                let SexpToken::Symbol(name) = rest.next()? else {
                    return Err(InvalidCommand);
                };
                let name = self.core.intern.symbols.intern(name);
                if self.declared_sorts.contains_key(&name) {
                    return Err(Shadow(name));
                }
                let args = rest.try_next_parse()?.unwrap_or(0);
                rest.finish()?;
                self.sort_stack.push(name);
                self.declared_sorts.insert(name, args);
            }
            Smt2Command::GetUnsatCore => {
                let State::Unsat(info) = &self.state else {
                    return Err(NoCore);
                };
                write!(self.writer, "(").unwrap();
                let mut iter = info
                    .core(self.core.last_unsat_core())
                    .map(|x| rest.p.lookup_range(*x));
                if let Some(x) = iter.next() {
                    write!(self.writer, "{x}").unwrap();
                }
                for x in iter {
                    write!(self.writer, " {x}").unwrap();
                }
                writeln!(self.writer, ")").unwrap();
                rest.finish()?;
            }
            Smt2Command::GetValue => {
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
                let mut iter = values.into_iter().map(|(exp, span)| {
                    (
                        exp.with_intern(&self.core.intern),
                        rest.p.lookup_range(span),
                    )
                });
                if let Some((x, lit)) = iter.next() {
                    write!(self.writer, "({lit} {x})").unwrap();
                }
                for (x, lit) in iter {
                    write!(self.writer, "\n ({lit} {x})").unwrap();
                }
                writeln!(self.writer, ")").unwrap();
                rest.finish()?;
            }
            Smt2Command::GetModel => {
                rest.finish()?;
                if !matches!(self.state, State::Model) {
                    return Err(NoModel);
                }
                let (funs, core) = self.core.function_info();
                writeln!(self.writer, "(").unwrap();
                let mut bound: Vec<_> = self
                    .bound
                    .keys()
                    .copied()
                    .filter(|k| !matches!(*k, TRUE_SYM | FALSE_SYM))
                    .collect();
                let intern = &core.intern;
                bound.sort_unstable_by_key(|x| intern.symbols.resolve(*x));
                for k in bound {
                    let k_i = k.with_intern(intern);
                    match &self.bound[&k] {
                        Bound::Const(x) => {
                            let x = core.canonize(*x);
                            let sort = core.sort(x).with_intern(intern);
                            let x = x.with_intern(intern);
                            writeln!(self.writer, " (define-fun {k_i} () {sort} {x})").unwrap();
                        }
                        Bound::Fn(f) => {
                            let args =
                                f.args.iter().enumerate().map(|(i, s)| {
                                    format_args2!("(x!{i} {})", s.with_intern(intern))
                                });
                            let args = parenthesized(args, " ");
                            let ret = f.ret.with_intern(intern);
                            writeln!(self.writer, " (define-fun {k_i} {args} {ret}").unwrap();
                            write_body(&mut self.writer, &funs, k, intern);
                        }
                    }
                }
                writeln!(self.writer, ")").unwrap();
            }
            Smt2Command::SetLogic => {
                match rest.next()? {
                    SexpToken::Symbol("QF_UF") => {}
                    SexpToken::Symbol(_) => return Err(Unsupported("logic")),
                    _ => return Err(InvalidCommand),
                }
                rest.finish()?;
            }
            Smt2Command::SetInfo => {
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
            Smt2Command::SetOption => {
                let mut prev_option = self.core.sat_options();
                match SetOption::from_parser(rest)? {
                    SetOption::VarDecay(x) => prev_option.var_decay = x,
                    SetOption::ClauseDecay(x) => prev_option.clause_decay = x,
                    SetOption::RandomVarFreq(x) => prev_option.random_var_freq = x,
                    SetOption::RandomSeed(x) => prev_option.random_seed = x,
                    SetOption::LubyRestart(x) => prev_option.luby_restart = x,
                    SetOption::CcminMode(x) => prev_option.ccmin_mode = x,
                    SetOption::PhaseSaving(x) => prev_option.phase_saving = x,
                    SetOption::RndPol(x) => prev_option.rnd_pol = x,
                    SetOption::RndInitAct(x) => prev_option.rnd_init_act = x,
                    SetOption::GarbageFrac(x) => prev_option.garbage_frac = x,
                    SetOption::MinLearntsLim(x) => prev_option.min_learnts_lim = x,
                    SetOption::RestartFirst(x) => prev_option.restart_first = x,
                    SetOption::RestartInc(x) => prev_option.restart_inc = x,
                    SetOption::LearntsizeFactor(x) => prev_option.learntsize_factor = x,
                    SetOption::LearntsizeInc(x) => prev_option.learntsize_inc = x,
                }
                self.core
                    .set_sat_options(prev_option)
                    .map_err(|()| InvalidOption)?;
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

    fn parse_fresh_binder<R: FullBufRead>(&mut self, token: SexpToken<R>) -> Result<Symbol> {
        let SexpToken::Symbol(name) = token else {
            return Err(InvalidCommand);
        };
        let name = self.core.intern.symbols.intern(name);
        if self.bound.contains_key(&name) {
            return Err(Shadow(name));
        }
        Ok(name)
    }

    fn clear(&mut self) {
        self.push_info.clear();
        self.global_stack.clear();
        self.bound.clear();
        self.core.clear();
        self.declared_sorts.clear();
        self.sort_stack.clear();
        self.declared_sorts.insert(BOOL_SYM, 0);
        self.bound
            .insert(TRUE_SYM, Bound::Const(BoolExp::TRUE.into()));
        self.bound
            .insert(FALSE_SYM, Bound::Const(BoolExp::FALSE.into()));
    }

    fn parse_destructive_command<R: FullBufRead>(
        &mut self,
        name: Smt2Command,
        mut rest: CountingParser<R>,
    ) -> Result<()> {
        self.reset_state();
        match name {
            Smt2Command::DeclareFn => {
                let name = self.parse_fresh_binder(rest.next()?)?;
                let SexpToken::List(mut l) = rest.next()? else {
                    return Err(InvalidCommand);
                };
                let args = l
                    .map(|t| self.parse_sort(t?))
                    .collect::<Result<SmallVec<_>>>()?;
                drop(l);
                let ret = self.parse_sort(rest.next()?)?;
                rest.finish()?;
                if args.is_empty() {
                    self.declare_const(name, ret);
                } else {
                    let fn_sort = FnSort { args, ret };
                    self.insert_bound(name, Bound::Fn(fn_sort));
                }
            }
            Smt2Command::DeclareConst => {
                let name = self.parse_fresh_binder(rest.next()?)?;
                let ret = self.parse_sort(rest.next()?)?;
                rest.finish()?;
                self.declare_const(name, ret);
            }
            Smt2Command::DefineConst => {
                let name = self.parse_fresh_binder(rest.next()?)?;
                self.define_const(name, rest)?;
            }
            Smt2Command::DefineFn => {
                let name = self.parse_fresh_binder(rest.next()?)?;
                let SexpToken::List(mut args) = rest.next()? else {
                    return Err(InvalidCommand);
                };
                if args.next().is_some() {
                    return Err(InvalidDefineFun);
                }
                drop(args);
                self.define_const(name, rest)?;
            }
            Smt2Command::Assert => {
                self.parse_assert(rest.next_full()?, false)?;
                rest.finish()?;
            }
            Smt2Command::CheckSat => {
                let res = self
                    .core
                    .check_sat_assuming_preserving_trail(&Default::default());
                self.set_state(res, Default::default())?;
                writeln!(self.writer, "{}", res.as_lower_str()).unwrap()
            }
            Smt2Command::CheckSatAssuming => {
                let SexpToken::List(mut l) = rest.next()? else {
                    return Err(InvalidCommand);
                };
                let conj = l
                    .zip_map_full(0.., |token, i| {
                        self.parse_bool((token?, i, name.to_str_sym()))
                    })
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
                let n = rest.try_next_parse()?.unwrap_or(1);
                for _ in 0..n {
                    self.core.push();
                    let info = PushInfo {
                        bound: self.global_stack.len(),
                        sort: self.sort_stack.len(),
                    };
                    self.push_info.push(info);
                }
            }
            Smt2Command::Pop => {
                let n = rest.try_next_parse()?.unwrap_or(1);
                if n > self.push_info.len() {
                    self.clear()
                } else if n > 0 {
                    self.core.pop(n);
                    let mut info = None;
                    for _ in 0..n {
                        info = self.push_info.pop();
                    }
                    let info = info.unwrap();
                    self.undo_base_bindings(info.bound);

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

    fn define_const<R: FullBufRead>(
        &mut self,
        name: Symbol,
        mut rest: CountingParser<R>,
    ) -> Result<()> {
        let sort = self.parse_sort(rest.next()?)?;
        self.currently_defining = Some(name);
        let ret = self.parse_exp(rest.next()?)?;
        self.currently_defining = None;
        if sort != self.core.sort(ret) {
            return Err(BindSortMismatch(self.core.sort(ret)));
        }
        rest.finish()?;
        self.insert_bound(name, Bound::Const(ret));
        Ok(())
    }

    fn insert_bound(&mut self, name: Symbol, val: Bound) {
        let res = self.bound.insert(name, val);
        debug_assert!(res.is_none());
        self.global_stack.push(name)
    }

    fn declare_const(&mut self, name: Symbol, ret: Sort) {
        let exp = if ret == self.core.bool_sort() {
            self.core.fresh_bool().into()
        } else {
            self.core.sorted_fn(name, Children::new(), ret)
        };
        debug!(
            "{} is bound to {exp:?}",
            name.with_intern(&self.core.intern)
        );
        self.insert_bound(name, Bound::Const(exp));
    }

    fn parse_command_token<R: FullBufRead>(&mut self, t: SexpToken<R>) -> Result<()> {
        match t {
            SexpToken::List(mut l) => {
                let s = match l.next().ok_or(InvalidCommand)?? {
                    SexpToken::Symbol(s) => Smt2Command::from_str(s, &mut self.core.intern),
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
            self,
            |this, t| this.parse_command_token(t?),
            |this, e| writeln!(err, "{}", e.map(|x| x.with_intern(&this.core.intern))).unwrap(),
        );
    }
}

fn write_body<W: Write>(
    writer: &mut W,
    info: &FullFunctionInfo,
    name: Symbol,
    intern: &InternInfo,
) {
    let cases = info.get(name);
    let name = name.with_intern(intern);
    let len = cases.len();
    for (case, res) in cases {
        let res = res.with_intern(intern);
        let mut case = case
            .enumerate()
            .map(|(i, x)| format_args2!("(= x!{i} {})", x.with_intern(intern)));
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
pub fn interp_smt2(data: impl FullBufRead, out: impl Write, err: impl Write) {
    let mut p = Parser::new(out);
    p.interp_smt2(data, err)
}
