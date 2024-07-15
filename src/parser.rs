use crate::egraph::Children;
use crate::euf::FullFunctionInfo;
use crate::full_buf_read::FullBufRead;
use crate::intern::{
    DisplayInterned, InternInfo, Sort, Symbol, WithIntern, BOOL_SORT, BOOL_SYM, FALSE_SYM, TRUE_SYM,
};
use crate::junction::{Conjunction, Disjunction};
use crate::parser::Error::*;
use crate::parser_core::{ParseError, SexpParser, SexpToken, SpanRange};
use crate::solver::{BoolExp, Exp, SolveResult, Solver, UnsatCoreConjunction};
use crate::util::{format_args2, parenthesized, powi, Bind, DefaultHashBuilder};
use core::fmt::Arguments;
use hashbrown::HashMap;
use log::debug;
use no_std_compat::prelude::v1::*;
use plat_egg::Id;
use second_stack_vec::{Stack, StackMemory};
use smallvec::SmallVec;
use std::fmt::Formatter;
use std::fmt::Write;
use std::iter;

struct PrintSuccessWriter<W> {
    writer: W,
    print_success: bool,
}

impl<W: Write> PrintSuccessWriter<W> {
    fn new(writer: W) -> Self {
        PrintSuccessWriter {
            writer,
            print_success: false,
        }
    }

    #[inline]
    fn write_fmt(&mut self, args: Arguments<'_>) {
        self.print_success = false;
        self.writer.write_fmt(args).unwrap()
    }
}

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
    ProduceCoreFalse,
    NoModel,
    ProduceModelFalse,
    NonInit,
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
            ProduceCoreFalse => write!(fmt, "The option `:produce-unsat-cores` must be set to true"),
            NoModel => write!(fmt, "The last command was not `check-sat-assuming` that returned `sat`"),
            ProduceModelFalse => write!(fmt, "The option `:produce-models` must be set to true"),
            NonInit => write!(fmt, "The option cannot be set after assertions, declarations, or definitions"),
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
    "reset-assertions" => ResetAssertions(0),
    "set-logic" => SetLogic(1),
    "set-info" => SetInfo(2),
    "set-option" => SetOption(2),
    "echo" => Echo(1),
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
    "random-seed" => BaseRandomSeed(f64),
    "produce-models" => ProduceModels(bool),
    "produce-unsat-cores" => ProduceUnsatCores(bool),
    "print-success" => PrintSuccess(bool),
}}

enum UnsatCoreElt {
    /// from `check_sat_assuming`
    Span(SpanRange),
    /// from `:named` assertions
    Sym(Symbol),
}

#[derive(Default)]
enum State {
    Unsat,
    Model,
    Base,
    #[default]
    Init,
}

struct PushInfo {
    sort: u32,
    bound: u32,
    named_assert: u32,
}

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
    /// assertions named a top level that we always add to assumption list of `check_sat` instead
    /// of immediately asserting.
    /// Between a command `(check-sat-assuming)` and the next destructive command,
    /// `named_assertions` also contains the assumptions from `check-sat-assuming` and
    /// `old_named_assertion` contains the length it had before they were added
    named_assertions: UnsatCoreConjunction<UnsatCoreElt>,
    // see above
    old_named_assertions: u32,
    push_info: Vec<PushInfo>,
    core: Solver,
    writer: PrintSuccessWriter<W>,
    state: State,
    options: Options,
    last_status_info: Option<SolveResult>,
}

struct Options {
    produce_models: bool,
    produces_unsat_cores: bool,
    print_success: bool,
}

impl Default for Options {
    fn default() -> Self {
        Options {
            produce_models: true,
            produces_unsat_cores: true,
            print_success: false,
        }
    }
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
        stack: &mut Stack,
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
        stack: &mut Stack,
    ) -> Result<Exp> {
        let res = match f {
            ExpKind::Let => unreachable!(),
            ExpKind::Not => {
                let x = p.parse_bool(rest.next_full()?, stack)?;
                rest.finish()?;
                (!x).into()
            }
            ExpKind::And => {
                let mut iter = rest.map_full(|token| p.parse_bool(token?, stack));
                let conj = iter.by_ref().collect::<Result<Conjunction>>()?;
                iter.try_for_each(|x| x.map(drop))?;
                drop(iter);
                p.core.collapse_bool(conj).into()
            }
            ExpKind::Or => {
                let mut iter = rest.map_full(|token| p.parse_bool(token?, stack));
                let disj = iter.by_ref().collect::<Result<Disjunction>>()?;
                iter.try_for_each(|x| x.map(drop))?;
                drop(iter);
                p.core.collapse_bool(disj).into()
            }
            ExpKind::Imp => {
                let mut last = p.parse_bool(rest.next_full()?, stack)?;
                let not_last = rest.map_full(|token| {
                    let item = p.parse_bool(token?, stack)?;
                    Ok(!std::mem::replace(&mut last, item))
                });
                let res = not_last.collect::<Result<Disjunction>>()? | last;
                p.core.collapse_bool(res).into()
            }
            ExpKind::Xor => {
                let mut res = BoolExp::FALSE;
                rest.map_full(|token| {
                    let parsed = p.parse_bool(token?, stack)?;
                    res = p.core.xor(res, parsed);
                    Ok(())
                })
                .collect::<Result<()>>()?;
                res.into()
            }
            ExpKind::Eq => {
                let exp1 = p.parse_exp(rest.next()?, stack)?;
                let (id1, sort1) = p.core.id_sort(exp1);
                let conj = rest
                    .map_full(|x| {
                        let id2 = p.parse_id(x?, sort1, stack)?;
                        Ok(p.core.raw_eq(id1, id2))
                    })
                    .collect::<Result<Conjunction>>()?;
                p.core.collapse_bool(conj).into()
            }
            ExpKind::Distinct => {
                let exp1 = p.parse_exp(rest.next()?, stack)?;
                let (id1, sort1) = p.core.id_sort(exp1);
                stack.with_vec(|mut ids| {
                    ids.push(id1);
                    while let Some(x) = rest.try_next_full() {
                        let id = p.parse_id(x?, sort1, &mut ids.stack())?;
                        ids.push(id);
                    }
                    let conj: Conjunction = pairwise_sym(&ids)
                        .map(|(&id1, &id2)| !p.core.raw_eq(id1, id2))
                        .collect();
                    Result::Ok(p.core.collapse_bool(conj).into())
                })?
            }
            ExpKind::Ite | ExpKind::If => {
                let i = p.parse_bool(rest.next_full()?, stack)?;
                let t = p.parse_exp(rest.next()?, stack)?;
                let e = p.parse_exp(rest.next()?, stack)?;
                rest.finish()?;
                let err_m = |(left, right)| IteSortMismatch { left, right };
                p.core.ite(i, t, e).map_err(err_m)?
            }
            ExpKind::Annot => {
                let exp = p.parse_exp(rest.next()?, stack)?;
                p.parse_annot_after_exp(exp, rest)?;
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
                            children.push(p.parse_id(rest.next_full()?, sort, stack)?)
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
    top_level: bool,
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
        stack: &mut Stack,
    ) -> Result<Self::Out> {
        match (f, self.negate) {
            (ExpKind::And, neg @ false) | (ExpKind::Or, neg @ true) => {
                rest.map_full(|token| p.parse_assert(token?, neg, false, stack))
                    .collect::<Result<()>>()?;
            }
            (ExpKind::Not, neg) => {
                p.parse_assert(rest.next_full()?, !neg, false, stack)?;
            }
            (ExpKind::Eq, false) => {
                let exp1 = p.parse_exp(rest.next()?, stack)?;
                let (id1, sort1) = p.core.id_sort(exp1);
                rest.map_full(|x| {
                    let id2 = p.parse_id(x?, sort1, stack)?;
                    Ok(p.core.assert_raw_eq(id1, id2))
                })
                .collect::<Result<()>>()?;
            }
            (ExpKind::Distinct, false) => {
                let exp1 = p.parse_exp(rest.next()?, stack)?;
                let (id1, sort1) = p.core.id_sort(exp1);
                stack.with_vec(|mut ids| {
                    ids.push(id1);
                    while let Some(x) = rest.try_next_full() {
                        let id =  p.parse_id(x?, sort1, &mut ids.stack())?;
                        ids.push(id);
                    }
                    p.core.assert_distinct(ids.iter().copied());
                    Result::Ok(())
                })?;
            }
            (ExpKind::Unknown(f), neg) => {
                let sig = p.bound.get(&f).ok_or(Unbound(f))?.clone();
                match sig {
                    Bound::Fn(sig) => {
                        rest.set_minimum_expected(sig.args.len());
                        let mut children = Children::new();
                        for sort in sig.args.iter().copied() {
                            children.push(p.parse_id(rest.next_full()?, sort, stack)?)
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
            (ExpKind::Annot, neg) => {
                if self.top_level {
                    debug_assert!(!neg);
                    let exp = p.parse_exp(rest.next()?, stack)?;
                    let name = p.parse_annot_after_exp(exp, rest)?;
                    match exp.as_bool() {
                        None => return Ok(Err(p.core.sort(exp))),
                        Some(b) => {
                            p.named_assertions.extend([(b, UnsatCoreElt::Sym(name))]);
                            p.old_named_assertions = p.named_assertions.push();
                        }
                    }
                } else {
                    p.parse_assert(rest.next_full()?, neg, false, stack)?;
                    // since we asserted exp ^ neg, exp will always equal !neg as long as the
                    // problem is satisfiable
                    p.parse_annot_after_exp(BoolExp::Const(!neg).into(), rest)?;
                }
            }
            (_, neg) => {
                let exp = BaseExpParser.parse(p, f, rest, stack)?;
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
            writer: PrintSuccessWriter::new(writer),
            state: State::Init,
            sort_stack: vec![],
            last_status_info: None,
            currently_defining: None,
            named_assertions: UnsatCoreConjunction::default(),
            old_named_assertions: 0,
            options: Default::default(),
        };
        res.declared_sorts.insert(BOOL_SYM, 0);
        res.bound
            .insert(TRUE_SYM, Bound::Const(BoolExp::TRUE.into()));
        res.bound
            .insert(FALSE_SYM, Bound::Const(BoolExp::FALSE.into()));
        res
    }

    fn handle_as<R: FullBufRead>(&mut self, rest: SexpParser<R>, stack: &mut Stack) -> Result<(ExpKind, Sort)> {
        let mut rest = CountingParser::new(rest, StrSym::Str("as"), 2);
        let SexpToken::Symbol(s) = rest.next()? else {
            return Err(InvalidExp);
        };
        let s = ExpKind::from_str(s, &mut self.core.intern);
        let sort = self.parse_sort(rest.next()?, stack)?;
        rest.finish()?;
        Ok((s, sort))
    }

    fn parse_exp_gen<R: FullBufRead, P: ExpParser>(
        &mut self,
        token: SexpToken<R>,
        p: &P,
        stack: &mut Stack
    ) -> Result<P::Out> {
        match token {
            SexpToken::Symbol(s) => {
                let exp = ExpKind::from_str(s, &mut self.core.intern);
                SexpParser::with_empty(|l| self.parse_fn_exp_gen(exp, l, None, p, stack))
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
                            let (s, sort) = self.handle_as(l2, stack)?;
                            Some((s, Some(sort)))
                        } else {
                            return Err(InvalidExp);
                        }
                    }
                    _ => return Err(InvalidExp),
                };
                if let Some((s, sort)) = status {
                    self.parse_fn_exp_gen(s, l, sort, p, stack)
                } else {
                    let (s, sort) = self.handle_as(l, stack)?;
                    SexpParser::with_empty(|l| self.parse_fn_exp_gen(s, l, Some(sort), p, stack))
                }
            }
            SexpToken::Keyword(_) => Err(InvalidExp),
        }
    }

    fn parse_bool<R: FullBufRead>(&mut self, (token, arg_n, f): InfoToken<R>, stack: &mut Stack) -> Result<BoolExp> {
        let exp = self.parse_exp(token, stack)?;
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
        top_level: bool,
        stack: &mut Stack
    ) -> Result<()> {
        let exp = self.parse_exp_gen(token, &AssertExpParser { negate, top_level }, stack)?;
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
        stack: &mut Stack,
    ) -> Result<Id> {
        let exp = self.parse_exp(token, stack)?;
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

    fn parse_binding<R: FullBufRead>(&mut self, token: SexpToken<R>, stack: &mut Stack) -> Result<(Symbol, Exp)> {
        match token {
            SexpToken::List(mut l) => {
                let sym = match l.next().ok_or(InvalidBinding)?? {
                    SexpToken::Symbol(s) => self.core.intern.symbols.intern(s),
                    _ => return Err(InvalidBinding),
                };
                let exp = self.parse_exp(l.next().ok_or(InvalidBinding)??, stack)?;
                Ok((sym, exp))
            }
            _ => Err(InvalidBinding),
        }
    }

    fn parse_annot_after_exp<R: FullBufRead>(
        &mut self,
        exp: Exp,
        mut rest: CountingParser<R>,
    ) -> Result<Symbol> {
        let SexpToken::Keyword(k) = rest.next()? else {
            return Err(InvalidAnnot);
        };
        if k != "named" {
            return Err(InvalidAnnotAttr(self.core.intern.symbols.intern(k)));
        }
        let SexpToken::Symbol(s) = rest.next()? else {
            return Err(InvalidAnnot);
        };
        let s = self.core.intern.symbols.intern(s);
        rest.finish()?;
        if self.bound.contains_key(&s) || self.currently_defining == Some(s) {
            return Err(NamedShadow(s));
        }
        // we now know that `s` isn't bound anywhere, so we can insert it without shadowing
        // a let bound variable that should have higher priority
        self.insert_bound(s, Bound::Const(exp));
        Ok(s)
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
        stack: &mut Stack
    ) -> Result<P::Out> {
        let mut rest = f.bind(rest);
        let res = match f {
            ExpKind::Let => {
                let old_len = self.let_bound_stack.len();
                match rest.next()? {
                    SexpToken::List(mut l) => l
                        .map(|token| {
                            let (name, exp) = self.parse_binding(token?, stack)?;
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
                let exp = self.parse_exp_gen(body, p, stack)?;
                rest.finish()?;
                self.undo_let_bindings(old_len);
                exp
            }
            _ => p.parse(self, f, rest, stack)?,
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

    fn parse_exp<R: FullBufRead>(&mut self, token: SexpToken<R>, stack: &mut Stack) -> Result<Exp> {
        self.parse_exp_gen(token, &BaseExpParser, stack)
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

    fn parse_sort<R: FullBufRead>(&mut self, token: SexpToken<R>, stack: &mut Stack) -> Result<Sort> {
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
                stack.with_vec(|mut params| {
                    while let Some(x) = l.next() {
                        let s = self.parse_sort(x?, &mut params.stack())?;
                        params.push(s);
                    }
                    Ok(self.create_sort(name, &params)?)
                })

            }
            _ => return Err(InvalidSort),
        }
    }

    fn reset_state(&mut self) {
        if !matches!(self.state, State::Base) {
            self.core.pop_model();
            self.named_assertions.pop_to(self.old_named_assertions);
            self.state = State::Base;
        }
    }

    fn parse_command<R: FullBufRead>(
        &mut self,
        name: Smt2Command,
        rest: SexpParser<R>,
        stack: &mut Stack,
    ) -> Result<()> {
        let old_len = self.global_stack.len();
        self.writer.print_success = self.options.print_success;
        match self.parse_command_h(name, rest, stack) {
            Ok(()) => {
                if self.writer.print_success {
                    writeln!(self.writer, "success");
                }
                Ok(())
            }
            Err(err) => {
                self.undo_base_bindings(old_len);
                self.named_assertions.pop_to(self.old_named_assertions);
                Err(err)
            }
        }
    }

    fn parse_command_h<R: FullBufRead>(
        &mut self,
        name: Smt2Command,
        rest: SexpParser<R>,
        stack: &mut Stack,
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
                let State::Unsat = &self.state else {
                    return Err(NoCore);
                };
                if !self.options.produces_unsat_cores {
                    return Err(ProduceCoreFalse);
                }
                write!(self.writer, "(");
                let mut iter = self
                    .named_assertions
                    .parts()
                    .1
                    .core(self.core.last_unsat_core())
                    .map(|x| match *x {
                        UnsatCoreElt::Span(s) => rest.p.lookup_range(s),
                        UnsatCoreElt::Sym(s) => self.core.intern.symbols.resolve(s),
                    });
                if let Some(x) = iter.next() {
                    write!(self.writer, "{x}");
                }
                for x in iter {
                    write!(self.writer, " {x}");
                }
                writeln!(self.writer, ")");
                rest.finish()?;
            }
            Smt2Command::GetValue => {
                if !matches!(self.state, State::Model) {
                    return Err(NoModel);
                }
                if !self.options.produce_models {
                    return Err(ProduceModelFalse);
                }
                stack.with_vec(|mut values| {
                    let SexpToken::List(mut l) = rest.next()? else {
                        return Err(InvalidCommand);
                    };
                    loop {
                        let start = l.start_idx();
                        let Some(x) = l.next() else {
                            break
                        };
                        let exp = self.parse_exp(x?, &mut values.stack())?;
                        values.push((exp, l.end_idx(start)));
                    }
                    drop(l);
                    write!(self.writer, "(");
                    let mut iter = values.iter().map(|&(exp, span)| {
                        (
                            exp.with_intern(&self.core.intern),
                            rest.p.lookup_range(span),
                        )
                    });
                    if let Some((x, lit)) = iter.next() {
                        write!(self.writer, "({lit} {x})");
                    }
                    for (x, lit) in iter {
                        write!(self.writer, "\n ({lit} {x})");
                    }
                    writeln!(self.writer, ")");
                    Result::Ok(())
                })?;

                rest.finish()?;
            }
            Smt2Command::GetModel => {
                rest.finish()?;
                if !matches!(self.state, State::Model) {
                    return Err(NoModel);
                }
                if !self.options.produce_models {
                    return Err(ProduceModelFalse);
                }
                let (funs, core) = self.core.function_info();
                writeln!(self.writer, "(");
                stack.with_vec(|mut bound| {
                    bound.extend(
                        self.bound
                            .keys()
                            .copied()
                            .filter(|k| !matches!(*k, TRUE_SYM | FALSE_SYM)),
                    );
                    let intern = &core.intern;
                    bound.sort_unstable_by_key(|x| intern.symbols.resolve(*x));
                    for &k in &*bound {
                        let k_i = k.with_intern(intern);
                        match &self.bound[&k] {
                            Bound::Const(x) => {
                                let x = core.canonize(*x);
                                let sort = core.sort(x).with_intern(intern);
                                let x = x.with_intern(intern);
                                writeln!(self.writer, " (define-fun {k_i} () {sort} {x})");
                            }
                            Bound::Fn(f) => {
                                let args = f.args.iter().enumerate().map(|(i, s)| {
                                    format_args2!("(x!{i} {})", s.with_intern(intern))
                                });
                                let args = parenthesized(args, " ");
                                let ret = f.ret.with_intern(intern);
                                writeln!(self.writer, " (define-fun {k_i} {args} {ret}");
                                write_body(&mut self.writer, &funs, k, ret, intern);
                            }
                        }
                    }
                    writeln!(self.writer, ")");
                });
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
                    SetOption::RandomSeed(mut x) | SetOption::BaseRandomSeed(mut x) => {
                        if x <= 0.0 {
                            // ensure x is positive since this is required by `platsat`
                            x = -x + f64::MIN_POSITIVE;
                        }
                        prev_option.random_seed = x
                    }
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
                    SetOption::ProduceUnsatCores(x) => {
                        if !matches!(self.state, State::Init) {
                            return Err(NonInit);
                        }
                        self.options.produces_unsat_cores = x;
                        return Ok(());
                    }
                    SetOption::ProduceModels(x) => {
                        self.options.produce_models = x;
                        return Ok(());
                    }
                    SetOption::PrintSuccess(x) => {
                        self.options.print_success = x;
                        self.writer.print_success = x; // apply to current command
                        return Ok(());
                    }
                }
                self.core
                    .set_sat_options(prev_option)
                    .map_err(|()| InvalidOption)?;
            }
            Smt2Command::Echo => {
                let start = rest.p.start_idx();
                let SexpToken::String(_) = rest.next()? else {
                    return Err(InvalidCommand);
                };
                let range = rest.p.end_idx(start);
                let s = rest.p.lookup_range(range);
                writeln!(self.writer, "{s}");
                rest.finish()?;
            }
            _ => return self.parse_destructive_command(name, rest, stack),
        }
        Ok(())
    }

    fn set_state(&mut self, res: SolveResult) -> Result<()> {
        self.state = if let SolveResult::Unsat = res {
            State::Unsat
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
        self.named_assertions.pop_to(0);
        self.old_named_assertions = 0;
        self.state = State::Init;
    }

    fn parse_destructive_command<R: FullBufRead>(
        &mut self,
        name: Smt2Command,
        mut rest: CountingParser<R>,
        stack: &mut Stack,
    ) -> Result<()> {
        self.reset_state();
        match name {
            Smt2Command::DeclareFn => {
                let name = self.parse_fresh_binder(rest.next()?)?;
                let SexpToken::List(mut l) = rest.next()? else {
                    return Err(InvalidCommand);
                };
                let args = l
                    .map(|t| self.parse_sort(t?, stack))
                    .collect::<Result<SmallVec<_>>>()?;
                drop(l);
                let ret = self.parse_sort(rest.next()?, stack)?;
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
                let ret = self.parse_sort(rest.next()?, stack)?;
                rest.finish()?;
                self.declare_const(name, ret);
            }
            Smt2Command::DefineConst => {
                let name = self.parse_fresh_binder(rest.next()?)?;
                self.define_const(name, rest, stack)?;
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
                self.define_const(name, rest, stack)?;
            }
            Smt2Command::Assert => {
                self.parse_assert(rest.next_full()?, false, self.options.produce_models, stack)?;
                rest.finish()?;
            }
            Smt2Command::CheckSat => {
                self.old_named_assertions = self.named_assertions.push();
                let res = self
                    .core
                    .check_sat_assuming_preserving_trail(self.named_assertions.parts().0);
                self.set_state(res)?;
                writeln!(self.writer, "{}", res.as_lower_str())
            }
            Smt2Command::CheckSatAssuming => {
                stack.with_vec(|mut conj| {
                    let SexpToken::List(mut l) = rest.next()? else {
                        return Err(InvalidCommand);
                    };
                    let mut i = 0;
                    loop {
                        let start = l.start_idx();
                        let Some(token) = l.next() else {
                            break
                        };
                        let b = self.parse_bool((token?, i, name.to_str_sym()), &mut conj.stack())?;
                        conj.push((b, l.end_idx(start)));
                        i += 1;
                    }
                    drop(l);
                    rest.finish()?;
                    self.named_assertions
                        .extend(conj.into_iter().map(|&(b, s)| (b, UnsatCoreElt::Span(s))));
                    Result::Ok(())
                })?;
                let res = self
                    .core
                    .check_sat_assuming_preserving_trail(self.named_assertions.parts().0);
                self.set_state(res)?;
                writeln!(self.writer, "{}", res.as_lower_str())
            }
            Smt2Command::Push => {
                let n = rest.try_next_parse()?.unwrap_or(1);
                for _ in 0..n {
                    self.core.push();
                    let info = PushInfo {
                        bound: self.global_stack.len() as u32,
                        sort: self.sort_stack.len() as u32,
                        named_assert: self.named_assertions.push(),
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
                    self.undo_base_bindings(info.bound as usize);

                    for s in self.sort_stack.drain(info.sort as usize..).rev() {
                        self.declared_sorts.remove(&s);
                    }
                    self.named_assertions.pop_to(info.named_assert)
                }
            }
            Smt2Command::ResetAssertions => {
                rest.finish()?;
                self.clear();
            }
            Smt2Command::Reset => {
                rest.finish()?;
                self.clear();
                self.core.set_sat_options(Default::default()).unwrap();
                self.options = Default::default();
                self.writer.print_success = self.options.print_success;
            }
            Smt2Command::Exit => {
                rest.p.close();
            }
            _ => return Err(InvalidCommand),
        }
        Ok(())
    }

    fn define_const<R: FullBufRead>(
        &mut self,
        name: Symbol,
        mut rest: CountingParser<R>,
        stack: &mut Stack
    ) -> Result<()> {
        let sort = self.parse_sort(rest.next()?, stack)?;
        self.currently_defining = Some(name);
        let ret = self.parse_exp(rest.next()?, stack)?;
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

    fn parse_command_token<R: FullBufRead>(
        &mut self,
        t: SexpToken<R>,
        stack: &mut Stack,
    ) -> Result<()> {
        match t {
            SexpToken::List(mut l) => {
                let s = match l.next().ok_or(InvalidCommand)?? {
                    SexpToken::Symbol(s) => Smt2Command::from_str(s, &mut self.core.intern),
                    _ => return Err(InvalidCommand),
                };
                self.parse_command(s, l, stack)
            }
            _ => Err(InvalidCommand),
        }
    }

    fn interp_smt2(&mut self, data: impl FullBufRead, mut err: impl Write) {
        let mut stack = StackMemory::new();
        SexpParser::parse_stream_keep_going(
            data,
            self,
            |this, t| this.parse_command_token(t?, &mut stack.stack()),
            |this, e| writeln!(err, "{}", e.map(|x| x.with_intern(&this.core.intern))).unwrap(),
        );
    }
}

fn write_body<W: Write>(
    writer: &mut PrintSuccessWriter<W>,
    info: &FullFunctionInfo,
    name: Symbol,
    ret: WithIntern<Sort>,
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
        write!(writer, "  (ite ");
        let c1 = case.next().unwrap();
        match case.next() {
            None => write!(writer, "{c1}"),
            Some(c2) => {
                write!(writer, "(and {c1} {c2}");
                for c in case {
                    write!(writer, " {c}");
                }
                write!(writer, ")");
            }
        }
        writeln!(writer, " {res}");
    }
    if ret.0 == BOOL_SORT {
        writeln!(writer, "   false{:)<len$})", "");
    } else {
        writeln!(writer, "   (as @{name}!default {ret}){:)<len$})", "");
    }
}

/// Evaluate `data`, the bytes of an `smt2` file, reporting results to `stdout` and errors to
/// `stderr`
pub fn interp_smt2(data: impl FullBufRead, out: impl Write, err: impl Write) {
    let mut p = Parser::new(out);
    p.interp_smt2(data, err)
}
