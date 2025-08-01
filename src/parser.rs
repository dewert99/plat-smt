use crate::full_buf_read::FullBufRead;
use crate::full_theory::FunctionAssignmentT;
use crate::intern::*;
use crate::outer_solver::{Bound, BoundDefinition, FnSort, Logic, OuterSolver, StartExpCtx};
use crate::parser::Error::*;
use crate::parser_core::{ParseError, SexpParser, SexpTerminal, SexpToken, SexpVisitor, SpanRange};
use crate::solver::{SolveResult, SolverCollapse, UnsatCoreConjunction};
use crate::util::{format_args2, parenthesized, powi, DefaultHashBuilder};
use crate::AddSexpError::*;
use crate::{euf, solver, AddSexpError, BoolExp, HasSort, SubExp, SuperExp};
use core::fmt::Arguments;
use hashbrown::HashMap;
use internal_iterator::InternalIterator;
use log::debug;
use no_std_compat::prelude::v1::*;
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
    BindSortMismatch(Sort),
    AddSexp(StrSym, AddSexpError),
    AssertBool(Sort),
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
    UnsupportedP(&'static str),
    Parser(ParseError),
}

impl DisplayInterned for Error {
    fn fmt(&self, i: &InternInfo, fmt: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            AddSexp(f, SortMismatch {
                arg_n,
                actual,
                expected,
            }) => write!(fmt, "the {arg_n}th argument of the function {} has sort {} but should have sort {}", f.with_intern(i), actual.with_intern(i), expected.with_intern(i)),
            AddSexp(f, Unsupported(u)) => write!(fmt, "unsupported feature {u} in the function {} ", f.with_intern(i)),
            AddSexp(f, AsSortMismatch {
                actual,
                expected
            }) => write!(fmt, "the function {} has return sort {} but should have sort {} because of as", f.with_intern(i), actual.with_intern(i), expected.with_intern(i)),
            AddSexp(f, MissingArgument {
                actual,
                expected,
            }) => write!(fmt, "the function `{}` expects at least {expected} arguments but only got {actual}", f.with_intern(i)),
            AddSexp(f, ExtraArgument {
                expected,
            }) => write!(fmt, "the function `{}` expects at most {expected} arguments", f.with_intern(i)),
            AddSexp(f, Unbound) => write!(fmt, "unknown identifier `{}`", f.with_intern(i)),
            AssertBool(s) => write!(fmt, "assertions expect `Bool` got `{}`", s.with_intern(i)),
            BindSortMismatch(s) => write!(fmt, "the definition had the incorrect sort {}", s.with_intern(i)),
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
            UnsupportedP(s) => write!(fmt, "unsupported {s}"),
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
            SexpToken::Terminal(SexpTerminal::Number(n)) => {
                Ok(n.try_into().map_err(|_| ParseError::Overflow)?)
            }
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
            SexpToken::Terminal(SexpTerminal::Number(n)) => Ok(n as f64),
            SexpToken::Terminal(SexpTerminal::Decimal(n, shift)) => {
                Ok(n as f64 * powi(0.1, shift as u32))
            }
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
            SexpToken::Terminal(SexpTerminal::Symbol("true")) => Ok(true),
            SexpToken::Terminal(SexpTerminal::Symbol("false")) => Ok(false),
            _ => Err(InvalidBool),
        }
    }
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

            fn bind<'a, 'b, R: FullBufRead>(self, p: &'a mut SexpParser<'b, R>) -> CountingParser<'a, 'b, R> {
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
    "get-info" => GetInfo(1),
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
                    SexpToken::Terminal(SexpTerminal::Keyword(s)) => match s {
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
    "sat.decay_on_theory_conflict" => DecayOnTheoryConflict(bool),
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

#[derive(Default)]
enum State {
    Unsat,
    Model,
    Base,
    #[default]
    Init,
}

struct LevelMarker<M> {
    sort: u32,
    bound: u32,
    named_assert: u32,
    solver: solver::LevelMarker<M>,
}

struct Parser<W: Write, L: Logic> {
    /// List of global variables in the order defined
    /// Used to remove global variable during `(pop)`
    global_stack: Vec<Symbol>,
    /// List of let bound variable with the old value they are shadowing
    let_bound_stack: Vec<(Symbol, Option<Bound<L::Exp>>)>,
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
    named_assertions: UnsatCoreConjunction<SpanRange>,
    // see above
    old_named_assertions: u32,
    push_info: Vec<LevelMarker<L::LevelMarker>>,
    core: OuterSolver<L>,
    writer: PrintSuccessWriter<W>,
    state: State,
    command_level_marker: Option<solver::LevelMarker<L::LevelMarker>>,
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

struct CountingParser<'a, 'b, R: FullBufRead> {
    p: &'a mut SexpParser<'b, R>,
    name: StrSym,
    actual: usize,
    minimum_expected: usize,
}

type InfoToken<'a, R> = (SexpToken<'a, R>, usize, StrSym);

impl<'a, 'b, R: FullBufRead> CountingParser<'a, 'b, R> {
    fn new(p: &'a mut SexpParser<'b, R>, name: StrSym, minimum_expected: usize) -> Self {
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

    fn next_full(&mut self) -> Result<InfoToken<'_, R>> {
        let actual = self.actual;
        let err = AddSexp(
            self.name,
            MissingArgument {
                actual,
                expected: self.minimum_expected,
            },
        );
        debug_assert!(self.actual < self.minimum_expected);
        self.actual += 1;
        Ok((self.p.next().ok_or(err)??, actual, self.name))
    }

    fn next(&mut self) -> Result<SexpToken<'_, R>> {
        Ok(self.next_full()?.0)
    }

    fn next_parse<N: FromSexp>(&mut self) -> Result<N> {
        N::from_sexp(self.next()?)
    }

    fn try_next_parse<N: FromSexp>(&mut self) -> Result<Option<N>> {
        match self.try_next_full() {
            None => Ok(None),
            Some(x) => N::from_sexp(x?.0).map(Some),
        }
    }

    fn finish(self) -> Result<()> {
        debug_assert!(self.actual >= self.minimum_expected);
        if self.p.next().is_some() {
            Err(AddSexp(
                self.name,
                ExtraArgument {
                    expected: self.actual,
                },
            ))
        } else {
            Ok(())
        }
    }
}

struct ExpVisitor<'a, W: Write, L: Logic>(&'a mut Parser<W, L>, StartExpCtx, Option<L::Exp>);

impl<'a, W: Write, L: Logic> ExpVisitor<'a, W, L> {
    fn parse_exp_terminal(&mut self, terminal: SexpTerminal, ctx: StartExpCtx) -> Result<L::Exp> {
        match terminal {
            SexpTerminal::Symbol(s) => {
                let s = self.0.core.intern_mut().symbols.intern(s);
                self.0.core.start_exp(s, None, ctx);
                self.0
                    .core
                    .end_exp_take()
                    .map_err(|(s, e)| AddSexp(s.into(), e))
            }
            SexpTerminal::String(_) => Err(UnsupportedP("strings")),
            SexpTerminal::Number(_) => Err(UnsupportedP("arithmetic")),
            SexpTerminal::Decimal(_, _) => Err(UnsupportedP("decimal")),
            SexpTerminal::BitVec { .. } => Err(UnsupportedP("bitvec")),
            SexpTerminal::Keyword(_) => Err(InvalidExp),
        }
    }

    fn start_exp_list<R: FullBufRead>(
        &mut self,
        list: &mut SexpParser<R>,
        ctx: StartExpCtx,
    ) -> Result<()> {
        let status = match list.next().ok_or(InvalidExp)?? {
            SexpToken::Terminal(SexpTerminal::Symbol("as")) => None,
            SexpToken::Terminal(SexpTerminal::Symbol(s)) => {
                Some((self.0.core.intern_mut().symbols.intern(s), None))
            }
            SexpToken::List(mut l2) => {
                if matches!(
                    l2.next().ok_or(InvalidExp)??,
                    SexpToken::Terminal(SexpTerminal::Symbol("as"))
                ) {
                    let (s, sort) = self.0.handle_as(&mut l2)?;
                    Some((s, Some(sort)))
                } else {
                    return Err(InvalidExp);
                }
            }
            _ => return Err(InvalidExp),
        };
        if let Some((s, sort)) = status {
            self.parse_fn_exp(s, list, sort, ctx)
        } else {
            let (s, sort) = self.0.handle_as(list)?;
            SexpParser::with_empty(|mut l| self.parse_fn_exp(s, &mut l, Some(sort), ctx))
        }
    }

    fn parse_fn_exp<R: FullBufRead>(
        &mut self,
        f: Symbol,
        rest: &mut SexpParser<R>,
        expect_res: Option<Sort>,
        ctx: StartExpCtx,
    ) -> Result<()> {
        match f {
            LET_SYM => {
                let mut rest = CountingParser::new(rest, StrSym::Sym(f), 2);
                let old_len = self.0.let_bound_stack.len();
                match rest.next()? {
                    SexpToken::List(mut l) => l
                        .map(|token| {
                            let (name, exp) = self.0.parse_binding(token?)?;
                            self.0.let_bound_stack.push((name, Some(Bound::Const(exp))));
                            Ok(())
                        })
                        .collect::<Result<()>>()?,
                    _ => return Err(InvalidLet),
                }
                let body = rest.next()?;
                for (name, bound) in &mut self.0.let_bound_stack[old_len..] {
                    *bound = self.0.core.raw_define(*name, bound.take())
                }
                let exp = self.0.parse_exp(body, ctx)?;
                rest.finish()?;
                self.0.undo_let_bindings(old_len);
                self.2 = Some(exp)
            }
            LET_STAR_SYM => {
                let mut rest = CountingParser::new(rest, StrSym::Sym(f), 2);
                let old_len = self.0.let_bound_stack.len();
                match rest.next()? {
                    SexpToken::List(mut l) => l
                        .map(|token| {
                            let (name, exp) = self.0.parse_binding(token?)?;
                            self.0.let_bound_stack.push((
                                name,
                                self.0.core.raw_define(name, Some(Bound::Const(exp))),
                            ));
                            Ok(())
                        })
                        .collect::<Result<()>>()?,
                    _ => return Err(InvalidLet),
                }
                let body = rest.next()?;
                let exp = self.0.parse_exp(body, ctx)?;
                rest.finish()?;
                self.0.undo_let_bindings(old_len);
                self.2 = Some(exp)
            }
            ANNOT_SYM => {
                let mut rest = CountingParser::new(rest, StrSym::Sym(f), 3);
                let mut exp = self.0.parse_exp(rest.next()?, StartExpCtx::Exact)?;
                let span = self.0.parse_annot_after_exp(exp, rest)?;
                if matches!(ctx, StartExpCtx::Assert) {
                    match exp.downcast() {
                        None => return Err(AssertBool(exp.sort())),
                        Some(b) => {
                            self.0.named_assertions.extend([(b, span)]);
                            self.0.old_named_assertions = self.0.named_assertions.push();
                            // don't return exp since we don't want it to be asserted
                            exp = BoolExp::TRUE.upcast()
                        }
                    };
                }
                self.2 = Some(exp);
            }
            _ => {
                self.0.core.start_exp(f, expect_res, ctx);
            }
        };
        Ok(())
    }

    fn end_exp_list(&mut self) -> Result<L::Exp> {
        if let Some(x) = self.2.take() {
            Ok(x)
        } else {
            self.0
                .core
                .end_exp_take()
                .map_err(|(s, err)| AddSexp(s.into(), err))
        }
    }
}

impl<'a, W: Write, L: Logic> SexpVisitor for ExpVisitor<'a, W, L> {
    type T = L::Exp;
    type E = Error;

    fn handle_outer_terminal(&mut self, s: SexpTerminal) -> Result<L::Exp> {
        self.parse_exp_terminal(s, self.1)
    }

    fn handle_inner_terminal(&mut self, s: SexpTerminal) -> Result<()> {
        let x = self.parse_exp_terminal(s, StartExpCtx::Opt)?;
        self.0.core.inject_exp(x);
        Ok(())
    }

    fn start_outer_list<R: FullBufRead>(&mut self, p: &mut SexpParser<R>) -> Result<()> {
        self.start_exp_list(p, self.1)
    }

    fn start_inner_list<R: FullBufRead>(&mut self, p: &mut SexpParser<R>) -> Result<()> {
        self.start_exp_list(p, StartExpCtx::Opt)
    }

    fn end_outer_list(&mut self) -> Result<L::Exp> {
        self.end_exp_list()
    }

    fn end_inner_list(&mut self) -> Result<()> {
        let x = self.end_exp_list()?;
        self.0.core.inject_exp(x);
        Ok(())
    }
}

impl<W: Write, L: Logic> Parser<W, L> {
    fn new(writer: W) -> Self {
        let mut res = Parser {
            global_stack: Default::default(),
            let_bound_stack: Default::default(),
            push_info: vec![],
            declared_sorts: Default::default(),
            core: Default::default(),
            writer: PrintSuccessWriter::new(writer),
            state: State::Init,
            command_level_marker: None,
            sort_stack: vec![],
            last_status_info: None,
            currently_defining: None,
            named_assertions: UnsatCoreConjunction::default(),
            old_named_assertions: 0,
            options: Default::default(),
        };
        res.declared_sorts.insert(BOOL_SYM, 0);
        res
    }

    fn handle_as<R: FullBufRead>(&mut self, rest: &mut SexpParser<R>) -> Result<(Symbol, Sort)> {
        let mut rest = CountingParser::new(rest, StrSym::Str("as"), 2);
        let SexpToken::Terminal(SexpTerminal::Symbol(s)) = rest.next()? else {
            return Err(InvalidExp);
        };
        let s = self.core.intern_mut().symbols.intern(s);
        let sort = self.parse_sort(rest.next()?)?;
        rest.finish()?;
        Ok((s, sort))
    }

    fn parse_exp<R: FullBufRead>(
        &mut self,
        token: SexpToken<R>,
        context: StartExpCtx,
    ) -> Result<L::Exp> {
        ExpVisitor(self, context, None).visit(token)
    }

    fn parse_binding<R: FullBufRead>(&mut self, token: SexpToken<R>) -> Result<(Symbol, L::Exp)> {
        match token {
            SexpToken::List(mut l) => {
                let sym = match l.next().ok_or(InvalidBinding)?? {
                    SexpToken::Terminal(SexpTerminal::Symbol(s)) => {
                        self.core.intern_mut().symbols.intern(s)
                    }
                    _ => return Err(InvalidBinding),
                };
                let exp = self.parse_exp(l.next().ok_or(InvalidBinding)??, StartExpCtx::Exact)?;
                Ok((sym, exp))
            }
            _ => Err(InvalidBinding),
        }
    }

    fn parse_annot_after_exp<R: FullBufRead>(
        &mut self,
        exp: L::Exp,
        mut rest: CountingParser<R>,
    ) -> Result<SpanRange> {
        let SexpToken::Terminal(SexpTerminal::Keyword(k)) = rest.next()? else {
            return Err(InvalidAnnot);
        };
        if k != "named" {
            return Err(InvalidAnnotAttr(self.core.intern_mut().symbols.intern(k)));
        }
        let start = rest.p.start_idx();
        let SexpToken::Terminal(SexpTerminal::Symbol(s)) = rest.next()? else {
            return Err(InvalidAnnot);
        };
        let s = self.core.intern_mut().symbols.intern(s);
        let span = rest.p.end_idx(start);
        if self.currently_defining == Some(s) {
            return Err(NamedShadow(s));
        }
        if self.core.define(s, Bound::Const(exp)).is_err() {
            return Err(NamedShadow(s));
        }
        rest.finish()?;
        self.global_stack.push(s);
        Ok(span)
    }

    fn undo_let_bindings(&mut self, old_len: usize) {
        for (name, bound) in self.let_bound_stack.drain(old_len..).rev() {
            self.core.raw_define(name, bound);
        }
    }
    fn undo_base_bindings(&mut self, old_len: usize) {
        for name in self.global_stack.drain(old_len..).rev() {
            self.core.raw_define(name, None);
        }
    }

    fn create_sort(&mut self, name: Symbol, params: &[Sort]) -> Result<Sort> {
        let len = params.len();
        match self.declared_sorts.get(&name) {
            None => Err(UnboundSort(name)),
            Some(x) if (*x as usize) < len => Err(AddSexp(
                name.into(),
                MissingArgument {
                    expected: *x as usize,
                    actual: len,
                },
            )),
            Some(x) if *x as usize > len => Err(AddSexp(
                name.into(),
                ExtraArgument {
                    expected: *x as usize,
                },
            )),
            _ => Ok(self.core.intern_mut().sorts.intern(name, params)),
        }
    }

    fn parse_sort<R: FullBufRead>(&mut self, token: SexpToken<R>) -> Result<Sort> {
        match token {
            SexpToken::Terminal(SexpTerminal::Symbol(s)) => {
                let s = self.core.intern_mut().symbols.intern(s);
                self.create_sort(s, &[])
            }
            SexpToken::List(mut l) => {
                let name = match l.next().ok_or(InvalidSort)?? {
                    SexpToken::Terminal(SexpTerminal::Symbol(s)) => {
                        self.core.intern_mut().symbols.intern(s)
                    }
                    _ => return Err(InvalidSort),
                };
                let params = l.map(|x| self.parse_sort(x?)).collect::<Result<Vec<_>>>()?;
                self.create_sort(name, &params)
            }
            _ => Err(InvalidSort),
        }
    }

    fn reset_state(&mut self) {
        if !matches!(self.state, State::Base) {
            self.core.solver_mut().pop_model();
            self.named_assertions.pop_to(self.old_named_assertions);
            self.command_level_marker = Some(self.core.solver_mut().create_level());
            self.state = State::Base;
        }
    }

    fn parse_command<R: FullBufRead>(
        &mut self,
        name: Smt2Command,
        rest: SexpParser<R>,
    ) -> Result<()> {
        let old_len = self.global_stack.len();
        self.writer.print_success = self.options.print_success;
        match self.parse_command_h(name, rest) {
            Ok(()) => {
                if self.writer.print_success {
                    writeln!(self.writer, "success");
                }
                Ok(())
            }
            Err(err) => {
                self.undo_base_bindings(old_len);
                self.named_assertions.pop_to(self.old_named_assertions);
                self.core.reset_working_exp();
                if let Some(c) = self.command_level_marker.clone() {
                    if matches!(self.state, State::Base) {
                        self.core.solver_mut().pop_to_level(c)
                    }
                } else {
                    self.core.solver_mut().clear()
                }
                Err(err)
            }
        }
    }

    fn parse_command_h<R: FullBufRead>(
        &mut self,
        name: Smt2Command,
        mut rest: SexpParser<R>,
    ) -> Result<()> {
        let mut rest = name.bind(&mut rest);
        match name {
            Smt2Command::DeclareSort => {
                let SexpToken::Terminal(SexpTerminal::Symbol(name)) = rest.next()? else {
                    return Err(InvalidCommand);
                };
                let name = self.core.intern_mut().symbols.intern(name);
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
                let mut need_space = false;
                self.named_assertions
                    .parts()
                    .1
                    .core(self.core.solver_mut().last_unsat_core())
                    .map(|x| match *x {
                        s => rest.p.lookup_range(s),
                    })
                    .for_each(|x| {
                        if need_space {
                            write!(self.writer, " {x}");
                        } else {
                            write!(self.writer, "{x}");
                            need_space = true;
                        }
                    });
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
                let SexpToken::List(mut l) = rest.next()? else {
                    return Err(InvalidCommand);
                };
                let values = l
                    .zip_map_full(iter::repeat(()), |x, ()| {
                        let exp = self.parse_exp(x?, StartExpCtx::Exact)?;
                        Ok(self.core.solver_mut().collapse(exp))
                    })
                    .collect::<Result<Vec<_>>>()?;
                drop(l);
                write!(self.writer, "(");
                let mut iter = values.into_iter().map(|(exp, span)| {
                    (
                        exp.with_intern(self.core.intern()),
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
                rest.finish()?;
            }
            Smt2Command::GetModel => {
                if !matches!(self.state, State::Model) {
                    return Err(NoModel);
                }
                if !self.options.produce_models {
                    return Err(ProduceModelFalse);
                }
                rest.finish()?;
                writeln!(self.writer, "(");
                self.core.get_definition_values(|k, v, intern| {
                    let k_i = k.with_intern(intern);
                    match v {
                        BoundDefinition::Const(x) => {
                            let sort = x.sort().with_intern(intern);
                            let x = x.with_intern(intern);
                            writeln!(self.writer, " (define-fun {k_i} () {sort} {x})");
                        }
                        BoundDefinition::Fn(f, assignment) => {
                            debug_assert!(!f.args().is_empty());
                            let args =
                                f.args().iter().enumerate().map(|(i, s)| {
                                    format_args2!("(x!{i} {})", s.with_intern(intern))
                                });
                            let args = parenthesized(args, " ");
                            let ret = f.ret().with_intern(intern);
                            writeln!(self.writer, " (define-fun {k_i} {args} {ret}");
                            write_body::<_, L>(&mut self.writer, assignment, k_i, ret, intern);
                        }
                    }
                });
                writeln!(self.writer, ")");
            }
            Smt2Command::GetInfo => {
                match rest.next()? {
                    SexpToken::Terminal(SexpTerminal::Keyword("name")) => {
                        writeln!(&mut self.writer, "(:name \"PlatSmt\")")
                    }
                    SexpToken::Terminal(SexpTerminal::Keyword("authors")) => {
                        writeln!(&mut self.writer, "(:authors \"David Ewert\")")
                    }
                    SexpToken::Terminal(
                        SexpTerminal::Keyword(s @ "error-behaviour")
                        | SexpTerminal::Keyword(s @ "error-behavior"),
                    ) => {
                        writeln!(&mut self.writer, "(:{s} continued-execution)")
                    }
                    SexpToken::Terminal(SexpTerminal::Keyword("version")) => {
                        writeln!(&mut self.writer, "(:version \"{}\")", env!("GIT_VERSION"));
                    }
                    SexpToken::Terminal(SexpTerminal::Keyword("assertion-stack-levels")) => {
                        writeln!(
                            &mut self.writer,
                            "(:assertion-stack-levels {})",
                            self.push_info.len()
                        )
                    }
                    _ => return Err(InvalidCommand),
                }
                rest.finish()?;
            }
            Smt2Command::SetLogic => {
                match rest.next()? {
                    SexpToken::Terminal(SexpTerminal::Symbol("QF_UF")) => {}
                    SexpToken::Terminal(SexpTerminal::Symbol(_)) => {
                        return Err(UnsupportedP("logic"))
                    }
                    _ => return Err(InvalidCommand),
                }
                rest.finish()?;
            }
            Smt2Command::SetInfo => {
                let SexpToken::Terminal(SexpTerminal::Keyword(key)) = rest.next()? else {
                    return Err(InvalidCommand);
                };
                let info_was_status = key == "status";
                let body = rest.next()?;
                if info_was_status {
                    self.last_status_info = match body {
                        SexpToken::Terminal(SexpTerminal::Symbol("sat")) => Some(SolveResult::Sat),
                        SexpToken::Terminal(SexpTerminal::Symbol("unsat")) => {
                            Some(SolveResult::Unsat)
                        }
                        SexpToken::Terminal(SexpTerminal::Symbol("unknown")) => {
                            Some(SolveResult::Unknown)
                        }
                        _ => return Err(InvalidCommand),
                    }
                }
            }
            Smt2Command::SetOption => {
                let mut prev_option = self.core.solver_mut().sat_options();
                match SetOption::from_parser(rest)? {
                    SetOption::VarDecay(x) => prev_option.var_decay = x,
                    SetOption::ClauseDecay(x) => prev_option.clause_decay = x,
                    SetOption::DecayOnTheoryConflict(x) => prev_option.decay_on_theory_conflict = x,
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
                    .solver_mut()
                    .set_sat_options(prev_option)
                    .map_err(|()| InvalidOption)?;
            }
            Smt2Command::Echo => {
                let start = rest.p.start_idx();
                let SexpToken::Terminal(SexpTerminal::String(_)) = rest.next()? else {
                    return Err(InvalidCommand);
                };
                let range = rest.p.end_idx(start);
                let s = rest.p.lookup_range(range);
                writeln!(self.writer, "{s}");
                rest.finish()?;
            }
            _ => return self.parse_destructive_command(name, rest),
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
        let SexpToken::Terminal(SexpTerminal::Symbol(name)) = token else {
            return Err(InvalidCommand);
        };
        let name = self.core.intern_mut().symbols.intern(name);
        Ok(name)
    }

    fn clear(&mut self) {
        self.push_info.clear();
        self.global_stack.clear();
        self.core.full_clear();
        self.declared_sorts.clear();
        self.sort_stack.clear();
        self.declared_sorts.insert(BOOL_SYM, 0);
        self.named_assertions.pop_to(0);
        self.command_level_marker = None;
        self.old_named_assertions = 0;
        self.state = State::Init;
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
                let fn_sort = FnSort::new(args, ret);
                self.insert_bound(name, Bound::Fn(fn_sort))?;
            }
            Smt2Command::DeclareConst => {
                let name = self.parse_fresh_binder(rest.next()?)?;
                let ret = self.parse_sort(rest.next()?)?;
                rest.finish()?;
                self.declare_const(name, ret)?;
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
                let exp = self.parse_exp(rest.next()?, StartExpCtx::Assert)?;
                self.core
                    .solver_mut()
                    .assert(exp.downcast().ok_or(AssertBool(exp.sort()))?);
                rest.finish()?;
            }
            Smt2Command::CheckSat => {
                self.old_named_assertions = self.named_assertions.push();
                let res = self
                    .core
                    .solver_mut()
                    .check_sat_assuming_preserving_trail(self.named_assertions.parts().0);
                self.set_state(res)?;
                writeln!(self.writer, "{}", res.as_lower_str())
            }
            Smt2Command::CheckSatAssuming => {
                let SexpToken::List(mut l) = rest.next()? else {
                    return Err(InvalidCommand);
                };
                let conj = l
                    .zip_map_full(0.., |token, _| {
                        let exp = self.parse_exp(token?, StartExpCtx::Exact)?;
                        exp.downcast().ok_or(AssertBool(exp.sort()))
                    })
                    .collect::<Result<Vec<_>>>()?;
                drop(l);
                rest.finish()?;
                self.command_level_marker = Some(self.core.solver_mut().create_level());
                self.named_assertions
                    .extend(conj.into_iter().map(|(b, s)| (b, s)));
                let res = self
                    .core
                    .solver_mut()
                    .check_sat_assuming_preserving_trail(self.named_assertions.parts().0);
                self.set_state(res)?;
                writeln!(self.writer, "{}", res.as_lower_str())
            }
            Smt2Command::Push => {
                let n = rest.try_next_parse()?.unwrap_or(1);
                for _ in 0..n {
                    let info = LevelMarker {
                        bound: self.global_stack.len() as u32,
                        sort: self.sort_stack.len() as u32,
                        named_assert: self.named_assertions.push(),
                        solver: self.core.solver_mut().create_level(),
                    };
                    debug!(
                        "Push ({} -> {})",
                        self.push_info.len(),
                        self.push_info.len() + 1
                    );
                    self.push_info.push(info);
                }
            }
            Smt2Command::Pop => {
                let n = rest.try_next_parse()?.unwrap_or(1);
                if n > self.push_info.len() {
                    debug!("Pop ({} -> clear)", self.push_info.len());
                    self.clear()
                } else if n > 0 {
                    debug!(
                        "Pop ({} -> {})",
                        self.push_info.len(),
                        self.push_info.len() - n
                    );
                    let mut info = None;
                    for _ in 0..n {
                        info = self.push_info.pop();
                    }
                    let info = info.unwrap();
                    self.core.solver_mut().pop_to_level(info.solver);
                    self.undo_base_bindings(info.bound as usize);

                    for s in self.sort_stack.drain(info.sort as usize..).rev() {
                        self.declared_sorts.remove(&s);
                    }
                    self.named_assertions.pop_to(info.named_assert);
                    self.old_named_assertions = self.named_assertions.push();
                }
            }
            Smt2Command::ResetAssertions => {
                rest.finish()?;
                self.clear();
            }
            Smt2Command::Reset => {
                rest.finish()?;
                self.clear();
                self.core
                    .solver_mut()
                    .set_sat_options(Default::default())
                    .unwrap();
                self.options = Default::default();
                self.writer.print_success = self.options.print_success;
            }
            Smt2Command::Exit => {
                rest.p.close();
            }
            _ => return Err(InvalidCommand),
        }
        if matches!(self.state, State::Base) {
            self.command_level_marker = Some(self.core.solver_mut().create_level());
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
        let ret = self.parse_exp(rest.next()?, StartExpCtx::Exact)?;
        self.currently_defining = None;
        if sort != ret.sort() {
            return Err(BindSortMismatch(ret.sort()));
        }
        rest.finish()?;
        self.insert_bound(name, Bound::Const(ret))?;
        Ok(())
    }

    fn insert_bound(&mut self, name: Symbol, val: Bound<L::Exp>) -> Result<()> {
        self.core.define(name, val).map_err(|_| Shadow(name))?;
        self.global_stack.push(name);
        Ok(())
    }

    fn declare_const(&mut self, name: Symbol, ret: Sort) -> Result<()> {
        self.insert_bound(name, Bound::Fn(FnSort::new([].into_iter().collect(), ret)))
    }

    fn parse_command_token<R: FullBufRead>(&mut self, t: SexpToken<R>) -> Result<()> {
        match t {
            SexpToken::List(mut l) => {
                let s = match l.next().ok_or(InvalidCommand)?? {
                    SexpToken::Terminal(SexpTerminal::Symbol(s)) => {
                        Smt2Command::from_str(s, self.core.intern_mut())
                    }
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
            |this, e| writeln!(err, "{}", e.map(|x| x.with_intern(this.core.intern()))).unwrap(),
        );
    }
}

fn write_body<'a, W: Write, L: Logic>(
    writer: &mut PrintSuccessWriter<W>,
    assignment: impl FunctionAssignmentT<L::Exp>,
    name: WithIntern<Symbol>,
    ret: WithIntern<Sort>,
    intern: &InternInfo,
) {
    let mut len = 0;
    for (case, res) in assignment {
        len += 1;
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
    let mut p = Parser::<_, (euf::Euf, euf::EufPf, _)>::new(out);
    p.interp_smt2(data, err)
}
