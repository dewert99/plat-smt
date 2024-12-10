use crate::full_buf_read::FullBufRead;
use core::fmt::{Debug, Display, Formatter};
use core::mem::ManuallyDrop;
use core::str::Utf8Error;
use no_std_compat::prelude::v1::*;
use std::string::FromUtf8Error;
fn is_white_space_byte(c: u8) -> bool {
    matches!(c, b' ' | b'\n' | b'\t' | b'\r')
}

pub(crate) fn is_symbol_byte(c: u8) -> bool {
    c.is_ascii_digit() || is_non_digit_symbol_byte(c)
}

pub(crate) fn is_non_digit_symbol_byte(c: u8) -> bool {
    matches!(c,
        b'a'..=b'z'
        | b'A'..=b'Z'
        | b'~'
        | b'!'
        | b'@'
        | b'$'
        | b'%'
        | b'^'
        | b'&'
        | b'*'
        | b'_'
        | b'-'
        | b'+'
        | b'='
        | b'<'
        | b'>'
        | b'.'
        | b'?'
        | b'/')
}

/// Record a position in the input stream.
#[derive(Debug, Copy, Clone, Default, Eq, PartialEq)]
pub struct Span {
    pub line: usize,
    pub idx: usize,
}

#[derive(thiserror_no_std::Error, Debug, Clone)]
pub enum ParseError {
    #[error("error parsing number with radix {}", *radix as u8)]
    NumberError { radix: Radix },
    #[error(transparent)]
    UTF8Error(#[from] Utf8Error),
    #[error(transparent)]
    FromUFTError(#[from] FromUtf8Error),
    #[error("unexpected literal prefix `#{prefix}`")]
    LiteralError { prefix: char },
    #[error("unexpected character `{found}`")]
    UnexpectedChar { found: char },
    #[error("unexpected end of input (expected `{expected}`)")]
    UnexpectedEOI { expected: char },
    #[error("integer overflow")]
    Overflow,
}
use crate::util::Bind;
use ParseError::*;

#[derive(Debug)]
pub struct Spanned<'a, T> {
    pub data: T,
    pub src: &'a [u8],
    pub span: Span,
}

impl<'a, T: Display> Display for Spanned<'a, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let idx = self.span.idx;
        let after = self.src[idx..].iter().position(|x| *x == b'\n');
        let end = after.map(|x| idx + x).unwrap_or(self.src.len());
        let before = self.src[..idx].iter().rev().position(|x| *x == b'\n');
        let start = before.map(|x| idx - x).unwrap_or(0);
        let char_count = String::from_utf8_lossy(&self.src[start..idx])
            .chars()
            .count();
        let str = String::from_utf8_lossy(&self.src[start..end]);
        writeln!(
            f,
            "{} at {}:{}",
            self.data,
            self.span.line + 1,
            char_count + 1
        )?;
        writeln!(f, "{str}")?;
        writeln!(f, "{:>char_count$}^", "")
    }
}

impl<'a, T> Spanned<'a, T> {
    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Spanned<'a, U> {
        Spanned {
            data: f(self.data),
            src: self.src,
            span: self.span,
        }
    }
}

pub(crate) struct SexpLexer<R> {
    reader: R,
    current_line: usize,
    idx: usize,
    last_span: Span,
    str_buf: Vec<u8>,
}

#[derive(Clone, Copy, Debug)]
pub enum Radix {
    Binary = 2,
    Decimal = 10,
    Hexidecimal = 16,
}

enum RawSexpToken<'a, R> {
    LeftParen(&'a mut SexpLexer<R>),
    RightParen,
    Terminal(SexpTerminal<'a>),
}

fn byte_to_digit(byte: u8, radix: Radix) -> Result<u128, ParseError> {
    let err = || NumberError { radix };
    Ok(char::from_u32(byte.into())
        .ok_or(err())?
        .to_digit(radix as u32)
        .ok_or(err())?
        .into())
}

enum DropToken {
    LeftParen,
    RightParen,
    ErrEOI,
    Eoi,
    None,
}

impl<R: FullBufRead> SexpLexer<R> {
    fn new(reader: R) -> Self {
        Self {
            reader,
            current_line: 0,
            idx: 0,
            last_span: Span::default(),
            str_buf: vec![],
        }
    }

    fn close(&mut self) {
        self.reader.close();
        self.idx = self.reader.data().len();
    }

    fn consume_byte(&mut self) {
        if let Some(c) = self.peek_byte() {
            if c == b'\n' {
                self.current_line += 1;
            }
            self.idx += 1;
        }
    }

    fn read_byte(&mut self) -> Option<u8> {
        let c = self.peek_byte();
        self.consume_byte();
        c
    }

    fn read_char(&mut self) -> char {
        let bytes = &self.reader.fill_to_data(self.idx + 4)[self.idx..];
        let end = core::cmp::min(4, bytes.len());
        let bytes = &bytes[..end];
        let s = match core::str::from_utf8(bytes) {
            Ok(s) => s,
            Err(err) => core::str::from_utf8(&bytes[..err.valid_up_to()]).unwrap(),
        };
        let c = s.chars().next();
        self.idx += c.map_or(1, char::len_utf8);
        c.unwrap_or(char::REPLACEMENT_CHARACTER)
    }

    fn peek_byte(&mut self) -> Option<u8> {
        self.reader
            .fill_to_data(self.idx + 1)
            .get(self.idx)
            .copied()
    }

    fn skip_whitespace(&mut self) -> bool {
        match self.peek_byte() {
            Some(b) if is_white_space_byte(b) => {
                self.consume_byte();
                true
            }
            _ => false,
        }
    }

    fn skip_comment(&mut self) -> bool {
        match self.peek_byte() {
            Some(c) if c == b';' => {
                self.consume_byte();
                while let Some(c) = self.read_byte() {
                    if c == b'\n' {
                        break;
                    }
                }
                true
            }
            _ => false,
        }
    }

    fn read_number_raw(
        &mut self,
        first_byte: Option<u8>,
        radix: Radix,
    ) -> Result<(u128, u8), ParseError> {
        let first_byte = first_byte.ok_or(NumberError { radix })?;
        let mut n = byte_to_digit(first_byte, radix)?;
        let mut chars = 1;
        self.consume_byte();
        while let Some(c) = self.peek_byte() {
            if !c.is_ascii_alphanumeric() {
                break;
            }
            chars += 1;
            n = n.checked_mul(radix as _).ok_or(Overflow)?;
            n = n.checked_add(byte_to_digit(c, radix)?).ok_or(Overflow)?;
            self.consume_byte();
        }
        Ok((n, chars))
    }

    fn read_number(&mut self, radix: Radix) -> Result<(u128, u8), ParseError> {
        let x = self.peek_byte();
        self.read_number_raw(x, radix)
    }

    fn last_str(&self, before: usize, off: usize) -> Result<&str, Utf8Error> {
        core::str::from_utf8(&self.reader.data()[before..self.idx - off])
    }

    fn skip(&mut self) {
        while self.skip_whitespace() || self.skip_comment() {}
    }

    // doesn't consume right paren
    fn lex(&mut self) -> Result<RawSexpToken<'_, R>, ParseError> {
        use RawSexpToken::*;
        use SexpTerminal::*;
        self.skip();
        self.update_last_span();
        match self.peek_byte() {
            // Parentheses
            Some(b'(') => {
                self.consume_byte();
                Ok(LeftParen(self))
            }
            Some(b')') => Ok(RightParen),
            // Quoted symbols
            Some(b'|') => {
                self.consume_byte();
                let before = self.idx;
                while let Some(c) = self.read_byte() {
                    if c == b'|' {
                        return Ok(Terminal(Symbol(self.last_str(before, 1)?)));
                    }
                }
                // Do not accept EOI as a terminator.
                Err(UnexpectedEOI { expected: '|' })
            }
            // String literals
            Some(b'"') => {
                self.consume_byte();
                self.str_buf.clear();
                while let Some(c) = self.read_byte() {
                    if c == b'"' {
                        if let Some(d) = self.peek_byte() {
                            if d == b'"' {
                                self.consume_byte();
                                self.str_buf.push(b'"');
                                continue;
                            }
                        }
                        return Ok(Terminal(String(std::str::from_utf8(&self.str_buf)?)));
                    }
                    self.str_buf.push(c);
                }
                // Do not accept EOI as a terminator.
                Err(UnexpectedEOI { expected: '"' })
            }
            // Binary and Hexadecimal literals
            Some(b'#') => {
                self.consume_byte();
                match self.peek_byte() {
                    Some(b'b') => {
                        self.consume_byte();
                        let (value, bits) = self.read_number(Radix::Binary)?;
                        Ok(Terminal(BitVec { value, bits }))
                    }
                    Some(b'x') => {
                        self.consume_byte();
                        let (value, hexits) = self.read_number(Radix::Hexidecimal)?;
                        Ok(Terminal(BitVec {
                            value,
                            bits: hexits * 4,
                        }))
                    }
                    Some(_) => Err(LiteralError {
                        prefix: self.read_char(),
                    }),
                    None => Err(UnexpectedEOI { expected: 'b' }),
                }
            }
            // Number literals
            Some(digit @ b'0'..=b'9') => {
                let n = self.read_number_raw(Some(digit), Radix::Decimal)?.0;
                if self.peek_byte() == Some(b'.') {
                    self.consume_byte();

                    let (after, exp) = self.read_number(Radix::Decimal)?;
                    Ok(Terminal(Decimal(n * 10u128.pow(exp.into()) + after, exp)))
                } else {
                    Ok(Terminal(Number(n)))
                }
            }
            // Keywords
            Some(b':') => {
                self.consume_byte();
                let before = self.idx;
                self.consume_symbols();
                Ok(Terminal(Keyword(self.last_str(before, 0)?)))
            }
            // Symbols (including `_` and `!`)
            Some(c) if is_non_digit_symbol_byte(c) => {
                let before = self.idx;
                self.consume_byte();
                self.consume_symbols();
                Ok(Terminal(Symbol(self.last_str(before, 0)?)))
            }
            Some(_) => Err(UnexpectedChar {
                found: self.read_char(),
            }),
            None => {
                self.update_last_span();
                Err(UnexpectedEOI { expected: ')' })
            }
        }
    }

    fn update_last_span(&mut self) {
        self.last_span = Span {
            idx: self.idx,
            line: self.current_line,
        };
    }

    fn lex_drop(&mut self) -> DropToken {
        match self.read_byte() {
            // Parentheses
            Some(b'(') => DropToken::LeftParen,
            Some(b')') => DropToken::RightParen,
            // Quoted symbols
            Some(b'|') => {
                while let Some(c) = self.read_byte() {
                    if c == b'|' {
                        return DropToken::None;
                    }
                }
                DropToken::ErrEOI
            }
            // String literals
            Some(b'"') => {
                while let Some(c) = self.read_byte() {
                    if c == b'"' {
                        if let Some(d) = self.peek_byte() {
                            if d == b'"' {
                                self.consume_byte();
                                continue;
                            }
                        }
                        return DropToken::None;
                    }
                }
                DropToken::ErrEOI
            }
            Some(_) => DropToken::None,
            // EOI or Error
            None => DropToken::Eoi,
        }
    }

    fn consume_symbols(&mut self) {
        while let Some(c) = self.peek_byte() {
            if !is_symbol_byte(c) {
                break;
            }
            self.consume_byte();
        }
    }
}

#[derive(Debug)]
pub enum SexpToken<'a, R: FullBufRead> {
    Terminal(SexpTerminal<'a>),
    List(SexpParser<'a, R>),
}

/// # Examples
///
/// ```
/// use std::io::Cursor;
/// use plat_smt::parser_core::{SexpParser, SexpToken::{self, Terminal}, Radix, SexpTerminal::*};
/// let sexp = "(|hello world| (+ x 1 (+ a b) (+ c (+ d e))) 42)";
/// SexpParser::parse_stream_keep_going(sexp.as_bytes(), (), |_, token| {
///     let Ok(SexpToken::List(mut list)) = token else {unreachable!()};
///     let t1 = list.next(); // *
///     assert!(matches!(t1, Some(Ok(Terminal(Symbol("hello world"))))));
///     drop(t1);
///     let t2 = list.next(); // (+ x 1 (+ a b) (+ c d))
///     let mut list2 = (|| match t2 {
///         Some(Ok(SexpToken::List(list2))) => list2,
///         _ => unreachable!(),
///     })();
///     let t21 = list2.next(); // +
///     assert!(matches!(t21, Some(Ok(Terminal(Symbol("+"))))));
///     drop(t21);
///     let _ = list2.next().unwrap(); // 1
///     let _ = list2.next().unwrap(); // (+ a b)
///     drop(list2);
///     let t3 = list.next();
///     assert!(matches!(t3, Some(Ok(Terminal(Number(42))))));
///     drop(t3);
///     assert!(list.next().is_none());
///     Ok::<(), ()>(())
/// }, |_, _| unreachable!());
/// ```
pub struct SexpParser<'a, R: FullBufRead>(&'a mut SexpLexer<R>);

impl<'a, R: FullBufRead> Debug for SexpParser<'a, R> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SexpParser").finish()
    }
}

#[derive(Copy, Clone)]
pub struct SpanRange(usize, usize);

impl<'a> SexpParser<'a, &'static [u8]> {
    pub fn with_empty<T>(mut f: impl FnMut(SexpParser<'_, &'static [u8]>) -> T) -> T {
        let mut lexer: SexpLexer<&[u8]> = SexpLexer::new(b")");
        f(SexpParser(&mut lexer))
    }
}

impl<'a, R: FullBufRead> SexpParser<'a, R> {
    pub fn parse_stream_keep_going<E, C>(
        reader: R,
        mut ctx: C,
        mut f: impl FnMut(&mut C, Result<SexpToken<'_, R>, ParseError>) -> Result<(), E>,
        mut handle_err: impl FnMut(&mut C, Spanned<E>),
    ) {
        let mut lexer = SexpLexer::new(reader);
        let mut p = SexpParser(&mut lexer);
        loop {
            let next = p.next();
            if next.is_some() {
                let next = next.unwrap();
                if let Err(UnexpectedEOI { expected: ')' }) = next {
                    return;
                }
                if let Err(e) = f(&mut ctx, next) {
                    handle_err(
                        &mut ctx,
                        Spanned {
                            data: e,
                            span: p.0.last_span,
                            src: p.0.reader.data(),
                        },
                    );
                }
            } else {
                return;
            }
        }
    }

    pub fn lookup_range(&self, r: SpanRange) -> &str {
        core::str::from_utf8(&self.0.reader.data()[r.0..r.1]).unwrap()
    }

    #[inline]
    pub fn next(&mut self) -> Option<Result<SexpToken<'_, R>, ParseError>> {
        match self.0.lex() {
            Ok(RawSexpToken::LeftParen(m)) => Some(Ok(SexpToken::List(SexpParser(m)))),
            Ok(RawSexpToken::Terminal(t)) => Some(Ok(SexpToken::Terminal(t))),
            Ok(RawSexpToken::RightParen) => None,
            Err(err) => Some(Err(err)),
        }
    }

    pub fn start_idx(&mut self) -> usize {
        self.0.skip();
        self.0.idx
    }

    pub fn end_idx(&mut self, start: usize) -> SpanRange {
        SpanRange(start, self.0.idx)
    }

    pub fn zip_map_full<
        U,
        E,
        F: FnMut(Result<SexpToken<'_, R>, ParseError>, I::Item) -> Result<U, E>,
        I: IntoIterator,
    >(
        &mut self,
        zip: I,
        mut f: F,
    ) -> impl Iterator<Item = Result<(U, SpanRange), E>> + Bind<(F, I, &mut Self)> {
        let mut iter = zip.into_iter();
        core::iter::from_fn(move || {
            let start = self.start_idx();
            let it_next = iter.next()?;
            let res = f(self.next()?, it_next);
            let range = self.end_idx(start);
            Some(res.map(|res| (res, range)))
        })
    }

    pub fn zip_map<
        U,
        F: FnMut(Result<SexpToken<'_, R>, ParseError>, I::Item) -> U,
        I: IntoIterator,
    >(
        &mut self,
        zip: I,
        mut f: F,
    ) -> impl Iterator<Item = U> + Bind<(F, I, &mut Self)> {
        let mut iter = zip.into_iter();
        core::iter::from_fn(move || {
            self.0.skip();
            let it_next = iter.next()?;
            let res = f(self.next()?, it_next);
            Some(res)
        })
    }

    pub fn map<U, F: FnMut(Result<SexpToken<'_, R>, ParseError>) -> U>(
        &mut self,
        mut f: F,
    ) -> impl Iterator<Item = U> + Bind<(F, &mut Self)> {
        core::iter::from_fn(move || Some(f(self.next()?)))
    }

    pub fn close(&mut self) {
        self.0.close();
    }

    fn drop_at_depth(&mut self, mut depth: u32) {
        loop {
            self.0.skip_whitespace();
            match self.0.lex_drop() {
                DropToken::None => {}
                DropToken::LeftParen => depth += 1,
                DropToken::RightParen if depth > 0 => depth -= 1,
                DropToken::RightParen | DropToken::Eoi | DropToken::ErrEOI => return,
            }
        }
    }
}

impl<'a, R: FullBufRead> Drop for SexpParser<'a, R> {
    fn drop(&mut self) {
        self.drop_at_depth(0);
    }
}

#[derive(Debug)]
pub enum SexpTerminal<'a> {
    Keyword(&'a str),
    Symbol(&'a str),
    String(&'a str),
    Number(u128),
    // x*10^-y
    Decimal(u128, u8),
    BitVec { value: u128, bits: u8 },
}

/// Trait for recursively visiting s-expressions without using the stack
///
/// ### Example
/// ```rust
/// use plat_smt::FullBufRead;
/// use plat_smt::parser_core::{ParseError, SexpParser, SexpTerminal, SexpToken, SexpVisitor};
///
/// #[derive(Default)]
/// struct AEVisitor {
///     res_stack: Vec<u128>,
///     op_stack: Vec<(usize, fn(&[u128]) -> u128)>
/// }
///
/// #[derive(thiserror_no_std::Error, Debug, Clone)]
/// enum AEError {
///    #[error("missing operator")]
///    MissingOp,
///    #[error("invalid operator")]
///    InvalidOp,
///    #[error("invalid argument")]
///    InvalidArg,
///    #[error(transparent)]
///    Parser(#[from] ParseError)
/// }
///
/// impl SexpVisitor for AEVisitor {
///     type T = u128;
///     type E = AEError;
///
///     fn handle_outer_terminal(&mut self, s: SexpTerminal) -> Result<Self::T, Self::E> {
///         match s {
///              SexpTerminal::Number(n) => Ok(n),
///              _ => Err(AEError::InvalidArg)
///         }
///     }
///
///     fn handle_inner_terminal(&mut self, s: SexpTerminal)  -> Result<(), Self::E> {
///         let res = self.handle_outer_terminal(s)?;
///         self.res_stack.push(res);
///         Ok(())
///     }
///
///     fn start_outer_list<R: FullBufRead>(&mut self, p: &mut SexpParser<R>) -> Result<(), Self::E> {
///         let op = match p.next().ok_or(AEError::MissingOp)?? {
///             SexpToken::Terminal(SexpTerminal::Symbol("+")) => |s: &[u128]| s.iter().copied().sum(),
///             SexpToken::Terminal(SexpTerminal::Symbol("*")) => |s: &[u128]| s.iter().copied().product(),
///             _ => return Err(AEError::InvalidOp),
///         };
///         self.op_stack.push((self.res_stack.len(), op));
///         Ok(())
///     }
///
///     fn end_outer_list(&mut self) -> Result<Self::T, Self::E> {
///         let (old_len, op) = self.op_stack.pop().unwrap();
///         let res = op(&self.res_stack[old_len..]);
///         self.res_stack.truncate(old_len);
///         Ok(res)
///     }
///
///     fn end_inner_list(&mut self) -> Result<(), Self::E> {
///         let res = self.end_outer_list()?;
///         self.res_stack.push(res);
///         Ok(())
///     }
/// }
///
/// let sexp = "((+ (* x 2) 3) (+ (* 2 3) (* 3 4)))";
/// SexpParser::parse_stream_keep_going(sexp.as_bytes(), (), |_, token| {
///     let Ok(SexpToken::List(mut list)) = token else {unreachable!()};
///     let t1 = list.next().unwrap().unwrap(); // (+ (* x 2) 3)
///     assert!(matches!(AEVisitor::default().visit(t1), Err(AEError::InvalidArg)));
///     let t1 = list.next().unwrap().unwrap(); // (+ (* 2 3) (* 3 4))
///     assert!(matches!(AEVisitor::default().visit(t1), Ok(18)));
///     Ok::<(), ()>(())
/// }, |_, _| unreachable!());
/// ```
pub trait SexpVisitor {
    type T;
    type E: From<ParseError>;

    /// Handle a terminal if it is the outermost element
    fn handle_outer_terminal(&mut self, s: SexpTerminal) -> Result<Self::T, Self::E>;

    /// Handle a terminal within a larger s-expression
    /// Defaults to calling [`handle_outer_terminal`](SexpVisitor::handle_outer_terminal)
    fn handle_inner_terminal(&mut self, s: SexpTerminal) -> Result<(), Self::E> {
        self.handle_outer_terminal(s).map(|_| ())
    }

    /// Start handling a list if it is the outermost element
    fn start_outer_list<R: FullBufRead>(&mut self, p: &mut SexpParser<R>) -> Result<(), Self::E>;

    /// Handle a terminal within a larger s-expression
    /// Defaults to calling [`start_outer_list`](SexpVisitor::start_outer_list)
    fn start_inner_list<R: FullBufRead>(&mut self, p: &mut SexpParser<R>) -> Result<(), Self::E> {
        self.start_outer_list(p)
    }

    /// Start handling a list if it is the outermost element
    fn end_outer_list(&mut self) -> Result<Self::T, Self::E>;

    /// Handle a terminal within a larger s-expression
    /// Defaults to calling [`start_outer_list`](SexpVisitor::start_outer_list)
    fn end_inner_list(&mut self) -> Result<(), Self::E> {
        self.end_outer_list().map(|_| ())
    }

    fn visit<R: FullBufRead>(&mut self, t: SexpToken<R>) -> Result<Self::T, Self::E> {
        match t {
            SexpToken::Terminal(t) => self.handle_outer_terminal(t),
            SexpToken::List(p) => {
                let mut depth = 0u32;
                let mut p = ManuallyDrop::new(p);
                let res = (|| {
                    self.start_outer_list(&mut p)?;
                    loop {
                        match p.0.lex()? {
                            RawSexpToken::LeftParen(_) => {
                                depth += 1;
                                self.start_inner_list(&mut p)?;
                            }
                            RawSexpToken::RightParen => {
                                p.0.consume_byte();
                                if depth == 0 {
                                    return Ok(());
                                }
                                depth -= 1;
                                self.end_inner_list()?;
                            }
                            RawSexpToken::Terminal(t) => self.handle_inner_terminal(t)?,
                        }
                    }
                })();
                if let Err(e) = res {
                    p.drop_at_depth(depth);
                    return Err(e);
                }
                self.end_outer_list()
            }
        }
    }
}
