use crate::full_buf_read::FullBufRead;
use core::fmt::{Debug, Display, Formatter};
use core::str::Utf8Error;
use std::string::FromUtf8Error;
fn is_white_space_byte(c: u8) -> bool {
    matches!(c, b' ' | b'\n' | b'\t' | b'\r')
}

fn is_digit_byte(c: u8) -> bool {
    matches!(c, b'0'..=b'9')
}

pub(crate) fn is_symbol_byte(c: u8) -> bool {
    is_digit_byte(c) || is_non_digit_symbol_byte(c)
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

#[derive(thiserror::Error, Debug, Clone)]
pub enum ParseError {
    #[error("error parsing number with radix {radix:?}")]
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

pub(crate) struct SexpLexer<R> {
    reader: R,
    current_line: usize,
    idx: usize,
    last_span: Span,
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
    Keyword(&'a str),
    Symbol(&'a str),
    String(String),
    Number(u128),
    BitVec { value: u128, bits: u8 },
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
    EOI,
    None,
}

impl<R: FullBufRead> SexpLexer<R> {
    fn new(reader: R) -> Self {
        Self {
            reader,
            current_line: 0,
            idx: 0,
            last_span: Span::default(),
        }
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
        let bytes = &self.reader.fill_to_data(self.idx + 4).unwrap()[self.idx..];
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
            .unwrap()
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

    fn read_number<'x>(
        &mut self,
        first_byte: Option<u8>,
        radix: Radix,
    ) -> Result<(u128, u8), ParseError> {
        let first_byte = first_byte.ok_or(NumberError { radix })?;
        let mut n = byte_to_digit(first_byte, radix)?;
        let mut chars = 1;
        self.consume_byte();
        while let Some(c) = self.peek_byte() {
            if !is_symbol_byte(c) {
                break;
            }
            chars += 1;
            n = n.checked_mul(radix as _).ok_or(Overflow)?;
            n = n.checked_add(byte_to_digit(c, radix)?).ok_or(Overflow)?;
            self.consume_byte();
        }
        Ok((n, chars))
    }

    fn last_str(&self, before: usize, off: usize) -> Result<&str, Utf8Error> {
        core::str::from_utf8(&self.reader.data()[before..self.idx - off])
    }

    fn skip(&mut self) {
        while self.skip_whitespace() || self.skip_comment() {}
    }

    fn lex(&mut self) -> Result<RawSexpToken<'_, R>, ParseError> {
        self.update_last_span();
        match self.peek_byte() {
            // Parentheses
            Some(b'(') => {
                self.consume_byte();
                Ok(RawSexpToken::LeftParen(self))
            }
            Some(b')') => {
                self.consume_byte();
                Ok(RawSexpToken::RightParen)
            }
            // Quoted symbols
            Some(b'|') => {
                self.consume_byte();
                let before = self.idx;
                while let Some(c) = self.read_byte() {
                    if c == b'|' {
                        return Ok(RawSexpToken::Symbol(self.last_str(before, 1)?));
                    }
                }
                // Do not accept EOI as a terminator.
                Err(UnexpectedEOI { expected: '|' })
            }
            // String literals
            Some(b'"') => {
                self.consume_byte();
                let mut buf = Vec::new();
                while let Some(c) = self.read_byte() {
                    if c == b'"' {
                        if let Some(d) = self.peek_byte() {
                            if d == b'"' {
                                self.consume_byte();
                                buf.push(b'"');
                                continue;
                            }
                        }
                        return Ok(RawSexpToken::String(String::from_utf8(buf)?));
                    }
                    buf.push(c);
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
                        let x = self.peek_byte();
                        let (value, bits) = self.read_number(x, Radix::Binary)?;
                        Ok(RawSexpToken::BitVec { value, bits })
                    }
                    Some(b'x') => {
                        self.consume_byte();
                        let x = self.peek_byte();
                        let (value, hexits) = self.read_number(x, Radix::Hexidecimal)?;
                        Ok(RawSexpToken::BitVec {
                            value,
                            bits: hexits * 16,
                        })
                    }
                    Some(_) => Err(LiteralError {
                        prefix: self.read_char(),
                    }),
                    None => Err(UnexpectedEOI { expected: 'b' }),
                }
            }
            // Number literals
            Some(digit @ b'0'..=b'9') => {
                let n = self.read_number(Some(digit), Radix::Decimal)?.0;
                Ok(RawSexpToken::Number(n))
            }
            // Keywords
            Some(b':') => {
                self.consume_byte();
                let before = self.idx;
                self.consume_symbols();
                Ok(RawSexpToken::Keyword(self.last_str(before, 0)?))
            }
            // Symbols (including `_` and `!`)
            Some(c) if is_non_digit_symbol_byte(c) => {
                let before = self.idx;
                self.consume_byte();
                self.consume_symbols();
                Ok(RawSexpToken::Symbol(self.last_str(before, 0)?))
            }
            Some(_) => Err(UnexpectedChar {
                found: self.read_char(),
            }),
            None => Err(UnexpectedEOI { expected: ')' }),
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
            None => DropToken::EOI,
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
    Keyword(&'a str),
    Symbol(&'a str),
    String(String),
    Number(u128),
    BitVec { value: u128, bits: u8 },
    List(SexpParser<'a, R>),
}

/// # Examples
///
/// ```
/// use std::io::Cursor;
/// use bat_egg_smt::parser_core::{SexpParser, SexpToken, Radix};
/// let sexp = "(|hello world| (+ x 1 (+ a b) (+ c (+ d e))) 42)";
/// SexpParser::parse_stream_keep_going(sexp.as_bytes(), |token| {
///     let Ok(SexpToken::List(mut list)) = token else {unreachable!()};
///     let t1 = list.next(); // *
///     assert!(matches!(t1, Some(Ok(SexpToken::Symbol("hello world")))));
///     drop(t1);
///     let t2 = list.next(); // (+ x 1 (+ a b) (+ c d))
///     let mut list2 = (|| match t2 {
///         Some(Ok(SexpToken::List(list2))) => list2,
///         _ => unreachable!(),
///     })();
///     let t21 = list2.next(); // +
///     assert!(matches!(t21, Some(Ok(SexpToken::Symbol("+")))));
///     drop(t21);
///     let _ = list2.next().unwrap(); // 1
///     let _ = list2.next().unwrap(); // (+ a b)
///     drop(list2);
///     let t3 = list.next();
///     assert!(matches!(t3, Some(Ok(SexpToken::Number(42)))));
///     drop(t3);
///     assert!(list.next().is_none());
///     Ok::<(), ()>(())
/// }, |_| unreachable!());
/// ```
pub struct SexpParser<'a, R: FullBufRead>(&'a mut SexpLexer<R>);

impl<'a, R: FullBufRead> Debug for SexpParser<'a, R> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SexpParser").finish()
    }
}

pub trait Bind<X> {}
impl<T, X> Bind<X> for T {}

#[derive(Copy, Clone)]
pub struct SpanRange(usize, usize);

impl<'a, R: FullBufRead> SexpParser<'a, R> {
    pub fn parse_stream_keep_going<E>(
        reader: R,
        mut f: impl FnMut(Result<SexpToken<'_, R>, ParseError>) -> Result<(), E>,
        mut handle_err: impl FnMut(Spanned<E>),
    ) {
        let mut lexer = SexpLexer::new(reader);
        let mut p = SexpParser(&mut lexer);
        loop {
            let next = p.next_raw(false);
            if next.is_some() {
                if let Err(e) = f(next.unwrap()) {
                    handle_err(Spanned {
                        data: e,
                        span: p.0.last_span,
                        src: p.0.reader.data(),
                    });
                }
            } else {
                return;
            }
        }
    }

    pub fn lookup_range(&self, r: SpanRange) -> &str {
        core::str::from_utf8(&self.0.reader.data()[r.0..r.1]).unwrap()
    }

    pub fn next_raw(&mut self, expect_paren: bool) -> Option<Result<SexpToken<'_, R>, ParseError>> {
        self.0.skip();
        if matches!(self.0.peek_byte(), Some(b')')) {
            None
        } else if self.0.peek_byte().is_none() {
            if expect_paren {
                self.0.update_last_span();
                Some(Err(UnexpectedEOI { expected: ')' }))
            } else {
                None
            }
        } else {
            let x = match self.0.lex() {
                Ok(RawSexpToken::LeftParen(m)) => SexpToken::List(SexpParser(m)),
                Ok(RawSexpToken::Keyword(k)) => SexpToken::Keyword(k),
                Ok(RawSexpToken::Symbol(s)) => SexpToken::Symbol(s),
                Ok(RawSexpToken::String(s)) => SexpToken::String(s),
                Ok(RawSexpToken::Number(n)) => SexpToken::Number(n),
                Ok(RawSexpToken::BitVec { value, bits }) => SexpToken::BitVec { value, bits },
                Ok(RawSexpToken::RightParen) => unreachable!(),
                Err(err) => return Some(Err(err)),
            };
            Some(Ok(x))
        }
    }

    pub fn next(&mut self) -> Option<Result<SexpToken<'_, R>, ParseError>> {
        self.next_raw(true)
    }

    pub fn zip_map_full<
        U,
        F: FnMut(Result<SexpToken<'_, R>, ParseError>, I::Item) -> U,
        I: IntoIterator,
    >(
        &mut self,
        zip: I,
        mut f: F,
    ) -> impl Iterator<Item = (U, SpanRange)> + Bind<(F, I, &mut Self)> {
        let mut iter = zip.into_iter();
        core::iter::from_fn(move || {
            self.0.skip();
            let it_next = iter.next()?;
            let start = self.0.idx;
            let res = f(self.next()?, it_next);
            let end = self.0.idx;
            Some((res, SpanRange(start, end)))
        })
    }

    pub fn zip_map<
        U,
        F: FnMut(Result<SexpToken<'_, R>, ParseError>, I::Item) -> U,
        I: IntoIterator,
    >(
        &mut self,
        zip: I,
        f: F,
    ) -> impl Iterator<Item = U> + Bind<(F, I, &mut Self)> {
        self.zip_map_full(zip, f).map(|(x, _)| x)
    }

    pub fn map<U, F: FnMut(Result<SexpToken<'_, R>, ParseError>) -> U>(
        &mut self,
        mut f: F,
    ) -> impl Iterator<Item = U> + Bind<(F, &mut Self)> {
        core::iter::from_fn(move || Some(f(self.next()?)))
    }
}

impl<'a, R: FullBufRead> Drop for SexpParser<'a, R> {
    fn drop(&mut self) {
        let mut depth = 0u32;
        loop {
            self.0.skip_whitespace();
            match self.0.lex_drop() {
                DropToken::None => {}
                DropToken::LeftParen => depth += 1,
                DropToken::RightParen if depth > 0 => depth -= 1,
                DropToken::RightParen | DropToken::EOI | DropToken::ErrEOI => return,
            }
        }
    }
}
