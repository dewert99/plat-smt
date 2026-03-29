use crate::outer_solver::Logic;
use crate::parser::parser::Parser;
use crate::parser::parser_core::SexpLexer;
use crate::FullBufRead;
use core::fmt::Display;
use core::fmt::Write;
use std::string::String;

pub struct IncrementalParser<L: Logic> {
    parser: Parser<String, L>,
    lexer: SexpLexer<String>,
    err: String,
}

impl FullBufRead for String {
    fn fill_to(&mut self, _: usize) {}

    fn data(&self) -> &[u8] {
        self.as_bytes()
    }

    fn close(&mut self) {}
}

impl<L: Logic> Default for IncrementalParser<L> {
    fn default() -> Self {
        IncrementalParser {
            parser: Parser::new(String::new()),
            lexer: SexpLexer::new(String::new()),
            err: String::new(),
        }
    }
}

impl<L: Logic> IncrementalParser<L> {
    /// Interprets `commands` which must be a whitespace separated list of smt2 commands
    /// Updates self.out() and self.err()
    pub fn interp_smt2_commands(&mut self, commands: impl Display) {
        write!(&mut self.lexer.reader, "{commands}").unwrap();
        self.parser.interp_smt2(&mut self.lexer, &mut self.err)
    }

    /// Returns the output emitted so far
    pub fn out(&self) -> &str {
        &*self.parser.writer.writer
    }

    /// Returns the errors emitted so far
    pub fn err(&self) -> &str {
        &*self.err
    }

    /// Returns the input recieved so far
    pub fn input(&self) -> &str {
        &*self.lexer.reader
    }

    /// Equivalent to `*self = Default::default()`
    pub fn clear(&mut self) {
        self.parser.clear();
        self.parser.writer.writer.clear();
        self.err.clear();
        self.lexer.clear();
        self.lexer.reader.clear();
    }
}
