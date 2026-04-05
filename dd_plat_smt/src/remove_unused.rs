use plat_smt::parser::{ParseError, SexpLexer, SexpParser, SexpTerminal, SexpToken};
use std::collections::HashMap;
use std::fmt::Write;

pub(crate) fn remove_unused(data: &str, out: &mut String) {
    let mut lex = SexpLexer::new(&*data);
    let mut symbols = HashMap::new();
    lex.parse_stream_keep_going(
        &mut symbols,
        |x, r| add_symbols(x, r?),
        |_, err| panic!("{err}"),
    );
    let mut lex = SexpLexer::new(&*data);
    lex.parse_stream_keep_going(
        out,
        |out, r| {
            handle_line(r?, &symbols, out);
            Ok::<_, ParseError>(())
        },
        |_, err| panic!("{err}"),
    );
}

fn add_symbols<'a>(
    symbols: &mut HashMap<String, u32>,
    token: SexpToken<'_, &str>,
) -> Result<(), ParseError> {
    match token {
        SexpToken::Terminal(SexpTerminal::Symbol(x)) => {
            *symbols.entry(x.to_owned()).or_default() += 1;
        }
        SexpToken::List(mut p) => {
            while let Some(r) = p.next() {
                add_symbols(symbols, r?)?
            }
        }
        _ => {}
    }
    Ok(())
}

fn handle_line(line: SexpToken<'_, &str>, symbols: &HashMap<String, u32>, out: &mut String) {
    match line {
        SexpToken::Terminal(_) => panic!("Invalid SMT command"),
        SexpToken::List(mut l) => {
            let idx = l.start_idx();
            let can_remove = can_remove(&mut l, symbols);
            while let Some(_) = l.next() {}
            let span = l.end_idx(idx);
            if !can_remove {
                write!(out, "({})\n", l.lookup_range(span)).unwrap();
            }
        }
    }
}

#[derive(Eq, PartialEq)]
enum CommandType {
    Assert,
    Declare,
}

fn can_remove(command: &mut SexpParser<'_, &str>, symbols: &HashMap<String, u32>) -> bool {
    let Some(Ok(SexpToken::Terminal(SexpTerminal::Symbol(name)))) = command.next() else {
        return false;
    };
    let kind = match name {
        "assert" => CommandType::Assert,
        "declare-const" | "declare-fun" => CommandType::Declare,
        _ => return false,
    };
    let Some(Ok(SexpToken::Terminal(SexpTerminal::Symbol(s)))) = command.next() else {
        return false;
    };
    if (kind, s) == (CommandType::Assert, "true") {
        return true;
    }
    let count = symbols.get(s).copied().unwrap_or(0);
    if count == 0 {
        panic!("{s} was found 0 times")
    };
    count == 1
}
