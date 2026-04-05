use plat_smt::parser::{ParseError, SexpLexer, SexpParser, SexpTerminal, SexpToken, SpanRange};
use std::fmt::{Debug, Write};

pub enum HandleResult<'a> {
    Remove,
    ReplaceWithConst(&'a str),
    ReplaceWithChild(SpanRange),
}
pub trait Mutator: Debug {
    type AncestorInfo;

    fn from_data(data: &str) -> Self;

    fn describe_parent(
        &self,
        parent: &str,
        ancestor: Option<&Self::AncestorInfo>,
    ) -> Self::AncestorInfo;

    fn handle<'a>(
        &'a mut self,
        parent_info: &Self::AncestorInfo,
        child: &SexpToken<'_, &str>,
        skip_first: &mut bool,
    ) -> Option<HandleResult<'a>>;

    fn clear_cursor(&mut self) {}
}

pub(crate) fn use_mutator(
    data: &str,
    out: &mut String,
    cursor: &mut Vec<u32>,
    mut skip_first: bool,
    m: &mut impl Mutator,
) {
    if cursor.is_empty() {
        cursor.push(0);
    }
    let mut lex = SexpLexer::new(&*data);
    let mut i = 0;
    lex.parse_stream_keep_going(
        (),
        |_, r| {
            if cursor[0] == i {
                let done = handle_line(r?, data, out, cursor, m, &mut skip_first)?;
                if !done {
                    m.clear_cursor();
                    cursor.truncate(0);
                    cursor.push(i + 1);
                    skip_first = false;
                }
            }
            i += 1;
            Ok::<(), ParseError>(())
        },
        |_, err| panic!("{err}"),
    );
    if i == cursor[0] {
        cursor.clear();
    }
}

fn handle_line(
    line: SexpToken<'_, &str>,
    data: &str,
    out: &mut String,
    cursor: &mut Vec<u32>,
    mutator: &mut impl Mutator,
    skip_first: &mut bool,
) -> Result<bool, ParseError> {
    match line {
        SexpToken::Terminal(_) => panic!("Invalid SMT command"),
        SexpToken::List(mut l) => {
            let Some(Ok(SexpToken::Terminal(SexpTerminal::Symbol("assert")))) = l.next() else {
                return Ok(false);
            };
            let assert = mutator.describe_parent("assert", None);
            handle_children(l, Some(assert), data, out, cursor, 1, mutator, skip_first)
        }
    }
}

fn handle_children<M: Mutator>(
    mut l: SexpParser<'_, &str>,
    ancestor: Option<M::AncestorInfo>,
    data: &str,
    out: &mut String,
    cursor: &mut Vec<u32>,
    depth: usize,
    mutator: &mut M,
    skip_first: &mut bool,
) -> Result<bool, ParseError> {
    if cursor.len() <= depth {
        cursor.push(0);
        mutator.clear_cursor();
        *skip_first = false;
    }
    let mut i = 0;
    let mut start_idx = l.start_idx();
    loop {
        let x = l.next();
        if x.is_none() {
            break;
        }
        {
            let x = x.unwrap()?;
            if cursor[depth] == i {
                if cursor.len() == depth + 1 {
                    let action = ancestor
                        .as_ref()
                        .and_then(|parent| mutator.handle(parent, &x, skip_first));
                    if let Some(action) = action {
                        drop(x);
                        let end_idx = l.start_idx();
                        let replacement = match action {
                            HandleResult::Remove => "",
                            HandleResult::ReplaceWithConst(c) => c,
                            HandleResult::ReplaceWithChild(s) => l.lookup_range(s),
                        };
                        write!(
                            out,
                            "{} {} {}",
                            &data[..start_idx],
                            replacement,
                            &data[end_idx..]
                        )
                        .unwrap();
                        return Ok(true);
                    }
                }
                let x = x;
                match x {
                    SexpToken::List(mut l) => {
                        let parent = match l.next() {
                            Some(Ok(SexpToken::Terminal(SexpTerminal::Symbol(parent)))) => {
                                Some(mutator.describe_parent(parent, ancestor.as_ref()))
                            }
                            _ => None,
                        };
                        if handle_children(
                            l,
                            parent,
                            data,
                            out,
                            cursor,
                            depth + 1,
                            mutator,
                            skip_first,
                        )? {
                            return Ok(true);
                        }
                    }
                    _ => {}
                }
                *skip_first = false;
                mutator.clear_cursor();
                cursor.truncate(depth);
                cursor.push(i + 1);
            }
        }
        i += 1;
        start_idx = l.start_idx();
    }
    Ok(false)
}
