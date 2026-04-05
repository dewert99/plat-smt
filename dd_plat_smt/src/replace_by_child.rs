use crate::use_mutator::{HandleResult, Mutator};
use plat_smt::parser::{SexpParser, SexpTerminal, SexpToken};
use std::mem;

#[derive(Debug, Default)]
pub struct ReplaceByChild(u8);
impl Mutator for ReplaceByChild {
    type AncestorInfo = ();

    fn from_data(_: &str) -> Self {
        ReplaceByChild(0)
    }

    fn describe_parent(&self, _: &str, _: Option<&Self::AncestorInfo>) -> Self::AncestorInfo {}

    fn handle(
        &mut self,
        _: &Self::AncestorInfo,
        child: &SexpToken<'_, &str>,
        skip_first: &mut bool,
    ) -> Option<HandleResult<'static>> {
        if *skip_first {
            return None;
        }
        let SexpToken::List(list) = child else {
            return None;
        };
        let mut lexer = list.clone_lex();
        let mut p = SexpParser::new(&mut lexer);
        let Some(Ok(SexpToken::Terminal(SexpTerminal::Symbol(command)))) = p.next() else {
            return None;
        };
        let is_ite = match command {
            "ite" | "if" => true,
            "and" | "or" => false,
            _ => return None,
        };
        let child = if is_ite {
            p.next();
            let start_idx = p.start_idx();
            p.next();
            if self.0 == 0 {
                self.0 = 1;
                Some(p.end_idx(start_idx))
            } else {
                let start_idx = p.start_idx();
                p.next();
                Some(p.end_idx(start_idx))
            }
        } else {
            let start_idx = p.start_idx();
            p.next();
            let span = p.end_idx(start_idx);
            p.next().is_none().then_some(span)
        };
        mem::forget(p);
        child.map(HandleResult::ReplaceWithChild)
    }

    fn clear_cursor(&mut self) {
        self.0 = 0;
    }
}
