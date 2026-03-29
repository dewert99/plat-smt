#![forbid(unsafe_code)]

use plat_smt::euf::{Euf, EufPf};
use plat_smt::outer_solver::Logic;
use plat_smt::recorder::InterpolantRecorder;
use plat_smt::IncrementalParser;
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
extern "C" {
    // Use `js_namespace` here to bind `console.log(..)` instead of just
    // `log(..)`
    #[wasm_bindgen(js_namespace = console)]
    fn log(s: &str);
}

pub struct ReplInner<L: Logic> {
    parser: IncrementalParser<L>,
}

pub trait ReplInnerT {
    fn set_input(&mut self, new_input: &str) -> bool;

    fn out(&self) -> &str;

    fn err(&self) -> &str;
}

impl<L: Logic> ReplInnerT for ReplInner<L> {
    fn set_input(&mut self, new_input: &str) -> bool {
        let to_add = match new_input.strip_prefix(self.parser.input()) {
            Some(to_add) => to_add,
            None => {
                self.parser.clear();
                new_input
            }
        };

        let mut last_command_end = None;
        let mut parens: u32 = 0;
        for (idx, b) in to_add.bytes().enumerate() {
            if b == b'(' {
                parens += 1;
            } else if b == b')' {
                parens = parens.saturating_sub(1);
                if parens == 0 {
                    last_command_end = Some(idx + 1)
                }
            }
        }
        if let Some(last_command_end) = last_command_end {
            self.parser
                .interp_smt2_commands(&to_add[..last_command_end]);
            true
        } else {
            false
        }
    }

    fn out(&self) -> &str {
        self.parser.out()
    }

    fn err(&self) -> &str {
        self.parser.err()
    }
}

#[wasm_bindgen]
pub struct Repl(Box<dyn ReplInnerT>);

#[wasm_bindgen]
impl Repl {
    pub fn new() -> Self {
        Repl(Box::new(ReplInner {
            parser: IncrementalParser::<(Euf, EufPf, InterpolantRecorder, _)>::default(),
        }))
    }

    pub fn out(&self) -> String {
        self.0.out().to_string()
    }

    pub fn err(&self) -> String {
        self.0.err().to_string()
    }

    pub fn set_input(&mut self, new_input: &str) -> bool {
        self.0.set_input(new_input)
    }
}
