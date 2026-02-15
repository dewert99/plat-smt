#![forbid(unsafe_code)]

use plat_smt::euf::{Euf, EufPf};
use plat_smt::recorder::InterpolantRecorder;
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub struct Repl;

#[wasm_bindgen(getter_with_clone)]
pub struct EvalResult {
    pub out: String,
    pub err: String,
}

#[wasm_bindgen]
impl Repl {
    pub fn eval(input: &str) -> EvalResult {
        let mut out = String::new();
        let mut err = String::new();
        plat_smt::interp_smt2::<(Euf, EufPf, InterpolantRecorder, _)>(
            input.as_bytes(),
            &mut out,
            &mut err,
        );
        EvalResult { out, err }
    }
}
