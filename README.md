This is a toy Rust SMT solver build using [platsat](https://github.com/dewert99/platsat) and [plat-egg](https://github.com/dewert99/plat-egg)
that accepts a subset of SMT2LIB syntax for the logic `QF_UF`

## WASM

Explore the [Live demo](https://dewert99.github.io/plat-smt/) via a browser.

## Supported syntax:
- [x] `true`, `false`, `and`, `or`, `not`,
- [x] `=>`, `xor`
- [x] `=`
- [x] `distinct`
- [x] `as`
- [x] `declare-sort`
- [x] `declare-function`
- [x] `assert`
- [x] `check-sat`
- [x] `check-sat-assuming`
- [x] `let`
- [x] `let*` (sequential let binding)
- [x] `if`
- [x] `get-value`
- [x] `get-model`
- [x] `:named`
- [x] `get-unsat-core`
- [x] `declare-const`
- [x] `define-const`
- [x] `push`,`pop`,`reset`,`reset-assertions`
- [x] `set-option`
- [x] `echo`
- [x] `set-info`
- [x] `get-info`
- [x] `get-interpolants`
- [ ] `get-proof`

## Binary usage
The binary (produced by `cargo build`) takes in a list of `.smt2` files and evaluates sequentially as if they were a single concatenated file.
This list can optionally be followed by `-i` which enters interactive mode (reading from `stdin`) after the files are evaluated.

## Parameters (`set-option`)
Most parameters currently come from [batsat](https://docs.rs/batsat/latest/batsat/core/struct.SolverOpts.html), and are prefixed by `sat.`,
for example random initial activations would be enabled with:

`(set-option :sat.rnd_init_act true)`

`plat-smt` also supports the SMT-LIB standard parameters:
* `:produce-models` (default `true`) 
* `:produce-unsat-cores` (default `true`)
* `:print-success` (default `false`)

## Interpolants
When build with the `interpolant` feature `plat-smt` supports interpolant generation based on the SMTInterpol [proposal](https://ultimate.informatik.uni-freiburg.de/smtinterpol/proposal.pdf).
`plat-smt` only supports binary interpolation, but does accept using `and` to include multiple formulas in the same partition.
The `get-interpolants` command requires that all assumptions (both named assertions and arguments to `check-sat-assuming`) are included in one of the partitions.
Unnamed assertions are included in all partitions when computing interpolants. 
When using the `interpolant` feature the `:produce-interpolants` option defaults to `true`, but when not using the feature it defaults to `false` and cannot be set to `true`.

## Misc
* The `yices-smt2` file is from `https://yices.csl.sri.com/` and is only included for testing
* The `scrambler` and `ModelValidator` files are from `https://smt-comp.github.io/2021/tools.html` and are also only used for testing
* If the environment variable `SEED` is set the initial decisions made are randomized based on it when running the star exec tests (these should otherwise be configured via `set-option`)