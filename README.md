This is a toy Rust SMT solver build using [batsat](https://github.com/c-cube/batsat) and [egg](https://github.com/dewert99/egg)
that accepts a subset of SMT2LIB syntax for the logic `QF_UF`

## Supported syntax:
- [x] `true`, `false`, `and`, `or`, `not`,
- [x] `=`
- [x] `=>`
- [x] `declare-sort`
- [x] `declare-function`
- [x] `assert`
- [x] `check-sat`
- [x] `check-sat-assuming`
- [x] `let`
- [x] `if`
- [x] `get-value`
- [ ] `get-model`
- [x] `get-unsat-core`
- [x] `declare-const`
- [ ] `define-const`
- [ ] `push` / `pop`
- [ ] `get-proof`

## Binary usage
The binary (produced by `cargo build`) takes in a list of `.smt2` files
and evaluates sequentially as if they were a single concatenated file.
This list can optionally be followed by `-i` which enters interactive mode
after the files are evaluated