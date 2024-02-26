This is a toy Rust SMT solver build using [batsat](https://github.com/c-cube/batsat) and [egg](https://github.com/dewert99/egg)
that accepts a subset of SMT2LIB syntax for the logic `QF_UF`

## Supported syntax:
- [x] `true`, `false`, `and`, `or`, `not`,
- [x] `=`
- [x] `declare-sort`
- [x] `declare-function`
- [x] `assert`
- [x] `check-sat`
- [x] `check-sat-assuming`
- [ ] `let`
- [ ] `if`
- [ ] `get-value`
- [ ] `get-model`
- [ ] `get-unsat-core`
- [x] `declare-const`
- [ ] `define-const`
- [ ] `push` / `pop`
- [ ] `get-proof`