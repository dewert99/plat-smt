use crate::junction::Junction;
use crate::theory::{Incremental, TheoryArg, TheoryWrapper};
use crate::{Approx, BLit, BoolExp};
use alloc::vec::Vec;
use core::cmp::Ordering;
use log::debug;
use platsat::{lbool, Lit};
use std::mem;

impl<Th: Incremental> TheoryWrapper<Th> {
    /// Returns an empty [`Conjunction`] or [`Disjunction`]  which reuses memory from the last call
    /// to [`collapse_bool`](Self::collapse_bool)
    pub fn new_junction<const IS_AND: bool>(&mut self) -> Junction<IS_AND> {
        self.arg.junction_buf.clear();
        Junction {
            absorbing: false,
            lits: mem::take(&mut self.arg.junction_buf),
        }
    }
}

impl<'a, L> TheoryArg<'a, L> {
    pub fn assert(&mut self, b: BoolExp) {
        match self.canonize(b).to_lit() {
            Ok(l) => self.add_clause_unchecked([l]),
            Err(true) => {}
            Err(false) => {
                self.add_clause_unchecked([]);
            }
        }
    }

    fn optimize_junction(&mut self, lits: &mut Vec<BLit>, is_and: bool) -> bool {
        lits.sort_unstable();

        let mut last_lit = Lit::UNDEF;
        let mut j = 0;
        // remove duplicates, true literals, etc.
        for i in 0..lits.len() {
            let lit_i = lits[i];
            let value = self.sat.value_lit(lit_i);
            if (value == lbool::TRUE ^ is_and) || lit_i == !last_lit {
                return true;
            } else if !(value ^ is_and == lbool::FALSE) && lit_i != last_lit {
                // not a duplicate
                last_lit = lit_i;
                lits[j] = lit_i;
                j += 1;
            }
        }
        lits.truncate(j);
        false
    }

    fn bind_junction(&mut self, lits: &mut Vec<BLit>, is_and: bool, approx: Approx, target: BLit) {
        for lit in &mut *lits {
            if approx != Approx::Approx(is_and) {
                self.sat
                    .add_clause_unchecked([*lit ^ !is_and, target ^ is_and].iter().copied());
            }
            *lit ^= is_and;
        }
        if approx != Approx::Approx(!is_and) {
            lits.push(target ^ !is_and);
            self.sat.add_clause_unchecked(lits.iter().copied());
        }
    }

    #[inline]
    fn andor_reuse(&mut self, lits: &mut Vec<BLit>, is_and: bool, approx: Approx) -> BoolExp {
        if self.optimize_junction(lits, is_and) {
            return BoolExp::from_bool(!is_and);
        }
        if lits.is_empty() {
            return BoolExp::from_bool(is_and);
        }

        if let [lit] = &**lits {
            return BoolExp::unknown(*lit);
        }
        let fresh = self.new_var_default();
        let res = Lit::new(fresh, true);
        self.bind_junction(lits, is_and, approx, res);
        BoolExp::unknown(res)
    }

    fn assert_junction_eq_inner(&mut self, lits: &mut Vec<BLit>, is_and: bool, target: BoolExp) {
        if self.optimize_junction(lits, is_and) {
            self.assert(target ^ is_and);
            return;
        }

        if lits.is_empty() {
            self.assert(target ^ !is_and);
        }

        match self.canonize(target).to_lit() {
            Ok(target) => {
                let mut approx = Approx::Exact;
                if let Ok(idx) = lits.binary_search_by(|lit| lit.var().cmp(&target.var())) {
                    let found = lits[idx];
                    lits.remove(idx);
                    if found == target {
                        approx = Approx::Approx(!is_and);
                    } else {
                        self.sat.add_clause_unchecked([target ^ is_and]);
                        if is_and {
                            lits.iter_mut().for_each(|l| *l = !*l);
                        }
                        self.sat.add_clause_unchecked(lits.iter().copied());
                        return;
                    }
                }
                self.bind_junction(lits, is_and, approx, target)
            }
            Err(target) => {
                if !target {
                    lits.iter_mut().for_each(|l| *l = !*l);
                }
                if is_and ^ target {
                    self.sat.add_clause_unchecked(lits.iter().copied());
                } else {
                    lits.iter().for_each(|l| {
                        self.sat.add_clause_unchecked([*l]);
                    });
                }
            }
        }
    }

    /// Similar to [`collapse_bool`](Self::collapse_bool), but returns a boolean that approximates `j`
    ///
    /// If `approx` is `None` the returned boolean exactly matches `j` (same behaviour as  [`collapse_bool`](Self::collapse_bool))
    ///
    /// If `approx` is `Some(false)` the returned boolean is assigned false whenever `j` is assigned to false,
    /// and when `j` is assigned to true the returned boolean is either also true or unconstrained
    ///
    /// If `approx` is `Some(true)` the returned boolean is assigned true whenever `j` is assigned to true,
    /// and when `j` is assigned to false the returned boolean is either also false or unconstrained
    ///
    /// ## Example
    /// ```
    /// use plat_smt::Approx;
    /// use plat_smt::euf::Euf;
    /// use plat_smt::Solver;
    /// use plat_smt::SolveResult;
    /// let mut s = Solver::<Euf>::default();
    /// let a = s.fresh_bool();
    /// let b = s.fresh_bool();
    /// let ab = s.collapse_bool_approx(a | b, Approx::Approx(false));
    /// s.assert(!a);
    /// s.assert(!b);
    /// s.assert(ab);
    /// assert!(matches!(s.check_sat(), SolveResult::Unsat))
    /// ```
    pub fn collapse_bool_approx<const IS_AND: bool>(
        &mut self,
        mut j: Junction<IS_AND>,
        approx: Approx,
    ) -> BoolExp {
        if !self.is_ok() {
            return BoolExp::TRUE;
        }
        debug!("{j:?} (approx: {approx:?}) was collapsed to ...");
        let res = match j.absorbing {
            true => BoolExp::from_bool(!IS_AND),
            false => self.andor_reuse(&mut j.lits, IS_AND, approx),
        };
        self.incr.junction_buf = j.lits;
        debug!("... {res}");
        res
    }

    pub fn assert_junction_eq<const IS_AND: bool>(
        &mut self,
        mut j: Junction<IS_AND>,
        target: BoolExp,
    ) {
        if !self.is_ok() {
            return;
        }
        let res = match j.absorbing {
            true => self.assert(target ^ IS_AND),
            false => self.assert_junction_eq_inner(&mut j.lits, IS_AND, target),
        };
        self.incr.junction_buf = j.lits;
        res
    }

    /// Returns an empty [`Conjunction`] or [`Disjunction`]  which reuses memory from the last call
    /// to [`collapse_bool`](Self::collapse_bool)
    pub fn new_junction<const IS_AND: bool>(&mut self) -> Junction<IS_AND> {
        self.incr.junction_buf.clear();
        Junction {
            absorbing: false,
            lits: mem::take(&mut self.incr.junction_buf),
        }
    }

    pub fn canonize(&mut self, b: BoolExp) -> BoolExp {
        match b.to_lit() {
            Ok(l) => {
                let v = self.value_lit(l);
                if v == lbool::TRUE {
                    BoolExp::TRUE
                } else if v == lbool::FALSE {
                    BoolExp::FALSE
                } else {
                    b
                }
            }
            _ => b,
        }
    }

    pub fn xor_approx(&mut self, b1: BoolExp, b2: BoolExp, approx: Approx) -> BoolExp {
        if !self.is_ok() {
            return BoolExp::TRUE;
        }
        let b1 = self.canonize(b1);
        let b2 = self.canonize(b2);
        let res = match (b1.to_lit(), b2.to_lit()) {
            (_, Err(b2)) => b1 ^ b2,
            (Err(b1), _) => b2 ^ b1,
            (Ok(l1), Ok(l2)) => {
                let (l1, l2) = match l1.var().cmp(&l2.var()) {
                    Ordering::Less => (l1, l2),
                    Ordering::Equal if l1 == l2 => return BoolExp::FALSE,
                    Ordering::Equal => return BoolExp::TRUE,
                    Ordering::Greater => (l2, l1),
                };
                let fresh = self.new_var_default();
                let fresh = Lit::new(fresh, true);
                if approx != Approx::Approx(true) {
                    self.sat
                        .add_clause_unchecked([l1, l2, !fresh].iter().copied());
                    self.sat
                        .add_clause_unchecked([!l1, !l2, !fresh].iter().copied());
                }
                if approx != Approx::Approx(false) {
                    self.sat
                        .add_clause_unchecked([!l1, l2, fresh].iter().copied());
                    self.sat
                        .add_clause_unchecked([l1, !l2, fresh].iter().copied());
                }
                BoolExp::unknown(fresh)
            }
        };
        debug!("{res} = (xor {b1} {b2})");
        res
    }

    pub fn assert_xor_eq(&mut self, b1: BoolExp, b2: BoolExp, target: BoolExp) {
        if !self.is_ok() {
            return;
        }
        let mut arr = [b1, b2, target];
        arr.sort_unstable();
        if arr[0].var() == arr[1].var() {
            arr[0] = BoolExp::from_bool(arr[0].sign());
            arr[1] = BoolExp::from_bool(arr[1].sign());
        }
        if arr[1].var() == arr[2].var() {
            arr[1] = BoolExp::from_bool(arr[1].sign());
            arr[2] = BoolExp::from_bool(arr[2].sign());
        }
        match arr.map(BoolExp::to_lit) {
            [Err(b1), Err(b2), Err(b3)] => {
                if b1 ^ b2 != b3 {
                    self.sat.add_clause_unchecked([]);
                }
            }
            [Ok(l), Err(b1), Err(b2)] | [Err(b1), Ok(l), Err(b2)] | [Err(b1), Err(b2), Ok(l)] => {
                self.sat.add_clause_unchecked([l ^ b1 ^ !b2]);
            }
            [Err(b), Ok(l1), Ok(l2)] | [Ok(l1), Err(b), Ok(l2)] | [Ok(l1), Ok(l2), Err(b)] => {
                self.sat.add_clause_unchecked([l1 ^ b, !l2].iter().copied());
                self.sat.add_clause_unchecked([!l1 ^ b, l2].iter().copied());
            }
            [Ok(l1), Ok(l2), Ok(l3)] => {
                self.sat.add_clause_unchecked([l1, l2, !l3].iter().copied());
                self.sat
                    .add_clause_unchecked([!l1, !l2, !l3].iter().copied());
                self.sat.add_clause_unchecked([!l1, l2, l3].iter().copied());
                self.sat.add_clause_unchecked([l1, !l2, l3].iter().copied());
            }
        }
    }
}
