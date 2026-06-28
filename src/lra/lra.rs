use crate::collapse::CollapseOut;
use crate::full_theory::{empty_fn_info, FullTheory, FunctionAssignmentT, PrepareModelKind};
use crate::intern::{Symbol, ADD_SYM, DIV_SYM, GE_SYM, GT_SYM, MUL_SYM, REAL_SORT, SUB_SYM};
use crate::lra::bound::EpsilonRational;
use crate::lra::tableau::{ineq, BoundDir, ModeledTableau, NumExp, NumVar, Sum};
use crate::recorder::Recorder;
use crate::rexp::{rexp_debug, AsRexp, Rexp};
use crate::theory::{Incremental, Theory, TheoryArgT};
use crate::tseitin::{SatExplainTheoryArgT, SatTheoryArgT};
use crate::{BoolExp, ExpLike, Sort, StaticSort};
use alloc::collections::btree_map::Entry;
use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use core::convert::Infallible;
use core::fmt::{Debug, Display, Formatter};
use core::ops::Bound::{Excluded, Unbounded};
use default_vec2::DefaultVec;
use lazy_rational::Rational32;
use log::debug;
use platsat::{lbool, Lit, Var};
use std::mem;

impl AsRexp for i32 {
    fn as_rexp<R>(&self, f: impl for<'a> FnOnce(Rexp<'a>) -> R) -> R {
        let x = Rexp::Int(self.unsigned_abs() as u128);
        if *self < 0 {
            f(Rexp::Call(SUB_SYM, &[x]))
        } else {
            f(x)
        }
    }
}
impl AsRexp for Rational32 {
    fn as_rexp<R>(&self, f: impl for<'a> FnOnce(Rexp<'a>) -> R) -> R {
        let (num, den) = self.parts();
        if den == 1 {
            num.as_rexp(f)
        } else {
            num.as_rexp(|num| {
                let den = Rexp::Int(den as u128);
                f(Rexp::Call(DIV_SYM, &[num, den]))
            })
        }
    }
}

impl AsRexp for NumVar {
    fn as_rexp<R>(&self, f: impl for<'a> FnOnce(Rexp<'a>) -> R) -> R {
        f(Rexp::Nv(self.to_nv()))
    }
}

rexp_debug!(NumVar);

fn add_as_rexp<R>(base: Rexp<'_>, add: Rational32, f: impl for<'a> FnOnce(Rexp<'a>) -> R) -> R {
    if add.is_zero() {
        f(base)
    } else if add > Rational32::ZERO {
        add.as_rexp(|add_rexp| f(Rexp::Call(ADD_SYM, &[base, add_rexp])))
    } else {
        (-add).as_rexp(|add_rexp| f(Rexp::Call(SUB_SYM, &[base, add_rexp])))
    }
}

impl AsRexp for NumExp {
    fn as_rexp<R>(&self, f: impl for<'a> FnOnce(Rexp<'a>) -> R) -> R {
        if let Some(var) = self.var {
            let vnv = Rexp::Nv(var.to_nv());
            if self.mul == Rational32::ONE {
                add_as_rexp(vnv, self.add, f)
            } else if self.mul == -Rational32::ONE {
                add_as_rexp(Rexp::Call(SUB_SYM, &[vnv]), self.add, f)
            } else {
                self.mul.as_rexp(|mul_rexp| {
                    add_as_rexp(Rexp::Call(MUL_SYM, &[vnv, mul_rexp]), self.add, f)
                })
            }
        } else {
            self.add.as_rexp(f)
        }
    }
}

rexp_debug!(NumExp);

impl Display for NumExp {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self.try_into_rational() {
            Some(c) => c.as_rexp(|r| Display::fmt(&r, f)),
            None => {
                write!(f, "(as {self:?} Real)")
            }
        }
    }
}

impl StaticSort for NumExp {
    const SORT: Sort = REAL_SORT;
}

impl CollapseOut for NumExp {
    type Out = NumExp;
}

impl ExpLike for NumExp {
    fn default_with_sort(s: Sort) -> Self {
        debug_assert_eq!(s, REAL_SORT);
        NumExp::from_int(0)
    }
}

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq)]
struct LowerBound {
    var: NumVar,
    bound: Rational32,
    strict: bool,
}

impl Debug for LowerBound {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "{:?} {} {:?}",
            self.var,
            ineq(BoundDir::Lower, self.strict),
            self.bound
        )
    }
}

#[derive(Default, Clone)]
pub struct Lra {
    bounds: BTreeMap<LowerBound, Var>,
    var_map: DefaultVec<Option<LowerBound>, Var>,
    tableau: ModeledTableau,
    bounds_def_history: Vec<Var>,
    pub(super) epsilon_def: Option<Rational32>,
}

impl Lra {
    pub(super) fn bind_sum<'a>(&mut self, sum: Sum, acts: &mut impl TheoryArgT) -> NumExp {
        self.tableau.sum(sum, acts)
    }
    pub(super) fn bind_lower_bound<'a>(
        &mut self,
        num: NumExp,
        bound: Rational32,
        mut strict: bool,
        acts: &mut impl SatTheoryArgT<'a>,
    ) -> BoolExp {
        let bound = (bound - num.add) / num.mul;
        if let Some(x) = num.var {
            let mut pol = true;
            debug_assert_ne!(num.mul, Rational32::ZERO);
            if num.mul < Rational32::ZERO {
                strict = !strict;
                pol = !pol;
            }
            let v = self.bind_lower_bound_h(x, bound, strict, acts);
            BoolExp::unknown(Lit::new(v, pol))
        } else {
            let res = bound > Rational32::ZERO || (!strict && bound.is_zero());
            BoolExp::from_bool(res)
        }
    }

    fn bind_lower_bound_h<'a>(
        &mut self,
        nvar: NumVar,
        bound: Rational32,
        strict: bool,
        acts: &mut impl SatTheoryArgT<'a>,
    ) -> Var {
        let lbound = LowerBound {
            var: nvar,
            bound,
            strict,
        };
        match self.bounds.entry(lbound) {
            Entry::Vacant(vac) => {
                let var = acts.new_var_default();
                let sym = if strict { GT_SYM } else { GE_SYM };
                acts.log_def(
                    BoolExp::unknown(Lit::new(var, true)),
                    sym,
                    [NumExp::from_var(nvar), NumExp::from_rational(bound)].into_iter(),
                );
                vac.insert(var);
                *self.var_map.get_mut(var) = Some(lbound);
                self.bounds_def_history.push(var);
                var
            }
            Entry::Occupied(occ) => *occ.get(),
        }
    }

    pub(super) fn get_value(&self, exp: NumExp) -> EpsilonRational {
        if let Some(x) = exp.var {
            self.tableau.get_value(x) * exp.mul + exp.add
        } else {
            EpsilonRational {
                base: exp.add,
                epsilon: Rational32::ZERO,
            }
        }
    }

    pub fn fresh_exp(&mut self) -> NumExp {
        NumExp::from_var(self.tableau.fresh_var())
    }

    pub fn reuse_sum(&mut self) -> Sum {
        self.tableau.reuse_sum()
    }
}

fn propagate<'a>(
    bounds: &BTreeMap<LowerBound, Var>,
    acts: &mut impl SatTheoryArgT<'a>,
    orig_var: NumVar,
    new: EpsilonRational,
    dir: BoundDir,
) -> Result<(), ()> {
    let is_lower = matches!(dir, BoundDir::Lower);
    let new = LowerBound {
        var: orig_var,
        bound: new.base,
        strict: new.epsilon.is_zero() ^ is_lower,
    };
    let res = if is_lower {
        bounds
            .range((Unbounded, Excluded(new)))
            .rev()
            .try_for_each(|(bound, var)| propagate_bound(acts, orig_var, dir, *bound, *var))
    } else {
        bounds
            .range((Excluded(new), Unbounded))
            .try_for_each(|(bound, var)| propagate_bound(acts, orig_var, dir, *bound, *var))
    };
    match res {
        Err(false) => Err(()),
        _ => Ok(()),
    }
}

fn propagate_bound<'a>(
    acts: &mut impl SatTheoryArgT<'a>,
    orig_var: NumVar,
    dir: BoundDir,
    bound: LowerBound,
    v: Var,
) -> Result<(), bool> {
    let LowerBound { var, bound, strict } = bound;
    let is_lower = matches!(dir, BoundDir::Lower);
    let l = Lit::new(v, is_lower);
    if var != orig_var || acts.value_lit(l) == lbool::TRUE {
        return Err(true);
    }
    debug!(
        "LRA propagating {l:?}: {var:?} {} {bound:?}",
        ineq(dir, strict ^ !is_lower)
    );
    let prop = acts.propagate(l);
    if !prop {
        return Err(false);
    }
    Ok(())
}

#[derive(Copy, Clone)]
pub struct PushInfo {
    defs: u32,
    bounds: u32,
    bounds_def: u32,
}

impl Incremental for Lra {
    type LevelMarker = PushInfo;

    fn create_level(&self) -> Self::LevelMarker {
        let (defs, bounds) = self.tableau.push_info();
        PushInfo {
            defs,
            bounds,
            bounds_def: self.bounds_def_history.len() as u32,
        }
    }

    fn pop_to_level(&mut self, marker: Self::LevelMarker, clear_lits: bool) {
        self.tableau.pop_bounds_to(marker.bounds);
        if clear_lits {
            self.tableau.pop_defs_to(marker.defs);
            for var in self.bounds_def_history.drain(marker.bounds_def as usize..) {
                let bounds = mem::take(self.var_map.get_mut(var)).unwrap();
                let x = self.bounds.remove(&bounds);
                debug_assert_eq!(x, Some(var));
            }
        }
    }

    fn clear(&mut self) {
        self.bounds.clear();
        self.var_map.clear();
        self.tableau.clear();
        self.bounds_def_history.clear();
    }
}

impl<'a, A: SatTheoryArgT<'a>, P> Theory<A, A::Explain<'a>, P> for Lra {
    fn learn(&mut self, lit: Lit, acts: &mut A) -> Result<(), ()> {
        let bound = self.var_map.get(lit.var());
        if let Some(LowerBound { var, bound, strict }) = bound {
            let strict = strict ^ !lit.sign();
            let dir = if lit.sign() {
                BoundDir::Lower
            } else {
                BoundDir::Upper
            };
            debug!("LRA learn {lit:?}: {var:?} {} {bound:?}", ineq(dir, strict));
            self.tableau
                .add_bound(var, bound, dir, strict, |var, new, dir| {
                    propagate(&self.bounds, acts, var, new, dir)
                })?;
        }
        Ok(())
    }

    fn pre_decision_check(&mut self, acts: &mut A) -> Result<(), ()> {
        match self.tableau.check() {
            Ok(_) => Ok(()),
            Err(iter) => {
                let mut explain = acts.for_explain();
                let builder = explain.clause_builder();
                builder.clear();
                for (var, bound, strict, dir) in iter {
                    let neg_pol = matches!(dir, BoundDir::Upper);
                    let strict = strict ^ neg_pol;
                    let bound = LowerBound { var, bound, strict };
                    let lit = Lit::new(*self.bounds.get(&bound).unwrap(), neg_pol);
                    builder.push(lit);
                }
                drop(explain);
                debug!("Current lits are {:?}", acts.model());
                acts.raise_conflict_using_builder(true);
                Err(())
            }
        }
    }

    fn explain_propagation(&mut self, p: Lit, acts: &mut A::Explain<'a>, _: bool, _: u8) {
        let is_lower = p.sign();
        let p = p.var();
        let mut bound = self.var_map.get(p).unwrap();
        bound.strict ^= !is_lower;
        let res = if is_lower {
            self.bounds
                .range((Unbounded, Excluded(bound)))
                .rev()
                .try_for_each(|(_, var)| Err(*var))
        } else {
            self.bounds
                .range((Excluded(bound), Unbounded))
                .try_for_each(|(_, var)| Err(*var))
        };
        let res_lit = Lit::new(res.err().unwrap(), !is_lower);
        acts.clause_builder().push(res_lit);
    }
}

impl<R: Recorder> FullTheory<R> for Lra {
    type Exp = NumExp;

    type FnSort = Infallible;
    fn prepare_model(&mut self, kind: PrepareModelKind) {
        match (kind, self.epsilon_def) {
            (PrepareModelKind::GetModel | PrepareModelKind::GetValues, None) => {
                self.epsilon_def = Some(self.tableau.find_epsilon())
            }
            (PrepareModelKind::Clear, Some(_)) => self.epsilon_def = None,
            _ => {}
        }
        debug!(
            "LRA prepare_model({kind:?}) epsilon_def={:?}",
            self.epsilon_def
        );
    }

    fn get_function_info(&self, _: Symbol) -> impl FunctionAssignmentT<Exp = NumExp> {
        empty_fn_info()
    }
}
