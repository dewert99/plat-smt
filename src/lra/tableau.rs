use crate::intern::ADD_SYM;
use crate::lra::bound::{Bounds, EpsilonRational};
use crate::rexp::{Namespace, NamespaceVar};
use crate::theory::TheoryArgT;
use crate::util::{format_args2, DebugIter};
use alloc::vec::Vec;
use core::cmp::Reverse;
use core::fmt::Debug;
use core::ops::{Add, AddAssign, Mul, Neg, Range, Sub, SubAssign};
use dary_heap::QuaternaryHeap;
use default_vec2::DefaultVec;
use lazy_rational::Rational32;
use log::{debug, trace};
use smallvec::SmallVec;
use std::mem;
use std::num::NonZeroU32;

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct NumVar(pub(crate) NonZeroU32);

impl NumVar {
    /// Always bound to be equal to 1
    pub const ONE: NumVar = NumVar(NonZeroU32::new(1).unwrap());

    pub fn to_nv(self) -> NamespaceVar {
        NamespaceVar(Namespace::Number, self.0.get() - 1)
    }
}

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq)]
pub struct NumExp {
    pub(super) var: Option<NumVar>,
    pub(super) mul: Rational32,
    pub(super) add: Rational32,
}

impl Add<Rational32> for NumExp {
    type Output = NumExp;

    fn add(self, rhs: Rational32) -> Self::Output {
        NumExp {
            var: self.var,
            mul: self.mul,
            add: self.add + rhs,
        }
    }
}

impl Mul<Rational32> for NumExp {
    type Output = NumExp;

    fn mul(self, rhs: Rational32) -> Self::Output {
        if rhs.is_zero() {
            NumExp::ZERO.weaken()
        } else {
            NumExp {
                var: self.var,
                mul: self.mul * rhs,
                add: self.add * rhs,
            }
        }
    }
}

impl Neg for NumExp {
    type Output = NumExp;

    fn neg(self) -> Self::Output {
        NumExp {
            var: self.var,
            mul: -self.mul,
            add: -self.add,
        }
    }
}

impl NumExp {
    pub const ZERO: NumExp = NumExp::from_rational(Rational32::ZERO);
    pub const ONE: NumExp = NumExp::from_rational(Rational32::ONE);
    pub const fn from_rational(rational: Rational32) -> Self {
        NumExp {
            var: None,
            mul: Rational32::ZERO,
            add: rational,
        }
    }

    pub const fn from_int(int: i32) -> Self {
        NumExp::from_rational(Rational32::new(int))
    }

    pub const fn from_var(var: NumVar) -> Self {
        NumExp {
            var: Some(var),
            mul: Rational32::ONE,
            add: Rational32::ZERO,
        }
    }

    /// Extracts the value of `self` if `self` is a constant
    pub fn try_into_rational(self) -> Option<Rational32> {
        self.var.is_none().then_some(self.add)
    }

    /// Like [`try_into_rational`] but dependent on implementation detail optimizations
    pub fn try_into_rational_for_opt(self) -> Option<Rational32> {
        self.mul.is_zero().then_some(self.add)
    }

    /// Degrades self so that it is not considered a constant by the type checker
    pub(super) fn weaken(mut self) -> Self {
        if self.var.is_none() {
            self.var = Some(NumVar::ONE);
            debug_assert_eq!(self.mul, Rational32::ZERO);
        }
        self
    }
}
impl Into<usize> for NumVar {
    fn into(self) -> usize {
        self.0.get() as usize
    }
}

#[derive(Default, Clone, Debug)]
pub struct Sum {
    elts: Vec<BufElt>,
    offset: Rational32,
}

impl AddAssign<NumExp> for Sum {
    fn add_assign(&mut self, rhs: NumExp) {
        self.offset = self.offset + rhs.add;
        if let Some(var) = rhs.var {
            self.elts.push((var, rhs.mul))
        }
    }
}

impl Add<NumExp> for Sum {
    type Output = Sum;

    fn add(mut self, rhs: NumExp) -> Self::Output {
        self += rhs;
        self
    }
}

impl Sub<NumExp> for Sum {
    type Output = Sum;

    fn sub(self, rhs: NumExp) -> Self::Output {
        self + (-rhs)
    }
}

impl SubAssign<NumExp> for Sum {
    fn sub_assign(&mut self, rhs: NumExp) {
        *self += -rhs
    }
}

impl Extend<NumExp> for Sum {
    fn extend<T: IntoIterator<Item = NumExp>>(&mut self, iter: T) {
        iter.into_iter().for_each(|x| *self += x)
    }
}

#[derive(Default, Clone)]
struct TableauAlloc {
    vars: Vec<NumVar>,
    coefficients: Vec<Rational32>,
    defs: DefaultVec<(u32, u32), NumVar>,
    buf: Vec<BufElt>,
}

impl TableauAlloc {
    fn get_range(&self, var: NumVar) -> Range<usize> {
        let (start, end) = self.defs.get(var);
        start as usize..end as usize
    }
    fn get_vars(&self, var: NumVar) -> &[NumVar] {
        &self.vars[self.get_range(var)]
    }

    fn get_coefficients(&self, var: NumVar) -> &[Rational32] {
        &self.coefficients[self.get_range(var)]
    }

    fn get(&self, var: NumVar) -> (&[NumVar], &[Rational32]) {
        let range = self.get_range(var);
        (&self.vars[range.clone()], &self.coefficients[range])
    }

    fn var_len(&self) -> u32 {
        debug_assert_eq!(self.vars.len(), self.coefficients.len());
        self.vars.len() as u32
    }

    fn push(&mut self, var: NumVar, coefficient: Rational32) {
        self.vars.push(var);
        self.coefficients.push(coefficient);
    }

    fn push_sum(&mut self, sum: Sum) -> Rational32 {
        let offset = sum.offset;
        for &(var, coefficients) in &sum.elts {
            self.push(var, coefficients)
        }
        self.buf = sum.elts;
        offset
    }

    fn push_var_def(&mut self, var: NumVar) {
        let range = self.get_range(var);
        self.vars.extend_from_within(range.clone());
        self.coefficients.extend_from_within(range.clone());
    }

    fn set_var(&mut self, var: NumVar, buf_start: u32, buf_end: u32) {
        *self.defs.get_mut(var) = (buf_start, buf_end);
    }

    fn take_buf(&mut self) -> Vec<BufElt> {
        self.buf.clear();
        mem::take(&mut self.buf)
    }

    fn resolve_inner(
        &mut self,
        fix_var: impl Fn(NumVar) -> Option<Rational32>,
        mut offset: Rational32,
        start: usize,
    ) -> (Rational32, Vec<BufElt>) {
        let mut curr = start;
        let mut last = start;
        while curr < self.vars.len() {
            trace!(
                "{:?}{:?} {:?}{:?} {offset:?}",
                &self.coefficients[start..last],
                &self.vars[start..last],
                &self.coefficients[curr..],
                &self.vars[curr..]
            );
            let var = self.vars[curr];
            let (start, end) = self.defs.get(var);
            if let Some(x) = fix_var(var) {
                offset += x * self.coefficients[curr];
            } else if start == end {
                debug_assert_eq!(start, 0);
                self.vars.swap(curr, last);
                self.coefficients.swap(curr, last);
                last += 1;
            } else {
                self.vars.extend_from_within(start as usize..end as usize);
                let coefficient = self.coefficients[curr];
                for i in start..end {
                    self.coefficients
                        .push(self.coefficients[i as usize] * coefficient);
                }
            }
            curr += 1;
        }
        let mut buf = self.take_buf();
        buf.extend(
            self.vars[start..last]
                .iter()
                .copied()
                .zip(self.coefficients[start..last].iter().copied()),
        );
        self.vars.truncate(start);
        self.coefficients.truncate(start);
        (offset, buf)
    }

    fn clear(&mut self) {
        self.vars.clear();
        self.coefficients.clear();
        self.defs.clear();
    }
}

type BufElt = (NumVar, Rational32);
type UsageVec = SmallVec<[(NumVar, u32); 2]>;
#[derive(Default, Clone)]
struct Tableau {
    alloc: TableauAlloc,
    usages: DefaultVec<UsageVec, NumVar>,
    def_log: Vec<(NumVar, u32, u32)>,
}

impl Tableau {
    fn resolve(
        &mut self,
        sum: Sum,
        fix_var: impl Fn(NumVar) -> Option<Rational32>,
    ) -> (Rational32, Vec<BufElt>) {
        debug!("Resolving {:?} ...", sum);
        let start = self.alloc.vars.len();
        let offset = self.alloc.push_sum(sum);
        let res = self.alloc.resolve_inner(fix_var, offset, start);
        debug!("... to {:?}", res);
        res
    }

    fn resolve_var(&mut self, var: NumVar) -> Vec<BufElt> {
        let offset = Rational32::ZERO;
        let start = self.alloc.vars.len();
        self.alloc.push_var_def(var);
        self.alloc.resolve_inner(|_| None, offset, start).1
    }

    fn unassign_var(&mut self, v: NumVar) {
        let (start, end) = self.alloc.defs.get(v);
        self.def_log.push((v, start, end));
        for (i, &var) in self.alloc.get_vars(v).iter().enumerate() {
            self.usages.get_mut(var).retain(|&mut (v2, i2)| {
                if v2 == v {
                    debug_assert_eq!(i as u32, i2);
                    false
                } else {
                    true
                }
            })
        }
        *self.alloc.defs.get_mut(v) = (0, 0);
    }

    fn assign_var(&mut self, v: NumVar, buf: Vec<BufElt>, mul: Rational32) {
        debug_assert_eq!(self.alloc.defs.get(v), (0, 0));
        self.def_log.push((v, 0, 0));
        let start = self.alloc.var_len();
        for (i, &(var, coefficient)) in buf.iter().enumerate() {
            self.alloc.push(var, coefficient * mul);
            self.usages.get_mut(var).push((v, i as u32))
        }
        self.alloc.buf = buf;
        let end = self.alloc.var_len();
        self.alloc.set_var(v, start, end);
    }

    fn reuse_buf(&mut self, buf: Vec<BufElt>) {
        self.alloc.buf = buf;
    }

    fn push_info(&self) -> u32 {
        self.def_log.len() as u32
    }

    fn pop_to(&mut self, push_info: u32) {
        let push_info = push_info as usize;
        for (v, start, end) in self.def_log.drain(push_info..).rev() {
            for (i, &var) in self.alloc.get_vars(v).iter().enumerate() {
                self.usages.get_mut(var).retain(|&mut (v2, i2)| {
                    if v2 == v {
                        debug_assert_eq!(i as u32, i2);
                        false
                    } else {
                        true
                    }
                })
            }
            self.alloc.set_var(v, start, end);
            for (i, &var) in self.alloc.get_vars(v).iter().enumerate() {
                self.usages.get_mut(var).push((v, i as u32))
            }
        }
    }

    fn clear(&mut self) {
        self.def_log.clear();
        self.usages.clear();
        self.alloc.clear();
    }

    fn is_free(&self, v: NumVar) -> bool {
        self.alloc.get_range(v).is_empty()
    }
}

#[derive(Copy, Clone, Debug)]
pub enum BoundDir {
    Upper,
    Lower,
}

#[derive(Clone)]
pub struct ModeledTableau {
    defs: Tableau,
    bounds: DefaultVec<Bounds, NumVar>,
    values: DefaultVec<EpsilonRational, NumVar>,
    bounds_history: Vec<(NumVar, Bounds)>,
    /// Stores all NumVars `v` such that `self.values.get(v)` is not in `self.bounds.get(v)`
    out_of_bounds: QuaternaryHeap<Reverse<NumVar>>,
    last_var: NumVar,
}

impl Default for ModeledTableau {
    fn default() -> Self {
        let mut res = ModeledTableau {
            defs: Tableau::default(),
            bounds: DefaultVec::default(),
            values: DefaultVec::default(),
            bounds_history: Vec::new(),
            out_of_bounds: QuaternaryHeap::new(),
            last_var: NumVar::ONE,
        };
        *res.bounds.get_mut(NumVar::ONE) = Bounds {
            lower: Some(Rational32::ONE.into()),
            upper: Some(Rational32::ONE.into()),
        };
        *res.values.get_mut(NumVar::ONE) = Rational32::ONE.into();
        res
    }
}

pub(super) trait ConflictIter:
    Iterator<Item = (NumVar, Rational32, bool, BoundDir)> + Clone
{
}

impl<I: Iterator<Item = (NumVar, Rational32, bool, BoundDir)> + Clone> ConflictIter for I {}

impl ModeledTableau {
    pub fn fresh_var(&mut self) -> NumVar {
        self.last_var.0 = self.last_var.0.checked_add(1).unwrap();
        self.last_var
    }

    pub fn vars(&self) -> impl Iterator<Item = NumVar> {
        (NonZeroU32::new(1).unwrap()..self.last_var.0.checked_add(1).unwrap())
            .into_iter()
            .map(|x| NumVar(x))
    }

    pub fn sum(&mut self, elts: Sum, acts: &mut impl TheoryArgT) -> NumExp {
        if elts.elts.is_empty() {
            return NumExp::from_rational(elts.offset).weaken();
        }
        let (offset, mut defs) = self.defs.resolve(elts, |x| {
            if let Bounds {
                upper: Some(upper),
                lower: Some(lower),
            } = self.bounds.get(x)
            {
                if upper.base == lower.base && upper.epsilon.is_zero() && lower.epsilon.is_zero() {
                    return Some(upper.base);
                }
            }
            None
        });

        dedup_defs(&mut defs);

        match &*defs {
            &[] => {
                self.defs.reuse_buf(defs);
                // this should not be considered a constant for type checking (see weaken)
                NumExp::from_rational(offset).weaken()
            }
            &[(var, mul)] => {
                self.defs.reuse_buf(defs);
                NumExp {
                    var: Some(var),
                    mul,
                    add: offset,
                }
            }
            _ => {
                let fresh = self.fresh_var();
                acts.log_def(
                    NumExp::from_var(fresh),
                    ADD_SYM,
                    defs.iter().map(|&(var, mul)| NumExp::from_var(var) * mul),
                );
                // TODO pick a better basic
                self.defs.assign_var(fresh, defs, Rational32::ONE);
                debug_assert!(matches!(
                    self.bounds.get(fresh),
                    Bounds {
                        lower: None,
                        upper: None
                    }
                ));
                let (vars, coefficients) = self.defs.alloc.get(fresh);
                let mut value: EpsilonRational = EpsilonRational::default();
                for (&var, &coefficient) in vars.iter().zip(coefficients) {
                    let add = self.values.get(var) * coefficient;
                    value = value + add;
                }
                *self.values.get_mut(fresh) = value;
                debug!("{fresh:?} starts with value {value:?}");
                NumExp {
                    var: Some(fresh),
                    mul: Rational32::ONE,
                    add: offset,
                }
            }
        }
    }

    pub fn add_bound(
        &mut self,
        var: NumVar,
        bound: Rational32,
        dir: BoundDir,
        strict: bool,
        prop: impl FnOnce(NumVar, EpsilonRational, BoundDir) -> Result<(), ()>,
    ) -> Result<(), ()> {
        let epsilon = match (dir, strict) {
            (_, false) => Rational32::ZERO,
            (BoundDir::Lower, true) => Rational32::ONE,
            (BoundDir::Upper, true) => -Rational32::ONE,
        };
        let bound = EpsilonRational {
            base: bound,
            epsilon,
        };
        let existing = self.bounds.get_mut(var);
        let value = self.values.get_mut(var);
        match dir {
            BoundDir::Lower => {
                if existing.lower.is_none_or(|existing| existing < bound) {
                    prop(var, bound, BoundDir::Lower)?;
                    self.bounds_history.push((var, *existing));
                    existing.lower = Some(bound);
                    debug!(
                        "Bounds are now {:?}* <= {var:?} = {value:?} <= {:?}",
                        existing.lower, existing.upper
                    );
                    if *value < bound {
                        self.try_update(var, bound);
                    }
                }
            }
            BoundDir::Upper => {
                if existing.upper.is_none_or(|existing| existing > bound) {
                    prop(var, bound, BoundDir::Upper)?;
                    self.bounds_history.push((var, *existing));
                    existing.upper = Some(bound);
                    debug!(
                        "Bounds are now {:?} <= {var:?} = {value:?} <= {:?}*",
                        existing.lower, existing.upper
                    );
                    if *value > bound {
                        self.try_update(var, bound);
                    }
                }
            }
        };
        Ok(())
    }

    fn try_update(&mut self, var: NumVar, val: EpsilonRational) {
        if self.defs.is_free(var) {
            self.update(var, val);
        } else {
            self.out_of_bounds.push(Reverse(var))
        }
    }

    fn update(&mut self, var: NumVar, val: EpsilonRational) {
        debug!("Updating {var:?} to {val:?}");
        let value = self.values.get_mut(var);
        let offset = val - *value;
        *value = val;
        let mut buf = self.defs.alloc.take_buf();
        let mut next = Some((var, Rational32::ONE));
        while let Some((var, mul)) = next {
            for &mut (v, n) in self.defs.usages.get_mut(var) {
                let v_mul = mul * self.defs.alloc.get_coefficients(v)[n as usize];
                debug_assert_eq!(var, self.defs.alloc.get_vars(v)[n as usize]);
                let v_value = self.values.get_mut(v);
                let old_value = *v_value;
                *v_value = old_value + (offset * v_mul);
                debug!("Updating {v:?} to {v_value:?} = {old_value:?} + ({offset:?} * {v_mul:?})");
                self.out_of_bounds.push(Reverse(v));
                buf.push((v, v_mul))
            }
            next = buf.pop();
        }
    }

    fn pivot_update(&mut self, var: NumVar, val: EpsilonRational) -> Result<(), EpsilonRational> {
        debug!("Pivot updating {var:?} to {val:?}");
        let mut var_def = self.defs.resolve_var(var);
        dedup_defs(&mut var_def);
        self.defs.unassign_var(var);
        let value = self.values.get_mut(var);
        let offset = val - *value;
        let success = self.pivot(var, var_def, offset);
        if success {
            self.update(var, val);
            Ok(())
        } else {
            // reassign var
            self.defs.pop_to(self.defs.push_info() - 1);
            Err(offset)
        }
    }

    /// Finds a pivot and pivots if possilble returning true, otherwise it returns false
    /// Restores var_def to the buf in either case
    fn pivot(&mut self, var: NumVar, mut var_def: Vec<BufElt>, offset: EpsilonRational) -> bool {
        debug!(
            "Looking for a pivot for {var:?} from {var_def:?} since it was offset by {offset:?}"
        );
        for (swap_var, coefficient) in &mut var_def {
            let swap_val = self.values.get(*swap_var);
            let swap_bounds = self.bounds.get(*swap_var);
            let swap_offset = offset / *coefficient;
            if !swap_bounds.at_bound(swap_val, swap_offset) {
                let (sv, sc) = (*swap_var, *coefficient);
                *swap_var = var;
                *coefficient = -Rational32::ONE;
                self.defs.assign_var(sv, var_def, -sc.recip());
                debug!("Pivoted {sv:?} := {:?}", self.defs.alloc.get(sv));
                return true;
            }
        }
        var_def.push((var, -Rational32::ONE));
        self.defs.reuse_buf(var_def);
        false
    }

    fn iter_bounds(&self, offset: EpsilonRational) -> impl ConflictIter + use<'_> {
        let offset = if offset.base.is_zero() {
            offset.epsilon
        } else {
            offset.base
        };
        self.defs
            .alloc
            .buf
            .iter()
            .map(move |&(bound_var, coefficient)| {
                let bounds = self.bounds.get(bound_var);
                let offset = offset / coefficient;
                let (bound, strict, dir) = bounds.pick_bound(offset);
                (bound_var, bound, strict, dir)
            })
    }

    pub fn check(&mut self) -> Result<(), impl ConflictIter + use<'_>> {
        while let Some(Reverse(var)) = self.out_of_bounds.pop() {
            debug!(
                "Checking {:?} <= {var:?} = {:?} <= {:?}",
                self.bounds.get(var).lower,
                self.values.get(var),
                self.bounds.get(var).upper
            );
            if let Some(val) = self.bounds.get(var).nearest_bound(self.values.get(var)) {
                debug_assert!(!self.defs.is_free(var));
                let res = self.pivot_update(var, val);
                if let Err(err) = res {
                    self.out_of_bounds.push(Reverse(var));
                    let err = self.iter_bounds(err);
                    debug!(
                        "Found conflict {:?}",
                        DebugIter(err.clone().map(|(var, bound, strict, dir)| format_args2!(
                            "{var:?} {} {bound:?}",
                            ineq(dir, strict)
                        )))
                    );
                    return Err(err);
                }
            }
        }
        Ok(())
    }

    pub fn push_info(&self) -> (u32, u32) {
        (self.defs.push_info(), self.bounds_history.len() as u32)
    }

    pub fn pop_bounds_to(&mut self, bounds_len: u32) {
        for (var, bounds) in self.bounds_history.drain(bounds_len as usize..).rev() {
            *self.bounds.get_mut(var) = bounds
        }
    }

    pub fn pop_defs_to(&mut self, defs_info: u32) {
        self.defs.pop_to(defs_info);
    }

    pub fn clear(&mut self) {
        self.defs.clear();
        self.bounds.clear();
        self.values.clear();
        self.bounds_history.clear();
        *self.bounds.get_mut(NumVar::ONE) = Bounds {
            lower: Some(Rational32::ONE.into()),
            upper: Some(Rational32::ONE.into()),
        };
        *self.values.get_mut(NumVar::ONE) = Rational32::ONE.into();
        self.last_var = NumVar::ONE;
    }

    pub fn get_value(&self, var: NumVar) -> EpsilonRational {
        self.values.get(var)
    }

    pub fn reuse_sum(&mut self) -> Sum {
        Sum {
            elts: self.defs.alloc.take_buf(),
            offset: Rational32::ZERO,
        }
    }

    pub(crate) fn find_epsilon(&self) -> Rational32 {
        let mut epsilon_def = Rational32::new(1);
        let half = Rational32::new(2).recip();
        for var in self.vars() {
            let bounds = self.bounds.get(var);
            let value = self.values.get(var);
            while !bounds.contains_with_epsilon_def(value, epsilon_def) {
                epsilon_def = epsilon_def * half;
            }
            debug!(
                "Confirmed {:?} <= {value:?} <= {:?} with {epsilon_def:?}",
                bounds.lower, bounds.upper
            )
        }
        epsilon_def
    }
}

fn dedup_defs(defs: &mut Vec<BufElt>) {
    defs.sort_unstable_by_key(|x| x.0);
    let mut last_checked = 0;
    for i in 1..defs.len() {
        if defs[i].0 == defs[last_checked].0 {
            let this = defs[i].1;
            defs[last_checked].1 += this;
        } else {
            if !defs[last_checked].1.is_zero() {
                last_checked += 1;
            }
            defs.swap(last_checked, i);
        }
    }
    if !defs[last_checked].1.is_zero() {
        last_checked += 1;
    }
    defs.truncate(last_checked);
}

pub(super) fn ineq(dir: BoundDir, strict: bool) -> &'static str {
    match (dir, strict) {
        (BoundDir::Upper, true) => "<",
        (BoundDir::Upper, false) => "<=",
        (BoundDir::Lower, true) => ">",
        (BoundDir::Lower, false) => ">=",
    }
}
