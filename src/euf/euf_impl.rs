use super::egraph::Children;
use super::euf::{litvec, BoolClass, EClass, Euf, FunctionInfoIter, PushInfo};
use super::euf_trait::EufT;
use super::explain::Justification;
use crate::intern::{DisplayInterned, InternInfo, Symbol, BOOL_SORT};
use crate::solver::ExpLike;
use crate::theory::TheoryArg;
use crate::util::{format_args2, pairwise_sym};
use crate::{Approx, BoolExp, Conjunction, Exp, HasSort, Solver, Sort};
use alloc::borrow::Cow;
use core::fmt::Formatter;
use plat_egg::raw::Language;
use plat_egg::Id;
use platsat::Lit;
use std::mem;

#[derive(Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Debug)]
pub struct UExp {
    pub(super) id: Id,
    pub(super) sort: Sort,
}

impl UExp {
    pub fn id(self) -> Id {
        self.id
    }

    pub fn new(id: Id, sort: Sort) -> Self {
        UExp { id, sort }
    }

    pub fn with_id(self, new_id: Id) -> Self {
        UExp {
            id: new_id,
            sort: self.sort,
        }
    }
}

impl DisplayInterned for UExp {
    fn fmt(&self, i: &InternInfo, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "(as @v{:?} {})", self.id(), self.sort().with_intern(i))
    }
}

impl HasSort for UExp {
    fn sort(self) -> Sort {
        self.sort
    }
}

impl From<UExp> for Exp<UExp> {
    fn from(value: UExp) -> Self {
        Exp::Other(value)
    }
}

#[derive(Debug)]
pub enum Never {}

impl Into<Cow<'static, str>> for Never {
    fn into(self) -> Cow<'static, str> {
        match self {}
    }
}
type Result<T> = core::result::Result<T, Never>;

impl EufT for Euf {
    type UExp = UExp;
    type Unsupported = Never;

    fn eq_approx(
        &mut self,
        e1: Exp<UExp>,
        e2: Exp<UExp>,
        _: Approx,
        acts: &mut TheoryArg<PushInfo>,
    ) -> BoolExp {
        let id1 = self.id_for_exp(e1, acts);
        let id2 = self.id_for_exp(e2, acts);
        self.add_eq_node(id1, id2, acts)
    }

    fn assert_eq(&mut self, e1: Exp<UExp>, e2: Exp<UExp>, acts: &mut TheoryArg<PushInfo>) -> () {
        match (e1, e2) {
            (Exp::Bool(b1), Exp::Bool(b2)) => match (b1.to_lit(), b2.to_lit()) {
                (Err(pol), Ok(l)) | (Ok(l), Err(pol)) => {
                    acts.propagate(l ^ !pol);
                }
                (Err(b1), Err(b2)) => {
                    if b1 != b2 {
                        acts.raise_conflict(&[], false);
                    }
                }
                (Ok(b1), Ok(b2)) => {
                    let id1 = self.id_for_lit(b1, acts);
                    let id2 = self.id_for_lit(b2, acts);
                    let _ = self.union(acts, id1, id2, Justification::NOOP);
                }
            },
            (Exp::Other(u1), Exp::Other(u2)) => {
                let _ = self.union(acts, u1.id, u2.id, Justification::NOOP);
            }
            _ => unreachable!(),
        }
    }

    fn distinct_approx(
        &mut self,
        exps: &[Exp<Self::UExp>],
        approx: Approx,
        acts: &mut TheoryArg<Self::LevelMarker>,
    ) -> BoolExp {
        if approx != Approx::Approx(false) {
            let mut c: Conjunction = acts.new_junction();
            c.extend(
                pairwise_sym(exps).map(|(e1, e2)| !self.eq_approx(*e1, *e2, Approx::Exact, acts)),
            );
            return acts.collapse_bool_approx(c, approx);
        }

        let Some(e0) = exps.first() else {
            return BoolExp::TRUE;
        };

        let Exp::Other(_) = e0 else {
            let b0 = e0.as_bool().unwrap();
            let mut bools = exps[1..].iter().map(|exp| exp.as_bool().unwrap());
            let Some(b1) = bools.next() else {
                return BoolExp::TRUE;
            };
            return if let Some(_) = bools.next() {
                BoolExp::FALSE
            } else {
                acts.xor_approx(b0, b1, approx)
            };
        };

        let distinct_sym = acts.intern_mut().symbols.gen_sym("distinct");
        self.distinct_gensym += 1;
        let b = BoolExp::unknown(Lit::new(acts.new_var_default(), true));
        for exp in exps {
            let id = self.id_for_exp(*exp, acts);
            let mut added = false;
            self.egraph
                .add(distinct_sym.into(), Children::from_slice(&[id]), |_| {
                    added = true;
                    EClass::Singleton(!b)
                });
            if !added {
                return BoolExp::FALSE;
            }
        }
        b
    }

    fn assert_distinct_eq(
        &mut self,
        exps: &[Exp<UExp>],
        target: BoolExp,
        acts: &mut TheoryArg<PushInfo>,
    ) {
        if target != BoolExp::TRUE {
            let mut c: Conjunction = acts.new_junction();
            c.extend(
                pairwise_sym(exps).map(|(e1, e2)| !self.eq_approx(*e1, *e2, Approx::Exact, acts)),
            );
            acts.assert_junction_eq(c, target);
            return;
        }

        let Some(e0) = exps.first() else { return };

        let Exp::Other(_) = e0 else {
            let b0 = e0.as_bool().unwrap();
            let mut bools = exps[1..].iter().map(|exp| exp.as_bool().unwrap());
            let Some(b1) = bools.next() else {
                return;
            };
            if let Some(_) = bools.next() {
                acts.add_clause_unchecked([]);
            } else {
                acts.assert_xor_eq(b0, b1, BoolExp::TRUE);
            }
            return;
        };

        let distinct_sym = acts.intern_mut().symbols.gen_sym("distinct");
        self.distinct_gensym += 1;
        for exp in exps {
            let id = self.id_for_exp(*exp, acts);
            let mut added = false;
            self.egraph
                .add(distinct_sym.into(), Children::from_slice(&[id]), |_| {
                    added = true;
                    EClass::Singleton(BoolExp::FALSE)
                });
            if !added {
                acts.raise_conflict(&[], false);
                return;
            }
        }
    }

    fn sorted_fn(
        &mut self,
        f: Symbol,
        children: impl Iterator<Item = Exp<UExp>>,
        target_sort: Sort,
        acts: &mut TheoryArg<PushInfo>,
    ) -> Result<Exp<UExp>> {
        Ok(self.sorted_fn_id(f, children, target_sort, acts)?.1)
    }

    fn assert_fn_eq(
        &mut self,
        f: Symbol,
        children: impl Iterator<Item = Exp<UExp>>,
        exp: Exp<UExp>,
        acts: &mut TheoryArg<PushInfo>,
    ) -> Result<()> {
        self.assert_fn_eq_id(f, children, exp, acts)?;
        Ok(())
    }
    fn ite_approx(
        &mut self,
        i: BoolExp,
        t: Exp<UExp>,
        e: Exp<UExp>,
        _: Approx,
        acts: &mut TheoryArg<PushInfo>,
    ) -> Result<Exp<UExp>> {
        let res = match i.to_lit() {
            Err(true) => t,
            Err(false) => e,
            Ok(ilit) => {
                if t == e {
                    t
                } else {
                    let tid = self.id_for_exp(t, acts);
                    let eid = self.id_for_exp(e, acts);
                    self.raw_ite(ilit, tid, eid, t.sort(), acts)
                }
            }
        };
        Ok(res)
    }

    fn assert_ite_eq(
        &mut self,
        i: BoolExp,
        t: Exp<UExp>,
        e: Exp<UExp>,
        target: Exp<UExp>,
        acts: &mut TheoryArg<PushInfo>,
    ) -> Result<()> {
        match i.to_lit() {
            Err(true) => self.assert_eq(t, target, acts),
            Err(false) => self.assert_eq(e, target, acts),
            Ok(ilit) => {
                if t == e {
                    self.assert_eq(t, target, acts)
                } else {
                    let tid = self.id_for_exp(t, acts);
                    let eid = self.id_for_exp(e, acts);
                    self.raw_ite_eq(ilit, tid, eid, target, acts);
                }
            }
        }
        Ok(())
    }

    fn placeholder_uexp_from_sort(sort: Sort) -> Self::UExp {
        UExp { id: Id::MAX, sort }
    }

    fn init_function_info(&mut self) {
        self.init_function_info()
    }

    type FunctionInfo<'a> = FunctionInfoIter<'a> where Self: 'a ;

    fn get_function_info(&self, f: Symbol) -> FunctionInfoIter<'_> {
        self.get_function_info(f)
    }
}

impl Euf {
    fn sorted_fn_id(
        &mut self,
        f: Symbol,
        children: impl Iterator<Item = Exp<UExp>>,
        target_sort: Sort,
        acts: &mut TheoryArg<PushInfo>,
    ) -> Result<(Id, Exp<UExp>)> {
        let children = self.resolve_children(children, acts);
        let id = self.egraph.add(f.into(), children, |id| {
            if target_sort == BOOL_SORT {
                let l = Lit::new(acts.new_var_default(), true);
                self.lit.add_id_to_lit(id, l);
                EClass::Bool(BoolClass::Unknown(litvec![l]))
            } else {
                EClass::Uninterpreted(target_sort)
            }
        });
        let intern = acts.intern();
        let exp = self.id_to_exp(id);
        if exp.sort() != target_sort {
            panic!(
                "trying to create function {}{:?} with sort {}, but it already has sort {}",
                f.with_intern(intern),
                self.egraph.id_to_node(id).children(),
                target_sort.with_intern(intern),
                exp.sort().with_intern(intern)
            )
        };
        Ok((id, exp))
    }

    fn assert_fn_eq_id(
        &mut self,
        f: Symbol,
        children: impl Iterator<Item = Exp<UExp>>,
        exp: Exp<UExp>,
        acts: &mut TheoryArg<PushInfo>,
    ) -> Result<Id> {
        let children = self.resolve_children(children, acts);
        let id = self.egraph.add(f.into(), children, |_| {
            if exp.sort() == BOOL_SORT {
                EClass::Bool(BoolClass::Unknown(litvec![]))
            } else {
                EClass::Uninterpreted(exp.sort())
            }
        });
        self.union_exp(exp, id, acts);
        Ok(id)
    }

    fn bind_ite(&mut self, i: Lit, t: Id, e: Id, target: Id, acts: &mut TheoryArg<PushInfo>) {
        let eqt = self.add_eq_node(target, t, acts);
        match eqt.to_lit() {
            Ok(l) => acts.add_theory_lemma(&[!i, l]),
            Err(true) => {}
            Err(false) => acts.add_theory_lemma(&[!i]),
        }
        let eqe = self.add_eq_node(target, e, acts);
        match eqe.to_lit() {
            Ok(l) => acts.add_theory_lemma(&[i, l]),
            Err(true) => {}
            Err(false) => acts.add_theory_lemma(&[i]),
        }
    }
    fn raw_ite(
        &mut self,
        i: Lit,
        t: Id,
        e: Id,
        s: Sort,
        acts: &mut TheoryArg<PushInfo>,
    ) -> Exp<UExp> {
        let mut ifs = mem::take(&mut self.ifs);
        let id = ifs.get_or_insert((i, t, e), || {
            let sym = acts
                .intern_mut()
                .symbols
                .gen_sym(&format_args2!("if|{i:?}|id{t}|id{e}"));
            let (fresh_id, _) = self.sorted_fn_id(sym, [].into_iter(), s, acts).unwrap();
            self.bind_ite(i, t, e, fresh_id, acts);
            fresh_id
        });
        self.ifs = ifs;
        self.id_to_exp(id)
    }

    fn raw_ite_eq(
        &mut self,
        i: Lit,
        t: Id,
        e: Id,
        target: Exp<UExp>,
        acts: &mut TheoryArg<PushInfo>,
    ) -> Exp<UExp> {
        let mut added = false;
        let mut ifs = mem::take(&mut self.ifs);
        let id = ifs.get_or_insert((i, t, e), || {
            added = true;
            let sym = acts
                .intern_mut()
                .symbols
                .gen_sym(&format_args2!("if|{i:?}|id{t}|id{e}"));
            let fresh_id = self
                .assert_fn_eq_id(sym, [].into_iter(), target, acts)
                .unwrap();
            self.bind_ite(i, t, e, fresh_id, acts);
            fresh_id
        });
        self.ifs = ifs;
        if !added {
            self.union_exp(target, id, acts)
        }
        self.id_to_exp(id)
    }
}

impl ExpLike<Euf> for UExp {
    fn canonize(self, solver: &Solver<Euf>) -> Self {
        UExp {
            id: solver.theory().find(self.id),
            sort: self.sort,
        }
    }
}
