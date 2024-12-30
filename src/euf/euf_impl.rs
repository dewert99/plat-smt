use super::egraph::Children;
use super::euf::{litvec, BoolClass, EClass, Euf, FunctionInfoIter, PushInfo};
use super::euf_trait::{assert_distinct, EufT};
use super::explain::Justification;
use crate::intern::{DisplayInterned, InternInfo, Symbol, BOOL_SORT};
use crate::local_error::LocalError::SortMismatch;
use crate::local_error::*;
use crate::solver::ExpLike;
use crate::theory::TheoryArg;
use crate::util::format_args2;
use crate::{Approx, BoolExp, Exp, HasSort, Solver, Sort};
use core::fmt::Formatter;
use plat_egg::raw::Language;
use plat_egg::Id;
use platsat::Lit;
use std::{iter, mem};

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
impl EufT for Euf {
    type UExp = UExp;

    fn eq_approx(
        &mut self,
        e1: Exp<UExp>,
        e2: Exp<UExp>,
        _: Approx,
        acts: &mut TheoryArg<PushInfo>,
    ) -> Result<BoolExp> {
        if e1.sort() != e2.sort() {
            Err(SortMismatch {
                actual: e2.sort(),
                expected: e1.sort(),
            })
        } else {
            let id1 = self.id_for_exp(e1, acts);
            let id2 = self.id_for_exp(e2, acts);
            Ok(self.add_eq_node(id1, id2, acts))
        }
    }

    fn assert_eq(
        &mut self,
        e1: Exp<UExp>,
        e2: Exp<UExp>,
        acts: &mut TheoryArg<PushInfo>,
    ) -> Result<()> {
        match (e1, e2) {
            (Exp::Bool(b1), Exp::Bool(b2)) => match (b1.to_lit(), b2.to_lit()) {
                (Err(pol), Ok(l)) | (Ok(l), Err(pol)) => {
                    acts.propagate(l ^ !pol);
                    Ok(())
                }
                (Err(b1), Err(b2)) => {
                    if b1 != b2 {
                        acts.raise_conflict(&[], false);
                    }
                    Ok(())
                }
                (Ok(b1), Ok(b2)) => {
                    let id1 = self.id_for_lit(b1, acts);
                    let id2 = self.id_for_lit(b2, acts);
                    let _ = self.union(acts, id1, id2, Justification::NOOP);
                    Ok(())
                }
            },
            (Exp::Other(u1), Exp::Other(u2)) => {
                if u2.sort != u1.sort {
                    Err(SortMismatch {
                        actual: u2.sort,
                        expected: u1.sort,
                    })
                } else {
                    let _ = self.union(acts, u1.id, u2.id, Justification::NOOP);
                    Ok(())
                }
            }
            (Exp::Bool(_), Exp::Other(u2)) => Err(SortMismatch {
                actual: u2.sort,
                expected: BOOL_SORT,
            }),
            (Exp::Other(u1), Exp::Bool(_)) => Err(SortMismatch {
                actual: BOOL_SORT,
                expected: u1.sort,
            }),
        }
    }

    fn assert_distinct(
        &mut self,
        mut exps: impl Iterator<Item = Exp<UExp>>,
        acts: &mut TheoryArg<PushInfo>,
    ) -> IResult<()> {
        let Some(e0) = exps.next() else { return Ok(()) };

        let Exp::Other(u0) = e0 else {
            let b0 = e0.as_bool().unwrap();
            let mut bools = exps.zip(1..).map(|(exp, i)| {
                exp.as_bool().ok_or((
                    SortMismatch {
                        actual: exp.sort(),
                        expected: BOOL_SORT,
                    },
                    i,
                ))
            });
            let Some(b1) = bools.next() else {
                return Ok(());
            };
            let b1 = b1?;
            if let Some(b2) = bools.next() {
                b2?;
                bools.try_for_each(|x| x.map(|_| ()))?;
                acts.raise_conflict(&[], false);
            } else {
                assert_distinct(b0, b1, acts);
            }
            return Ok(());
        };

        let distinct_sym = acts.intern_mut().symbols.gen_sym("distinct");
        self.distinct_gensym += 1;
        for (idx, exp) in iter::once(e0).chain(exps).enumerate() {
            if exp.sort() != u0.sort {
                return Err((
                    SortMismatch {
                        actual: exp.sort(),
                        expected: u0.sort,
                    },
                    idx,
                ));
            }
            let id = self.id_for_exp(exp, acts);
            let mut added = false;
            self.egraph
                .add(distinct_sym.into(), Children::from_slice(&[id]), |_| {
                    added = true;
                    EClass::Singleton
                });
            if !added {
                acts.raise_conflict(&[], false);
                return Ok(());
            }
        }
        Ok(())
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
                    if t.sort() != target.sort() {
                        return Err(SortMismatch {
                            actual: t.sort(),
                            expected: target.sort(),
                        });
                    }
                    let tid = self.id_for_exp(t, acts);
                    let eid = self.id_for_exp(e, acts);
                    self.raw_ite_eq(ilit, tid, eid, target, acts);
                    Ok(())
                }
            }
        }
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
