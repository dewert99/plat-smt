use crate::collapse::{Collapse, CollapseOut, ExprContext};
use crate::exp::Fresh;
use crate::intern::{Symbol, AND_SYM, BOOL_SORT, IMP_SYM, NOT_SYM, OR_SYM, XOR_SYM};
use crate::junction::Junction;
use crate::parser_fragment::{exact_args, index_iter, mandatory_args, ParserFragment, PfResult};
use crate::solver::{ReuseMem, SolverCollapse};
use crate::theory::{Incremental, TheoryArg, TheoryWrapper};
use crate::util::extend_result;
use crate::{AddSexpError, BLit, BoolExp, Disjunction, ExpLike, SubExp, SuperExp};
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

    /// Optimizes `lits` by removing duplicates
    /// Returns `true` if lits are absorbing (eg `(and false)` `(or true)`)
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

    fn bind_junction(
        &mut self,
        lits: &mut Vec<BLit>,
        is_and: bool,
        ctx: ExprContext<BoolExp>,
        target: BLit,
    ) {
        for lit in &mut *lits {
            if ctx != ExprContext::Approx(is_and) {
                self.sat
                    .add_clause_unchecked([*lit ^ !is_and, target ^ is_and].iter().copied());
            }
            *lit ^= is_and;
        }
        if ctx != ExprContext::Approx(!is_and) {
            lits.push(target ^ !is_and);
            self.sat.add_clause_unchecked(lits.iter().copied());
        }
    }

    pub fn collapse_const(&mut self, c: bool, ctx: ExprContext<BoolExp>) -> BoolExp {
        if let ExprContext::AssertEq(b) = ctx {
            self.assert(b ^ !c);
            b
        } else {
            BoolExp::from_bool(c)
        }
    }

    #[inline]
    fn andor_reuse(
        &mut self,
        lits: &mut Vec<BLit>,
        is_and: bool,
        absorbing: bool,
        ctx: ExprContext<BoolExp>,
    ) -> BoolExp {
        if absorbing || self.optimize_junction(lits, is_and) {
            return self.collapse_const(!is_and, ctx);
        }
        if lits.is_empty() {
            return self.collapse_const(is_and, ctx);
        }

        if let [lit] = &**lits {
            return BoolExp::unknown(*lit);
        }

        if let ExprContext::AssertEq(b) = ctx {
            self.assert_junction_eq_inner(lits, is_and, b);
            return b;
        }

        let fresh = self.new_var_default();
        let res = Lit::new(fresh, true);
        self.bind_junction(lits, is_and, ctx, res);
        BoolExp::unknown(res)
    }

    fn assert_junction_eq_inner(&mut self, lits: &mut Vec<BLit>, is_and: bool, target: BoolExp) {
        match self.canonize(target).to_lit() {
            Ok(target) => {
                let mut approx = ExprContext::Exact;
                if let Ok(idx) = lits.binary_search_by(|lit| lit.var().cmp(&target.var())) {
                    let found = lits[idx];
                    lits.remove(idx);
                    if found == target {
                        approx = ExprContext::Approx(!is_and);
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

    pub fn collapse_bool<const IS_AND: bool>(
        &mut self,
        mut j: Junction<IS_AND>,
        ctx: ExprContext<BoolExp>,
    ) -> BoolExp {
        debug_assert!(self.is_ok());
        // if !self.is_ok() {
        //     return BoolExp::TRUE;
        // }
        debug!("{j:?} (ctx: {ctx:?}) was collapsed to ...");
        let res = self.andor_reuse(&mut j.lits, IS_AND, j.absorbing, ctx);
        self.incr.junction_buf = j.lits;
        debug!("... {res}");
        res
    }

    pub fn add_clause(&mut self, i: impl IntoIterator<Item = BoolExp>) {
        let mut j: Disjunction = self.new_junction();
        j.extend(i);
        if j.absorbing || self.optimize_junction(&mut j.lits, false) {
            // assert true
            return;
        }
        self.add_clause_unchecked(j.lits.iter().copied());
        self.incr.junction_buf = j.lits;
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

    pub fn xor(&mut self, b1: BoolExp, b2: BoolExp, ctx: ExprContext<BoolExp>) -> BoolExp {
        let b1 = self.canonize(b1);
        let b2 = self.canonize(b2);
        if let ExprContext::AssertEq(target) = ctx {
            self.assert_xor_eq(b1, b2, target);
            return target;
        }
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
                if ctx != ExprContext::Approx(true) {
                    self.sat
                        .add_clause_unchecked([l1, l2, !fresh].iter().copied());
                    self.sat
                        .add_clause_unchecked([!l1, !l2, !fresh].iter().copied());
                }
                if ctx != ExprContext::Approx(false) {
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

    fn assert_xor_eq(&mut self, b1: BoolExp, b2: BoolExp, target: BoolExp) {
        let mut arr = [b1, b2, self.canonize(target)];
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

pub struct TseitenMarker;

impl<const IS_AND: bool> CollapseOut for Junction<IS_AND> {
    type Out = BoolExp;
}

impl<'a, T, M, const IS_AND: bool> Collapse<Junction<IS_AND>, TheoryArg<'a, M>, TseitenMarker>
    for T
{
    fn collapse(
        &mut self,
        j: Junction<IS_AND>,
        acts: &mut TheoryArg<'a, M>,
        ctx: ExprContext<BoolExp>,
    ) -> BoolExp {
        acts.collapse_bool(j, ctx)
    }

    fn placeholder(&self, _: &Junction<IS_AND>) -> BoolExp {
        BoolExp::TRUE
    }
}

pub struct Xor(pub BoolExp, pub BoolExp);

impl CollapseOut for Xor {
    type Out = BoolExp;
}

impl<'a, T, M> Collapse<Xor, TheoryArg<'a, M>, TseitenMarker> for T {
    fn collapse(
        &mut self,
        Xor(b1, b2): Xor,
        acts: &mut TheoryArg<'a, M>,
        ctx: ExprContext<BoolExp>,
    ) -> BoolExp {
        acts.xor(b1, b2, ctx)
    }

    fn placeholder(&self, _: &Xor) -> BoolExp {
        BoolExp::TRUE
    }
}

impl CollapseOut for BoolExp {
    type Out = BoolExp;
}

impl<'a, T, M> Collapse<BoolExp, TheoryArg<'a, M>, TseitenMarker> for T {
    fn collapse(
        &mut self,
        b: BoolExp,
        acts: &mut TheoryArg<'a, M>,
        _: ExprContext<BoolExp>,
    ) -> BoolExp {
        acts.canonize(b)
    }

    fn placeholder(&self, b: &BoolExp) -> BoolExp {
        *b
    }
}

impl<'a, T, M> Collapse<Fresh<BoolExp>, TheoryArg<'a, M>, TseitenMarker> for T {
    fn collapse(
        &mut self,
        f: Fresh<BoolExp>,
        acts: &mut TheoryArg<'a, M>,
        _: ExprContext<BoolExp>,
    ) -> BoolExp {
        assert_eq!(f.sort, BOOL_SORT);
        BoolExp::unknown(Lit::new(acts.new_var_default(), true))
    }

    fn placeholder(&self, f: &Fresh<BoolExp>) -> BoolExp {
        assert_eq!(f.sort, BOOL_SORT);
        BoolExp::TRUE
    }
}

#[derive(Default)]
pub struct JunctionPf<const B: bool>;

impl<
        'a,
        M,
        Exp: ExpLike + SuperExp<BoolExp, M>,
        S: SolverCollapse<Junction<IS_AND>, TseitenMarker> + ReuseMem<Junction<IS_AND>>,
        const IS_AND: bool,
    > ParserFragment<Exp, S, M> for JunctionPf<IS_AND>
{
    fn supports(&self, s: Symbol) -> bool {
        s == (if IS_AND { AND_SYM } else { OR_SYM })
    }
    fn handle_non_terminal(
        &self,
        _: Symbol,
        children: &mut [Exp],
        solver: &mut S,
        ctx: ExprContext<Exp>,
    ) -> Result<Exp, AddSexpError> {
        let mut j: Junction<IS_AND> = solver.reuse_mem();
        extend_result(&mut j, index_iter(children).map(|x| x.downcast()))?;
        Ok(solver.collapse_in_ctx(j, ctx.downcast()).upcast())
    }

    fn sub_ctx(&self, _: Symbol, _: &[Exp], ctx: ExprContext<Exp>) -> ExprContext<Exp> {
        andor_sub_ctx(ctx, IS_AND)
    }
}

pub fn andor_sub_ctx<Exp: SuperExp<BoolExp, M> + Eq, M>(
    ctx: ExprContext<Exp>,
    is_and: bool,
) -> ExprContext<Exp> {
    match ctx {
        ExprContext::AssertEq(x) if x == BoolExp::from_bool(is_and).upcast() => {
            ExprContext::AssertEq(BoolExp::from_bool(is_and).upcast()).into()
        }
        ExprContext::Approx(x) => ExprContext::Approx(x).into(),
        _ => ExprContext::Exact.into(),
    }
}

pub type AndPf = JunctionPf<true>;
pub type OrPf = JunctionPf<false>;

#[derive(Default)]
pub struct XorPf;

impl<'a, M, Exp: ExpLike + SuperExp<BoolExp, M>, S: SolverCollapse<Xor, TseitenMarker>>
    ParserFragment<Exp, S, M> for XorPf
{
    fn supports(&self, s: Symbol) -> bool {
        s == XOR_SYM
    }
    fn handle_non_terminal(
        &self,
        _: Symbol,
        children: &mut [Exp],
        solver: &mut S,
        ctx: ExprContext<Exp>,
    ) -> Result<Exp, AddSexpError> {
        let child_len = children.len();
        let mut children = index_iter(children);
        let first_res = if child_len == 0 {
            BoolExp::FALSE
        } else {
            let mut first_children = children.by_ref().take(child_len - 1);
            first_children.try_fold(BoolExp::FALSE, |b1, b2| {
                Ok::<_, AddSexpError>(
                    solver.collapse_in_ctx(Xor(b1, b2.downcast()?), ExprContext::Exact),
                )
            })?
        };
        let last_child = if let Some(last_child) = children.next() {
            last_child.downcast()?
        } else {
            BoolExp::FALSE
        };
        Ok(solver
            .collapse_in_ctx(Xor(first_res, last_child), ctx.downcast())
            .upcast())
    }
}

#[derive(Default)]
pub struct ImpPf;

impl<
        'a,
        M,
        Exp: ExpLike + SuperExp<BoolExp, M>,
        S: SolverCollapse<Disjunction, TseitenMarker> + ReuseMem<Disjunction>,
    > ParserFragment<Exp, S, M> for ImpPf
{
    fn supports(&self, s: Symbol) -> bool {
        s == IMP_SYM
    }
    fn handle_non_terminal(
        &self,
        _: Symbol,
        children: &mut [Exp],
        solver: &mut S,
        ctx: ExprContext<Exp>,
    ) -> Result<Exp, AddSexpError> {
        let mut children = index_iter(children);
        let mut d: Disjunction = solver.reuse_mem();
        let [arg] = mandatory_args(&mut children)?;
        let mut last: BoolExp = arg.downcast()?;
        let other =
            children.map(|x| Ok::<_, AddSexpError>(!mem::replace(&mut last, x.downcast()?)));
        extend_result(&mut d, other)?;
        d.push(last);
        Ok(solver.collapse_in_ctx(d, ctx.downcast()).upcast())
    }
}

#[derive(Default)]
pub struct NotPf;

impl<'a, M, Exp: ExpLike + SuperExp<BoolExp, M>, S> ParserFragment<Exp, S, M> for NotPf {
    fn supports(&self, s: Symbol) -> bool {
        s == NOT_SYM
    }
    fn handle_non_terminal(
        &self,
        _: Symbol,
        children: &mut [Exp],
        _: &mut S,
        _: ExprContext<Exp>,
    ) -> Result<Exp, AddSexpError> {
        let [child] = exact_args(&mut index_iter(children))?;
        let bool_child: BoolExp = child.downcast()?;
        Ok((!bool_child).upcast())
    }
    fn sub_ctx(&self, _: Symbol, _: &[Exp], ctx: ExprContext<Exp>) -> ExprContext<Exp> {
        ctx.negate()
    }
}

pub type BoolOpPf = (NotPf, (AndPf, (OrPf, (ImpPf, XorPf))));
