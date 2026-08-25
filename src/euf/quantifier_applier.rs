use crate::AddSexpError::SortMismatch;
use crate::collapse::BaseMarker;
use crate::full_theory::{Instruction, Logic, QuantContext, QuantExp, Trigger};
use crate::intern::{BOOL_SORT, DisplayInterned, InternInfo, Symbol};
use crate::outer_solver::StartExpCtx;
use crate::theory::Incremental;
use crate::util::{Either, HashMap};
use crate::{AddSexpError, BoolExp, ExpLike, HasSort, OuterSolver, SubExp, SuperExp, full_theory};
use alloc::vec::Vec;
use core::fmt::Formatter;
use core::num::NonZeroU32;
use perfect_derive::perfect_derive;
use smallvec::SmallVec;
use std::mem;

#[derive(Copy, Clone)]
struct CompactInstruction(u32);
const U31_MAX: u32 = i32::MAX as u32;

impl CompactInstruction {
    fn expand(self) -> Instruction<u32> {
        if self.0 > U31_MAX {
            Instruction::Var(self.0 & U31_MAX)
        } else if self.0 == 0 {
            Instruction::END
        } else {
            Instruction::Start(Symbol(NonZeroU32::new(self.0).unwrap()))
        }
    }

    fn end() -> Self {
        CompactInstruction(0)
    }

    fn start(s: Symbol) -> Self {
        CompactInstruction(s.0.get())
    }

    fn var(n: u32) -> Self {
        CompactInstruction(n | (U31_MAX + 1))
    }
}

#[test]
fn test() {
    use crate::intern::AND_SYM;
    use core::assert_matches;
    assert_matches!(CompactInstruction::var(5).expand(), Instruction::Var(5));
    assert_matches!(
        CompactInstruction::start(AND_SYM).expand(),
        Instruction::Start(AND_SYM)
    );
    assert_matches!(CompactInstruction::end().expand(), Instruction::END);
}

///
/// `QuantifierApplier.vm[vm_start..vm_end]` is the `vm` for this quantifier, and
/// `QuantifierApplier.vars[captures_start..captures_end]` are expressions captured by the quantifier
///
/// The `vm` looks similar to the source s-expression but use
///
#[derive(Copy, Clone)]
struct QuantifierBody {
    vm_start: u32,
    vm_end: u32,
    captures_start: u32,
    captures_end: u32,
}

#[derive(Copy, Clone)]
struct Pending {
    q: QuantifierBody,
    matched_start: u32,
}

#[perfect_derive(Default, Clone)]
pub struct QuantifierApplier<Exp> {
    vm: Vec<CompactInstruction>,
    var_buf: Vec<Exp>,
    vars: Vec<Exp>,
    simple_quantifiers: HashMap<Trigger, SmallVec<[QuantifierBody; 1]>>,
    quant_log: Vec<Trigger>,
    pending_instantiations: Vec<Pending>,
}

impl<Exp: ExpLike> full_theory::QuantifierApplier<Exp> for QuantifierApplier<Exp> {
    fn run<L: Logic<Exp = Exp, Q = Self>>(
        outer: &mut OuterSolver<L>,
    ) -> Result<(), (Option<Symbol>, AddSexpError)> {
        let this = outer.quantifier_applier();
        let vm = mem::take(&mut this.vm);
        let mut var_buf = mem::take(&mut this.var_buf);
        let res = Self::run_inner(outer, &vm, &mut var_buf);
        let this = outer.quantifier_applier();
        this.vm = vm;
        this.var_buf = var_buf;
        this.pending_instantiations.clear();
        res
    }

    fn clear_pending(&mut self) {
        self.pending_instantiations.clear();
    }

    fn enabled(&self) -> bool {
        true
    }

    fn create_context(&self, qvars: u32) -> QuantContext {
        QuantContext {
            qvars,
            captures: self.vars.len() as u32,
            vm: self.vm.len() as u32,
        }
    }

    fn add_instruction(&mut self, ctx: &QuantContext, instruction: Instruction<QuantExp<Exp>>) {
        let instruction = match instruction {
            Instruction::End => CompactInstruction::end(),
            Instruction::Start(s) => CompactInstruction::start(s),
            Instruction::Var(QuantExp::QuantVar(v)) => {
                debug_assert!(
                    v < ctx.qvars,
                    "Trying to access the {v}th quantified variable when only {} exist",
                    ctx.qvars
                );
                CompactInstruction::var(v)
            }
            Instruction::Var(QuantExp::Exp(e)) => {
                let captures = &self.vars[ctx.captures as usize..];
                if let Some(i) = captures.iter().position(|&e1| e1 == e) {
                    CompactInstruction::var(i as u32 + ctx.qvars)
                } else {
                    let res =
                        CompactInstruction::var(self.vars.len() as u32 - ctx.captures + ctx.qvars);
                    self.vars.push(e);
                    res
                }
            }
            Instruction::Var(QuantExp::LetVar(v)) => CompactInstruction::var(U31_MAX - v),
        };
        self.vm.push(instruction)
    }

    fn bind_instructions(&mut self, ctx: &QuantContext, triggers: impl Iterator<Item = Trigger>) {
        // To save space the last end paren is skipped
        let last = self.vm.pop();
        debug_assert_eq!(last.map(CompactInstruction::expand), Some(Instruction::END));
        let non_let_vars = ctx.qvars + self.vars.len() as u32 - ctx.captures;
        for x in &mut self.vm[ctx.vm as usize..] {
            if let Instruction::Var(v) = x.expand()
                && v > non_let_vars
            {
                *x = CompactInstruction::var(U31_MAX - v + non_let_vars)
            }
        }
        let body = QuantifierBody {
            captures_start: ctx.captures,
            captures_end: self.vars.len() as u32,
            vm_start: ctx.vm,
            vm_end: self.vm.len() as u32,
        };
        debug_assert!(body.vm_end > body.vm_start);
        for trigger in triggers {
            self.quant_log.push(trigger);
            self.simple_quantifiers
                .entry(trigger)
                .or_insert(SmallVec::new())
                .push(body);
        }
    }

    fn debug_cxt(
        &self,
        ctx: &QuantContext,
        intern: &InternInfo,
        f: &mut Formatter,
    ) -> core::fmt::Result {
        let vm = &self.vm[ctx.vm as usize..];
        let captures = &self.vars[ctx.captures as usize..];
        let cap_max = ctx.qvars + captures.len() as u32;
        for instruction in vm {
            match instruction.expand() {
                Instruction::Start(s) => write!(f, " ({}", s.with_intern(intern))?,
                Instruction::END => write!(f, ")")?,
                Instruction::Var(v) if v < ctx.qvars => write!(f, " q!{v}")?,
                Instruction::Var(v) if v < cap_max => write!(
                    f,
                    " {}",
                    captures[(v - ctx.qvars) as usize].with_intern(intern)
                )?,
                Instruction::Var(v) => write!(f, " l!{}", U31_MAX - v)?,
            }
        }
        Ok(())
    }
}

pub(super) trait QuantifierChecker<Exp, M>: Incremental {
    fn check_call(&mut self, f: Symbol, args: impl Iterator<Item = Exp> + Clone, res: Exp);
    fn check_new_exp(&mut self, e: Exp);
}

impl<Exp> QuantifierChecker<Exp, BaseMarker> for () {
    fn check_call(&mut self, _: Symbol, _: impl Iterator<Item = Exp>, _: Exp) {}

    fn check_new_exp(&mut self, _: Exp) {}
}

impl<M, Exp: ExpLike, Super: SuperExp<Exp, M>> QuantifierChecker<Exp, M>
    for QuantifierApplier<Super>
{
    fn check_call(&mut self, f: Symbol, args: impl Iterator<Item = Exp> + Clone, _: Exp) {
        if let Some(qs) = self.simple_quantifiers.get(&Either::Left(f)) {
            for &q in qs {
                let matched_start = self.vars.len() as u32;
                self.vars.extend(args.clone().map(SubExp::upcast));
                self.pending_instantiations
                    .push(Pending { q, matched_start })
            }
        }
    }

    fn check_new_exp(&mut self, e: Exp) {
        if let Some(qs) = self.simple_quantifiers.get(&Either::Right(e.sort())) {
            for &q in qs {
                let matched_start = self.vars.len() as u32;
                self.vars.push(e.upcast());
                self.pending_instantiations
                    .push(Pending { q, matched_start })
            }
        }
    }
}

impl<Exp: Copy> QuantifierApplier<Exp> {
    fn run_inner<L: Logic<Exp = Exp, Q = Self>>(
        outer: &mut OuterSolver<L>,
        vm: &[CompactInstruction],
        var_buf: &mut Vec<Exp>,
    ) -> Result<(), (Option<Symbol>, AddSexpError)> {
        while let Some(pending) = outer.quantifier_applier().pending_instantiations.pop() {
            let vars = &mut outer.quantifier_applier().vars;
            var_buf.clear();
            var_buf.extend(&vars[pending.matched_start as usize..]);
            var_buf
                .extend(&vars[pending.q.captures_start as usize..pending.q.captures_end as usize]);
            vars.truncate(pending.matched_start as usize);
            for instruction in &vm[pending.q.vm_start as usize..pending.q.vm_end as usize] {
                let exp = match instruction.expand() {
                    Instruction::Start(s) => {
                        outer.start_exp(s, None, StartExpCtx::ASSERT_OR_OPT);
                        continue;
                    }
                    Instruction::END => {
                        if let Some(x) = outer.end_exp_take_q().map_err(|(s, e)| (Some(s), e))? {
                            x
                        } else {
                            // we ended a let binding block don't add anything as an arg for the outer function
                            continue;
                        }
                    }
                    Instruction::Var(v) => var_buf[v as usize],
                };
                if outer.in_q_let() {
                    // if this is a child if a let block add it to vars so it can be referenced later
                    var_buf.push(exp)
                } else {
                    outer.inject_exp(exp);
                }
            }
            // Trailing end paren is omitted from vm
            let last: L::Exp = outer.end_exp_take().map_err(|(s, e)| (Some(s), e))?;
            fn l_downcast<L: Logic>(
                exp: L::Exp,
            ) -> Result<BoolExp, (Option<Symbol>, AddSexpError)> {
                exp.downcast().ok_or((
                    None,
                    SortMismatch {
                        actual: exp.sort(),
                        expected: BOOL_SORT,
                        arg_n: 0,
                    },
                ))
            }
            let last = l_downcast::<L>(last)?;
            outer.solver_mut().assert(last);
        }
        Ok(())
    }
}

#[derive(Copy, Clone)]
pub struct PushInfo {
    vm: u32,
    vars: u32,
    quant_log: u32,
}
impl<Exp> Incremental for QuantifierApplier<Exp> {
    type LevelMarker = PushInfo;

    fn create_level(&self) -> Self::LevelMarker {
        debug_assert!(self.pending_instantiations.is_empty());
        PushInfo {
            vm: self.vm.len() as u32,
            vars: self.vars.len() as u32,
            quant_log: self.quant_log.len() as u32,
        }
    }

    fn pop_to_level(&mut self, marker: Self::LevelMarker, _: bool) {
        self.vars.truncate(marker.vars as usize);
        self.vm.truncate(marker.vm as usize);
        for x in self.quant_log.drain(marker.quant_log as usize..).rev() {
            self.simple_quantifiers.get_mut(&x).unwrap().pop();
        }
        self.pending_instantiations.clear();
    }

    fn clear(&mut self) {
        self.vars.clear();
        self.vm.clear();
        self.quant_log.clear();
        self.simple_quantifiers.clear();
        self.pending_instantiations.clear();
    }
}
