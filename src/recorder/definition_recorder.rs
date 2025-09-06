use crate::intern::{
    DisplayInterned, InternInfo, RecInfo, RecInfoArg, Symbol, FALSE_SYM, TRUE_SYM,
};
use crate::recorder::{ClauseKind, Recorder};
use crate::rexp::{AsRexp, NamespaceVar, Rexp};
use crate::util::{display_sexp, DisplayFn, HashMap};
use crate::{BoolExp, ExpLike};
use alloc::vec::Vec;
use core::cmp::max;
use core::convert::Infallible;
use core::fmt::{Display, Formatter};
use core::num::{NonZeroU32, Saturating};
use default_vec2::DefaultVec;
use platsat::Lit;

#[derive(Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Debug)]
pub struct DefExp(NonZeroU32);

impl RecInfoArg for DefExp {
    fn new(x: NonZeroU32) -> Self {
        DefExp(x)
    }

    fn inner(self) -> NonZeroU32 {
        self.0
    }
}

impl Into<usize> for DefExp {
    fn into(self) -> usize {
        self.0.get() as usize
    }
}

pub struct DefinitionRecorder {
    defs: RecInfo<DefExp>,
    buf: Vec<DefExp>,
    aliases: HashMap<DefExp, Symbol>,
    var_defs: HashMap<NamespaceVar, DefExp>,
    uses: DefaultVec<Saturating<u8>, DefExp>,
}

pub const FALSE_DEF_EXP: DefExp = DefExp(NonZeroU32::new(1).unwrap());
pub const TRUE_DEF_EXP: DefExp = DefExp(NonZeroU32::new(2).unwrap());

impl Default for DefinitionRecorder {
    fn default() -> Self {
        let mut res = DefinitionRecorder {
            defs: Default::default(),
            buf: Default::default(),
            aliases: Default::default(),
            var_defs: Default::default(),
            uses: Default::default(),
        };
        let f = res.defs.intern(FALSE_SYM, &[]);
        debug_assert_eq!(f, FALSE_DEF_EXP);
        let t = res.defs.intern(TRUE_SYM, &[]);
        debug_assert_eq!(t, TRUE_DEF_EXP);
        res
    }
}

impl DefinitionRecorder {
    fn intern_rexp_h(&mut self, r: &Rexp<'_>) {
        match r {
            Rexp::Nv(nv) => self.buf.push(*self.var_defs.get(nv).unwrap()),
            Rexp::Call(s, args) => {
                let buf_len = self.buf.len();
                args.iter().for_each(|r| self.intern_rexp_h(r));
                let res = self.defs.intern(*s, &self.buf[buf_len..]);
                self.buf.truncate(buf_len);
                self.buf.push(res);
            }
        }
    }

    pub fn intern_exp<E: AsRexp>(&mut self, exp: E) -> DefExp {
        exp.as_rexp(|rexp| self.intern_rexp_h(&rexp));
        self.buf.pop().unwrap()
    }

    pub fn intern_call(&mut self, name: Symbol, children: &[DefExp]) -> DefExp {
        self.defs.intern(name, children)
    }
    pub fn resolve(&self, def: DefExp) -> (Symbol, &[DefExp]) {
        self.defs.resolve(def)
    }

    fn finish_usages(&mut self, last: DefExp) {
        for i in (1..last.0.get() + 1).into_iter().rev() {
            let def = DefExp(NonZeroU32::new(i).unwrap());
            let uses = self.uses.get(def);
            if uses.0 == 0 {
                continue;
            }
            let def = DefExp(NonZeroU32::new(i).unwrap());
            let children = self.defs.resolve(def).1;
            let alias = self.aliases.contains_key(&def);
            if uses.0 > 1 && (children.len() == 0 || alias) {
                *self.uses.get_mut(def) = Saturating(1)
            }
            if !alias {
                for child in children {
                    *self.uses.get_mut(*child) += 1;
                }
            }
        }
    }

    /// Creates aliases for expressions and returns a struct that can be displayed to see the
    /// definitions
    #[must_use]
    pub fn dump_global_defs<'a>(&'a mut self, intern: &'a InternInfo) -> DisplayGlobalDefs<'a> {
        self.uses.clear();
        let mut max_def_exp = None;
        for &v in self.var_defs.values() {
            *self.uses.get_mut(v) = Saturating(2);
            if let Some(x) = max_def_exp {
                max_def_exp = Some(max(x, v));
            } else {
                max_def_exp = Some(v)
            }
        }
        if let Some(max_def_exp) = max_def_exp {
            self.finish_usages(max_def_exp)
        }
        DisplayGlobalDefs(self, max_def_exp, intern)
    }

    pub fn display_def<'a>(
        &'a self,
        def_exp: DefExp,
        interner: &'a InternInfo,
    ) -> DisplayDefExp<'a> {
        DisplayDefExp {
            def_exp,
            recorder: self,
            interner,
            uses: self.uses.get(def_exp),
        }
    }

    pub fn display_stand_alone_def<'a>(
        &'a mut self,
        def_exp: DefExp,
        interner: &'a InternInfo,
    ) -> DisplayStandAloneDefExp<'a> {
        self.uses.clear();
        *self.uses.get_mut(def_exp) = Saturating(2);
        self.finish_usages(def_exp);
        DisplayStandAloneDefExp {
            def_exp,
            recorder: self,
            interner,
        }
    }

    pub fn display_exp<'a, E: ExpLike>(
        &'a self,
        exp: E,
        interner: &'a InternInfo,
    ) -> impl Display + use<'a, E> {
        DisplayFn(move |f| {
            exp.as_rexp(|rexp| {
                Display::fmt(
                    &DisplayRexp {
                        rexp,
                        recorder: self,
                        interner,
                    },
                    f,
                )
            })
        })
    }

    pub(crate) fn display_clause<'a, I: Iterator<Item = Lit> + Clone>(
        &'a self,
        clause: I,
        interner: &'a InternInfo,
    ) -> impl Display + use<'a, I> {
        display_sexp(
            "or",
            clause.map(|l| self.display_exp(BoolExp::unknown(l), interner)),
        )
    }
}

impl Recorder for DefinitionRecorder {
    type Interpolant<'a> = Infallible;

    fn log_def<Exp: ExpLike, Exp2: ExpLike>(
        &mut self,
        val: Exp,
        f: Symbol,
        arg: impl Iterator<Item = Exp2> + Clone,
        _: &InternInfo,
    ) {
        arg.for_each(|exp| exp.as_rexp(|rexp| self.intern_rexp_h(&rexp)));
        let res = self.defs.intern(f, &self.buf);
        self.buf.clear();
        let nv = val.as_rexp(|rexp| rexp.unwrap_nv());
        self.var_defs.insert(nv, res);
    }

    fn log_def_exp<Exp: ExpLike, Exp2: ExpLike>(&mut self, val: Exp, def: Exp2, _: &InternInfo) {
        let res = self.intern_exp(def);
        let nv = val.as_rexp(|rexp| rexp.unwrap_nv());
        self.var_defs.insert(nv, res);
    }

    fn log_alias<Exp: ExpLike>(&mut self, alias: Symbol, exp: Exp, _: &InternInfo) {
        let res = self.intern_exp(exp);
        self.aliases.insert(res, alias);
    }

    fn log_clause(&mut self, _: &[Lit], _: ClauseKind) {}

    type BoolBufMarker = ();

    fn intern_bools(&mut self, _: impl Iterator<Item = BoolExp>) -> Self::BoolBufMarker {}
}

#[derive(Copy, Clone)]
pub struct DisplayDefExp<'a> {
    def_exp: DefExp,
    recorder: &'a DefinitionRecorder,
    interner: &'a InternInfo,
    uses: Saturating<u8>,
}

impl<'a> Display for DisplayDefExp<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        if let Some(v) = self.recorder.aliases.get(&self.def_exp) {
            DisplayInterned::fmt(v, self.interner, f)
        } else if self.uses.0 > 1 {
            write!(f, "@d{}", self.def_exp.0)
        } else {
            let (sym, children) = self.recorder.defs.resolve(self.def_exp);
            if children.len() == 0 {
                DisplayInterned::fmt(&sym, self.interner, f)
            } else {
                let disp = display_sexp(
                    sym.with_intern(&self.interner),
                    children
                        .iter()
                        .map(|&def_exp| self.recorder.display_def(def_exp, self.interner)),
                );
                Display::fmt(&disp, f)
            }
        }
    }
}

pub struct DisplayGlobalDefs<'a>(&'a DefinitionRecorder, Option<DefExp>, &'a InternInfo);

impl<'a> Display for DisplayGlobalDefs<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        let Some(x) = self.1 else { return Ok(()) };
        for i in 1..x.0.get() + 1 {
            let def_exp = DefExp(NonZeroU32::new(i).unwrap());
            let uses = self.0.uses.get(def_exp);
            if uses.0 > 1 {
                writeln!(
                    f,
                    "(define-const @d{} _ {})",
                    i,
                    DisplayDefExp {
                        def_exp,
                        recorder: self.0,
                        interner: self.2,
                        uses: Saturating(0)
                    }
                )?;
            }
        }
        Ok(())
    }
}

#[derive(Copy, Clone)]
pub struct DisplayRexp<'a> {
    rexp: Rexp<'a>,
    recorder: &'a DefinitionRecorder,
    interner: &'a InternInfo,
}

impl<'a> Display for DisplayRexp<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self.rexp {
            Rexp::Nv(nv) => {
                let def_exp = *self.recorder.var_defs.get(&nv).unwrap();
                let disp = self.recorder.display_def(def_exp, self.interner);
                Display::fmt(&disp, f)
            }
            Rexp::Call(sym, &[]) => DisplayInterned::fmt(&sym, self.interner, f),
            Rexp::Call(sym, children) => {
                let disp = display_sexp(
                    sym.with_intern(self.interner),
                    children.iter().map(|&rexp| DisplayRexp {
                        rexp,
                        recorder: &self.recorder,
                        interner: &self.interner,
                    }),
                );
                Display::fmt(&disp, f)
            }
        }
    }
}

#[derive(Copy, Clone)]
pub struct DisplayStandAloneDefExp<'a> {
    def_exp: DefExp,
    recorder: &'a DefinitionRecorder,
    interner: &'a InternInfo,
}

impl<'a> Display for DisplayStandAloneDefExp<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        let mut end_parens = 0;
        for i in 1..self.def_exp.0.get() {
            let def_exp = DefExp(NonZeroU32::new(i).unwrap());
            let uses = self.recorder.uses.get(def_exp);
            if uses.0 > 1 {
                writeln!(
                    f,
                    "(let @d{} {}",
                    i,
                    DisplayDefExp {
                        def_exp,
                        recorder: self.recorder,
                        interner: self.interner,
                        uses: Saturating(0)
                    }
                )?;
                end_parens += 1;
            }
        }
        let indent = if end_parens == 0 { "" } else { "  " };
        write!(
            f,
            "{indent}{}{:)<end_parens$}",
            DisplayDefExp {
                def_exp: self.def_exp,
                recorder: self.recorder,
                interner: self.interner,
                uses: Saturating(0)
            },
            ""
        )
    }
}
