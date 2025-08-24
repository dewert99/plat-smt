use crate::intern::{DisplayInterned, InternInfo, RecInfo, RecInfoArg, Symbol};
use crate::recorder::{ClauseKind, Recorder};
use crate::rexp::{NamespaceVar, Rexp};
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

#[derive(Default)]
pub struct DefinitionRecorder {
    defs: RecInfo<DefExp>,
    buf: Vec<DefExp>,
    aliases: HashMap<DefExp, Symbol>,
    var_defs: HashMap<NamespaceVar, DefExp>,
    uses: DefaultVec<Saturating<u8>, DefExp>,
}

impl DefinitionRecorder {
    fn intern_rexp(&mut self, r: &Rexp<'_>) {
        match r {
            Rexp::Nv(nv) => self.buf.push(*self.var_defs.get(nv).unwrap()),
            Rexp::Call(s, args) => {
                let buf_len = self.buf.len();
                args.iter().for_each(|r| self.intern_rexp(r));
                let res = self.defs.intern(*s, &self.buf[buf_len..]);
                self.buf.truncate(buf_len);
                self.buf.push(res);
            }
        }
    }

    pub fn intern_exp<E: ExpLike>(&mut self, exp: E) -> DefExp {
        exp.as_rexp(|rexp| self.intern_rexp(&rexp));
        self.buf.pop().unwrap()
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

    fn display_def<'a>(&'a self, def_exp: DefExp, interner: &'a InternInfo) -> DisplayDefExp<'a> {
        DisplayDefExp {
            def_exp,
            recorder: self,
            interner,
            uses: self.uses.get(def_exp),
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
        arg.for_each(|exp| exp.as_rexp(|rexp| self.intern_rexp(&rexp)));
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
