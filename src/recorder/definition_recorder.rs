use crate::intern::{
    DisplayInterned, InternInfo, RecInfo, RecInfoArg, Symbol, FALSE_SYM, TRUE_SYM,
};
use crate::recorder::{ClauseKind, Recorder};
use crate::rexp::{AsRexp, NamespaceVar, Rexp};
use crate::theory::Incremental;
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

pub const FALSE_DEF_EXP: DefExp = DefExp(NonZeroU32::new(1).unwrap());
pub const TRUE_DEF_EXP: DefExp = DefExp(NonZeroU32::new(2).unwrap());

impl RecInfoArg for DefExp {
    fn new(x: NonZeroU32) -> Self {
        DefExp(x)
    }

    fn inner(self) -> NonZeroU32 {
        self.0
    }

    fn init_rec_info(init: &mut RecInfo<Self>) {
        let f = init.intern(FALSE_SYM, &[]);
        debug_assert_eq!(f, FALSE_DEF_EXP);
        let t = init.intern(TRUE_SYM, &[]);
        debug_assert_eq!(t, TRUE_DEF_EXP);
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
    alias_log: Vec<DefExp>,
    var_defs: HashMap<NamespaceVar, DefExp>,
    var_log: Vec<NamespaceVar>,
    uses: DefaultVec<Saturating<u8>, DefExp>,
}

#[derive(Copy, Clone)]
pub struct LevelMarker {
    def_maker: u32,
    alias_len: u32,
    var_len: u32,
}

impl DefinitionRecorder {
    fn intern_rexp_h(&mut self, r: &Rexp<'_>) {
        match r {
            Rexp::Nv(nv) => self.buf.push(
                *self
                    .var_defs
                    .get(nv)
                    .unwrap_or_else(|| panic!("Missing {nv}")),
            ),
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

    fn define_nv(&mut self, nv: NamespaceVar, def_exp: DefExp) {
        let old = self.var_defs.insert(nv, def_exp);
        debug_assert_eq!(old, None);
        self.var_log.push(nv);
    }
}

impl Incremental for DefinitionRecorder {
    type LevelMarker = LevelMarker;

    fn create_level(&self) -> Self::LevelMarker {
        LevelMarker {
            def_maker: self.defs.create_level(),
            alias_len: self.alias_log.len() as u32,
            var_len: self.var_log.len() as u32,
        }
    }

    fn pop_to_level(&mut self, marker: Self::LevelMarker, _: bool) {
        self.defs.pop_to_level(marker.def_maker);
        for alias in self.alias_log.drain(marker.alias_len as usize..) {
            self.aliases.remove(&alias);
        }
        for var in self.var_log.drain(marker.var_len as usize..) {
            self.var_defs.remove(&var);
        }
    }

    fn clear(&mut self) {
        self.defs.clear();
        self.alias_log.clear();
        self.aliases.clear();
        self.var_log.clear();
        self.var_defs.clear();
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
        arg.clone()
            .for_each(|exp| exp.as_rexp(|rexp| self.intern_rexp_h(&rexp)));
        let res = self.defs.intern(f, &self.buf);
        self.buf.clear();
        let nv = val.as_rexp(|rexp| rexp.unwrap_nv());
        self.define_nv(nv, res);
    }

    fn log_def_exp<Exp: ExpLike, Exp2: ExpLike>(&mut self, val: Exp, def: Exp2, _: &InternInfo) {
        let res = self.intern_exp(def);
        let nv = val.as_rexp(|rexp| rexp.unwrap_nv());
        self.define_nv(nv, res);
    }

    fn log_alias<Exp: ExpLike>(&mut self, alias: Symbol, exp: Exp, _: &InternInfo) {
        let res = self.intern_exp(exp);
        self.aliases.insert(res, alias);
        self.alias_log.push(res);
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
                    "(let (@d{} {})",
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
