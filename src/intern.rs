use crate::util::DefaultHashBuilder;
use core::num::NonZeroU32;
use hashbrown::hash_table::Entry;
use hashbrown::HashTable;
use no_std_compat::prelude::v1::*;
use std::fmt::{Debug, Display, Formatter};
use std::hash::BuildHasher;

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug)]
pub struct Symbol(pub(crate) NonZeroU32);

#[derive(Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Debug)]
pub struct Sort(NonZeroU32);

const BASE_SYMBOLS: &[&str] = &[
    "Bool", "true", "false", "and", "or", "not", "=>", "xor", "ite", "if", "=", "distinct", "let",
    "let*", "!",
];

pub fn resolve_or_fail(s: Symbol) -> &'static str {
    BASE_SYMBOLS[s.0.get() as usize - 1]
}

const fn u8_slice_eq(s0: &[u8], s1: &[u8]) -> bool {
    match (s0, s1) {
        ([], []) => true,
        ([x0, rest0 @ ..], [x1, rest1 @ ..]) if *x0 == *x1 => u8_slice_eq(rest0, rest1),
        _ => false,
    }
}

const fn base_symbol(s: &str) -> Symbol {
    const fn h(s: &str, x: usize) -> Symbol {
        if u8_slice_eq(BASE_SYMBOLS[x].as_bytes(), s.as_bytes()) {
            let Some(x) = NonZeroU32::new(x as u32 + 1) else {
                panic!();
            };
            Symbol(x)
        } else {
            h(s, x + 1)
        }
    }
    h(s, 0)
}

pub const BOOL_SYM: Symbol = base_symbol("Bool");
pub const TRUE_SYM: Symbol = base_symbol("true");
pub const FALSE_SYM: Symbol = base_symbol("false");
pub const AND_SYM: Symbol = base_symbol("and");
pub const OR_SYM: Symbol = base_symbol("or");
pub const NOT_SYM: Symbol = base_symbol("not");
pub const IMP_SYM: Symbol = base_symbol("=>");
pub const XOR_SYM: Symbol = base_symbol("xor");
pub const IF_SYM: Symbol = base_symbol("if");
pub const ITE_SYM: Symbol = base_symbol("ite");
pub const EQ_SYM: Symbol = base_symbol("=");
pub const DISTINCT_SYM: Symbol = base_symbol("distinct");
pub const LET_SYM: Symbol = base_symbol("let");

pub const LET_STAR_SYM: Symbol = base_symbol("let*");

pub const ANNOT_SYM: Symbol = base_symbol("!");

const BASE_SORTS: &[(Symbol, &[Sort])] = &[(BOOL_SYM, &[])];

pub fn resolve_sort_or_fail(s: Sort) -> impl Display {
    resolve_or_fail(BASE_SORTS[s.0.get() as usize - 1].0)
}

const fn sort_slice_eq(s0: &[Sort], s1: &[Sort]) -> bool {
    match (s0, s1) {
        ([], []) => true,
        ([x0, rest0 @ ..], [x1, rest1 @ ..]) if x0.0.get() == x1.0.get() => {
            sort_slice_eq(rest0, rest1)
        }
        _ => false,
    }
}
const fn base_sort(name: Symbol, children: &[Sort]) -> Sort {
    const fn h(name: Symbol, children: &[Sort], x: usize) -> Sort {
        let (b_name, b_children) = BASE_SORTS[x];
        if b_name.0.get() == name.0.get() && sort_slice_eq(b_children, children) {
            let Some(x) = NonZeroU32::new(x as u32 + 1) else {
                panic!()
            };
            Sort(x)
        } else {
            h(name, children, x + 1)
        }
    }
    h(name, children, 0)
}

pub const BOOL_SORT: Sort = base_sort(BOOL_SYM, &[]);

pub struct SymbolInfo {
    symbol_data: String,
    symbol_indices: Vec<usize>,
    map: HashTable<(usize, usize, Symbol)>,
    hasher: DefaultHashBuilder,
}

impl SymbolInfo {
    pub fn intern(&mut self, s: &str) -> Symbol {
        let hash = self.hasher.hash_one(s.as_bytes());
        match self.map.entry(
            hash,
            |&(start, end, _)| &self.symbol_data.as_bytes()[start..end] == s.as_bytes(),
            |&(start, end, _)| {
                self.hasher
                    .hash_one(&self.symbol_data.as_bytes()[start..end])
            },
        ) {
            Entry::Occupied(occ) => occ.get().2,
            Entry::Vacant(vac) => {
                let old_len = self.symbol_data.len();
                self.symbol_data.push_str(s);
                let res = self.symbol_indices.len();
                if res > (u32::MAX as usize >> 2) {
                    panic!("Too many symbols");
                }
                let res = Symbol(NonZeroU32::new(res as u32).unwrap());
                vac.insert((old_len, self.symbol_data.len(), res));
                self.symbol_indices.push(self.symbol_data.len());
                res
            }
        }
    }

    pub fn gen_sym(&mut self, name: &(impl Display + ?Sized)) -> Symbol {
        use std::fmt::Write;
        let res = self.symbol_indices.len();
        if res > u32::MAX as usize >> 2 {
            panic!("Too many symbols");
        }
        let res = res as u32;
        if cfg!(debug_assertions) {
            // this is only useful for logging
            write!(&mut self.symbol_data, "{name}@@{res}").unwrap();
        }
        self.symbol_indices.push(self.symbol_data.len());
        Symbol(NonZeroU32::new(res).unwrap())
    }

    pub fn resolve(&self, s: Symbol) -> &str {
        let idx = s.0.get() as usize;
        &self.symbol_data[self.symbol_indices[idx - 1]..self.symbol_indices[idx]]
    }
}

impl Default for SymbolInfo {
    fn default() -> Self {
        let mut res = SymbolInfo {
            symbol_data: "".to_owned(),
            symbol_indices: vec![0],
            map: Default::default(),
            hasher: Default::default(),
        };
        for (i, &elt) in BASE_SYMBOLS.iter().enumerate() {
            let s = res.intern(elt);
            assert_eq!(s.0.get(), i as u32 + 1);
        }
        res
    }
}

#[cfg(debug_assertions)]
#[test]
fn test_symbols() {
    let mut symbols = SymbolInfo::default();
    let hello = symbols.intern("hello");
    let world = symbols.intern("world");
    let hello2 = symbols.intern("hello");
    assert_eq!(hello, hello2);
    assert_eq!(symbols.resolve(hello), "hello");
    assert_eq!(symbols.resolve(world), "world");
    let g1 = symbols.gen_sym("gen_sym");
    let g2 = symbols.gen_sym("gen_sym");
    assert_ne!(g1, g2);
    let x = symbols.resolve(g1);
    assert!(symbols.resolve(g1).starts_with("gen_sym"));
    assert!(symbols.resolve(g2).starts_with("gen_sym"));
    assert_eq!(symbols.resolve(TRUE_SYM), "true")
}

pub struct SortInfo {
    sort_args: Vec<Sort>,
    sorts: Vec<(Symbol, u32)>,
    map: HashTable<(Symbol, u32, u32, Sort)>,
    hasher: DefaultHashBuilder,
}

impl SortInfo {
    pub fn intern(&mut self, name: Symbol, args: &[Sort]) -> Sort {
        let hash = self.hasher.hash_one((name, args));
        match self.map.entry(
            hash,
            |&(sym, start, end, _)| {
                (sym, &self.sort_args[start as usize..end as usize]) == (name, args)
            },
            |&(sym, start, end, _)| {
                self.hasher
                    .hash_one((sym, &self.sort_args[start as usize..end as usize]))
            },
        ) {
            Entry::Occupied(occ) => occ.get().3,
            Entry::Vacant(vac) => {
                let old_len = self.sort_args.len();
                self.sort_args.extend_from_slice(args);
                let res = self.sorts.len();
                if res > u32::MAX as usize {
                    panic!("Too many symbols");
                }
                if self.sort_args.len() > u32::MAX as usize {
                    panic!("Too many sort args");
                }
                let res = Sort(NonZeroU32::new(res as u32).unwrap());
                vac.insert((name, old_len as u32, self.sort_args.len() as u32, res));
                self.sorts.push((name, self.sort_args.len() as u32));
                res
            }
        }
    }

    pub fn resolve(&self, s: Sort) -> (Symbol, &[Sort]) {
        let idx = s.0.get() as usize;
        let name = self.sorts[idx].0;
        let children = &self.sort_args[self.sorts[idx - 1].1 as usize..self.sorts[idx].1 as usize];
        (name, children)
    }
}

impl Default for SortInfo {
    fn default() -> Self {
        let mut res = SortInfo {
            sort_args: vec![],
            sorts: vec![(Symbol(NonZeroU32::new(1).unwrap()), 0)],
            map: Default::default(),
            hasher: Default::default(),
        };
        for (i, &(name, args)) in BASE_SORTS.iter().enumerate() {
            let s = res.intern(name, args);
            assert_eq!(s.0.get(), i as u32 + 1);
        }
        res
    }
}

#[derive(Default)]
pub struct InternInfo {
    pub sorts: SortInfo,
    pub symbols: SymbolInfo,
}

pub trait DisplayInterned {
    fn fmt(&self, i: &InternInfo, f: &mut Formatter<'_>) -> std::fmt::Result;

    fn with_intern(self, i: &InternInfo) -> WithIntern<Self>
    where
        Self: Sized,
    {
        WithIntern(self, i)
    }

    fn to_string(self, i: &InternInfo) -> String
    where
        Self: Sized,
    {
        format!("{}", self.with_intern(i))
    }
}

pub struct WithIntern<'a, X>(pub X, &'a InternInfo);

impl<'a, X: DisplayInterned> Display for WithIntern<'a, X> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(self.1, f)
    }
}

impl<'a, X: DisplayInterned> Debug for WithIntern<'a, X> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(self.1, f)
    }
}

impl DisplayInterned for Symbol {
    fn fmt(&self, i: &InternInfo, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str(i.symbols.resolve(*self))
    }
}

impl DisplayInterned for Sort {
    fn fmt(&self, i: &InternInfo, f: &mut Formatter<'_>) -> std::fmt::Result {
        let (name, params) = i.sorts.resolve(*self);
        if params.is_empty() {
            write!(f, "{}", name.with_intern(i))
        } else {
            write!(f, "({}", name.with_intern(i))?;
            for x in params {
                write!(f, " {}", x.with_intern(i))?;
            }
            write!(f, ")")
        }
    }
}

impl<D: Display> DisplayInterned for D {
    fn fmt(&self, _: &InternInfo, f: &mut Formatter<'_>) -> std::fmt::Result {
        Display::fmt(self, f)
    }
}
