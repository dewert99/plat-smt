use crate::index::Idx;
use crate::slice_vec::SliceVec;
use crate::util::DefaultHashBuilder;
use batsat::intmap::AsIndex;
use hashbrown::hash_table::Entry;
use hashbrown::HashTable;
use no_std_compat::prelude::v1::*;
use std::fmt::{Display, Formatter};
use std::hash::BuildHasher;

pub struct SymbolK;
pub type Symbol = Idx<SymbolK>;
pub struct SortK;

pub type Sort = Idx<SortK>;

const BASE_SYMBOLS: &'static [&'static str] = &[
    "|Default|",
    "Bool",
    "true",
    "false",
    "and",
    "or",
    "not",
    "=>",
    "xor",
    "ite",
    "if",
    "=",
    "distinct",
];

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
            Symbol::new(x as u32)
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

const BASE_SORTS: &'static [(Symbol, &'static [Sort])] = &[(BOOL_SYM, &[])];

const fn sort_slice_eq(s0: &[Sort], s1: &[Sort]) -> bool {
    match (s0, s1) {
        ([], []) => true,
        ([x0, rest0 @ ..], [x1, rest1 @ ..]) if x0.idx() == x1.idx() => sort_slice_eq(rest0, rest1),
        _ => false,
    }
}
const fn base_sort(name: Symbol, children: &[Sort]) -> Sort {
    const fn h(name: Symbol, children: &[Sort], x: usize) -> Sort {
        let (b_name, b_children) = BASE_SORTS[x];
        if b_name.idx() == name.idx() && sort_slice_eq(b_children, children) {
            Sort::new(x as u32)
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
                let res = self.symbol_indices.len() - 1;
                if res > (u32::MAX as usize >> 2) {
                    panic!("Too many symbols");
                }
                let res = Symbol::from_index(res);
                vac.insert((old_len, self.symbol_data.len(), res));
                self.symbol_indices.push(self.symbol_data.len());
                res
            }
        }
    }

    pub fn gen_sym(&mut self, name: &(impl Display + ?Sized)) -> Symbol {
        use std::fmt::Write;
        let res = self.symbol_indices.len() - 1;
        if res > u32::MAX as usize >> 2 {
            panic!("Too many symbols");
        }
        if cfg!(debug_assertions) {
            // this is only useful for logging
            write!(&mut self.symbol_data, "{name}|{res}").unwrap();
        }
        self.symbol_indices.push(self.symbol_data.len());
        Symbol::from_index(res)
    }

    pub fn resolve(&self, s: Symbol) -> &str {
        let idx = s.as_index();
        &self.symbol_data[self.symbol_indices[idx]..self.symbol_indices[idx + 1]]
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
            debug_assert_eq!(s, Symbol::from_index(i));
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
    assert!(symbols.resolve(g1).starts_with("gen_sym"));
    assert!(symbols.resolve(g2).starts_with("gen_sym"));
    assert_eq!(symbols.resolve(TRUE_SYM), "true")
}

pub struct SortInfo {
    data: SliceVec<Sort, Symbol, Sort>,
    map: HashTable<(Symbol, u32, u32, Sort)>,
    hasher: DefaultHashBuilder,
}

impl SortInfo {
    pub fn intern(&mut self, name: Symbol, args: &[Sort]) -> Sort {
        let hash = self.hasher.hash_one((name, args));
        match self.map.entry(
            hash,
            |x| {
                (|&(sym, start, end, _)| (sym, self.data.range_to_slice(start, end)))(x)
                    == (name, args)
            },
            |x| {
                self.hasher.hash_one((|&(sym, start, end, _)| {
                    (sym, self.data.range_to_slice(start, end))
                })(x))
            },
        ) {
            Entry::Occupied(occ) => occ.get().3,
            Entry::Vacant(vac) => {
                let old_len = self.data.slice_data_len();
                let res = self.data.push(name, args);
                vac.insert((name, old_len, self.data.slice_data_len(), res));
                res
            }
        }
    }

    pub fn resolve(&self, s: Sort) -> (Symbol, &[Sort]) {
        let (name, children) = self.data.lookup(s);
        (*name, children)
    }
}

impl Default for SortInfo {
    fn default() -> Self {
        let mut res = SortInfo {
            data: Default::default(),
            map: Default::default(),
            hasher: Default::default(),
        };

        for (i, &(name, args)) in BASE_SORTS.iter().enumerate() {
            let s = res.intern(name, args);
            debug_assert_eq!(s, Sort::from_index(i));
        }
        res
    }
}

#[test]
fn test_sorts() {
    let mut sorts = SortInfo::default();
    let sort = sorts.intern(EQ_SYM, &[BOOL_SORT, BOOL_SORT]);
    let (sym, args) = sorts.resolve(sort);
    assert_eq!(sym, EQ_SYM);
    assert_eq!(args, &[BOOL_SORT, BOOL_SORT]);
    let (b_sym, b_args) = sorts.resolve(BOOL_SORT);
    assert_eq!(b_sym, BOOL_SYM);
    assert_eq!(b_args, &[]);
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

impl DisplayInterned for Symbol {
    fn fmt(&self, i: &InternInfo, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str(i.symbols.resolve(*self))
    }
}

impl DisplayInterned for Sort {
    fn fmt(&self, i: &InternInfo, f: &mut Formatter<'_>) -> std::fmt::Result {
        let (name, params) = i.sorts.resolve(*self);
        if params.len() == 0 {
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
