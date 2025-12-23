use std::fmt::Debug;
use std::hash::Hash;

use string_interner::{DefaultSymbol, StringInterner, backend::DefaultBackend};

/// A byte-offset span into the original source.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }

    pub fn merge(self, other: Span) -> Span {
        Span {
            start: std::cmp::min(self.start, other.start),
            end: std::cmp::max(self.end, other.end),
        }
    }

    // Alias for compatibility with CEL code if needed, or we can refactor CEL to use merge
    pub fn combine(&self, other: &Span) -> Span {
        self.merge(*other)
    }
}

/// A syntax object: a value paired with its source span.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Syntax<T> {
    pub span: Span,
    pub value: T,
}

impl<T> Syntax<T> {
    #[inline]
    pub fn new(span: Span, value: T) -> Self {
        Self { span, value }
    }
}

/// A handle to a string (symbol or string literal).
/// Must be cheap to copy, compare, and hash.
///
/// Common implementations:
/// - `u64` or `u32` (for interned strings)
/// - `&'a str` (for non-interned strings)
pub trait StringId: Clone + Eq + Hash + Debug {}
impl<T: Clone + Eq + Hash + Debug> StringId for T {}

/// The source of truth that converts between `&str` and `StringId`.
///
/// This is typically passed to the top-level Reader or Expander,
/// not stored in the Datum itself.
pub trait Interner {
    type Id: StringId;
    fn intern(&mut self, text: &str) -> Self::Id;
    fn resolve<'a>(&'a self, id: &'a Self::Id) -> Option<&'a str>;
}

/// A no-op interner that uses `String` as the ID.
/// Useful for simple implementations or testing where interning is not required.
#[derive(Default, Debug, Clone, Copy)]
pub struct NoOpInterner;

impl Interner for NoOpInterner {
    type Id = String;

    fn intern(&mut self, text: &str) -> Self::Id {
        text.to_string()
    }

    fn resolve<'a>(&'a self, id: &'a Self::Id) -> Option<&'a str> {
        Some(id.as_str())
    }
}

/// A general-purpose interner backed by `string_interner`.
///
/// This is suitable for both Scheme and CEL usage when you want stable IDs.
#[derive(Default, Debug, Clone)]
pub struct SymbolInterner(StringInterner<DefaultBackend>);

impl SymbolInterner {
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }
}

impl Interner for SymbolInterner {
    type Id = DefaultSymbol;

    #[inline]
    fn intern(&mut self, text: &str) -> Self::Id {
        self.0.get_or_intern(text)
    }

    #[inline]
    fn resolve<'a>(&'a self, id: &'a Self::Id) -> Option<&'a str> {
        self.0.resolve(*id)
    }
}

/// The default string ID used by `SymbolInterner`.
pub type InternId = DefaultSymbol;
