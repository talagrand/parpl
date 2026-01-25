use std::fmt::Debug;
use std::hash::Hash;

use string_interner::{DefaultSymbol, StringInterner, backend::DefaultBackend};

/// A byte-offset span into the original source.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Span {
    /// Starting byte offset (inclusive).
    pub start: usize,
    /// Ending byte offset (exclusive).
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
}

/// A syntax object: a value paired with its source span.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Syntax<T> {
    /// The source location of this syntax object.
    pub span: Span,
    /// The wrapped value.
    pub value: T,
}

impl<T> Syntax<T> {
    #[inline]
    pub fn new(span: Span, value: T) -> Self {
        Self { span, value }
    }
}

/// A handle to a string (symbol or string literal).
///
/// Common implementations:
/// - `u64` or `u32` (for interned strings)
/// - `String` (for non-interned strings)
pub trait StringId: Clone + Eq + Hash + Debug {}
impl<T: Clone + Eq + Hash + Debug> StringId for T {}

/// The source of truth that converts between `&str` and `StringId`.
///
/// This is typically passed to the top-level Reader or Expander,
/// not stored in the Datum itself.
pub trait Interner {
    /// The handle type returned by [`intern`](Interner::intern).
    type Id: StringId;

    /// Intern a string, returning a handle.
    ///
    /// If the string was previously interned, returns the existing handle.
    fn intern(&mut self, text: &str) -> Self::Id;

    /// Resolve a handle back to the original string.
    ///
    /// Returns `None` if the ID is invalid (should not happen with well-formed IDs).
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

/// The default string ID used by `StringPool`.
pub type StringPoolId = DefaultSymbol;
/// A general-purpose interner backed by `string_interner`.
#[derive(Default, Debug, Clone)]
pub struct StringPool(StringInterner<DefaultBackend>);

impl StringPool {
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    #[inline]
    pub fn resolve_id(&self, id: StringPoolId) -> Option<&str> {
        self.0.resolve(id)
    }
}

impl Interner for StringPool {
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
