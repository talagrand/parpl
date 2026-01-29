//! Common types shared across all parsers.
//!
//! This module provides foundational types used by both CEL and Scheme parsers:
//!
//! - [`Span`]: Source location tracking (byte offsets)
//! - [`Syntax`]: A value paired with its source span
//! - [`Interner`] / [`StringPool`]: String interning for memory-efficient symbol storage
//! - [`StringId`]: Trait for interned string handles

use std::{fmt::Debug, hash::Hash};
use string_interner::{DefaultSymbol, StringInterner, backend::DefaultBackend};

/// A byte-offset span into the original source.
///
/// Spans track the start and end positions (as byte offsets) of parsed elements.
/// They are used for error reporting, source mapping, and debugging.
///
/// # Example
///
/// ```
/// use parpl::Span;
///
/// let span = Span::new(0, 5);
/// assert_eq!(span.start, 0);
/// assert_eq!(span.end, 5);
///
/// // Merge two spans to get their union
/// let span2 = Span::new(3, 10);
/// let merged = span.merge(span2);
/// assert_eq!(merged, Span::new(0, 10));
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Span {
    /// Starting byte offset (inclusive).
    pub start: usize,
    /// Ending byte offset (exclusive).
    pub end: usize,
}

impl Span {
    /// Creates a new span with the given start and end byte offsets.
    pub fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }

    /// Merges two spans, returning the smallest span that contains both.
    pub fn merge(self, other: Span) -> Span {
        Span {
            start: std::cmp::min(self.start, other.start),
            end: std::cmp::max(self.end, other.end),
        }
    }
}

/// A syntax object: a value paired with its source span.
///
/// `Syntax<T>` wraps any value with source location information, enabling
/// precise error messages and source mapping. It is used extensively in
/// the Scheme parser for tokens and AST nodes.
///
/// # Example
///
/// ```
/// use parpl::{Span, Syntax};
///
/// let span = Span::new(0, 5);
/// let syntax = Syntax::new(span, "hello");
///
/// assert_eq!(syntax.value, "hello");
/// assert_eq!(syntax.span.start, 0);
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Syntax<T> {
    /// The source location of this syntax object.
    pub span: Span,
    /// The wrapped value.
    pub value: T,
}

impl<T> Syntax<T> {
    /// Create a new syntax object with the given span and value.
    #[inline]
    pub fn new(span: Span, value: T) -> Self {
        Self { span, value }
    }
}

/// A handle to a string (symbol or string literal).
///
/// `StringId` is a marker trait for types that can serve as string handles.
/// The trait bounds (`Clone + Eq + Hash + Debug`) ensure handles can be
/// compared, hashed (for use in maps), and debugged.
///
/// # Common Implementations
///
/// - [`StringPoolId`]: Default interned symbol (from `string_interner`)
/// - `String`: For non-interned implementations (see [`NoOpInterner`])
/// - `u64` or `u32`: For custom interning schemes
///
/// # Example
///
/// ```
/// use parpl::{StringPool, Interner};
///
/// let mut pool = StringPool::new();
/// let id1 = pool.intern("hello");
/// let id2 = pool.intern("hello");
///
/// // Same string => same ID
/// assert_eq!(id1, id2);
/// ```
pub trait StringId: Clone + Eq + Hash + Debug {}
impl<T: Clone + Eq + Hash + Debug> StringId for T {}

/// An interner that converts between `&str` and opaque string handles.
///
/// Interning ensures that identical strings share the same handle, reducing
/// memory usage and enabling O(1) equality comparisons. This is essential
/// for languages with many repeated identifiers (like Scheme symbols).
///
/// # Provided Implementations
///
/// - [`StringPool`]: Production interner using `string_interner` crate
/// - [`NoOpInterner`]: Simple implementation using `String` as the ID
///
/// You are free to implement your own interner by implementing this trait.
///
/// # Usage Pattern
///
/// The interner is passed to the parser/writer, which calls [`intern`](Interner::intern)
/// for each string. Later, [`resolve`](Interner::resolve) converts IDs back to strings.
///
/// ```
/// use parpl::{StringPool, Interner};
///
/// let mut pool = StringPool::new();
/// let id = pool.intern("hello");
/// assert_eq!(pool.resolve(&id), Some("hello"));
/// ```
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

/// The default string ID type used by [`StringPool`].
///
/// This is an opaque handle from the `string_interner` crate. It is
/// `Copy`, `Eq`, `Hash`, and very compact (typically 4 bytes).
///
/// To convert back to a string, use [`Interner::resolve`].
pub type StringPoolId = DefaultSymbol;

/// A production-ready string interner backed by `string_interner`.
///
/// `StringPool` provides efficient string interning with O(1) amortized
/// insertion and lookup. It is the recommended [`Interner`] implementation
/// for production use.
///
/// # Example
///
/// ```
/// use parpl::{StringPool, Interner};
///
/// let mut pool = StringPool::new();
///
/// // Intern strings
/// let hello = pool.intern("hello");
/// let world = pool.intern("world");
/// let hello2 = pool.intern("hello");
///
/// // Same content => same ID
/// assert_eq!(hello, hello2);
/// assert_ne!(hello, world);
///
/// // Resolve back to strings
/// assert_eq!(pool.resolve(&hello), Some("hello"));
/// assert_eq!(pool.resolve(&world), Some("world"));
/// ```
#[derive(Default, Debug, Clone)]
pub struct StringPool(StringInterner<DefaultBackend>);

impl StringPool {
    /// Create a new, empty string pool.
    #[inline]
    #[must_use]
    pub fn new() -> Self {
        Self::default()
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
