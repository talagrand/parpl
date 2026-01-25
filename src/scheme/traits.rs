use crate::{Error, Interner, Span, StringId, scheme::lex};
use std::fmt::Debug;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DatumKind {
    Bool,
    Integer,
    Float,
    Number,
    Character,
    String,
    Symbol,
    ByteVector,
    Pair,
    Null,
    Vector,
    Labeled,
    LabelRef,
    // For opaque host objects or other extensions
    Other,
}

/// Abstract interface for Scheme number operations.
/// This decouples the Reader and Inspector from the concrete number representation.
pub trait SchemeNumberOps: Debug + Sized {
    /// The opaque semantic number type used by the backend/expander.
    type Number: Debug + Clone;

    /// The single lowering hook.
    /// The Reader calls this once per number token.
    fn from_literal(lit: &lex::NumberLiteral<'_>, span: Span) -> Result<Self::Number, Error>;

    /// The semantic equality hook.
    /// Required for `syntax-rules` pattern matching (e.g. matching `1` against `1.0`).
    /// We use a method instead of `Eq` to allow Scheme's specific `eqv?` rules.
    fn eqv(a: &Self::Number, b: &Self::Number) -> bool;
}

pub trait DatumInspector: Sized {
    /// Fast type check.
    fn kind(&self) -> DatumKind;

    /// Access the source span, if this implementation tracks it.
    fn span(&self) -> Option<Span>;
    type N: SchemeNumberOps;

    /// Returns the number if this datum is a number.
    fn as_number(&self) -> Option<&<Self::N as SchemeNumberOps>::Number>;

    fn as_char(&self) -> Option<char>;

    /// The type of string ID used by this inspector.
    type StringId<'a>: StringId + 'a
    where
        Self: 'a;

    /// Returns the ID for a symbol.
    /// To get the text, pass this ID to the `Interner`.
    fn as_sym<'a>(&'a self) -> Option<Self::StringId<'a>>;

    /// Returns the ID for a string literal.
    /// To get the text, pass this ID to the `Interner`.
    fn as_str<'a>(&'a self) -> Option<Self::StringId<'a>>;

    fn as_bytes(&self) -> Option<&[u8]>;

    // --- Compounds (Recursive Views) ---

    /// The type of a "child" handle.
    /// For ASTs, this can be `&Self`.
    /// For Rc Graphs, this can be `Self` (the Rc itself).
    /// For Arenas, this can be `Self` (the Index).
    type Child<'a>: DatumInspector
    where
        Self: 'a;

    /// Returns references to the head and tail.
    fn as_pair<'a>(&'a self) -> Option<(Self::Child<'a>, Self::Child<'a>)>;

    /// Returns an iterator over vector elements.
    type VectorIter<'a>: Iterator<Item = Self::Child<'a>>
    where
        Self: 'a;
    fn vector_iter<'a>(&'a self) -> Option<Self::VectorIter<'a>>;

    /// Returns the label ID and the inner datum if this is a labeled datum.
    fn as_labeled<'a>(&'a self) -> Option<(u64, Self::Child<'a>)>;

    /// Returns the label ID if this is a label reference.
    fn as_label_ref(&self) -> Option<u64>;

    // --- Utilities ---

    fn is_null(&self) -> bool {
        matches!(self.kind(), DatumKind::Null)
    }

    /// Returns an iterator over list elements (proper or improper).
    type ListIter<'a>: Iterator<Item = Self::Child<'a>> + ExactSizeIterator
    where
        Self: 'a;

    fn list_iter<'a>(&'a self) -> Self::ListIter<'a>;

    /// Returns the improper tail of the list, if one exists.
    /// For `(a b . c)`, this returns `Some(c)`.
    /// For `(a b)`, this returns `None`.
    fn improper_tail<'a>(&'a self) -> Option<Self::Child<'a>>;
}

pub trait DatumWriter {
    /// The concrete type being built
    type Output;
    /// The error type returned by this writer
    type Error: std::error::Error + Send + Sync + 'static;

    /// The interner used by this writer.
    ///
    /// The Reader will call `writer.interner().intern(text)` to obtain IDs
    /// for symbols and strings.
    type Interner: Interner<Id = Self::StringId>;

    /// The stable ID type for interned strings/symbols.
    type StringId: StringId;

    /// Mutable access to the writer's interner.
    fn interner(&mut self) -> &mut Self::Interner;

    type N: SchemeNumberOps;

    // --- Atoms ---
    fn bool(&mut self, v: bool, s: Span) -> Result<Self::Output, Self::Error>;
    fn number(
        &mut self,
        v: <Self::N as SchemeNumberOps>::Number,
        s: Span,
    ) -> Result<Self::Output, Self::Error>;
    fn char(&mut self, v: char, s: Span) -> Result<Self::Output, Self::Error>;

    // Both strings and symbols now take IDs.
    // The caller (Reader/Expander) must use their Interner to produce these IDs.
    fn string(&mut self, v: Self::StringId, s: Span) -> Result<Self::Output, Self::Error>;
    fn symbol(&mut self, v: Self::StringId, s: Span) -> Result<Self::Output, Self::Error>;

    fn bytevector(&mut self, v: &[u8], s: Span) -> Result<Self::Output, Self::Error>;

    // --- Compounds ---

    /// Construct a proper list from the given elements.
    ///
    /// Empty lists (`()` / nil) are also sent here with an empty iterator.
    /// Implementations are free to represent empty lists however they choose
    /// (e.g., a dedicated `EmptyList` variant, or `List(vec![])`).
    fn list<I>(&mut self, iter: I, s: Span) -> Result<Self::Output, Self::Error>
    where
        I: IntoIterator<Item = Self::Output>,
        I::IntoIter: ExactSizeIterator;

    fn improper_list<I>(
        &mut self,
        head: I,
        tail: Self::Output,
        s: Span,
    ) -> Result<Self::Output, Self::Error>
    where
        I: IntoIterator<Item = Self::Output>,
        I::IntoIter: ExactSizeIterator;

    fn vector<I>(&mut self, iter: I, s: Span) -> Result<Self::Output, Self::Error>
    where
        I: IntoIterator<Item = Self::Output>,
        I::IntoIter: ExactSizeIterator;

    fn labeled(
        &mut self,
        id: u64,
        inner: Self::Output,
        s: Span,
    ) -> Result<Self::Output, Self::Error>;

    fn label_ref(&mut self, id: u64, s: Span) -> Result<Self::Output, Self::Error>;

    // --- Optimization Hook ---

    /// Zero-cost copy of a datum.
    ///
    /// Because `source` is `&Self::Output`, this enforces at compile time
    /// that the source datum is compatible with this writer (same arena,
    /// same string pool, same number representation).
    ///
    /// For arena-based writers, this is typically just a clone of the
    /// reference structure - O(1) for atoms, O(n) shallow pointer copies
    /// for compound structures. No new allocations are needed.
    ///
    /// This is designed for macro expansion where unchanged subtrees
    /// are copied directly into the output without transformation.
    fn copy(&mut self, source: &Self::Output) -> Result<Self::Output, Self::Error>;
}

// NOTE: We intentionally do not define a reader-owned number-literal IR.
// `SchemeNumberOps::from_literal` receives a borrowed lexer `NumberLiteral`.
// If an implementation wants to retain an unknown literal, it can clone the
// raw token text (`lit.text`) into its own representation.
