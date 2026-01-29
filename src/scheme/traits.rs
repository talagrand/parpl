use crate::{Error, Interner, Span, StringId};
use std::{fmt::Debug, ops::Deref};

/// Classification of Scheme datum types.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DatumKind {
    /// Boolean: `#t` or `#f`
    Bool,
    /// Integer number
    Integer,
    /// Floating-point number
    Float,
    /// Generic number (includes rationals, complex)
    Number,
    /// Character: `#\x`, `#\newline`, etc.
    Character,
    /// String: `"hello"`
    String,
    /// Symbol: `foo`, `+`, `lambda`
    Symbol,
    /// Bytevector: `#u8(1 2 3)`
    ByteVector,
    /// Pair (cons cell): `(a . b)`
    Pair,
    /// Empty list: `()`
    Null,
    /// Vector: `#(1 2 3)`
    Vector,
    /// Labeled datum: `#0=...`
    Labeled,
    /// Label reference: `#0#`
    LabelRef,
    /// Extension point for custom datum types
    Other,
}

/// Trait for converting lexer number tokens to semantic number values.
///
/// This trait decouples the reader from specific number representations,
/// allowing different implementations (exact integers, floating point,
/// rationals, bignums, etc.).
///
/// # Implementing
///
/// Implement this trait to define how number literals are converted to
/// your number type:
///
/// ```ignore
/// impl SchemeNumberOps for MyNumberOps {
///     type Number = MyNumber;
///
///     fn from_literal(lit: &NumberLiteral<'_>, span: Span) -> Result<MyNumber, Error> {
///         // Parse the literal and return your number type
///     }
///
///     fn eqv(a: &MyNumber, b: &MyNumber) -> bool {
///         // Implement Scheme's eqv? semantics
///     }
/// }
/// ```
///
/// # See Also
///
/// - [`reference::numbers::SimpleNumberOps`](crate::scheme::reference::numbers::SimpleNumberOps)
///   for a reference implementation using `i64`/`f64`
pub trait SchemeNumberOps: Debug + Sized {
    /// The opaque semantic number type used by the backend/expander.
    type Number: Debug + Clone;

    /// The single lowering hook.
    /// The Reader calls this once per number token.
    fn from_literal(
        lit: &crate::scheme::NumberLiteral<'_>,
        span: Span,
    ) -> Result<Self::Number, Error>;

    /// The semantic equality hook.
    /// Required for `syntax-rules` pattern matching (e.g. matching `1` against `1.0`).
    /// We use a method instead of `Eq` to allow Scheme's specific `eqv?` rules.
    fn eqv(a: &Self::Number, b: &Self::Number) -> bool;
}

/// Trait for inspecting Scheme datum values.
///
/// `DatumInspector` provides read-only access to datum structure, enabling
/// generic algorithms over any datum representation (arena-allocated,
/// Rc-based, boxed, etc.).
///
/// # Associated Types
///
/// The trait uses associated types to handle different ownership models:
///
/// - `NumberOps`: Number operations type (see [`SchemeNumberOps`])
/// - `NumberRef<'a>`: Return type for number access (enables zero-copy or reconstruction)
/// - `StringId<'a>`: Handle type for interned strings
/// - `Child<'a>`: Type for child references (may be `&Self` or owned)
///
/// # Example
///
/// ```ignore
/// fn count_atoms<D: DatumInspector>(datum: &D) -> usize {
///     match datum.kind() {
///         DatumKind::Pair => {
///             let (car, cdr) = datum.as_pair().unwrap();
///             count_atoms(&car) + count_atoms(&cdr)
///         }
///         DatumKind::Null => 0,
///         _ => 1,
///     }
/// }
/// ```
pub trait DatumInspector: Sized {
    /// Fast type check.
    fn kind(&self) -> DatumKind;

    /// Access the source span, if this implementation tracks it.
    fn span(&self) -> Option<Span>;

    /// The number operations type used by this inspector.
    type NumberOps: SchemeNumberOps;

    /// The type returned by [`as_number`](Self::as_number).
    ///
    /// This associated type allows implementations to choose their return strategy:
    /// - **Unified storage** (e.g., `Datum::Number(SimpleNumber)`): Use `&'a Number` for zero-cost borrowing
    /// - **Split storage** (e.g., `Datum::Integer(i64)` + `Datum::Float(f64)`): Return `Number` by value
    ///   if it implements `Copy`, or use `Cow<'a, Number>` to reconstruct on demand
    ///
    /// The `Deref` bound ensures callers can always obtain `&Number` via `&*num_ref`.
    type NumberRef<'a>: Deref<Target = <Self::NumberOps as SchemeNumberOps>::Number>
    where
        Self: 'a;

    /// Returns the number if this datum is a number.
    ///
    /// The returned value dereferences to `&Number`, allowing uniform access
    /// regardless of the underlying storage strategy.
    fn as_number<'a>(&'a self) -> Option<Self::NumberRef<'a>>;

    /// Returns the character if this datum is a character.
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

    /// Returns the byte vector if this datum is a byte vector.
    fn as_bytes(&self) -> Option<&[u8]>;

    // --- Compounds (Recursive Views) ---

    /// The type of a "child" handle.
    /// For ASTs, this can be `&Self`.
    /// For Rc Graphs, this can be `Self` (the Rc itself).
    /// For Arenas, this can be `Self` (the Index).
    type Child<'a>: DatumInspector
    where
        Self: 'a;

    /// Returns references to the head and tail if this datum is a pair.
    fn as_pair<'a>(&'a self) -> Option<(Self::Child<'a>, Self::Child<'a>)>;

    /// Returns an iterator over vector elements.
    type VectorIter<'a>: Iterator<Item = Self::Child<'a>>
    where
        Self: 'a;

    /// Returns an iterator over vector elements if this is a vector.
    fn vector_iter<'a>(&'a self) -> Option<Self::VectorIter<'a>>;

    /// Returns the label ID and the inner datum if this is a labeled datum.
    fn as_labeled<'a>(&'a self) -> Option<(u64, Self::Child<'a>)>;

    /// Returns the label ID if this is a label reference.
    fn as_label_ref(&self) -> Option<u64>;

    // --- Utilities ---

    /// Returns true if this datum is the empty list.
    fn is_null(&self) -> bool {
        matches!(self.kind(), DatumKind::Null)
    }

    /// Returns an iterator over list elements (proper or improper).
    type ListIter<'a>: Iterator<Item = Self::Child<'a>> + ExactSizeIterator
    where
        Self: 'a;

    /// Returns an iterator over the elements of a list.
    fn list_iter<'a>(&'a self) -> Self::ListIter<'a>;

    /// Returns the improper tail of the list, if one exists.
    /// For `(a b . c)`, this returns `Some(c)`.
    /// For `(a b)`, this returns `None`.
    fn improper_tail<'a>(&'a self) -> Option<Self::Child<'a>>;
}

/// Trait for constructing Scheme datums during parsing.
///
/// `DatumWriter` abstracts over AST construction, allowing the parser to work
/// with any datum representation (arena-allocated, Rc-based, boxed, etc.).
///
/// # Implementing
///
/// Implement this trait to use your own datum types with the parser:
///
/// ```ignore
/// impl DatumWriter for MyWriter {
///     type Output = MyDatum;
///     type Error = MyError;
///     type Interner = StringPool;
///     type StringId = StringPoolId;
///     type NumberOps = SimpleNumberOps;
///
///     fn interner(&mut self) -> &mut Self::Interner { &mut self.interner }
///
///     fn bool(&mut self, v: bool, s: Span) -> Result<Self::Output, Self::Error> {
///         Ok(MyDatum::Bool(v))
///     }
///
///     // ... implement other methods
/// }
/// ```
///
/// # See Also
///
/// - [`reference::arena::ArenaDatumWriter`](crate::scheme::reference::arena::ArenaDatumWriter)
///   for a full reference implementation
/// - [`reference::mini::MiniDatumWriter`](crate::scheme::reference::mini::MiniDatumWriter)
///   for a minimal implementation
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

    /// The number operations type used by this writer.
    type NumberOps: SchemeNumberOps;

    // --- Atoms ---

    /// Constructs a boolean datum.
    fn bool(&mut self, v: bool, s: Span) -> Result<Self::Output, Self::Error>;

    /// Constructs a number datum.
    fn number(
        &mut self,
        v: <Self::NumberOps as SchemeNumberOps>::Number,
        s: Span,
    ) -> Result<Self::Output, Self::Error>;

    /// Constructs a character datum.
    fn char(&mut self, v: char, s: Span) -> Result<Self::Output, Self::Error>;

    /// Constructs a string datum from an interned string ID.
    fn string(&mut self, v: Self::StringId, s: Span) -> Result<Self::Output, Self::Error>;

    /// Constructs a symbol datum from an interned string ID.
    fn symbol(&mut self, v: Self::StringId, s: Span) -> Result<Self::Output, Self::Error>;

    /// Constructs a byte vector datum.
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

    /// Constructs an improper list (dotted pair) from head elements and a tail.
    fn improper_list<I>(
        &mut self,
        head: I,
        tail: Self::Output,
        s: Span,
    ) -> Result<Self::Output, Self::Error>
    where
        I: IntoIterator<Item = Self::Output>,
        I::IntoIter: ExactSizeIterator;

    /// Constructs a vector from the given elements.
    fn vector<I>(&mut self, iter: I, s: Span) -> Result<Self::Output, Self::Error>
    where
        I: IntoIterator<Item = Self::Output>,
        I::IntoIter: ExactSizeIterator;

    /// Constructs a labeled datum (`#n=datum`).
    fn labeled(
        &mut self,
        id: u64,
        inner: Self::Output,
        s: Span,
    ) -> Result<Self::Output, Self::Error>;

    /// Constructs a label reference (`#n#`).
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
