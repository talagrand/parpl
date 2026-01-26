//! R7RS Scheme datum parser.
//!
//! This module provides a complete, standards-conformant parser for R7RS Scheme's syntax ("datums").
//! It is designed as a foundation for building Scheme interpreters, compilers, and S-expression tools.
//! It supports the full R7RS datum syntax: atoms, lists, vectors, bytevectors, labels, and quotation.
//!
//! # Integration
//!
//! Parpl is designed to integrate into your project. You provide your own datum (AST)
//! representation by implementing [`DatumWriter`](traits::DatumWriter), and the
//! parser calls your methods to construct values as it reads.
//!
//! ```ignore
//! impl DatumWriter for MySchemeReader {
//!     type Output = MyDatum;
//!     // ...
//!     fn list<I>(&mut self, items: I, span: Span) -> Result<Self::Output, Self::Error> {
//!         Ok(MyDatum::List(items.collect()))
//!     }
//! }
//!
//! let parser = parpl::scheme::SchemeParser::default();
//! let datum = parser.parse("(+ 1 2)", &mut my_reader)?;
//! ```
//!
//! # Starter Implementation
//!
//! The [`mod@reference`] module (requires the `reference` feature) provides
//! working implementations designed to be studied and forked. Use them as-is
//! for quick integration, or adapt the code to your project's needs.
//!
//! ```
//! # #[cfg(feature = "reference")]
//! # fn example() -> Result<(), parpl::Error> {
//! use parpl::StringPool;
//! use parpl::scheme::reference::arena::{ArenaDatumWriter, read};
//! use bumpalo::Bump;
//!
//! let arena = Bump::new();
//! let mut interner = StringPool::new();
//! let datum = read("(define (square x) (* x x))", &arena, &mut interner)?;
//! # Ok(())
//! # }
//! ```
//!
//! # Supported Syntax
//!
//! The parser supports the complete R7RS external representation syntax:
//!
//! - **Atoms**: booleans, numbers, characters, strings, symbols
//! - **Numbers**: integers, rationals, floats, complex (lexed; conversion delegated to your [`SchemeNumberOps`](traits::SchemeNumberOps))
//! - **Compound**: lists, dotted pairs, vectors, bytevectors
//! - **Quotation**: `'`, `` ` ``, `,`, `,@`
//! - **Labels**: `#n=` / `#n#` for shared structure
//! - **Comments**: `;`, `#|...|#`, `#;` datum comments
//!
//! # Parsing Multiple Datums
//!
//! For REPLs or parsing programs with multiple top-level expressions, use
//! [`SchemeParser::token_stream`] to get a [`TokenStream`] that yields
//! datums one at a time:
//!
//! ```ignore
//! let parser = SchemeParser::default();
//! let mut stream = parser.token_stream("(+ 1 2) (define x 10)");
//! let mut writer = MyWriter::new();
//!
//! while !stream.is_empty() {
//!     let (datum, span) = stream.parse(&mut writer)?;
//!     // process datum...
//! }
//! ```
//!
//! # Safety Limits
//!
//! The parser enforces a configurable maximum nesting depth to prevent stack overflow.
//! Use [`Builder::max_depth`] to specify a custom limit:
//!
//! ```
//! # #[cfg(feature = "reference")]
//! # fn example() -> Result<(), parpl::Error> {
//! use parpl::StringPool;
//! use parpl::scheme::{Builder, reference::arena::ArenaDatumWriter};
//! use bumpalo::Bump;
//!
//! let arena = Bump::new();
//! let mut interner = StringPool::new();
//! let mut writer = ArenaDatumWriter::new(&arena, &mut interner);
//! let parser = Builder::default().max_depth(32).build();
//! let datum = parser.parse("((()))", &mut writer)?;
//! # Ok(())
//! # }
//! ```

pub(crate) mod constants;
mod context;
pub(crate) mod lex;
mod reader;
#[cfg(any(test, feature = "reference"))]
pub mod reference;
pub mod traits;

// Re-export key types for convenient access (single canonical path)
pub use context::{Builder, SchemeParser};
pub use reader::TokenStream;

/// Result type alias for parser operations.
pub type Result<T> = std::result::Result<T, crate::Error>;

// ============================================================================
// Unsupported Feature Constants
// ============================================================================

/// Documented string constants for unsupported features.
///
/// These are used with [`crate::Error::Unsupported`] to indicate features or formats
/// that a [`DatumWriter`](traits::DatumWriter) or
/// [`SchemeNumberOps`](traits::SchemeNumberOps) implementation may reject.
///
/// Using `&'static str` instead of an enum allows language-specific extensions
/// without modifying the core error type.
pub mod unsupported {
    // --- Datum types (rejected by DatumWriter) ---
    /// Vector literals `#(...)`.
    pub const VECTOR: &str = "vector";
    /// Bytevector literals `#u8(...)`.
    pub const BYTEVECTOR: &str = "bytevector";
    /// Labeled data `#n=` / `#n#`.
    pub const LABEL: &str = "label";
    /// Character literals `#\x`.
    pub const CHARACTER: &str = "character";
    /// Improper (dotted) lists.
    pub const IMPROPER_LIST: &str = "improper-list";

    // --- Lexer restrictions (rejected by LexConfig) ---
    /// Comments (`;`, `#|...|#`, `#;`) rejected by configuration.
    pub const COMMENT: &str = "comment";
    /// Fold-case directives (`#!fold-case`, `#!no-fold-case`) rejected.
    pub const FOLD_CASE_DIRECTIVE: &str = "fold-case-directive";

    // --- Number conversion (rejected by SchemeNumberOps) ---
    /// Integer literal exceeds the target type's range.
    pub const NUMERIC_OVERFLOW: &str = "numeric-overflow";
    /// Number representation not handled by the implementation
    /// (e.g., floats, rationals, complex numbers, exactness prefixes).
    pub const NUMERIC_REPRESENTATION: &str = "numeric-representation";
}
