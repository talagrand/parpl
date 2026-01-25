pub mod lex;
mod reader;
#[cfg(any(test, feature = "reference"))]
pub mod reference;
pub mod traits;

// Re-export key types for convenient access (single canonical path)
pub use reader::{TokenStream, parse_datum, parse_datum_with_max_depth};

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
