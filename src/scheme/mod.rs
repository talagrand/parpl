pub mod lex;
mod reader;
#[cfg(any(test, feature = "reference"))]
pub mod reference;
pub mod traits;

use crate::Span;

// Re-export key types for convenient access (single canonical path)
pub use crate::LimitExceeded;
pub use reader::{TokenStream, parse_datum, parse_datum_with_max_depth};

// ============================================================================
// Error Categories
// ============================================================================

/// Type alias for a boxed writer error.
pub type WriterErrorInner = Box<dyn std::error::Error + Send + Sync + 'static>;

/// Documented string constants for unsupported features.
///
/// These are used with [`Error::Unsupported`] to indicate features or formats
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

/// Top-level error type for Scheme parsing.
#[derive(Debug, thiserror::Error)]
pub enum Error {
    /// The input ends in the middle of a grammatically valid construct
    /// and more characters are required to decide the result.
    ///
    /// In a REPL, this is the cue to prompt the user for more input
    /// instead of reporting a hard error.
    #[error("input is incomplete; more data required")]
    Incomplete,

    /// An error from the [`DatumWriter`](traits::DatumWriter) implementation.
    #[error("writer error: {0}")]
    WriterError(WriterErrorInner),

    /// The input ends in the middle of a token (e.g., `#\`, `1e+`, `3/`).
    ///
    /// Unlike `Incomplete`, this indicates an incomplete token rather than
    /// an incomplete multi-line construct. In a REPL context, this is
    /// typically a user error rather than a prompt-for-more signal.
    /// In a streaming context, this still means more input is needed.
    #[error("incomplete token; input ends mid-token")]
    IncompleteToken,

    /// A syntax error detected while lexing or parsing a particular
    /// nonterminal (for example, `<token>`, `<string>`, or `<datum>`).
    #[error("syntax error in {nonterminal} at {span:?}: {message}")]
    Syntax {
        span: Span,
        nonterminal: &'static str,
        message: String,
    },

    /// A feature or format is not supported.
    ///
    /// The `kind` field is a string describing the unsupported feature.
    /// See [`unsupported`] module for documented constant values.
    #[error("unsupported at {span:?}: {kind}")]
    Unsupported { span: Span, kind: &'static str },

    /// A safety limit was exceeded.
    #[error("limit exceeded at {span:?}: {kind}")]
    LimitExceeded { span: Span, kind: LimitExceeded },
}

impl Error {
    /// Helper for constructing a syntax error.
    #[must_use]
    pub fn syntax(span: Span, nonterminal: &'static str, message: impl Into<String>) -> Self {
        Error::Syntax {
            span,
            nonterminal,
            message: message.into(),
        }
    }

    /// Helper for constructing an unsupported error.
    ///
    /// Use constants from the [`unsupported`] module for the `kind` parameter.
    #[must_use]
    pub fn unsupported(span: Span, kind: &'static str) -> Self {
        Error::Unsupported { span, kind }
    }

    /// Helper for constructing a limit exceeded error.
    #[must_use]
    pub fn limit_exceeded(span: Span, kind: LimitExceeded) -> Self {
        Error::LimitExceeded { span, kind }
    }
}
