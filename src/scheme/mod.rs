pub mod lex;
mod reader;
#[cfg(any(test, feature = "reference"))]
pub mod reference;
pub mod traits;

use crate::{LimitExceeded, Span};

// Re-export key types for convenient access (single canonical path)
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
    /// and more characters are required to complete parsing.
    ///
    /// In a REPL, this is the cue to prompt the user for more input
    /// instead of reporting a hard error.
    ///
    /// CEL examples: `(1 + 2`, `[1, 2,`, `a ? b`
    ///
    /// Scheme examples: `(define x`, `"unterminated`, `#(`
    #[error("input is incomplete; more data required")]
    Incomplete,

    /// The input ends in the middle of a token.
    ///
    /// Unlike `Incomplete`, this indicates an incomplete token rather than
    /// an incomplete multi-line construct.
    ///
    /// Scheme examples: `#\`, `1e+`, `3/`
    ///
    /// Note: CEL does not emit this variant; incomplete tokens are reported
    /// as `Syntax` errors because pest combines lexing and parsing in one pass.
    #[error("incomplete token; input ends mid-token")]
    IncompleteToken,

    /// A syntax error detected while lexing or parsing a particular
    /// nonterminal (for example, `<primary>`, `<expr>`, or `<datum>`).
    #[error("syntax error in {nonterminal} at {span:?}: {message}")]
    Syntax {
        /// Source location of the error.
        ///
        /// Note: For CEL, this spans from the error position to the end of
        /// input, since pest reports cursor positions rather than token spans.
        span: Span,
        /// The grammar nonterminal being parsed when the error occurred.
        nonterminal: String,
        /// Human-readable description of the error.
        message: String,
    },

    /// A feature or format is not supported.
    ///
    /// The `kind` field is a string describing the unsupported feature.
    /// See [`unsupported`] module for documented constant values.
    #[error("unsupported at {span:?}: {kind}")]
    Unsupported {
        /// Source location of the unsupported construct.
        span: Span,
        /// The unsupported feature identifier.
        kind: &'static str,
    },

    /// A safety limit was exceeded.
    #[error("limit exceeded at {span:?}: {kind}")]
    LimitExceeded {
        /// Source location where the limit was exceeded.
        span: Span,
        /// The specific limit that was exceeded.
        kind: LimitExceeded,
    },

    /// An error from the writer implementation.
    #[error("writer error at {span:?}: {source}")]
    WriterError {
        /// Source location where the writer error occurred.
        span: Span,
        /// The underlying writer error.
        source: WriterErrorInner,
    },
}

impl Error {
    /// Construct a syntax error.
    #[must_use]
    pub fn syntax(span: Span, nonterminal: impl Into<String>, message: impl Into<String>) -> Self {
        Error::Syntax {
            span,
            nonterminal: nonterminal.into(),
            message: message.into(),
        }
    }

    /// Construct an unsupported error.
    ///
    /// Use constants from the [`unsupported`] module for the `kind` parameter.
    #[must_use]
    pub fn unsupported(span: Span, kind: &'static str) -> Self {
        Error::Unsupported { span, kind }
    }

    /// Construct a nesting depth exceeded error.
    ///
    /// If `details` is `Some((depth, max))`, the message includes specific values.
    /// If `None`, a generic message is used.
    #[must_use]
    pub fn nesting_depth(span: Span, details: Option<(usize, usize)>) -> Self {
        let message = match details {
            Some((depth, max)) => {
                format!("Nesting depth {depth} exceeds maximum of {max}")
            }
            None => "maximum nesting depth exceeded".to_string(),
        };
        Error::LimitExceeded {
            span,
            kind: LimitExceeded::NestingDepth { message },
        }
    }
}

/// Result type alias for parser operations.
pub type Result<T> = std::result::Result<T, Error>;
