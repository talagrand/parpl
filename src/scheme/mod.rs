pub mod lex;
mod reader;
#[cfg(any(test, feature = "reference"))]
pub mod reference;
pub mod traits;

use crate::Span;

// Re-export key types for convenient access (single canonical path)
pub use reader::{TokenStream, parse_datum, parse_datum_with_max_depth};

// ============================================================================
// Error Categories
// ============================================================================

/// Type alias for a boxed writer error.
pub type WriterErrorInner = Box<dyn std::error::Error + Send + Sync + 'static>;

/// Features or formats that a [`DatumWriter`](traits::DatumWriter) or
/// [`SchemeNumberOps`](traits::SchemeNumberOps) implementation may reject.
///
/// These variants represent errors that implementations *can* raise when
/// they encounter constructs they don't handle. For example:
/// - A minimal writer might reject vectors or characters
/// - A lexer configuration might reject comments
/// - A number implementation might reject floats or bignums
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Unsupported {
    // --- Datum types (rejected by DatumWriter) ---
    /// Vector literals `#(...)`.
    Vectors,
    /// Bytevector literals `#u8(...)`.
    Bytevectors,
    /// Quasiquote/unquote forms.
    Quasiquote,
    /// Labeled data `#n=` / `#n#`.
    Labels,
    /// Character literals `#\x`.
    Characters,
    /// Improper (dotted) lists.
    ImproperLists,

    // --- Lexer restrictions (rejected by LexConfig) ---
    /// Comments (`;`, `#|...|#`, `#;`) rejected by configuration.
    Comments,
    /// Fold-case directives (`#!fold-case`, `#!no-fold-case`) rejected.
    FoldCaseDirectives,

    // --- Number conversion (rejected by SchemeNumberOps) ---
    /// Integer literal exceeds the target type's range.
    /// (R7RS recommends arbitrary precision, but implementations may use fixed-width types.)
    NumericOverflow,
    /// Number representation not handled by the implementation
    /// (e.g., floats, rationals, complex numbers, exactness prefixes).
    NumericRepresentation,
}

impl std::fmt::Display for Unsupported {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            // Datum types
            Unsupported::Vectors => "vectors",
            Unsupported::Bytevectors => "bytevectors",
            Unsupported::Quasiquote => "quasiquote/unquote",
            Unsupported::Labels => "labels",
            Unsupported::Characters => "characters",
            Unsupported::ImproperLists => "improper lists",
            // Lexer restrictions
            Unsupported::Comments => "comments",
            Unsupported::FoldCaseDirectives => "fold-case directives",
            // Number conversion
            Unsupported::NumericOverflow => "numeric overflow",
            Unsupported::NumericRepresentation => "unsupported numeric representation",
        };
        f.write_str(s)
    }
}

/// Safety limits exceeded during parsing.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LimitExceeded {
    /// Maximum nesting depth was exceeded.
    NestingDepth,
}

impl std::fmt::Display for LimitExceeded {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            LimitExceeded::NestingDepth => "maximum nesting depth exceeded",
        };
        f.write_str(s)
    }
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
    #[error("unsupported at {span:?}: {kind}")]
    Unsupported { span: Span, kind: Unsupported },

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
    #[must_use]
    pub fn unsupported(span: Span, kind: Unsupported) -> Self {
        Error::Unsupported { span, kind }
    }

    /// Helper for constructing a limit exceeded error.
    #[must_use]
    pub fn limit_exceeded(span: Span, kind: LimitExceeded) -> Self {
        Error::LimitExceeded { span, kind }
    }
}
