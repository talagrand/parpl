pub mod lex;
pub mod primitivenumbers;
pub mod reader;
#[cfg(any(test, feature = "samples"))]
pub mod samples;
pub mod traits;

use crate::common::Span;

/// Enumerates specific unsupported features that can be reported via
/// `ParseError::Unsupported`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Unsupported {
    Vectors,
    Bytevectors,
    Quasiquote,
    Labels,
    Characters,
    Comments,
    DepthLimit,
    ImproperLists,
    IntegerOverflow,
    InvalidIntegerFormat,
    NonIntegerNumber,
    FoldCaseDirectives,
}

impl std::fmt::Display for Unsupported {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Unsupported::Vectors => "vectors",
            Unsupported::Bytevectors => "bytevectors",
            Unsupported::Quasiquote => "quasiquote/unquote",
            Unsupported::Labels => "labels",
            Unsupported::Characters => "characters",
            Unsupported::Comments => "comments",
            Unsupported::DepthLimit => "maximum nesting depth",
            Unsupported::ImproperLists => "improper lists",
            Unsupported::IntegerOverflow => "integer overflow",
            Unsupported::InvalidIntegerFormat => "invalid integer format",
            Unsupported::NonIntegerNumber => "non-integer number",
            Unsupported::FoldCaseDirectives => "fold-case directives",
        };
        f.write_str(s)
    }
}

/// Top-level parse error type. This will grow as the implementation
/// starts enforcing more of `syn.tex`.
#[derive(Debug, thiserror::Error, Clone)]
pub enum ParseError {
    /// The input ends in the middle of a grammatically valid construct
    /// and more characters are required to decide the result.
    ///
    /// In a REPL, this is the cue to prompt the user for more input
    /// instead of reporting a hard error.
    #[error("input is incomplete; more data required")]
    Incomplete,

    #[error("writer error: {0}")]
    WriterError(String),

    /// The input ends in the middle of a token (e.g., `#\`, `1e+`, `3/`).
    ///
    /// Unlike `Incomplete`, this indicates an incomplete token rather than
    /// an incomplete multi-line construct. In a REPL context, this is
    /// typically a user error rather than a prompt-for-more signal.
    /// In a streaming context, this still means more input is needed.
    #[error("incomplete token; input ends mid-token")]
    IncompleteToken,

    /// A lexical error detected while recognizing a particular
    /// nonterminal (for example, `<string>` or `<identifier>`).
    #[error("lexical error in {nonterminal} at {span:?}: {message}")]
    Lex {
        span: Span,
        nonterminal: &'static str,
        message: String,
    },

    /// A syntactic error detected while parsing a particular
    /// nonterminal (for example, `<datum>` or `<expression>`).
    #[error("syntax error in {nonterminal} at {span:?}: {message}")]
    Syntax {
        span: Span,
        nonterminal: &'static str,
        message: String,
    },

    /// An unsupported feature was encountered.
    #[error("unsupported feature at {span:?}: {feature}")]
    Unsupported { span: Span, feature: Unsupported },
}

impl ParseError {
    /// Helper for constructing a lexical error.
    pub fn lexical(span: Span, nonterminal: &'static str, message: impl Into<String>) -> Self {
        ParseError::Lex {
            span,
            nonterminal,
            message: message.into(),
        }
    }

    /// Helper for constructing a syntax error.
    pub fn syntax(span: Span, nonterminal: &'static str, message: impl Into<String>) -> Self {
        ParseError::Syntax {
            span,
            nonterminal,
            message: message.into(),
        }
    }

    /// Helper for constructing an unsupported error.
    pub fn unsupported(span: Span, feature: Unsupported) -> Self {
        ParseError::Unsupported { span, feature }
    }
}
