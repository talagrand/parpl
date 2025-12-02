pub mod ast;
pub mod lex;
pub mod parser;

use crate::ast::Span;

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

    /// Temporary catch-all while the parser is still a stub.
    #[error("unimplemented parser")]
    Unimplemented,
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
}
