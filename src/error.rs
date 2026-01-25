// Error types for parpl parsers.

use crate::Span;

// ============================================================================
// Safety Limits
// ============================================================================

/// Safety limits exceeded during parsing.
///
/// This enum captures various resource limits that parsers enforce to prevent
/// denial-of-service attacks or stack overflow.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LimitExceeded {
    /// Maximum nesting depth was exceeded.
    /// Deep nesting in expressions can cause stack overflow during parsing
    /// or evaluation. Both CEL and Scheme parsers enforce configurable limits.
    ///
    /// The `message` field contains a human-readable description. CEL populates
    /// this with specific depth/limit values; Scheme uses a fixed message.
    NestingDepth { message: String },
}

impl std::fmt::Display for LimitExceeded {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LimitExceeded::NestingDepth { message } => f.write_str(message),
        }
    }
}

// ============================================================================
// Error Types
// ============================================================================

/// Type alias for a boxed writer error.
pub type WriterErrorInner = Box<dyn std::error::Error + Send + Sync + 'static>;

/// Top-level error type for parsing.
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
    /// See [`crate::scheme::unsupported`] module for documented constant values.
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
    /// Use constants from the [`crate::scheme::unsupported`] module for the `kind` parameter.
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

    /// Construct an invalid escape sequence error.
    #[must_use]
    pub fn invalid_escape(span: Span, message: impl Into<String>) -> Self {
        let msg = format!("Invalid escape sequence: {}", message.into());
        Error::Syntax {
            span,
            nonterminal: "<escape-sequence>".to_string(),
            message: msg,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! test_cases {
        ($($name:ident: $test:expr),* $(,)?) => {
            $(
                #[test]
                fn $name() {
                    $test
                }
            )*
        };
    }

    // ============================================================
    // Section: Error Construction and Display Tests
    // ============================================================

    test_cases! {
        test_error_display: {
            let err = Error::syntax(Span::new(5, 10), "<primary>", "unexpected token");
            let display = format!("{err}");
            assert!(display.contains("unexpected token"));
            assert!(display.contains("start: 5") && display.contains("end: 10"));
        },

        test_nesting_depth_error: {
            let err = Error::nesting_depth(Span::new(0, 10), Some((129, 128)));
            assert!(matches!(
                err,
                Error::LimitExceeded { kind: LimitExceeded::NestingDepth { .. }, .. }
            ));
        },

        test_limit_exceeded_span: {
            let err = Error::nesting_depth(Span::new(10, 15), Some((129, 128)));
            let display = format!("{err}");
            assert!(display.contains("start: 10") && display.contains("end: 15"));
        },
    }
}
