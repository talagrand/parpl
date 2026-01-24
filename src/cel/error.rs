// Error types for the CEL parser
//
// This module defines error types for CEL parsing:
// - Parsing errors (syntax errors from pest)
// - AST construction errors (literal parsing, etc.)
//
// By centralizing error handling, we avoid exposing pest's error types
// throughout the codebase and provide consistent error reporting.

use crate::{Span, cel::parser::Rule};
use std::fmt;

/// Main error type for CEL parser operations
#[derive(Debug, Clone, PartialEq)]
pub struct Error {
    /// The kind of error
    pub kind: ErrorKind,
    /// Source location (if available)
    pub span: Option<Span>,
    /// Human-readable error message
    pub message: String,
}

/// The kind of error that occurred
#[derive(Debug, Clone, PartialEq)]
pub enum ErrorKind {
    /// Syntax error from the parser
    Syntax(SyntaxError),
    /// Nesting depth exceeded
    NestingDepthExceeded { depth: usize, max: usize },
    /// Writer error (from CelWriter implementation)
    WriterError(String),
}

/// Syntax error details
#[derive(Debug, Clone, PartialEq)]
pub struct SyntaxError {
    /// What was expected
    pub expected: String,
    /// What was found (if available)
    pub found: Option<String>,
    /// Position in the input
    pub position: usize,
}

impl Error {
    /// Create a new error
    pub fn new(kind: ErrorKind, message: String) -> Self {
        Self {
            kind,
            span: None,
            message,
        }
    }

    /// Add span information to the error
    pub fn with_span(mut self, span: Span) -> Self {
        self.span = Some(span);
        self
    }

    /// Create a syntax error
    pub fn syntax(message: String, position: usize) -> Self {
        Self {
            kind: ErrorKind::Syntax(SyntaxError {
                expected: String::new(),
                found: None,
                position,
            }),
            span: Some(Span::new(position, position)),
            message,
        }
    }

    /// Create a nesting depth error
    pub fn nesting_depth(depth: usize, max: usize) -> Self {
        Self {
            kind: ErrorKind::NestingDepthExceeded { depth, max },
            span: None,
            message: format!(
                "Nesting depth {depth} exceeds maximum of {max} (CEL spec requires 12, we support {max})"
            ),
        }
    }

    /// Create an invalid escape sequence error
    pub fn invalid_escape(message: String) -> Self {
        Self {
            kind: ErrorKind::Syntax(SyntaxError {
                expected: String::new(),
                found: None,
                position: 0,
            }),
            span: None,
            message: format!("Invalid escape sequence: {message}"),
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.message)?;

        // Add span information if available
        if let Some(span) = &self.span {
            write!(f, " at {}..{}", span.start, span.end)?;
        }

        Ok(())
    }
}

impl std::error::Error for Error {}

/// Convert from pest parsing errors
impl From<pest::error::Error<Rule>> for Error {
    fn from(err: pest::error::Error<Rule>) -> Self {
        use pest::error::ErrorVariant;

        let message = format!("{err}");
        let position = match err.location {
            pest::error::InputLocation::Pos(pos) => pos,
            pest::error::InputLocation::Span((start, _)) => start,
        };

        match err.variant {
            ErrorVariant::ParsingError {
                positives,
                negatives,
            } => {
                let expected: String = positives
                    .iter()
                    .map(|r| format!("{r:?}"))
                    .chain(negatives.iter().map(|r| format!("not {r:?}")))
                    .collect::<Vec<_>>()
                    .join(", ");

                Self {
                    kind: ErrorKind::Syntax(SyntaxError {
                        expected,
                        found: None,
                        position,
                    }),
                    span: Some(Span::new(position, position)),
                    message,
                }
            }
            ErrorVariant::CustomError { message: msg } => {
                // Check if this is our nesting depth error
                if msg.contains("Nesting depth") && msg.contains("exceeds maximum") {
                    // Extract depth and max from message if possible
                    // Message format: "Nesting depth N exceeds maximum of M ..."
                    let parts: Vec<&str> = msg.split_whitespace().collect();
                    let depth = parts
                        .iter()
                        .position(|&s| s == "depth")
                        .and_then(|i| parts.get(i + 1))
                        .and_then(|s| s.parse().ok())
                        .unwrap_or(0);
                    let max = parts
                        .iter()
                        .position(|&s| s == "of")
                        .and_then(|i| parts.get(i + 1))
                        .and_then(|s| s.parse().ok())
                        .unwrap_or(0);

                    Self {
                        kind: ErrorKind::NestingDepthExceeded { depth, max },
                        span: Some(Span::new(position, position)),
                        message: msg,
                    }
                } else {
                    // We only emit NestingDepthExceeded as custom errors during parsing,
                    // so this branch should never be reached. We handle it defensively
                    // as a syntax error since it occurs during parsing, not writing.
                    Self {
                        kind: ErrorKind::Syntax(SyntaxError {
                            expected: String::new(),
                            found: None,
                            position,
                        }),
                        span: Some(Span::new(position, position)),
                        message: msg,
                    }
                }
            }
        }
    }
}

/// Result type alias for CEL parser operations
pub type Result<T> = std::result::Result<T, Error>;

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
            let err = Error::syntax("unexpected token".to_string(), 5);
            let display = format!("{err}");
            assert!(display.contains("unexpected token"));
            assert!(display.contains("5..5"));
        },

        test_nesting_depth_error: {
            let err = Error::nesting_depth(129, 128);
            assert!(matches!(
                err.kind,
                ErrorKind::NestingDepthExceeded { depth: 129, max: 128 }
            ));
        },

        test_error_with_span: {
            let err = Error::new(
                ErrorKind::NestingDepthExceeded { depth: 10, max: 5 },
                "Test error".to_string(),
            )
            .with_span(Span::new(10, 15));

            assert_eq!(err.span, Some(Span::new(10, 15)));
            let display = format!("{err}");
            assert!(display.contains("10..15"));
        },
    }
}
