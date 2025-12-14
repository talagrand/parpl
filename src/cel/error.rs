// Error types for the CEL parser
//
// This module defines error types for all phases of CEL processing:
// - Parsing errors (syntax errors from pest)
// - AST construction errors
// - Evaluation errors (runtime errors)
// - Type errors (if type checking is enabled)
//
// By centralizing error handling, we avoid exposing pest's error types
// throughout the codebase and provide consistent error reporting.

use crate::cel::{ast::Span, parser::Rule};
use std::fmt;

/// Main error type for all CEL parser operations
#[derive(Debug, Clone, PartialEq)]
pub struct Error {
    /// The phase where the error occurred
    pub phase: Phase,
    /// The kind of error
    pub kind: ErrorKind,
    /// Source location (if available)
    pub span: Option<Span>,
    /// Human-readable error message
    pub message: String,
}

/// The phase of processing where an error occurred
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Phase {
    /// Error during parsing (syntax error)
    Parsing,
    /// Error during AST construction
    AstConstruction,
    /// Error during evaluation (runtime error)
    Evaluation,
    /// Error during type checking
    TypeChecking,
}

/// The kind of error that occurred
#[derive(Debug, Clone, PartialEq)]
pub enum ErrorKind {
    /// Syntax error from the parser
    Syntax(SyntaxError),
    /// Nesting depth exceeded
    NestingDepthExceeded { depth: usize, max: usize },
    /// Call limit exceeded (DoS protection)
    CallLimitExceeded,
    /// Invalid escape sequence in string literal
    InvalidEscape { message: String },
    /// Invalid numeric literal
    InvalidNumber { literal: String },
    /// Undefined variable reference
    UndefinedVariable { name: String },
    /// Type mismatch during evaluation
    TypeMismatch { expected: String, got: String },
    /// Division by zero
    DivisionByZero,
    /// Index out of bounds
    IndexOutOfBounds { index: i64, length: usize },
    /// Invalid member access
    InvalidMember { type_name: String, member: String },
    /// Function not found
    UndefinedFunction { name: String },
    /// Wrong number of arguments
    ArgumentCount { expected: usize, got: usize },
    /// Custom error (for extension points)
    Custom(String),
}

/// Syntax error details
#[derive(Debug, Clone, PartialEq)]
pub struct SyntaxError {
    /// What was expected
    pub expected: Vec<String>,
    /// What was found (if available)
    pub found: Option<String>,
    /// Position in the input
    pub position: usize,
}

impl Error {
    /// Create a new error
    pub fn new(phase: Phase, kind: ErrorKind, message: String) -> Self {
        Self {
            phase,
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
            phase: Phase::Parsing,
            kind: ErrorKind::Syntax(SyntaxError {
                expected: vec![],
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
            phase: Phase::Parsing,
            kind: ErrorKind::NestingDepthExceeded { depth, max },
            span: None,
            message: format!(
                "Nesting depth {} exceeds maximum of {} (CEL spec requires 12, we support {})",
                depth, max, max
            ),
        }
    }

    /// Create an undefined variable error
    pub fn undefined_variable(name: String, span: Span) -> Self {
        Self {
            phase: Phase::Evaluation,
            kind: ErrorKind::UndefinedVariable { name: name.clone() },
            span: Some(span),
            message: format!("Undefined variable: {}", name),
        }
    }

    /// Create a type mismatch error
    pub fn type_mismatch(expected: String, got: String, span: Span) -> Self {
        Self {
            phase: Phase::Evaluation,
            kind: ErrorKind::TypeMismatch {
                expected: expected.clone(),
                got: got.clone(),
            },
            span: Some(span),
            message: format!("Type mismatch: expected {}, got {}", expected, got),
        }
    }

    /// Create an invalid number error
    pub fn invalid_number(literal: String) -> Self {
        Self {
            phase: Phase::AstConstruction,
            kind: ErrorKind::InvalidNumber {
                literal: literal.clone(),
            },
            span: None,
            message: format!("Invalid number: {}", literal),
        }
    }

    /// Create an invalid escape sequence error
    pub fn invalid_escape(message: String) -> Self {
        Self {
            phase: Phase::AstConstruction,
            kind: ErrorKind::InvalidEscape {
                message: message.clone(),
            },
            span: None,
            message: format!("Invalid escape sequence: {}", message),
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Format: [Phase] message
        write!(f, "[{:?}] {}", self.phase, self.message)?;

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

        let message = format!("{}", err);
        let position = match err.location {
            pest::error::InputLocation::Pos(pos) => pos,
            pest::error::InputLocation::Span((start, _)) => start,
        };

        match err.variant {
            ErrorVariant::ParsingError {
                positives,
                negatives,
            } => {
                let expected: Vec<String> = positives
                    .iter()
                    .map(|r| format!("{:?}", r))
                    .chain(negatives.iter().map(|r| format!("not {:?}", r)))
                    .collect();

                Self {
                    phase: Phase::Parsing,
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
                        phase: Phase::Parsing,
                        kind: ErrorKind::NestingDepthExceeded { depth, max },
                        span: Some(Span::new(position, position)),
                        message: msg,
                    }
                } else {
                    Self {
                        phase: Phase::Parsing,
                        kind: ErrorKind::Custom(msg.clone()),
                        span: Some(Span::new(position, position)),
                        message: msg,
                    }
                }
            }
        }
    }
}

impl fmt::Display for Phase {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Phase::Parsing => write!(f, "Parsing"),
            Phase::AstConstruction => write!(f, "AST Construction"),
            Phase::Evaluation => write!(f, "Evaluation"),
            Phase::TypeChecking => write!(f, "Type Checking"),
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
            let display = format!("{}", err);
            assert!(display.contains("Parsing"));
            assert!(display.contains("unexpected token"));
            assert!(display.contains("5..5"));
        },

        test_nesting_depth_error: {
            let err = Error::nesting_depth(129, 128);
            assert_eq!(err.phase, Phase::Parsing);
            assert!(matches!(
                err.kind,
                ErrorKind::NestingDepthExceeded { depth: 129, max: 128 }
            ));
        },

        test_undefined_variable_error: {
            let err = Error::undefined_variable("x".to_string(), Span::new(10, 11));
            assert_eq!(err.phase, Phase::Evaluation);
            assert!(err.message.contains("Undefined variable: x"));
        },

        test_type_mismatch_error: {
            let err = Error::type_mismatch("int".to_string(), "string".to_string(), Span::new(5, 10));
            assert_eq!(err.phase, Phase::Evaluation);
            assert!(err.message.contains("expected int, got string"));
        },

        test_error_with_span: {
            let err = Error::new(
                Phase::Evaluation,
                ErrorKind::DivisionByZero,
                "Division by zero".to_string(),
            )
            .with_span(Span::new(10, 15));

            assert_eq!(err.span, Some(Span::new(10, 15)));
            let display = format!("{}", err);
            assert!(display.contains("10..15"));
        },
    }
}
