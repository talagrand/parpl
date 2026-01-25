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

/// Type alias for a boxed writer error.
pub type WriterErrorInner = Box<dyn std::error::Error + Send + Sync + 'static>;

/// Main error type for CEL parser operations
#[derive(Debug)]
pub struct Error {
    /// The kind of error
    pub kind: ErrorKind,
    /// Human-readable error message
    pub message: String,
}

/// The kind of error that occurred
#[derive(Debug)]
pub enum ErrorKind {
    /// The input ends in the middle of a grammatically valid construct
    /// and more characters are required to complete parsing.
    ///
    /// In a REPL, this is the cue to prompt the user for more input
    /// instead of reporting a hard error.
    ///
    /// Examples: `(1 + 2`, `[1, 2,`, `a ? b`
    Incomplete,

    /// The input ends in the middle of a token.
    ///
    /// Note: For CEL, this is is not emitted; incomplete expressions in the middle
    /// of tokens are reported as `Syntax` errors instead. Scheme supports this
    /// for streaming scenarions, but CEL operations are single-expressions, minimizing
    /// the value of streaming. (Internally, CEL combines lexing and parsing in one pass
    /// using pest, making it difficult to distinguish incomplete tokens from syntax errors.)
    IncompleteToken,

    /// A syntax error detected while lexing or parsing a particular
    /// nonterminal (for example, `<primary>`, `<expr>`, or `<literal>`).
    Syntax {
        /// Source location of the error.
        ///
        /// For CEL (pest-based parser), this spans from the error position
        /// to the end of input, since pest reports cursor positions rather
        /// than token spans.
        span: Span,
        /// The grammar nonterminal being parsed when the error occurred.
        ///
        /// For CEL, this is derived from pest's expected rules (e.g., `<primary>`).
        nonterminal: String,
        /// Human-readable description of the error.
        message: String,
    },

    /// A safety limit was exceeded.
    LimitExceeded {
        /// Source location where the limit was exceeded.
        span: Span,
        /// The specific limit that was exceeded.
        kind: crate::LimitExceeded,
    },

    /// Writer error (from CelWriter implementation).
    WriterError {
        /// Source location where the writer error occurred.
        span: Span,
        /// The underlying writer error.
        source: WriterErrorInner,
    },
}

impl Error {
    /// Create a new error
    pub fn new(kind: ErrorKind, message: String) -> Self {
        Self { kind, message }
    }

    /// Create a syntax error.
    ///
    /// The span extends from `position` to `input_len` since we don't know
    /// the problematic token's width.
    pub fn syntax(message: String, position: usize, input_len: usize) -> Self {
        let span = Span::new(position, input_len);
        Self {
            kind: ErrorKind::Syntax {
                span,
                nonterminal: String::new(),
                message: message.clone(),
            },
            message,
        }
    }

    /// Create a nesting depth error
    pub fn nesting_depth(span: Span, depth: usize, max: usize) -> Self {
        let message = format!(
            "Nesting depth {depth} exceeds maximum of {max} (CEL spec requires 12, we support {max})"
        );
        Self {
            kind: ErrorKind::LimitExceeded {
                span,
                kind: crate::LimitExceeded::NestingDepth {
                    message: message.clone(),
                },
            },
            message,
        }
    }

    /// Create an invalid escape sequence error.
    ///
    /// Position information is not available for escape sequence errors
    /// since they occur during literal parsing after the main parse.
    pub fn invalid_escape(message: String) -> Self {
        let msg = format!("Invalid escape sequence: {message}");
        Self {
            kind: ErrorKind::Syntax {
                span: Span::new(0, 0),
                nonterminal: "<escape-sequence>".to_string(),
                message: msg.clone(),
            },
            message: msg,
        }
    }

    /// Create an incomplete input error.
    ///
    /// This indicates the parser consumed all input but expected more tokens.
    pub fn incomplete() -> Self {
        Self {
            kind: ErrorKind::Incomplete,
            message: "input is incomplete; more data required".to_string(),
        }
    }

    /// Create an error from a pest parsing error, using input length to detect
    /// incomplete input.
    ///
    /// If the error position is at or beyond the input length, the parser
    /// consumed all input and still expected more, indicating incomplete input.
    pub fn from_pest_error(err: pest::error::Error<Rule>, input_len: usize) -> Self {
        use pest::error::ErrorVariant;

        let position = match err.location {
            pest::error::InputLocation::Pos(pos) => pos,
            pest::error::InputLocation::Span((start, _)) => start,
        };

        // If error is at end of input, it's incomplete (parser wanted more)
        if position >= input_len {
            return Self::incomplete();
        }

        // Span extends from error position to end of input
        let span = Span::new(position, input_len);
        let message = format!("{err}");

        match err.variant {
            ErrorVariant::ParsingError {
                positives,
                negatives,
            } => {
                // Format rules with angle brackets, converting pest built-ins to friendly names
                let format_rule = |r: &Rule| -> String {
                    let name = format!("{r:?}");
                    match name.as_str() {
                        "EOI" => "<end-of-input>".to_string(),
                        "SOI" => "<start-of-input>".to_string(),
                        _ => format!("<{name}>"),
                    }
                };

                let nonterminal: String = positives
                    .iter()
                    .map(format_rule)
                    .chain(negatives.iter().map(|r| format!("not {}", format_rule(r))))
                    .collect::<Vec<_>>()
                    .join(", ");

                Self {
                    kind: ErrorKind::Syntax {
                        span,
                        nonterminal,
                        message: message.clone(),
                    },
                    message,
                }
            }
            ErrorVariant::CustomError { message: msg } => {
                // Check if this is our nesting depth error
                if msg.contains("Nesting depth") && msg.contains("exceeds maximum") {
                    Self {
                        kind: ErrorKind::LimitExceeded {
                            span,
                            kind: crate::LimitExceeded::NestingDepth {
                                message: msg.clone(),
                            },
                        },
                        message: msg,
                    }
                } else {
                    // Defensive fallback for unexpected custom errors
                    Self {
                        kind: ErrorKind::Syntax {
                            span,
                            nonterminal: String::new(),
                            message: msg.clone(),
                        },
                        message: msg,
                    }
                }
            }
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.message)?;

        // Add span information if available from the error kind
        let span = match &self.kind {
            ErrorKind::Syntax { span, .. } => Some(span),
            ErrorKind::LimitExceeded { span, .. } => Some(span),
            ErrorKind::Incomplete | ErrorKind::IncompleteToken => None,
            ErrorKind::WriterError { span, .. } => Some(span),
        };
        if let Some(span) = span {
            write!(f, " at {}..{}", span.start, span.end)?;
        }

        Ok(())
    }
}

impl std::error::Error for Error {}

/// Result type alias for CEL parser operations
pub type Result<T> = std::result::Result<T, Error>;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cel::parser::{CelParser, Rule};
    use pest::Parser;

    #[test]
    fn test_nonterminal_format() {
        // Test that nonterminals use angle bracket format
        let bad_inputs = vec![
            (")", "<primary>"),                     // single rule
            ("foo bar", "<end-of-input>, <relop>"), // EOI converted + multiple rules
        ];

        for (input, expected_contains) in bad_inputs {
            match CelParser::parse(Rule::cel, input) {
                Ok(_) => panic!("expected error for {input:?}"),
                Err(e) => {
                    let err = Error::from_pest_error(e, input.len());
                    if let ErrorKind::Syntax { nonterminal, .. } = &err.kind {
                        assert!(
                            nonterminal.contains(expected_contains)
                                || nonterminal == expected_contains,
                            "for {input:?}: expected nonterminal containing {expected_contains:?}, got {nonterminal:?}"
                        );
                    } else {
                        panic!("expected syntax error");
                    }
                }
            }
        }
    }

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
            let err = Error::syntax("unexpected token".to_string(), 5, 10);
            let display = format!("{err}");
            assert!(display.contains("unexpected token"));
            assert!(display.contains("5..10"));  // span extends to input_len
        },

        test_nesting_depth_error: {
            let err = Error::nesting_depth(Span::new(0, 10), 129, 128);
            assert!(matches!(
                err.kind,
                ErrorKind::LimitExceeded { kind: crate::LimitExceeded::NestingDepth { .. }, .. }
            ));
        },

        test_limit_exceeded_span: {
            let err = Error::nesting_depth(Span::new(10, 15), 129, 128);
            let display = format!("{err}");
            assert!(display.contains("10..15"));
        },
    }
}
