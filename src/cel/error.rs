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
    /// Source location (if available)
    pub span: Option<Span>,
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

    /// Syntax error from the parser
    Syntax(SyntaxError),

    /// A safety limit was exceeded.
    LimitExceeded(crate::LimitExceeded),

    /// Writer error (from CelWriter implementation)
    WriterError(WriterErrorInner),
}

/// Syntax error details.
///
/// This structure matches the Scheme parser's `Error::Syntax` variant
/// for API consistency across parsers.
#[derive(Debug, Clone, PartialEq)]
pub struct SyntaxError {
    /// Source location of the error.
    ///
    /// For CEL (pest-based parser), this spans from the error position
    /// to the end of input, since pest reports cursor positions rather
    /// than token spans.
    pub span: Span,
    /// The grammar nonterminal being parsed when the error occurred.
    ///
    /// For CEL, this is derived from pest's expected rules (e.g., "primary").
    pub nonterminal: String,
    /// Human-readable description of the error.
    pub message: String,
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

    /// Create a syntax error.
    ///
    /// The span extends from `position` to `input_len` since we don't know
    /// the problematic token's width.
    pub fn syntax(message: String, position: usize, input_len: usize) -> Self {
        let span = Span::new(position, input_len);
        Self {
            kind: ErrorKind::Syntax(SyntaxError {
                span,
                nonterminal: String::new(),
                message: message.clone(),
            }),
            span: Some(span),
            message,
        }
    }

    /// Create a nesting depth error
    pub fn nesting_depth(depth: usize, max: usize) -> Self {
        Self {
            kind: ErrorKind::LimitExceeded(crate::LimitExceeded::NestingDepth),
            span: None,
            message: format!(
                "Nesting depth {depth} exceeds maximum of {max} (CEL spec requires 12, we support {max})"
            ),
        }
    }

    /// Create an invalid escape sequence error.
    ///
    /// Position information is not available for escape sequence errors
    /// since they occur during literal parsing after the main parse.
    pub fn invalid_escape(message: String) -> Self {
        let msg = format!("Invalid escape sequence: {message}");
        Self {
            kind: ErrorKind::Syntax(SyntaxError {
                span: Span::new(0, 0),
                nonterminal: "<escape-sequence>".to_string(),
                message: msg.clone(),
            }),
            span: None,
            message: msg,
        }
    }

    /// Create an incomplete input error.
    ///
    /// This indicates the parser consumed all input but expected more tokens.
    pub fn incomplete() -> Self {
        Self {
            kind: ErrorKind::Incomplete,
            span: None,
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
                    kind: ErrorKind::Syntax(SyntaxError {
                        span,
                        nonterminal,
                        message: message.clone(),
                    }),
                    span: Some(span),
                    message,
                }
            }
            ErrorVariant::CustomError { message: msg } => {
                // Check if this is our nesting depth error
                if msg.contains("Nesting depth") && msg.contains("exceeds maximum") {
                    Self {
                        kind: ErrorKind::LimitExceeded(crate::LimitExceeded::NestingDepth),
                        span: Some(span),
                        message: msg,
                    }
                } else {
                    // Defensive fallback for unexpected custom errors
                    Self {
                        kind: ErrorKind::Syntax(SyntaxError {
                            span,
                            nonterminal: String::new(),
                            message: msg.clone(),
                        }),
                        span: Some(span),
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

        // Add span information if available
        if let Some(span) = &self.span {
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
                    if let ErrorKind::Syntax(syn) = &err.kind {
                        assert!(
                            syn.nonterminal.contains(expected_contains)
                                || syn.nonterminal == expected_contains,
                            "for {input:?}: expected nonterminal containing {expected_contains:?}, got {:?}",
                            syn.nonterminal
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
            let err = Error::nesting_depth(129, 128);
            assert!(matches!(
                err.kind,
                ErrorKind::LimitExceeded(crate::LimitExceeded::NestingDepth)
            ));
        },

        test_error_with_span: {
            let err = Error::new(
                ErrorKind::LimitExceeded(crate::LimitExceeded::NestingDepth),
                "Test error".to_string(),
            )
            .with_span(Span::new(10, 15));

            assert_eq!(err.span, Some(Span::new(10, 15)));
            let display = format!("{err}");
            assert!(display.contains("10..15"));
        },
    }
}
