use crate::{ParseError, Unsupported};
use crate::ast::{Span, Syntax};
use crate::lex::{
    FiniteReal, FiniteRealKind, Lexer, NumberLiteral, NumberRadix, NumberValue, RealRepr,
    SpannedToken, Token,
};
use std::iter::Peekable;

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    /// Numbers (integers only)
    Number(i64),
    /// Symbols (identifiers)
    Symbol(String),
    /// String literals
    String(String),
    /// Boolean values
    Bool(bool),
    /// Lists (including proper and improper lists, empty list represents nil)
    List(Vec<Syntax<Value>>),
}

pub struct MiniReader<'a> {
    lexer: Peekable<Lexer<'a>>,
}

impl<'a> MiniReader<'a> {
    pub fn new(source: &'a str) -> Self {
        let lexer = crate::lex::lex_with_config(
            source,
            crate::lex::LexConfig {
                // MiniReader intentionally does not support fold-case
                // semantics or directives.
                enable_fold_case: false,
            },
        );
        Self {
            lexer: lexer.peekable(),
        }
    }

    fn peek(&mut self) -> Result<Option<&SpannedToken<'a>>, ParseError> {
        match self.lexer.peek() {
            Some(Ok(token)) => Ok(Some(token)),
            Some(Err(e)) => Err(e.clone()),
            None => Ok(None),
        }
    }

    fn next(&mut self) -> Result<Option<SpannedToken<'a>>, ParseError> {
        match self.lexer.next() {
            Some(Ok(token)) => Ok(Some(token)),
            Some(Err(e)) => Err(e),
            None => Ok(None),
        }
    }

    pub fn parse_value(&mut self) -> Result<Syntax<Value>, ParseError> {
        loop {
            let token = self.next()?.ok_or(ParseError::Incomplete)?;

            match token.value {
                Token::DatumComment => {
                    // Recursively parse the next datum and discard it
                    let _ = self.parse_value()?;
                    continue;
                }
                Token::Boolean(b) => {
                    return Ok(Syntax::new(token.span, Value::Bool(b)));
                }
                Token::Identifier(s) => {
                    return Ok(Syntax::new(token.span, Value::Symbol(s.to_string())));
                }
                Token::String(s) => {
                    return Ok(Syntax::new(token.span, Value::String(s.into_owned())));
                }
                Token::Number(n) => return self.parse_number(n, token.span),
                Token::LParen => return self.parse_list(token.span),
                Token::Quote => {
                    // Expand 'x to (quote x)
                    let datum = self.parse_value()?;
                    let quote = Syntax::new(token.span, Value::Symbol("quote".to_string()));
                    let span = token.span.merge(datum.span);
                    return Ok(Syntax::new(span, Value::List(vec![quote, datum])));
                }
                Token::VectorStart => {
                    return Err(ParseError::unsupported(token.span, Unsupported::Vectors));
                }
                Token::ByteVectorStart => {
                    return Err(ParseError::unsupported(
                        token.span,
                        Unsupported::Bytevectors,
                    ));
                }
                Token::RParen => {
                    return Err(ParseError::syntax(token.span, "datum", "unexpected ')'"));
                }
                Token::Dot => {
                    return Err(ParseError::syntax(token.span, "datum", "unexpected '.'"));
                }
                Token::Comma | Token::CommaAt | Token::Backquote => {
                    return Err(ParseError::unsupported(
                        token.span,
                        Unsupported::Quasiquote,
                    ));
                }
                Token::LabelDef(_) | Token::LabelRef(_) => {
                    return Err(ParseError::unsupported(token.span, Unsupported::Labels));
                }
                Token::Character(_) => {
                    return Err(ParseError::unsupported(
                        token.span,
                        Unsupported::Characters,
                    ));
                }
            }
        }
    }

    fn parse_list(&mut self, start_span: Span) -> Result<Syntax<Value>, ParseError> {
        let mut elements: Vec<Syntax<Value>> = Vec::new();
        let mut end_span = start_span;
        loop {
            let peeked = self.peek()?;
            match peeked {
                Some(t) => match t.value {
                    Token::RParen => {
                        let closing = self.next()?.ok_or(ParseError::Incomplete)?;
                        end_span = closing.span;
                        return Ok(Syntax::new(
                            start_span.merge(end_span),
                            Value::List(elements),
                        ));
                    }
                    Token::Dot => {
                        return Err(ParseError::unsupported(
                            t.span,
                            Unsupported::ImproperLists,
                        ));
                    }
                    Token::DatumComment => {
                        // We must handle datum comments here to support lists ending with a comment,
                        // e.g. `(1 2 #; 3)`. If we delegated to `parse_value`, it would consume
                        // the comment and then fail to find a value before the closing `)`.
                        self.next()?; // consume #;
                        let _ = self.parse_value()?; // parse and discard
                    }
                    _ => {
                        elements.push(self.parse_value()?);
                    }
                },
                None => return Err(ParseError::Incomplete),
            }
        }
    }

    fn parse_number(&self, n: NumberLiteral, span: Span) -> Result<Syntax<Value>, ParseError> {
        match n.kind.value {
            NumberValue::Real(RealRepr::Finite(FiniteReal {
                kind: FiniteRealKind::Integer,
                spelling,
            })) => {
                let radix = match n.kind.radix {
                    NumberRadix::Binary => 2,
                    NumberRadix::Octal => 8,
                    NumberRadix::Decimal => 10,
                    NumberRadix::Hexadecimal => 16,
                };

                let (sign, digits) = if let Some(stripped) = spelling.strip_prefix('+') {
                    (1, stripped)
                } else if let Some(stripped) = spelling.strip_prefix('-') {
                    (-1, stripped)
                } else {
                    (1, spelling)
                };

                let val = u64::from_str_radix(digits, radix).map_err(|_| {
                    ParseError::unsupported(
                        span,
                        Unsupported::IntegerOverflowOrInvalidFormat,
                    )
                })?;

                let result = if sign == 1 {
                    i64::try_from(val).map_err(|_| {
                        ParseError::unsupported(span, Unsupported::IntegerOverflow)
                    })?
                } else {
                    if val > i64::MIN.unsigned_abs() {
                        return Err(ParseError::unsupported(
                            span,
                            Unsupported::IntegerOverflow,
                        ));
                    }
                    (val as i64).wrapping_neg()
                };

                Ok(Syntax::new(span, Value::Number(result)))
            }
            _ => Err(ParseError::unsupported(span, Unsupported::NonIntegerNumber)),
        }
    }
}

pub fn read(source: &str) -> Result<Syntax<Value>, ParseError> {
    let mut reader = MiniReader::new(source);
    reader.parse_value()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ParseError, Unsupported};

    struct TestCase {
        name: &'static str,
        input: &'static str,
        expected: Expected<ValueMatcher>,
    }

    enum Expected<T> {
        Success(T),
        Error(ErrorMatcher),
    }

    #[derive(Debug)]
    enum ValueMatcher {
        Number(i64),
        Symbol(&'static str),
        Str(&'static str),
        Bool(bool),
        List(Vec<ValueMatcher>),
    }

    #[derive(Debug)]
    enum ErrorMatcher {
        Incomplete,
        Syntax(&'static str),
        Unsupported(Unsupported),
    }

    impl TestCase {
        fn run(&self) {
            let result = read(self.input);
            match &self.expected {
                Expected::Success(matcher) => {
                    let syntax = result
                        .unwrap_or_else(|e| panic!("{}: expected success, got {:?}", self.name, e));
                    matcher.check(&syntax.value, self.name);
                }
                Expected::Error(matcher) => {
                    let err =
                        result.expect_err(&format!("{}: expected error, got success", self.name));
                    matcher.check(&err, self.name);
                }
            }
        }
    }

    impl ValueMatcher {
        fn check(&self, value: &Value, test_name: &str) {
            match (self, value) {
                (ValueMatcher::Number(e), Value::Number(a)) => {
                    assert_eq!(e, a, "{}: number mismatch", test_name)
                }
                (ValueMatcher::Symbol(e), Value::Symbol(a)) => {
                    assert_eq!(e, a, "{}: symbol mismatch", test_name)
                }
                (ValueMatcher::Str(e), Value::String(a)) => {
                    assert_eq!(e, a, "{}: string mismatch", test_name)
                }
                (ValueMatcher::Bool(e), Value::Bool(a)) => {
                    assert_eq!(e, a, "{}: bool mismatch", test_name)
                }
                (ValueMatcher::List(elems), Value::List(actual)) => {
                    assert_eq!(
                        elems.len(),
                        actual.len(),
                        "{}: list length mismatch",
                        test_name
                    );
                    for (e, a) in elems.iter().zip(actual.iter()) {
                        e.check(&a.value, test_name);
                    }
                }
                _ => panic!(
                    "{}: value type mismatch. Expected {:?}, got {:?}",
                    test_name, self, value
                ),
            }
        }
    }

    impl ErrorMatcher {
        fn check(&self, err: &ParseError, test_name: &str) {
            match (self, err) {
                (ErrorMatcher::Incomplete, ParseError::Incomplete) => {}
                (ErrorMatcher::Syntax(expected_msg), ParseError::Syntax { message, .. }) => {
                    assert_eq!(
                        expected_msg, message,
                        "{}: syntax message mismatch",
                        test_name
                    )
                }
                (
                    ErrorMatcher::Unsupported(expected_feature),
                    ParseError::Unsupported { feature, .. },
                ) => {
                    assert_eq!(
                        expected_feature, feature,
                        "{}: unsupported feature mismatch",
                        test_name
                    )
                }
                _ => panic!(
                    "{}: error mismatch. Expected {:?}, got {:?}",
                    test_name, self, err
                ),
            }
        }
    }

    fn list_matcher(elements: Vec<ValueMatcher>) -> ValueMatcher {
        ValueMatcher::List(elements)
    }

    #[test]
    fn run_all_tests() {
        use Expected::{Error, Success};

        let cases = vec![
            // Basic atoms
            TestCase {
                name: "number_simple",
                input: "123",
                expected: Success(ValueMatcher::Number(123)),
            },
            TestCase {
                name: "number_negative",
                input: "-42",
                expected: Success(ValueMatcher::Number(-42)),
            },
            TestCase {
                name: "symbol_simple",
                input: "abc",
                expected: Success(ValueMatcher::Symbol("abc")),
            },
            TestCase {
                name: "string_simple",
                input: "\"hello\"",
                expected: Success(ValueMatcher::Str("hello")),
            },
            TestCase {
                name: "bool_true",
                input: "#t",
                expected: Success(ValueMatcher::Bool(true)),
            },
            TestCase {
                name: "bool_false",
                input: "#f",
                expected: Success(ValueMatcher::Bool(false)),
            },
            // Lists
            TestCase {
                name: "list_proper",
                input: "(1 2 3)",
                expected: Success(list_matcher(vec![
                    ValueMatcher::Number(1),
                    ValueMatcher::Number(2),
                    ValueMatcher::Number(3),
                ])),
            },
            // Datum comments
            TestCase {
                name: "datum_comment_prefix",
                input: "#; 1 2",
                expected: Success(ValueMatcher::Number(2)),
            },
            TestCase {
                name: "datum_comment_in_list",
                input: "(1 #; 2 3)",
                expected: Success(list_matcher(vec![
                    ValueMatcher::Number(1),
                    ValueMatcher::Number(3),
                ])),
            },
            // Quote expansion
            TestCase {
                name: "quote_simple",
                input: "'foo",
                expected: Success(list_matcher(vec![
                    ValueMatcher::Symbol("quote"),
                    ValueMatcher::Symbol("foo"),
                ])),
            },
            // Unsupported features
            TestCase {
                name: "unsupported_vector",
                input: "#(1 2)",
                expected: Error(ErrorMatcher::Unsupported(Unsupported::Vectors)),
            },
            TestCase {
                name: "unsupported_float",
                input: "1.5",
                expected: Error(ErrorMatcher::Unsupported(Unsupported::NonIntegerNumber)),
            },
            // Syntax errors
            TestCase {
                name: "syntax_unexpected_rparen",
                input: ")",
                expected: Error(ErrorMatcher::Syntax("unexpected ')'")),
            },
            // Number edge cases
            TestCase {
                name: "number_i64_max",
                input: "9223372036854775807",
                expected: Success(ValueMatcher::Number(i64::MAX)),
            },
            TestCase {
                name: "number_i64_min",
                input: "-9223372036854775808",
                expected: Success(ValueMatcher::Number(i64::MIN)),
            },
            TestCase {
                name: "number_overflow_max_plus_one",
                input: "9223372036854775808",
                expected: Error(ErrorMatcher::Unsupported(Unsupported::IntegerOverflow)),
            },
            TestCase {
                name: "number_overflow_min_minus_one",
                input: "-9223372036854775809",
                expected: Error(ErrorMatcher::Unsupported(Unsupported::IntegerOverflow)),
            },
            // Fold-case directives are not supported in MiniReader; they
            // should be reported as unsupported features rather than
            // silently ignored.
            TestCase {
                name: "unsupported_fold_case_directive_on",
                input: "#!fold-case 1",
                expected: Error(ErrorMatcher::Unsupported(Unsupported::FoldCaseDirectives)),
            },
            TestCase {
                name: "unsupported_fold_case_directive_off",
                input: "#!no-fold-case 1",
                expected: Error(ErrorMatcher::Unsupported(Unsupported::FoldCaseDirectives)),
            },
        ];

        for case in cases {
            case.run();
        }
    }
}
