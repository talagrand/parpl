use crate::{
    Error, NoOpInterner, Span,
    scheme::{
        lex::{self, FiniteRealKind, NumberExactness, Sign},
        traits::{DatumWriter, SchemeNumberOps},
        unsupported,
    },
};

#[derive(Debug, Clone, PartialEq)]
pub enum MiniDatum {
    /// Numbers (integers only)
    Number(i64),
    /// Symbols (identifiers)
    Symbol(String),
    /// String literals
    String(String),
    /// Boolean values
    Bool(bool),
    /// Lists (proper lists only)
    List(Vec<MiniDatum>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MiniNumberOps;

impl SchemeNumberOps for MiniNumberOps {
    type Number = i64;

    fn from_literal(lit: &lex::NumberLiteral<'_>, span: Span) -> Result<Self::Number, Error> {
        // MiniScheme only supports integers.
        // Logic adapted from minireader.rs parse_number

        match lit.kind.exactness {
            NumberExactness::Unspecified => {}
            NumberExactness::Exact | NumberExactness::Inexact => {
                return Err(Error::unsupported(
                    span,
                    unsupported::NUMERIC_REPRESENTATION,
                ));
            }
        }

        match &lit.kind.value {
            lex::NumberValue::Real(real) => match &real.magnitude {
                lex::RealMagnitude::Finite(finite) if finite.kind == FiniteRealKind::Integer => {
                    let radix = lit.kind.radix;
                    let val = match u64::from_str_radix(finite.spelling, radix) {
                        Ok(v) => v,
                        Err(e) => {
                            let kind = match e.kind() {
                                std::num::IntErrorKind::PosOverflow
                                | std::num::IntErrorKind::NegOverflow => {
                                    unsupported::NUMERIC_OVERFLOW
                                }
                                _ => unsupported::NUMERIC_REPRESENTATION,
                            };
                            return Err(Error::unsupported(span, kind));
                        }
                    };

                    let result = match real.effective_sign() {
                        Sign::Positive => i64::try_from(val)
                            .map_err(|_| Error::unsupported(span, unsupported::NUMERIC_OVERFLOW))?,
                        Sign::Negative => {
                            if val > i64::MIN.unsigned_abs() {
                                return Err(Error::unsupported(
                                    span,
                                    unsupported::NUMERIC_OVERFLOW,
                                ));
                            }
                            (val as i64).wrapping_neg()
                        }
                    };

                    Ok(result)
                }
                _ => Err(Error::unsupported(
                    span,
                    unsupported::NUMERIC_REPRESENTATION,
                )),
            },
            _ => Err(Error::unsupported(
                span,
                unsupported::NUMERIC_REPRESENTATION,
            )),
        }
    }

    fn eqv(a: &Self::Number, b: &Self::Number) -> bool {
        a == b
    }
}

#[derive(Default)]
pub struct MiniDatumWriter {
    interner: NoOpInterner,
}

impl DatumWriter for MiniDatumWriter {
    type Output = MiniDatum;
    type Error = Error;
    type Interner = NoOpInterner;
    type StringId = String;
    type NumberOps = MiniNumberOps;

    fn interner(&mut self) -> &mut Self::Interner {
        &mut self.interner
    }

    fn bool(&mut self, v: bool, _s: Span) -> Result<Self::Output, Self::Error> {
        Ok(MiniDatum::Bool(v))
    }

    fn number(&mut self, v: i64, _s: Span) -> Result<Self::Output, Self::Error> {
        Ok(MiniDatum::Number(v))
    }

    fn char(&mut self, _v: char, s: Span) -> Result<Self::Output, Self::Error> {
        Err(Error::unsupported(s, unsupported::CHARACTER))
    }

    fn string(&mut self, v: Self::StringId, _s: Span) -> Result<Self::Output, Self::Error> {
        Ok(MiniDatum::String(v))
    }

    fn symbol(&mut self, v: Self::StringId, _s: Span) -> Result<Self::Output, Self::Error> {
        Ok(MiniDatum::Symbol(v))
    }

    fn bytevector(&mut self, _v: &[u8], s: Span) -> Result<Self::Output, Self::Error> {
        Err(Error::unsupported(s, unsupported::BYTEVECTOR))
    }

    fn list<I>(&mut self, iter: I, _s: Span) -> Result<Self::Output, Self::Error>
    where
        I: IntoIterator<Item = Self::Output>,
        I::IntoIter: ExactSizeIterator,
    {
        let elements: Vec<_> = iter.into_iter().collect();
        Ok(MiniDatum::List(elements))
    }

    fn improper_list<I>(
        &mut self,
        _head: I,
        _tail: Self::Output,
        s: Span,
    ) -> Result<Self::Output, Self::Error>
    where
        I: IntoIterator<Item = Self::Output>,
        I::IntoIter: ExactSizeIterator,
    {
        Err(Error::unsupported(s, unsupported::IMPROPER_LIST))
    }

    fn vector<I>(&mut self, _iter: I, s: Span) -> Result<Self::Output, Self::Error>
    where
        I: IntoIterator<Item = Self::Output>,
        I::IntoIter: ExactSizeIterator,
    {
        Err(Error::unsupported(s, unsupported::VECTOR))
    }

    fn labeled(
        &mut self,
        _id: u64,
        _inner: Self::Output,
        s: Span,
    ) -> Result<Self::Output, Self::Error> {
        Err(Error::unsupported(s, unsupported::LABEL))
    }

    fn label_ref(&mut self, _id: u64, s: Span) -> Result<Self::Output, Self::Error> {
        Err(Error::unsupported(s, unsupported::LABEL))
    }

    fn copy(&mut self, source: &Self::Output) -> Result<Self::Output, Self::Error> {
        Ok(source.clone())
    }
}

pub fn read(source: &str) -> Result<MiniDatum, Error> {
    read_with_max_depth(source, 64)
}

pub fn read_with_max_depth(source: &str, max_depth: u32) -> Result<MiniDatum, Error> {
    let lexer = crate::scheme::lex::lex_with_config(
        source,
        crate::scheme::lex::LexConfig {
            reject_fold_case: true,
            reject_comments: true,
        },
    );
    let mut stream = crate::scheme::reader::TokenStream::new(lexer);
    let mut writer = MiniDatumWriter::default();
    stream
        .parse_with_max_depth(&mut writer, max_depth)
        .map(|(datum, _span)| datum)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Error, scheme::unsupported};

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
        Unsupported(&'static str),
    }

    impl TestCase {
        fn run(&self) {
            let result = read(self.input);
            match &self.expected {
                Expected::Success(matcher) => {
                    let value = result
                        .unwrap_or_else(|e| panic!("{}: expected success, got {:?}", self.name, e));
                    matcher.check(&value, self.name);
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
        fn check(&self, value: &MiniDatum, test_name: &str) {
            match (self, value) {
                (ValueMatcher::Number(e), MiniDatum::Number(a)) => {
                    assert_eq!(e, a, "{test_name}: number mismatch")
                }
                (ValueMatcher::Symbol(e), MiniDatum::Symbol(a)) => {
                    assert_eq!(e, a, "{test_name}: symbol mismatch")
                }
                (ValueMatcher::Str(e), MiniDatum::String(a)) => {
                    assert_eq!(e, a, "{test_name}: string mismatch")
                }
                (ValueMatcher::Bool(e), MiniDatum::Bool(a)) => {
                    assert_eq!(e, a, "{test_name}: bool mismatch")
                }
                (ValueMatcher::List(elems), MiniDatum::List(actual)) => {
                    assert_eq!(
                        elems.len(),
                        actual.len(),
                        "{test_name}: list length mismatch"
                    );
                    for (e, a) in elems.iter().zip(actual.iter()) {
                        e.check(a, test_name);
                    }
                }
                _ => {
                    panic!("{test_name}: MiniDatum type mismatch. Expected {self:?}, got {value:?}")
                }
            }
        }
    }

    impl ErrorMatcher {
        fn check(&self, err: &Error, test_name: &str) {
            match (self, err) {
                (ErrorMatcher::Incomplete, Error::Incomplete) => {}
                (ErrorMatcher::Syntax(expected_msg), Error::Syntax { message, .. }) => {
                    assert_eq!(
                        expected_msg, message,
                        "{test_name}: syntax message mismatch"
                    )
                }
                (ErrorMatcher::Unsupported(expected_kind), Error::Unsupported { kind, .. }) => {
                    assert_eq!(expected_kind, kind, "{test_name}: unsupported mismatch")
                }
                (ErrorMatcher::Unsupported(expected_kind), Error::WriterError { source, .. }) => {
                    // The generic reader wraps writer errors in WriterError.
                    // Check if the feature name is present in the message.
                    let kind_str = expected_kind.to_string();
                    let msg = source.to_string();
                    assert!(
                        msg.contains(&kind_str),
                        "{test_name}: expected WriterError containing {kind_str:?}, got {msg:?}"
                    )
                }
                _ => panic!("{test_name}: error mismatch. Expected {self:?}, got {err:?}"),
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
            // Datum comments are not supported by MiniReader when
            // `reject_comments` is enabled in the lexer configuration.
            TestCase {
                name: "datum_comment_prefix",
                input: "#; 1 2",
                expected: Error(ErrorMatcher::Unsupported(unsupported::COMMENT)),
            },
            TestCase {
                name: "datum_comment_in_list",
                input: "(1 #; 2 3)",
                expected: Error(ErrorMatcher::Unsupported(unsupported::COMMENT)),
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
            // Quasiquote/unquote forms are not supported
            // Unsupported features
            TestCase {
                name: "unsupported_vector",
                input: "#(1 2)",
                expected: Error(ErrorMatcher::Unsupported(unsupported::VECTOR)),
            },
            TestCase {
                name: "unsupported_float",
                input: "1.5",
                expected: Error(ErrorMatcher::Unsupported(
                    unsupported::NUMERIC_REPRESENTATION,
                )),
            },
            TestCase {
                name: "unsupported_exact_number",
                input: "#e42",
                expected: Error(ErrorMatcher::Unsupported(
                    unsupported::NUMERIC_REPRESENTATION,
                )),
            },
            TestCase {
                name: "unsupported_inexact_number",
                input: "#i42",
                expected: Error(ErrorMatcher::Unsupported(
                    unsupported::NUMERIC_REPRESENTATION,
                )),
            },
            // Syntax errors
            TestCase {
                name: "syntax_unexpected_rparen",
                input: ")",
                expected: Error(ErrorMatcher::Syntax("unexpected token RParen")),
            },
            TestCase {
                name: "incomplete_list",
                input: "(1 2",
                expected: Error(ErrorMatcher::Incomplete),
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
                expected: Error(ErrorMatcher::Unsupported(unsupported::NUMERIC_OVERFLOW)),
            },
            TestCase {
                name: "number_overflow_min_minus_one",
                input: "-9223372036854775809",
                expected: Error(ErrorMatcher::Unsupported(unsupported::NUMERIC_OVERFLOW)),
            },
            // Fold-case directives are not supported in MiniReader; they
            // should be reported as unsupported features rather than
            // silently ignored.
            TestCase {
                name: "unsupported_fold_case_directive_on",
                input: "#!fold-case 1",
                expected: Error(ErrorMatcher::Unsupported(unsupported::FOLD_CASE_DIRECTIVE)),
            },
            TestCase {
                name: "unsupported_fold_case_directive_off",
                input: "#!no-fold-case 1",
                expected: Error(ErrorMatcher::Unsupported(unsupported::FOLD_CASE_DIRECTIVE)),
            },
        ];

        for case in cases {
            case.run();
        }
    }
}
