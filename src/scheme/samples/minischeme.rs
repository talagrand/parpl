use crate::common::{Interner, Span};
use crate::scheme::datumtraits::{DatumInspector, DatumWriter, SchemeNumberOps};
use crate::scheme::lex::{self, FiniteRealKind, NumberExactness, Sign};
use crate::scheme::{ParseError, Unsupported};
use std::collections::HashMap;

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
    /// Lists (proper lists only)
    List(Vec<Value>),
}

/// A simple string ID.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct MiniStringId(u32);

// impl StringId for MiniStringId {}

/// A simple interner.
#[derive(Default)]
pub struct MiniInterner {
    map: HashMap<String, u32>,
    vec: Vec<String>,
}

impl Interner for MiniInterner {
    type Id = MiniStringId;

    fn intern(&mut self, text: &str) -> Self::Id {
        if let Some(&id) = self.map.get(text) {
            return MiniStringId(id);
        }
        let id = self.vec.len() as u32;
        self.vec.push(text.to_string());
        self.map.insert(text.to_string(), id);
        MiniStringId(id)
    }

    fn resolve(&self, id: Self::Id) -> &str {
        self.vec.get(id.0 as usize).map(|s| s.as_str()).unwrap()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MiniNumberOps;

impl SchemeNumberOps for MiniNumberOps {
    type Number = i64;

    fn from_literal(lit: &lex::NumberLiteral<'_>, span: Span) -> Result<Self::Number, ParseError> {
        // MiniScheme only supports integers.
        // Logic adapted from minireader.rs parse_number

        match lit.kind.exactness {
            NumberExactness::Unspecified => {}
            NumberExactness::Exact | NumberExactness::Inexact => {
                return Err(ParseError::unsupported(
                    span,
                    Unsupported::InvalidIntegerFormat,
                ));
            }
        }

        match &lit.kind.value {
            lex::NumberValue::Real(real) => match &real.magnitude {
                lex::RealMagnitude::Finite(finite) if finite.kind == FiniteRealKind::Integer => {
                    let radix = lit.kind.radix;
                    let val = match u64::from_str_radix(&finite.spelling, radix) {
                        Ok(v) => v,
                        Err(e) => {
                            let feature = match e.kind() {
                                std::num::IntErrorKind::PosOverflow
                                | std::num::IntErrorKind::NegOverflow => {
                                    Unsupported::IntegerOverflow
                                }
                                _ => Unsupported::InvalidIntegerFormat,
                            };
                            return Err(ParseError::unsupported(span, feature));
                        }
                    };

                    let result = match real.effective_sign() {
                        Sign::Positive => i64::try_from(val).map_err(|_| {
                            ParseError::unsupported(span, Unsupported::IntegerOverflow)
                        })?,
                        Sign::Negative => {
                            if val > i64::MIN.unsigned_abs() {
                                return Err(ParseError::unsupported(
                                    span,
                                    Unsupported::IntegerOverflow,
                                ));
                            }
                            (val as i64).wrapping_neg()
                        }
                    };

                    Ok(result)
                }
                _ => Err(ParseError::unsupported(span, Unsupported::NonIntegerNumber)),
            },
            _ => Err(ParseError::unsupported(span, Unsupported::NonIntegerNumber)),
        }
    }

    fn eqv(a: &Self::Number, b: &Self::Number) -> bool {
        a == b
    }
}

pub struct MiniWriter {
    interner: MiniInterner,
}

impl MiniWriter {
    pub fn new() -> Self {
        Self {
            interner: MiniInterner::default(),
        }
    }
}

impl DatumWriter for MiniWriter {
    type Output = Value;
    type Error = ParseError;
    type Interner = MiniInterner;
    type StringId = MiniStringId;
    type N = MiniNumberOps;

    fn interner(&mut self) -> &mut Self::Interner {
        &mut self.interner
    }

    fn bool(&mut self, v: bool, _s: Span) -> Result<Self::Output, Self::Error> {
        Ok(Value::Bool(v))
    }

    fn number(&mut self, v: i64, _s: Span) -> Result<Self::Output, Self::Error> {
        Ok(Value::Number(v))
    }

    fn char(&mut self, _v: char, s: Span) -> Result<Self::Output, Self::Error> {
        Err(ParseError::unsupported(s, Unsupported::Characters))
    }

    fn string(&mut self, v: Self::StringId, _s: Span) -> Result<Self::Output, Self::Error> {
        let str_val = self.interner.resolve(v).to_string();
        Ok(Value::String(str_val))
    }

    fn symbol(&mut self, v: Self::StringId, _s: Span) -> Result<Self::Output, Self::Error> {
        let sym_val = self.interner.resolve(v).to_string();
        Ok(Value::Symbol(sym_val))
    }

    fn bytevector(&mut self, _v: &[u8], s: Span) -> Result<Self::Output, Self::Error> {
        Err(ParseError::unsupported(s, Unsupported::Bytevectors))
    }

    fn null(&mut self, _s: Span) -> Result<Self::Output, Self::Error> {
        // Empty list is represented as List(vec![]) in Value::List?
        // Or maybe we should have an EmptyList variant?
        // minireader.rs says: "Lists (including proper and improper lists, empty list represents nil) List(Vec<Syntax<Value>>)"
        // But wait, minireader.rs Value definition:
        // List(Vec<Syntax<Value>>),
        // It doesn't have EmptyList.
        // So null is List(vec![]).
        // But we need a span for it.
        // Syntax::new(s, Value::List(vec![]))
        Ok(Value::List(vec![]))
    }

    fn list<I>(&mut self, iter: I, _s: Span) -> Result<Self::Output, Self::Error>
    where
        I: IntoIterator<Item = Self::Output>,
        I::IntoIter: ExactSizeIterator,
    {
        let elements: Vec<_> = iter.into_iter().collect();
        Ok(Value::List(elements))
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
        Err(ParseError::unsupported(s, Unsupported::ImproperLists))
    }

    fn vector<I>(&mut self, _iter: I, s: Span) -> Result<Self::Output, Self::Error>
    where
        I: IntoIterator<Item = Self::Output>,
        I::IntoIter: ExactSizeIterator,
    {
        Err(ParseError::unsupported(s, Unsupported::Vectors))
    }

    fn labeled(
        &mut self,
        _id: u64,
        _inner: Self::Output,
        s: Span,
    ) -> Result<Self::Output, Self::Error> {
        Err(ParseError::unsupported(s, Unsupported::Labels))
    }

    fn label_ref(&mut self, _id: u64, s: Span) -> Result<Self::Output, Self::Error> {
        Err(ParseError::unsupported(s, Unsupported::Labels))
    }

    fn copy<I>(&mut self, _inspector: &I) -> Result<Self::Output, Self::Error>
    where
        I: DatumInspector,
    {
        Err(ParseError::unsupported(Span::new(0, 0), Unsupported::Quasiquote)) // Just a dummy error, copy not supported
    }
}

pub fn read(source: &str) -> Result<Value, ParseError> {
    read_with_max_depth(source, 64)
}

pub fn read_with_max_depth(source: &str, max_depth: u32) -> Result<Value, ParseError> {
    let lexer = crate::scheme::lex::lex_with_config(
        source,
        crate::scheme::lex::LexConfig {
            reject_fold_case: true,
            reject_comments: true,
        },
    );
    let mut stream = crate::scheme::reader::TokenStream::new(lexer);
    let mut writer = MiniWriter::new();
    stream
        .parse_datum_with_max_depth(&mut writer, max_depth)
        .map(|(datum, _span)| datum)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scheme::{ParseError, Unsupported};

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
                        e.check(a, test_name);
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
                (
                    ErrorMatcher::Unsupported(expected_feature),
                    ParseError::WriterError(msg),
                ) => {
                    // The generic reader wraps writer errors in WriterError(String).
                    // We check if the debug string of the feature is present in the message.
                    let feature_str = format!("{:?}", expected_feature);
                    if !msg.contains(&feature_str) {
                        panic!(
                            "{}: expected WriterError containing {:?}, got {:?}",
                            test_name, feature_str, msg
                        );
                    }
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
            // Datum comments are not supported by MiniReader when
            // `reject_comments` is enabled in the lexer configuration.
            TestCase {
                name: "datum_comment_prefix",
                input: "#; 1 2",
                expected: Error(ErrorMatcher::Unsupported(Unsupported::Comments)),
            },
            TestCase {
                name: "datum_comment_in_list",
                input: "(1 #; 2 3)",
                expected: Error(ErrorMatcher::Unsupported(Unsupported::Comments)),
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
            TestCase {
                name: "unsupported_exact_number",
                input: "#e42",
                expected: Error(ErrorMatcher::Unsupported(Unsupported::InvalidIntegerFormat)),
            },
            TestCase {
                name: "unsupported_inexact_number",
                input: "#i42",
                expected: Error(ErrorMatcher::Unsupported(Unsupported::InvalidIntegerFormat)),
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
