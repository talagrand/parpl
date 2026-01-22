use crate::scheme::{Unsupported, lex::*};

// --- Test Infrastructure ---

struct TestCase {
    name: &'static str,
    input: &'static str,
    expected: Expected,
}

enum Expected {
    Tokens(Vec<TokenMatcher>),
    Error(ErrorMatcher),
    Empty,
}

enum ErrorMatcher {
    Incomplete,
    IncompleteToken,
    /// Lex error with expected span.
    /// Parameters: (nonterminal, start, end).
    LexSpan(&'static str, usize, usize),
    /// Unsupported feature with expected enum value.
    Unsupported(Unsupported),
}

enum TokenMatcher {
    Bool(bool),
    Char(char),
    Str(&'static str),
    Ident(&'static str),
    LabelDef(u64),
    LabelRef(u64),
    LParen,
    RParen,
    Quote,
    Backquote,
    Comma,
    CommaAt,
    Dot,
    VectorStart,
    ByteVectorStart,
    DatumComment,
    Num(&'static str, NumCheck),
}

enum NumCheck {
    Any, // Just check text
    Int(&'static str),
    Dec(&'static str),
    Rat(&'static str),
    RectInt(&'static str, &'static str),     // real int, imag int
    RectRat(&'static str, &'static str),     // real int, imag rat
    PolarInt(&'static str, &'static str),    // mag int, ang int
    PolarRatDec(&'static str, &'static str), // mag rat, ang dec
    Inf(InfinityNan),
    RectInfImag(&'static str, InfinityNan), // real int, imag inf

    // Wrappers
    Exact(Box<NumCheck>),
    Inexact(Box<NumCheck>),
    Radix(NumberRadix, Box<NumCheck>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum InfinityNan {
    PositiveInfinity,
    NegativeInfinity,
    PositiveNaN,
    NegativeNaN,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SpecialMagnitude {
    Infinity,
    NaN,
}

impl InfinityNan {
    fn expected(self) -> (Option<Sign>, SpecialMagnitude) {
        match self {
            InfinityNan::PositiveInfinity => (Some(Sign::Positive), SpecialMagnitude::Infinity),
            InfinityNan::NegativeInfinity => (Some(Sign::Negative), SpecialMagnitude::Infinity),
            InfinityNan::PositiveNaN => (Some(Sign::Positive), SpecialMagnitude::NaN),
            InfinityNan::NegativeNaN => (Some(Sign::Negative), SpecialMagnitude::NaN),
        }
    }
}

fn split_expected_sign(expected: &str) -> (Option<Sign>, &str) {
    if let Some(rest) = expected.strip_prefix('-') {
        (Some(Sign::Negative), rest)
    } else if let Some(rest) = expected.strip_prefix('+') {
        (Some(Sign::Positive), rest)
    } else {
        (None, expected)
    }
}

fn assert_finite(
    repr: &RealRepr<'_>,
    expected_kind: FiniteRealKind,
    expected: &str,
    test_name: &str,
    index: usize,
    part: &str,
) {
    let (expected_sign, expected_spelling) = split_expected_sign(expected);
    assert_eq!(
        repr.sign, expected_sign,
        "{test_name}: token {index} {part} sign mismatch"
    );

    match &repr.magnitude {
        RealMagnitude::Finite(FiniteRealMagnitude { kind, spelling }) => {
            assert_eq!(
                *kind, expected_kind,
                "{test_name}: token {index} {part} kind mismatch"
            );
            assert_eq!(
                *spelling, expected_spelling,
                "{test_name}: token {index} {part} spelling mismatch"
            );
        }
        _ => panic!("{test_name}: token {index} expected finite {part}"),
    }
}

fn assert_infnan(
    repr: &RealRepr<'_>,
    expected: InfinityNan,
    test_name: &str,
    index: usize,
    part: &str,
) {
    let (expected_sign, expected_kind) = expected.expected();
    assert_eq!(
        repr.sign, expected_sign,
        "{test_name}: token {index} {part} sign mismatch"
    );
    match &repr.magnitude {
        RealMagnitude::Infinity => assert_eq!(
            expected_kind,
            SpecialMagnitude::Infinity,
            "{test_name}: token {index} {part} magnitude mismatch"
        ),
        RealMagnitude::NaN => assert_eq!(
            expected_kind,
            SpecialMagnitude::NaN,
            "{test_name}: token {index} {part} magnitude mismatch"
        ),
        _ => panic!("{test_name}: token {index} expected infnan {part}"),
    }
}

impl TestCase {
    fn run(&self) {
        let result: Result<Vec<SpannedToken>, ParseError> = lex(self.input).collect();
        self.run_with_result(result);
    }

    fn run_with_config(&self, config: LexConfig) {
        let result: Result<Vec<SpannedToken>, ParseError> =
            lex_with_config(self.input, config).collect();
        self.run_with_result(result);
    }

    fn run_with_result(&self, result: Result<Vec<SpannedToken>, ParseError>) {
        match &self.expected {
            Expected::Tokens(expected_tokens) => {
                let tokens = result.unwrap_or_else(|e| {
                    panic!("{}: expected tokens, got error {:?}", self.name, e)
                });
                assert_eq!(
                    tokens.len(),
                    expected_tokens.len(),
                    "{}: token count mismatch",
                    self.name
                );
                for (i, (tok, matcher)) in tokens.iter().zip(expected_tokens.iter()).enumerate() {
                    matcher.check(&tok.value, self.name, i);
                }
            }
            Expected::Error(matcher) => {
                let err = result.expect_err(&format!("{}: expected error, got tokens", self.name));
                matcher.check(&err, self.name);
            }
            Expected::Empty => {
                let tokens = result.unwrap_or_else(|e| {
                    panic!("{}: expected success, got error {:?}", self.name, e)
                });
                assert!(tokens.is_empty(), "{}: expected empty tokens", self.name);
            }
        }
    }
}

impl ErrorMatcher {
    fn check(&self, err: &ParseError, test_name: &str) {
        match (self, err) {
            (ErrorMatcher::Incomplete, ParseError::Incomplete) => {}
            (ErrorMatcher::IncompleteToken, ParseError::IncompleteToken) => {}
            (
                ErrorMatcher::LexSpan(nt, start, end),
                ParseError::Lex {
                    span, nonterminal, ..
                },
            ) => {
                assert_eq!(nt, nonterminal, "{test_name}: error nonterminal mismatch");
                assert_eq!(
                    *start, span.start,
                    "{}: error span.start mismatch (expected {}, got {})",
                    test_name, start, span.start
                );
                assert_eq!(
                    *end, span.end,
                    "{}: error span.end mismatch (expected {}, got {})",
                    test_name, end, span.end
                );
            }
            (
                ErrorMatcher::Unsupported(expected_feature),
                ParseError::Unsupported { feature, .. },
            ) => {
                assert_eq!(
                    expected_feature, feature,
                    "{test_name}: unsupported feature mismatch"
                );
            }
            _ => panic!("{test_name}: error mismatch. Expected {self:?}, got {err:?}"),
        }
    }
}

impl std::fmt::Debug for ErrorMatcher {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Incomplete => write!(f, "Incomplete"),
            Self::IncompleteToken => write!(f, "IncompleteToken"),
            Self::LexSpan(arg0, arg1, arg2) => f
                .debug_tuple("LexSpan")
                .field(arg0)
                .field(arg1)
                .field(arg2)
                .finish(),
            Self::Unsupported(msg) => f.debug_tuple("Unsupported").field(msg).finish(),
        }
    }
}

impl TokenMatcher {
    fn check(&self, token: &Token, test_name: &str, index: usize) {
        match (self, token) {
            (TokenMatcher::Bool(e), Token::Boolean(a)) => {
                assert_eq!(e, a, "{test_name}: token {index} mismatch")
            }
            (TokenMatcher::Char(e), Token::Character(a)) => {
                assert_eq!(e, a, "{test_name}: token {index} mismatch")
            }
            (TokenMatcher::Str(e), Token::String(a)) => {
                assert_eq!(e, a, "{test_name}: token {index} mismatch")
            }
            (TokenMatcher::Ident(e), Token::Identifier(a)) => {
                assert_eq!(e, a, "{test_name}: token {index} mismatch")
            }
            (TokenMatcher::LabelDef(e), Token::LabelDef(a)) => {
                assert_eq!(e, a, "{test_name}: token {index} mismatch")
            }
            (TokenMatcher::LabelRef(e), Token::LabelRef(a)) => {
                assert_eq!(e, a, "{test_name}: token {index} mismatch")
            }
            (TokenMatcher::LParen, Token::LParen) => {}
            (TokenMatcher::RParen, Token::RParen) => {}
            (TokenMatcher::Quote, Token::Quote) => {}
            (TokenMatcher::Backquote, Token::Backquote) => {}
            (TokenMatcher::Comma, Token::Comma) => {}
            (TokenMatcher::CommaAt, Token::CommaAt) => {}
            (TokenMatcher::Dot, Token::Dot) => {}
            (TokenMatcher::VectorStart, Token::VectorStart) => {}
            (TokenMatcher::ByteVectorStart, Token::ByteVectorStart) => {}
            (TokenMatcher::DatumComment, Token::DatumComment) => {}
            (TokenMatcher::Num(text, check), Token::Number(n)) => {
                assert_eq!(text, &n.text, "{test_name}: token {index} text mismatch");
                check.verify(&n.kind, test_name, index);
            }
            _ => {
                panic!("{test_name}: token {index} type mismatch. Expected {self:?}, got {token:?}")
            }
        }
    }
}

impl std::fmt::Debug for TokenMatcher {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Bool(b) => f.debug_tuple("Bool").field(b).finish(),
            Self::Char(c) => f.debug_tuple("Char").field(c).finish(),
            Self::Str(s) => f.debug_tuple("Str").field(s).finish(),
            Self::Ident(s) => f.debug_tuple("Ident").field(s).finish(),
            Self::LabelDef(n) => f.debug_tuple("LabelDef").field(n).finish(),
            Self::LabelRef(n) => f.debug_tuple("LabelRef").field(n).finish(),
            Self::LParen => write!(f, "LParen"),
            Self::RParen => write!(f, "RParen"),
            Self::Quote => write!(f, "Quote"),
            Self::Backquote => write!(f, "Backquote"),
            Self::Comma => write!(f, "Comma"),
            Self::CommaAt => write!(f, "CommaAt"),
            Self::Dot => write!(f, "Dot"),
            Self::VectorStart => write!(f, "VectorStart"),
            Self::ByteVectorStart => write!(f, "ByteVectorStart"),
            Self::DatumComment => write!(f, "DatumComment"),
            Self::Num(s, _) => f.debug_tuple("Num").field(s).finish(),
        }
    }
}

impl NumCheck {
    fn verify(&self, kind: &NumberLiteralKind, test_name: &str, index: usize) {
        match self {
            NumCheck::Any => {}
            NumCheck::Int(s) => {
                if let NumberValue::Real(real) = &kind.value {
                    assert_finite(real, FiniteRealKind::Integer, s, test_name, index, "real");
                } else {
                    panic!("{test_name}: token {index} expected Real, got {kind:?}");
                }
            }
            NumCheck::Dec(s) => {
                if let NumberValue::Real(real) = &kind.value {
                    assert_finite(real, FiniteRealKind::Decimal, s, test_name, index, "real");
                } else {
                    panic!("{test_name}: token {index} expected Real, got {kind:?}");
                }
            }
            NumCheck::Rat(s) => {
                if let NumberValue::Real(real) = &kind.value {
                    assert_finite(real, FiniteRealKind::Rational, s, test_name, index, "real");
                } else {
                    panic!("{test_name}: token {index} expected Real, got {kind:?}");
                }
            }
            NumCheck::RectInt(r, i) => {
                if let NumberValue::Rectangular { real, imag } = &kind.value {
                    assert_finite(
                        real,
                        FiniteRealKind::Integer,
                        r,
                        test_name,
                        index,
                        "real part",
                    );
                    assert_finite(
                        imag,
                        FiniteRealKind::Integer,
                        i,
                        test_name,
                        index,
                        "imag part",
                    );
                } else {
                    panic!("{test_name}: token {index} expected Rectangular");
                }
            }
            NumCheck::RectRat(r, i) => {
                if let NumberValue::Rectangular { real, imag } = &kind.value {
                    assert_finite(
                        real,
                        FiniteRealKind::Integer,
                        r,
                        test_name,
                        index,
                        "real part",
                    );
                    assert_finite(
                        imag,
                        FiniteRealKind::Rational,
                        i,
                        test_name,
                        index,
                        "imag part",
                    );
                } else {
                    panic!("{test_name}: token {index} expected Rectangular");
                }
            }
            NumCheck::PolarInt(m, a) => {
                if let NumberValue::Polar { magnitude, angle } = &kind.value {
                    assert_finite(
                        magnitude,
                        FiniteRealKind::Integer,
                        m,
                        test_name,
                        index,
                        "magnitude",
                    );
                    assert_finite(angle, FiniteRealKind::Integer, a, test_name, index, "angle");
                } else {
                    panic!("{test_name}: token {index} expected Polar");
                }
            }
            NumCheck::PolarRatDec(m, a) => {
                if let NumberValue::Polar { magnitude, angle } = &kind.value {
                    assert_finite(
                        magnitude,
                        FiniteRealKind::Rational,
                        m,
                        test_name,
                        index,
                        "magnitude",
                    );
                    assert_finite(angle, FiniteRealKind::Decimal, a, test_name, index, "angle");
                } else {
                    panic!("{test_name}: token {index} expected Polar");
                }
            }
            NumCheck::Inf(k) => {
                if let NumberValue::Real(real) = &kind.value {
                    assert_infnan(real, *k, test_name, index, "real");
                } else {
                    panic!("{test_name}: token {index} expected Real");
                }
            }
            NumCheck::RectInfImag(r, k) => {
                if let NumberValue::Rectangular { real, imag } = &kind.value {
                    assert_finite(
                        real,
                        FiniteRealKind::Integer,
                        r,
                        test_name,
                        index,
                        "real part",
                    );
                    assert_infnan(imag, *k, test_name, index, "imag part");
                } else {
                    panic!("{test_name}: token {index} expected Rectangular");
                }
            }
            NumCheck::Exact(inner) => {
                assert_eq!(
                    kind.exactness,
                    NumberExactness::Exact,
                    "{test_name}: token {index} expected Exact"
                );
                inner.verify(kind, test_name, index);
            }
            NumCheck::Inexact(inner) => {
                assert_eq!(
                    kind.exactness,
                    NumberExactness::Inexact,
                    "{test_name}: token {index} expected Inexact"
                );
                inner.verify(kind, test_name, index);
            }
            NumCheck::Radix(r, inner) => {
                assert_eq!(kind.radix, *r, "{test_name}: token {index} radix mismatch");
                inner.verify(kind, test_name, index);
            }
        }
    }
}

// --- Tests ---

fn number_test_cases() -> Vec<TestCase> {
    vec![
        // Number grammar coverage (`syn.tex`, `<number>` section):
        //
        //   <ureal R>       -> covered by: decimal_numbers, rationals, nondecimal_numbers
        //   <real R>        -> covered by: decimal_numbers, infnan_plain, infnan_prefixed
        //   <complex R>     -> covered by: decimal_complex, decimal_complex_unit_imaginary_with_real,
        //                        pure_imaginary_and_polar, nondecimal_complex_unit_imaginary_with_real,
        //                        prefixed_complex, prefixed_polar, nondecimal_complex
        //   error cases     -> covered by: malformed_number_suffix, malformed_rational_*,
        //                        invalid_hex_literal, nondecimal_errors_*, infnan_errors_*,
        //                        ambiguous_complex_*, pure_imaginary_signless_*_invalid,
        //                        number_invalid_exponent_space, number_incomplete_exponent_eof
        //
        // This block of tests is intended to track the R7RS numeric
        // productions closely: for each production we have at least one
        // positive and (where sensible) one negative example. Some
        // implementation-specific edge cases and deviations are also
        // exercised and called out in individual test names/comments.
        TestCase {
            name: "decimal_numbers",
            input: "42 -7 3.14 .5 1e3 2.0e-2",
            expected: Expected::Tokens(vec![
                TokenMatcher::Num("42", NumCheck::Int("42")),
                TokenMatcher::Num("-7", NumCheck::Int("-7")),
                TokenMatcher::Num("3.14", NumCheck::Dec("3.14")),
                TokenMatcher::Num(".5", NumCheck::Dec(".5")),
                TokenMatcher::Num("1e3", NumCheck::Dec("1e3")),
                TokenMatcher::Num("2.0e-2", NumCheck::Dec("2.0e-2")),
            ]),
        },
        TestCase {
            name: "incomplete_decimal_1",
            input: "1e",
            expected: Expected::Error(ErrorMatcher::IncompleteToken),
        },
        TestCase {
            name: "incomplete_decimal_2",
            input: "1.0e+",
            expected: Expected::Error(ErrorMatcher::IncompleteToken),
        },
        TestCase {
            name: "malformed_number_suffix",
            input: "0 42foo",
            // Error is in the second number token ("42foo");
            // span covers the valid numeric prefix of that token.
            expected: Expected::Error(ErrorMatcher::LexSpan("<number>", 2, 4)),
        },
        TestCase {
            name: "rationals",
            input: "3/4 -3/4",
            expected: Expected::Tokens(vec![
                TokenMatcher::Num("3/4", NumCheck::Rat("3/4")),
                TokenMatcher::Num("-3/4", NumCheck::Rat("-3/4")),
            ]),
        },
        TestCase {
            name: "incomplete_rational",
            input: "3/",
            expected: Expected::Error(ErrorMatcher::IncompleteToken),
        },
        TestCase {
            name: "malformed_rational_1",
            input: "3/x",
            expected: Expected::Error(ErrorMatcher::LexSpan("<number>", 0, 2)),
        },
        TestCase {
            name: "malformed_rational_2",
            input: "1/2/3",
            expected: Expected::Error(ErrorMatcher::LexSpan("<number>", 0, 3)),
        },
        TestCase {
            name: "invalid_hex_literal",
            input: "0x1",
            expected: Expected::Error(ErrorMatcher::LexSpan("<number>", 0, 1)),
        },
        TestCase {
            name: "decimal_complex",
            input: "1+2i 1-3/4i 1+2.5i 1-1e3i",
            expected: Expected::Tokens(vec![
                TokenMatcher::Num("1+2i", NumCheck::RectInt("1", "+2")),
                TokenMatcher::Num("1-3/4i", NumCheck::RectRat("1", "-3/4")),
                TokenMatcher::Num("1+2.5i", NumCheck::Any),
                TokenMatcher::Num("1-1e3i", NumCheck::Any),
            ]),
        },
        TestCase {
            name: "decimal_complex_unit_imaginary_with_real",
            input: "1+i 1-i",
            expected: Expected::Tokens(vec![
                TokenMatcher::Num("1+i", NumCheck::RectInt("1", "+1")),
                TokenMatcher::Num("1-i", NumCheck::RectInt("1", "-1")),
            ]),
        },
        TestCase {
            name: "pure_imaginary_and_polar",
            input: "+i -i +2i -3/4i 1@2 -3/4@5.0 +inf.0i 1+inf.0i",
            expected: Expected::Tokens(vec![
                TokenMatcher::Num("+i", NumCheck::RectInt("0", "+1")),
                TokenMatcher::Num("-i", NumCheck::RectInt("0", "-1")),
                TokenMatcher::Num("+2i", NumCheck::RectInt("0", "+2")),
                TokenMatcher::Num("-3/4i", NumCheck::RectRat("0", "-3/4")),
                TokenMatcher::Num("1@2", NumCheck::PolarInt("1", "2")),
                TokenMatcher::Num("-3/4@5.0", NumCheck::PolarRatDec("-3/4", "5.0")),
                TokenMatcher::Num(
                    "+inf.0i",
                    NumCheck::RectInfImag("0", InfinityNan::PositiveInfinity),
                ),
                TokenMatcher::Num(
                    "1+inf.0i",
                    NumCheck::RectInfImag("1", InfinityNan::PositiveInfinity),
                ),
            ]),
        },
        TestCase {
            name: "complex_double_sign_invalid_1",
            input: "1+-2i",
            expected: Expected::Error(ErrorMatcher::LexSpan("<number>", 0, 1)),
        },
        TestCase {
            name: "complex_double_sign_invalid_2",
            input: "1-+2i",
            expected: Expected::Error(ErrorMatcher::LexSpan("<number>", 0, 1)),
        },
        TestCase {
            name: "complex_double_sign_invalid_3",
            input: "1--2i",
            expected: Expected::Error(ErrorMatcher::LexSpan("<number>", 0, 1)),
        },
        TestCase {
            name: "complex_double_sign_invalid_4",
            input: "1++2i",
            expected: Expected::Error(ErrorMatcher::LexSpan("<number>", 0, 1)),
        },
        TestCase {
            name: "complex_infnan_valid",
            input: "1+inf.0i 1-inf.0i 1+nan.0i",
            expected: Expected::Tokens(vec![
                TokenMatcher::Num(
                    "1+inf.0i",
                    NumCheck::RectInfImag("1", InfinityNan::PositiveInfinity),
                ),
                TokenMatcher::Num(
                    "1-inf.0i",
                    NumCheck::RectInfImag("1", InfinityNan::NegativeInfinity),
                ),
                TokenMatcher::Num(
                    "1+nan.0i",
                    NumCheck::RectInfImag("1", InfinityNan::PositiveNaN),
                ),
            ]),
        },
        TestCase {
            name: "complex_infnan_double_sign_invalid",
            input: "1+-inf.0i",
            expected: Expected::Error(ErrorMatcher::LexSpan("<number>", 0, 1)),
        },
        TestCase {
            name: "nondecimal_complex_unit_imaginary_with_real",
            input: "#b1+i #x1-i",
            expected: Expected::Tokens(vec![
                TokenMatcher::Num(
                    "#b1+i",
                    NumCheck::Radix(2, Box::new(NumCheck::RectInt("1", "+1"))),
                ),
                TokenMatcher::Num(
                    "#x1-i",
                    NumCheck::Radix(16, Box::new(NumCheck::RectInt("1", "-1"))),
                ),
            ]),
        },
        TestCase {
            name: "pure_imaginary_signless_integer_invalid",
            input: "2i",
            expected: Expected::Error(ErrorMatcher::LexSpan("<number>", 0, 1)),
        },
        TestCase {
            name: "pure_imaginary_signless_rational_invalid",
            input: "3/4i",
            expected: Expected::Error(ErrorMatcher::LexSpan("<number>", 0, 3)),
        },
        TestCase {
            name: "pure_imaginary_signless_decimal_invalid",
            input: "1.0e3i",
            expected: Expected::Error(ErrorMatcher::LexSpan("<number>", 0, 5)),
        },
        TestCase {
            name: "pure_imaginary_signless_unit_invalid",
            input: "1i",
            expected: Expected::Error(ErrorMatcher::LexSpan("<number>", 0, 1)),
        },
        TestCase {
            name: "prefixed_decimal",
            input: "#d42 #e3.0 #i-5/6 #d#e1 #e#d2",
            expected: Expected::Tokens(vec![
                TokenMatcher::Num("#d42", NumCheck::Int("42")),
                TokenMatcher::Num("#e3.0", NumCheck::Exact(Box::new(NumCheck::Dec("3.0")))),
                TokenMatcher::Num("#i-5/6", NumCheck::Inexact(Box::new(NumCheck::Rat("-5/6")))),
                TokenMatcher::Num("#d#e1", NumCheck::Exact(Box::new(NumCheck::Int("1")))),
                TokenMatcher::Num("#e#d2", NumCheck::Exact(Box::new(NumCheck::Int("2")))),
            ]),
        },
        TestCase {
            name: "prefixed_complex",
            input: "#d1+2i #e1-3/4i #i+2i #e1-1e3i #d+inf.0i #e1+inf.0i",
            expected: Expected::Tokens(vec![
                TokenMatcher::Num("#d1+2i", NumCheck::RectInt("1", "+2")),
                TokenMatcher::Num(
                    "#e1-3/4i",
                    NumCheck::Exact(Box::new(NumCheck::RectRat("1", "-3/4"))),
                ),
                TokenMatcher::Num("#i+2i", NumCheck::Inexact(Box::new(NumCheck::Any))),
                TokenMatcher::Num("#e1-1e3i", NumCheck::Exact(Box::new(NumCheck::Any))),
                TokenMatcher::Num(
                    "#d+inf.0i",
                    NumCheck::RectInfImag("0", InfinityNan::PositiveInfinity),
                ),
                TokenMatcher::Num(
                    "#e1+inf.0i",
                    NumCheck::Exact(Box::new(NumCheck::RectInfImag(
                        "1",
                        InfinityNan::PositiveInfinity,
                    ))),
                ),
            ]),
        },
        TestCase {
            name: "prefixed_polar",
            input: "#e1@2 #d-3/4@5.0 #b+inf.0@1 -3/4@5.0",
            expected: Expected::Tokens(vec![
                TokenMatcher::Num(
                    "#e1@2",
                    NumCheck::Exact(Box::new(NumCheck::PolarInt("1", "2"))),
                ),
                TokenMatcher::Num("#d-3/4@5.0", NumCheck::PolarRatDec("-3/4", "5.0")),
                TokenMatcher::Num("#b+inf.0@1", NumCheck::Radix(2, Box::new(NumCheck::Any))), // Simplified check
                TokenMatcher::Num("-3/4@5.0", NumCheck::PolarRatDec("-3/4", "5.0")),
            ]),
        },
        TestCase {
            name: "prefixed_errors_1",
            input: "#d#d1",
            expected: Expected::Error(ErrorMatcher::LexSpan("<number>", 0, 1)),
        },
        TestCase {
            name: "prefixed_errors_2",
            input: "#e#i1",
            expected: Expected::Error(ErrorMatcher::LexSpan("<number>", 0, 1)),
        },
        TestCase {
            name: "prefixed_errors_3",
            input: "#d42foo",
            expected: Expected::Error(ErrorMatcher::LexSpan("<number>", 0, 1)),
        },
        TestCase {
            name: "prefixed_errors_4",
            input: "#d",
            expected: Expected::Error(ErrorMatcher::IncompleteToken),
        },
        TestCase {
            name: "infnan_plain",
            input: "+inf.0 -inf.0 +nan.0 -nan.0",
            expected: Expected::Tokens(vec![
                TokenMatcher::Num("+inf.0", NumCheck::Inf(InfinityNan::PositiveInfinity)),
                TokenMatcher::Num("-inf.0", NumCheck::Inf(InfinityNan::NegativeInfinity)),
                TokenMatcher::Num("+nan.0", NumCheck::Inf(InfinityNan::PositiveNaN)),
                TokenMatcher::Num("-nan.0", NumCheck::Inf(InfinityNan::NegativeNaN)),
            ]),
        },
        TestCase {
            name: "infnan_prefixed",
            input: "#e+inf.0 #i-nan.0 #b+inf.0 #x-nan.0 #b#e+inf.0 #i#x-nan.0",
            expected: Expected::Tokens(vec![
                TokenMatcher::Num(
                    "#e+inf.0",
                    NumCheck::Exact(Box::new(NumCheck::Inf(InfinityNan::PositiveInfinity))),
                ),
                TokenMatcher::Num(
                    "#i-nan.0",
                    NumCheck::Inexact(Box::new(NumCheck::Inf(InfinityNan::NegativeNaN))),
                ),
                TokenMatcher::Num(
                    "#b+inf.0",
                    NumCheck::Radix(2, Box::new(NumCheck::Inf(InfinityNan::PositiveInfinity))),
                ),
                TokenMatcher::Num(
                    "#x-nan.0",
                    NumCheck::Radix(16, Box::new(NumCheck::Inf(InfinityNan::NegativeNaN))),
                ),
                TokenMatcher::Num(
                    "#b#e+inf.0",
                    NumCheck::Exact(Box::new(NumCheck::Radix(
                        2,
                        Box::new(NumCheck::Inf(InfinityNan::PositiveInfinity)),
                    ))),
                ),
                TokenMatcher::Num(
                    "#i#x-nan.0",
                    NumCheck::Inexact(Box::new(NumCheck::Radix(
                        16,
                        Box::new(NumCheck::Inf(InfinityNan::NegativeNaN)),
                    ))),
                ),
            ]),
        },
        TestCase {
            name: "nondecimal_numbers",
            input: "#b1010 #o77 #x1f #b101/11 #xA/F #b#e1 #i#o7",
            expected: Expected::Tokens(vec![
                TokenMatcher::Num(
                    "#b1010",
                    NumCheck::Radix(2, Box::new(NumCheck::Int("1010"))),
                ),
                TokenMatcher::Num("#o77", NumCheck::Radix(8, Box::new(NumCheck::Int("77")))),
                TokenMatcher::Num("#x1f", NumCheck::Radix(16, Box::new(NumCheck::Int("1f")))),
                TokenMatcher::Num(
                    "#b101/11",
                    NumCheck::Radix(2, Box::new(NumCheck::Rat("101/11"))),
                ),
                TokenMatcher::Num("#xA/F", NumCheck::Radix(16, Box::new(NumCheck::Rat("A/F")))),
                TokenMatcher::Num(
                    "#b#e1",
                    NumCheck::Exact(Box::new(NumCheck::Radix(2, Box::new(NumCheck::Int("1"))))),
                ),
                TokenMatcher::Num(
                    "#i#o7",
                    NumCheck::Inexact(Box::new(NumCheck::Radix(8, Box::new(NumCheck::Int("7"))))),
                ),
            ]),
        },
        TestCase {
            name: "nondecimal_errors_1",
            input: "#b102",
            expected: Expected::Error(ErrorMatcher::LexSpan("<number>", 0, 1)),
        },
        TestCase {
            name: "nondecimal_errors_2",
            input: "#o7/",
            expected: Expected::Error(ErrorMatcher::IncompleteToken),
        },
        TestCase {
            name: "nondecimal_errors_3",
            input: "#xA/G",
            expected: Expected::Error(ErrorMatcher::LexSpan("<number>", 0, 1)),
        },
        TestCase {
            name: "nondecimal_errors_4",
            input: "#b#b1",
            expected: Expected::Error(ErrorMatcher::LexSpan("<number>", 0, 1)),
        },
        TestCase {
            name: "nondecimal_errors_5",
            input: "#i#e#b1",
            expected: Expected::Error(ErrorMatcher::LexSpan("<number>", 0, 1)),
        },
        TestCase {
            name: "nondecimal_errors_6",
            input: "#b1010foo",
            expected: Expected::Error(ErrorMatcher::LexSpan("<number>", 0, 1)),
        },
        TestCase {
            name: "nondecimal_errors_7",
            input: "#b101e10",
            expected: Expected::Error(ErrorMatcher::LexSpan("<number>", 0, 1)),
        },
        TestCase {
            name: "nondecimal_errors_8",
            input: "#x1.2",
            expected: Expected::Error(ErrorMatcher::LexSpan("<number>", 0, 1)),
        },
        TestCase {
            name: "nondecimal_complex",
            input: "#b1+10i #x1-2i #b+i #o-i #b1@10 #x1+inf.0i #b+inf.0i",
            expected: Expected::Tokens(vec![
                TokenMatcher::Num(
                    "#b1+10i",
                    NumCheck::Radix(2, Box::new(NumCheck::RectInt("1", "+10"))),
                ),
                TokenMatcher::Num(
                    "#x1-2i",
                    NumCheck::Radix(16, Box::new(NumCheck::RectInt("1", "-2"))),
                ),
                TokenMatcher::Num(
                    "#b+i",
                    NumCheck::Radix(2, Box::new(NumCheck::RectInt("0", "+1"))),
                ),
                TokenMatcher::Num(
                    "#o-i",
                    NumCheck::Radix(8, Box::new(NumCheck::RectInt("0", "-1"))),
                ),
                TokenMatcher::Num(
                    "#b1@10",
                    NumCheck::Radix(2, Box::new(NumCheck::PolarInt("1", "10"))),
                ),
                TokenMatcher::Num(
                    "#x1+inf.0i",
                    NumCheck::Radix(
                        16,
                        Box::new(NumCheck::RectInfImag("1", InfinityNan::PositiveInfinity)),
                    ),
                ),
                TokenMatcher::Num(
                    "#b+inf.0i",
                    NumCheck::Radix(
                        2,
                        Box::new(NumCheck::RectInfImag("0", InfinityNan::PositiveInfinity)),
                    ),
                ),
            ]),
        },
        TestCase {
            name: "infnan_errors_1",
            input: "+inf.0foo",
            expected: Expected::Error(ErrorMatcher::LexSpan("<number>", 0, 6)),
        },
        TestCase {
            name: "infnan_errors_2",
            input: "#e+inf.0bar",
            expected: Expected::Error(ErrorMatcher::LexSpan("<number>", 0, 1)),
        },
        TestCase {
            name: "ambiguous_complex_1",
            input: "1+2",
            expected: Expected::Error(ErrorMatcher::IncompleteToken),
        },
        TestCase {
            name: "ambiguous_complex_2",
            input: "1+2)",
            expected: Expected::Error(ErrorMatcher::LexSpan("<number>", 0, 1)),
        },
        TestCase {
            name: "ambiguous_complex_3",
            input: "#e1@foo",
            expected: Expected::Error(ErrorMatcher::LexSpan("<number>", 0, 1)),
        },
        TestCase {
            name: "ambiguous_complex_4",
            input: "#b1@10x",
            expected: Expected::Error(ErrorMatcher::LexSpan("<number>", 0, 1)),
        },
        TestCase {
            name: "ambiguous_complex_5",
            input: "+inf.0x",
            expected: Expected::Error(ErrorMatcher::LexSpan("<number>", 0, 6)),
        },
        TestCase {
            name: "ambiguous_complex_6",
            input: "+inf.0i0",
            expected: Expected::Error(ErrorMatcher::LexSpan("<number>", 0, 6)),
        },
        TestCase {
            name: "number_invalid_exponent_space",
            input: "(+ 1e 1e)",
            // 1e followed by space is invalid number format, not incomplete token
            expected: Expected::Error(ErrorMatcher::LexSpan("<number>", 3, 5)),
        },
        TestCase {
            name: "number_incomplete_exponent_eof",
            input: "1e",
            // 1e at EOF is incomplete token
            expected: Expected::Error(ErrorMatcher::IncompleteToken),
        },
    ]
}

#[test]
fn run_all_tests() {
    let cases = vec![
        TestCase {
            name: "simple_identifier_call",
            input: "(foo)",
            expected: Expected::Tokens(vec![
                TokenMatcher::LParen,
                TokenMatcher::Ident("foo"),
                TokenMatcher::RParen,
            ]),
        },
        // --- Identifier Tests ---
        TestCase {
            name: "identifier_simple",
            input: "hello",
            expected: Expected::Tokens(vec![TokenMatcher::Ident("hello")]),
        },
        TestCase {
            name: "identifier_with_digits",
            input: "foo123",
            expected: Expected::Tokens(vec![TokenMatcher::Ident("foo123")]),
        },
        TestCase {
            name: "identifier_special_initial",
            input: "!important",
            expected: Expected::Tokens(vec![TokenMatcher::Ident("!important")]),
        },
        TestCase {
            name: "identifier_all_special_initials",
            input: "!$%&*/:<=>?^_~",
            expected: Expected::Tokens(vec![TokenMatcher::Ident("!$%&*/:<=>?^_~")]),
        },
        TestCase {
            name: "identifier_with_special_subsequent",
            input: "foo+bar",
            expected: Expected::Tokens(vec![TokenMatcher::Ident("foo+bar")]),
        },
        TestCase {
            name: "identifier_kebab_case",
            input: "my-identifier",
            expected: Expected::Tokens(vec![TokenMatcher::Ident("my-identifier")]),
        },
        TestCase {
            name: "identifier_question_mark",
            input: "null?",
            expected: Expected::Tokens(vec![TokenMatcher::Ident("null?")]),
        },
        TestCase {
            name: "identifier_arrow",
            input: "->string",
            expected: Expected::Tokens(vec![TokenMatcher::Ident("->string")]),
        },
        TestCase {
            name: "identifier_dots",
            input: "...",
            expected: Expected::Tokens(vec![TokenMatcher::Ident("...")]),
        },
        TestCase {
            name: "identifier_plus",
            input: "+",
            expected: Expected::Tokens(vec![TokenMatcher::Ident("+")]),
        },
        TestCase {
            name: "identifier_minus",
            input: "-",
            expected: Expected::Tokens(vec![TokenMatcher::Ident("-")]),
        },
        TestCase {
            name: "identifier_plus_word",
            input: "+foo",
            expected: Expected::Tokens(vec![TokenMatcher::Ident("+foo")]),
        },
        TestCase {
            name: "identifier_minus_word",
            input: "-bar",
            expected: Expected::Tokens(vec![TokenMatcher::Ident("-bar")]),
        },
        TestCase {
            name: "identifier_if_not_plusi",
            input: "+if",
            expected: Expected::Tokens(vec![TokenMatcher::Ident("+if")]),
        },
        TestCase {
            name: "identifier_vertical_line",
            input: "|hello world|",
            expected: Expected::Tokens(vec![TokenMatcher::Ident("hello world")]),
        },
        TestCase {
            name: "identifier_vertical_line_escape",
            input: r"|hello\|pipe|",
            expected: Expected::Tokens(vec![TokenMatcher::Ident("hello|pipe")]),
        },
        TestCase {
            name: "identifier_vertical_line_newline_escape",
            input: "|hello\\nworld|",
            expected: Expected::Tokens(vec![TokenMatcher::Ident("hello\nworld")]),
        },
        TestCase {
            name: "identifier_vertical_line_hex_escape",
            input: r"|hello\x41;world|",
            expected: Expected::Tokens(vec![TokenMatcher::Ident("helloAworld")]),
        },
        TestCase {
            name: "identifier_vertical_line_backslash_escape",
            input: r"foo |foo\\bar|",
            // R7RS does not define `\\` as a symbol escape inside `|...|`;
            // a backslash must be written via an inline hex escape instead.
            // Error is in the second identifier token ("|foo\\bar|");
            // span covers the valid prefix up to the bad escape.
            expected: Expected::Error(ErrorMatcher::LexSpan("<identifier>", 4, 10)),
        },
        TestCase {
            name: "identifier_unicode",
            input: "λ",
            expected: Expected::Tokens(vec![TokenMatcher::Ident("λ")]),
        },
        TestCase {
            name: "identifier_unicode_mixed",
            input: "α-beta",
            expected: Expected::Tokens(vec![TokenMatcher::Ident("α-beta")]),
        },
        TestCase {
            name: "identifier_unicode_reject_punctuation_bullet",
            input: "x •item",
            // R7RS would allow this (bullet is Po), but our
            // conservative identifier rules reject it.
            expected: Expected::Error(ErrorMatcher::LexSpan("<token>", 2, 5)),
        },
        TestCase {
            name: "identifier_unicode_reject_currency_euro",
            input: "x €price",
            expected: Expected::Error(ErrorMatcher::LexSpan("<token>", 2, 5)),
        },
        // Numbers that should NOT be identifiers
        TestCase {
            name: "not_identifier_plusi",
            input: "+i",
            expected: Expected::Tokens(vec![TokenMatcher::Num("+i", NumCheck::Any)]),
        },
        TestCase {
            name: "not_identifier_minusi",
            input: "-i",
            expected: Expected::Tokens(vec![TokenMatcher::Num("-i", NumCheck::Any)]),
        },
        TestCase {
            name: "not_identifier_plus_inf",
            input: "+inf.0",
            expected: Expected::Tokens(vec![TokenMatcher::Num(
                "+inf.0",
                NumCheck::Inf(InfinityNan::PositiveInfinity),
            )]),
        },
        TestCase {
            name: "not_identifier_minus_inf",
            input: "-inf.0",
            expected: Expected::Tokens(vec![TokenMatcher::Num(
                "-inf.0",
                NumCheck::Inf(InfinityNan::NegativeInfinity),
            )]),
        },
        TestCase {
            name: "not_identifier_plus_nan",
            input: "+nan.0",
            expected: Expected::Tokens(vec![TokenMatcher::Num(
                "+nan.0",
                NumCheck::Inf(InfinityNan::PositiveNaN),
            )]),
        },
        TestCase {
            name: "not_identifier_minus_nan",
            input: "-nan.0",
            expected: Expected::Tokens(vec![TokenMatcher::Num(
                "-nan.0",
                NumCheck::Inf(InfinityNan::NegativeNaN),
            )]),
        },
        TestCase {
            name: "whitespace_comments",
            input: "   ; comment here\n  #| nested ; comment |#   ",
            expected: Expected::Empty,
        },
        TestCase {
            name: "incomplete_nested_comment",
            input: "#| unclosed nested comment",
            expected: Expected::Error(ErrorMatcher::Incomplete),
        },
        TestCase {
            name: "incomplete_character_prefix",
            input: r#"#\"#,
            expected: Expected::Error(ErrorMatcher::IncompleteToken),
        },
        TestCase {
            name: "incomplete_hash_only",
            input: "#",
            expected: Expected::Error(ErrorMatcher::IncompleteToken),
        },
        TestCase {
            name: "incomplete_double_prefix",
            input: "#b#",
            expected: Expected::Error(ErrorMatcher::IncompleteToken),
        },
        TestCase {
            name: "unknown_directive",
            input: "#!unknown-directive",
            expected: Expected::Error(ErrorMatcher::LexSpan("<directive>", 0, 2)),
        },
        TestCase {
            name: "fold_case_directives",
            input: "#!fold-case\n  #!no-fold-case  ; rest is comment\n",
            // Directives are treated as intertoken space and do not
            // produce tokens; the lexer only updates its internal
            // fold-case mode.
            expected: Expected::Empty,
        },
        TestCase {
            name: "directive_requires_delimiter_1",
            input: "#!fold-caseX",
            expected: Expected::Error(ErrorMatcher::LexSpan("<directive>", 0, 11)),
        },
        TestCase {
            name: "directive_requires_delimiter_2",
            input: "#!no-fold-caseX",
            expected: Expected::Error(ErrorMatcher::LexSpan("<directive>", 0, 14)),
        },
        TestCase {
            name: "boolean_tokens",
            input: "  #t  #FaLsE  #true #FALSE",
            expected: Expected::Tokens(vec![
                TokenMatcher::Bool(true),
                TokenMatcher::Bool(false),
                TokenMatcher::Bool(true),
                TokenMatcher::Bool(false),
            ]),
        },
        TestCase {
            name: "character_tokens",
            input: "#\\a #\\space #\\x41",
            expected: Expected::Tokens(vec![
                TokenMatcher::Char('a'),
                TokenMatcher::Char(' '),
                TokenMatcher::Char('A'),
            ]),
        },
        TestCase {
            name: "punctuation_tokens",
            input: "( ) ' ` , ,@ . #( #u8(",
            expected: Expected::Tokens(vec![
                TokenMatcher::LParen,
                TokenMatcher::RParen,
                TokenMatcher::Quote,
                TokenMatcher::Backquote,
                TokenMatcher::Comma,
                TokenMatcher::CommaAt,
                TokenMatcher::Dot,
                TokenMatcher::VectorStart,
                TokenMatcher::ByteVectorStart,
            ]),
        },
        TestCase {
            name: "bytevector_start",
            input: "#u8(",
            expected: Expected::Tokens(vec![TokenMatcher::ByteVectorStart]),
        },
        TestCase {
            name: "labels_def_and_ref_simple",
            input: "#1= #2#",
            expected: Expected::Tokens(vec![TokenMatcher::LabelDef(1), TokenMatcher::LabelRef(2)]),
        },
        TestCase {
            name: "labels_with_following_datum",
            input: "#3=(foo) #4#",
            expected: Expected::Tokens(vec![
                TokenMatcher::LabelDef(3),
                TokenMatcher::LParen,
                TokenMatcher::Ident("foo"),
                TokenMatcher::RParen,
                TokenMatcher::LabelRef(4),
            ]),
        },
        TestCase {
            name: "strings_simple",
            input: "  \"hi\"  \"a\\n\\t\\r\\b\\a\\\\\\\"\"  \"\\x41;\"",
            expected: Expected::Tokens(vec![
                TokenMatcher::Str("hi"),
                TokenMatcher::Str("a\n\t\r\u{8}\u{7}\\\""),
                TokenMatcher::Str("A"),
            ]),
        },
        TestCase {
            name: "strings_splice",
            input: "\"foo\\\n   bar\"",
            expected: Expected::Tokens(vec![TokenMatcher::Str("foobar")]),
        },
        TestCase {
            name: "strings_raw_newline_error",
            input: "\"foo\nbar\"",
            // The error is reported from the opening quote up to
            // (but not including) the embedded newline.
            expected: Expected::Error(ErrorMatcher::LexSpan("<string>", 0, 4)),
        },
        TestCase {
            name: "strings_raw_newline_error_offset",
            input: "\"ok\" \"foo\nbar\"",
            // Second string has a raw newline; span should start at the
            // opening quote of the second string (offset 5) and end just
            // before the newline (offset 9).
            expected: Expected::Error(ErrorMatcher::LexSpan("<string>", 5, 9)),
        },
        TestCase {
            name: "strings_incomplete",
            input: "\"unterminated",
            expected: Expected::Error(ErrorMatcher::Incomplete),
        },
        TestCase {
            name: "strings_invalid_hex",
            input: "\"\\xZZ;\"",
            // The error is reported from the opening quote up to
            // the start of the invalid hex digits.
            expected: Expected::Error(ErrorMatcher::LexSpan("<string>", 0, 3)),
        },
        TestCase {
            name: "strings_invalid_hex_offset",
            input: "\"ok\" \"\\xZZ;\"",
            // Second string has an invalid hex escape; span should start
            // at the opening quote of the second string (offset 5) and
            // end at the first invalid hex digit (offset 8).
            expected: Expected::Error(ErrorMatcher::LexSpan("<string>", 5, 8)),
        },
        TestCase {
            name: "strings_incomplete_hex",
            input: "\"\\x",
            expected: Expected::Error(ErrorMatcher::IncompleteToken),
        },
        TestCase {
            name: "strings_missing_hex_semicolon_offset",
            input: "\"ok\" \"\\x41X\"",
            // Missing ';' terminator in the hex escape of the second
            // string; span should start at the opening quote of the
            // second string (offset 5) and end at the unexpected
            // character after the hex digits (offset 10).
            expected: Expected::Error(ErrorMatcher::LexSpan("<string>", 5, 10)),
        },
        TestCase {
            name: "strings_invalid_escape_offset",
            input: "\"ok\" \"foo\\qbar\"",
            // Invalid mnemonic escape "\\q" inside the second string.
            // Desired behavior: report this as a `<string>` lexical error
            // with a span from the opening quote of the second string
            // (offset 5) to the position of the invalid escape character
            // (offset 10).
            expected: Expected::Error(ErrorMatcher::LexSpan("<string>", 5, 10)),
        },
        TestCase {
            name: "character_ambiguous_hash_x_literal",
            input: "#\\x ",
            // Ambiguous `#\\x` with no hex digits: treated as `#\\ <any character>`
            // where the character is literally 'x'.
            expected: Expected::Tokens(vec![TokenMatcher::Char('x')]),
        },
        TestCase {
            name: "datum_comment",
            input: "#; (foo)",
            // The lexer emits DatumComment token; the parser handles skipping.
            // Here we verify the lexer produces: DatumComment, LParen, Ident, RParen
            expected: Expected::Tokens(vec![
                TokenMatcher::DatumComment,
                TokenMatcher::LParen,
                TokenMatcher::Ident("foo"),
                TokenMatcher::RParen,
            ]),
        },
        TestCase {
            name: "datum_comment_simple",
            input: "#; foo bar",
            // Lexer sees: DatumComment, Ident("foo"), Ident("bar")
            // Parser would skip "foo", leaving "bar"
            expected: Expected::Tokens(vec![
                TokenMatcher::DatumComment,
                TokenMatcher::Ident("foo"),
                TokenMatcher::Ident("bar"),
            ]),
        },
        TestCase {
            name: "directive_case_insensitive",
            input: "#!FOLD-CASE",
            // Case-insensitive directive spelling is accepted and, with
            // fold-case enabled by default, treated purely as intertoken
            // space with no tokens.
            expected: Expected::Empty,
        },
        TestCase {
            name: "reserved_bracket_is_error",
            input: "[",
            // Single reserved bracket at start of input.
            expected: Expected::Error(ErrorMatcher::LexSpan("<token>", 0, 1)),
        },
        TestCase {
            name: "char_name_case_sensitive",
            input: "#\\Space",
            // Should NOT be parsed as space char.
            // Since 'S' is alphabetic, it tries to parse a named char "Space".
            // "Space" != "space", so it fails named char lookup.
            // The error is reported for the "#\\S" prefix.
            expected: Expected::Error(ErrorMatcher::LexSpan("<character>", 0, 3)),
        },
    ];

    for case in cases {
        case.run();
    }
}

#[test]
fn run_number_tests() {
    for case in number_test_cases() {
        case.run();
    }
}

#[test]
fn run_reject_feature_tests() {
    // Use a config that rejects both fold-case directives and all comments.
    let config = LexConfig {
        reject_fold_case: true,
        reject_comments: true,
    };

    let cases = vec![
        TestCase {
            name: "directives_unsupported_when_reject_fold_case_enabled",
            input: "#!fold-case",
            expected: Expected::Error(ErrorMatcher::Unsupported(Unsupported::FoldCaseDirectives)),
        },
        TestCase {
            name: "comments_unsupported_when_reject_comments_enabled_intertoken",
            input: "; comment here\n42",
            expected: Expected::Error(ErrorMatcher::Unsupported(Unsupported::Comments)),
        },
        TestCase {
            name: "datum_comments_unsupported_when_reject_comments_enabled",
            input: "#; 1 2",
            expected: Expected::Error(ErrorMatcher::Unsupported(Unsupported::Comments)),
        },
    ];

    for case in cases {
        case.run_with_config(config);
    }
}
