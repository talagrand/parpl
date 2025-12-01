use super::*;
use crate::ast::{
    FiniteRealRepr, InfinityNan, NumberExactness, NumberLiteralKind, NumberRadix, NumberValue,
    RealRepr,
};

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
    Lex(&'static str), // nonterminal
}

enum TokenMatcher {
    Bool(bool),
    Char(char),
    Str(&'static str),
    Ident(&'static str),
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

impl TestCase {
    fn run(&self) {
        let result = lex(self.input);
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
            (ErrorMatcher::Lex(nt), ParseError::Lex { nonterminal, .. }) => {
                assert_eq!(nt, nonterminal, "{}: error nonterminal mismatch", test_name);
            }
            _ => panic!(
                "{}: error mismatch. Expected {:?}, got {:?}",
                test_name, self, err
            ),
        }
    }
}

impl std::fmt::Debug for ErrorMatcher {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Incomplete => write!(f, "Incomplete"),
            Self::IncompleteToken => write!(f, "IncompleteToken"),
            Self::Lex(arg0) => f.debug_tuple("Lex").field(arg0).finish(),
        }
    }
}

impl TokenMatcher {
    fn check(&self, token: &Token, test_name: &str, index: usize) {
        match (self, token) {
            (TokenMatcher::Bool(e), Token::Boolean(a)) => {
                assert_eq!(e, a, "{}: token {} mismatch", test_name, index)
            }
            (TokenMatcher::Char(e), Token::Character(a)) => {
                assert_eq!(e, a, "{}: token {} mismatch", test_name, index)
            }
            (TokenMatcher::Str(e), Token::String(a)) => {
                assert_eq!(e, a, "{}: token {} mismatch", test_name, index)
            }
            (TokenMatcher::Ident(e), Token::Identifier(a)) => {
                assert_eq!(e, a, "{}: token {} mismatch", test_name, index)
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
                assert_eq!(
                    text, &n.text,
                    "{}: token {} text mismatch",
                    test_name, index
                );
                check.verify(&n.kind, test_name, index);
            }
            _ => panic!(
                "{}: token {} type mismatch. Expected {:?}, got {:?}",
                test_name, index, self, token
            ),
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
                if let NumberValue::Real(RealRepr::Finite(FiniteRealRepr::Integer { spelling })) =
                    &kind.value
                {
                    assert_eq!(
                        spelling, s,
                        "{}: token {} integer spelling mismatch",
                        test_name, index
                    );
                } else {
                    panic!(
                        "{}: token {} expected Integer, got {:?}",
                        test_name, index, kind
                    );
                }
            }
            NumCheck::Dec(s) => {
                if let NumberValue::Real(RealRepr::Finite(FiniteRealRepr::Decimal { spelling })) =
                    &kind.value
                {
                    assert_eq!(
                        spelling, s,
                        "{}: token {} decimal spelling mismatch",
                        test_name, index
                    );
                } else {
                    panic!(
                        "{}: token {} expected Decimal, got {:?}",
                        test_name, index, kind
                    );
                }
            }
            NumCheck::Rat(s) => {
                if let NumberValue::Real(RealRepr::Finite(FiniteRealRepr::Rational { spelling })) =
                    &kind.value
                {
                    assert_eq!(
                        spelling, s,
                        "{}: token {} rational spelling mismatch",
                        test_name, index
                    );
                } else {
                    panic!(
                        "{}: token {} expected Rational, got {:?}",
                        test_name, index, kind
                    );
                }
            }
            NumCheck::RectInt(r, i) => {
                if let NumberValue::Rectangular { real, imag } = &kind.value {
                    match real {
                        RealRepr::Finite(FiniteRealRepr::Integer { spelling }) => {
                            assert_eq!(spelling, r)
                        }
                        _ => {
                            panic!("{}: token {} expected Integer real part", test_name, index)
                        }
                    }
                    match imag {
                        RealRepr::Finite(FiniteRealRepr::Integer { spelling }) => {
                            assert_eq!(spelling, i)
                        }
                        _ => {
                            panic!("{}: token {} expected Integer imag part", test_name, index)
                        }
                    }
                } else {
                    panic!("{}: token {} expected Rectangular", test_name, index);
                }
            }
            NumCheck::RectRat(r, i) => {
                if let NumberValue::Rectangular { real, imag } = &kind.value {
                    match real {
                        RealRepr::Finite(FiniteRealRepr::Integer { spelling }) => {
                            assert_eq!(spelling, r)
                        }
                        _ => {
                            panic!("{}: token {} expected Integer real part", test_name, index)
                        }
                    }
                    match imag {
                        RealRepr::Finite(FiniteRealRepr::Rational { spelling }) => {
                            assert_eq!(spelling, i)
                        }
                        _ => {
                            panic!("{}: token {} expected Rational imag part", test_name, index)
                        }
                    }
                } else {
                    panic!("{}: token {} expected Rectangular", test_name, index);
                }
            }
            NumCheck::PolarInt(m, a) => {
                if let NumberValue::Polar { magnitude, angle } = &kind.value {
                    match magnitude {
                        RealRepr::Finite(FiniteRealRepr::Integer { spelling }) => {
                            assert_eq!(spelling, m)
                        }
                        _ => {
                            panic!("{}: token {} expected Integer magnitude", test_name, index)
                        }
                    }
                    match angle {
                        RealRepr::Finite(FiniteRealRepr::Integer { spelling }) => {
                            assert_eq!(spelling, a)
                        }
                        _ => panic!("{}: token {} expected Integer angle", test_name, index),
                    }
                } else {
                    panic!("{}: token {} expected Polar", test_name, index);
                }
            }
            NumCheck::PolarRatDec(m, a) => {
                if let NumberValue::Polar { magnitude, angle } = &kind.value {
                    match magnitude {
                        RealRepr::Finite(FiniteRealRepr::Rational { spelling }) => {
                            assert_eq!(spelling, m)
                        }
                        _ => {
                            panic!("{}: token {} expected Rational magnitude", test_name, index)
                        }
                    }
                    match angle {
                        RealRepr::Finite(FiniteRealRepr::Decimal { spelling }) => {
                            assert_eq!(spelling, a)
                        }
                        _ => panic!("{}: token {} expected Decimal angle", test_name, index),
                    }
                } else {
                    panic!("{}: token {} expected Polar", test_name, index);
                }
            }
            NumCheck::Inf(k) => {
                if let NumberValue::Real(RealRepr::Infnan(val)) = &kind.value {
                    assert_eq!(val, k, "{}: token {} infnan mismatch", test_name, index);
                } else {
                    panic!("{}: token {} expected Infnan", test_name, index);
                }
            }
            NumCheck::RectInfImag(r, k) => {
                if let NumberValue::Rectangular { real, imag } = &kind.value {
                    match real {
                        RealRepr::Finite(FiniteRealRepr::Integer { spelling }) => {
                            assert_eq!(spelling, r)
                        }
                        _ => {
                            panic!("{}: token {} expected Integer real part", test_name, index)
                        }
                    }
                    match imag {
                        RealRepr::Infnan(val) => assert_eq!(val, k),
                        _ => panic!("{}: token {} expected Infnan imag part", test_name, index),
                    }
                } else {
                    panic!("{}: token {} expected Rectangular", test_name, index);
                }
            }
            NumCheck::Exact(inner) => {
                assert_eq!(
                    kind.exactness,
                    NumberExactness::Exact,
                    "{}: token {} expected Exact",
                    test_name,
                    index
                );
                inner.verify(kind, test_name, index);
            }
            NumCheck::Inexact(inner) => {
                assert_eq!(
                    kind.exactness,
                    NumberExactness::Inexact,
                    "{}: token {} expected Inexact",
                    test_name,
                    index
                );
                inner.verify(kind, test_name, index);
            }
            NumCheck::Radix(r, inner) => {
                assert_eq!(
                    kind.radix, *r,
                    "{}: token {} radix mismatch",
                    test_name, index
                );
                inner.verify(kind, test_name, index);
            }
        }
    }
}

// --- Tests ---

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
            name: "identifier_unicode",
            input: "λ",
            expected: Expected::Tokens(vec![TokenMatcher::Ident("λ")]),
        },
        TestCase {
            name: "identifier_unicode_mixed",
            input: "α-beta",
            expected: Expected::Tokens(vec![TokenMatcher::Ident("α-beta")]),
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
            expected: Expected::Error(ErrorMatcher::Lex("<directive>")),
        },
        TestCase {
            name: "fold_case_directives",
            input: "#!fold-case\n  #!no-fold-case  ; rest is comment\n",
            expected: Expected::Empty,
        },
        TestCase {
            name: "directive_requires_delimiter_1",
            input: "#!fold-caseX",
            expected: Expected::Error(ErrorMatcher::Lex("<directive>")),
        },
        TestCase {
            name: "directive_requires_delimiter_2",
            input: "#!no-fold-caseX",
            expected: Expected::Error(ErrorMatcher::Lex("<directive>")),
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
            input: "42foo",
            expected: Expected::Error(ErrorMatcher::Lex("<number>")),
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
            expected: Expected::Error(ErrorMatcher::Lex("<number>")),
        },
        TestCase {
            name: "malformed_rational_2",
            input: "1/2/3",
            expected: Expected::Error(ErrorMatcher::Lex("<number>")),
        },
        TestCase {
            name: "invalid_hex_literal",
            input: "0x1",
            expected: Expected::Error(ErrorMatcher::Lex("<number>")),
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
            name: "pure_imaginary_and_polar",
            input: "+i -i +2i -3/4i 1@2 -3/4@5.0 +inf.0i 1+inf.0i",
            expected: Expected::Tokens(vec![
                TokenMatcher::Num("+i", NumCheck::RectInt("0", "1")),
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
                TokenMatcher::Num(
                    "#b+inf.0@1",
                    NumCheck::Radix(NumberRadix::Binary, Box::new(NumCheck::Any)),
                ), // Simplified check
                TokenMatcher::Num("-3/4@5.0", NumCheck::PolarRatDec("-3/4", "5.0")),
            ]),
        },
        TestCase {
            name: "prefixed_errors_1",
            input: "#d#d1",
            expected: Expected::Error(ErrorMatcher::Lex("<number>")),
        },
        TestCase {
            name: "prefixed_errors_2",
            input: "#e#i1",
            expected: Expected::Error(ErrorMatcher::Lex("<number>")),
        },
        TestCase {
            name: "prefixed_errors_3",
            input: "#d42foo",
            expected: Expected::Error(ErrorMatcher::Lex("<number>")),
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
                    NumCheck::Radix(
                        NumberRadix::Binary,
                        Box::new(NumCheck::Inf(InfinityNan::PositiveInfinity)),
                    ),
                ),
                TokenMatcher::Num(
                    "#x-nan.0",
                    NumCheck::Radix(
                        NumberRadix::Hexadecimal,
                        Box::new(NumCheck::Inf(InfinityNan::NegativeNaN)),
                    ),
                ),
                TokenMatcher::Num(
                    "#b#e+inf.0",
                    NumCheck::Exact(Box::new(NumCheck::Radix(
                        NumberRadix::Binary,
                        Box::new(NumCheck::Inf(InfinityNan::PositiveInfinity)),
                    ))),
                ),
                TokenMatcher::Num(
                    "#i#x-nan.0",
                    NumCheck::Inexact(Box::new(NumCheck::Radix(
                        NumberRadix::Hexadecimal,
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
                    NumCheck::Radix(NumberRadix::Binary, Box::new(NumCheck::Int("1010"))),
                ),
                TokenMatcher::Num(
                    "#o77",
                    NumCheck::Radix(NumberRadix::Octal, Box::new(NumCheck::Int("77"))),
                ),
                TokenMatcher::Num(
                    "#x1f",
                    NumCheck::Radix(NumberRadix::Hexadecimal, Box::new(NumCheck::Int("1f"))),
                ),
                TokenMatcher::Num(
                    "#b101/11",
                    NumCheck::Radix(NumberRadix::Binary, Box::new(NumCheck::Rat("101/11"))),
                ),
                TokenMatcher::Num(
                    "#xA/F",
                    NumCheck::Radix(NumberRadix::Hexadecimal, Box::new(NumCheck::Rat("A/F"))),
                ),
                TokenMatcher::Num(
                    "#b#e1",
                    NumCheck::Exact(Box::new(NumCheck::Radix(
                        NumberRadix::Binary,
                        Box::new(NumCheck::Int("1")),
                    ))),
                ),
                TokenMatcher::Num(
                    "#i#o7",
                    NumCheck::Inexact(Box::new(NumCheck::Radix(
                        NumberRadix::Octal,
                        Box::new(NumCheck::Int("7")),
                    ))),
                ),
            ]),
        },
        TestCase {
            name: "nondecimal_errors_1",
            input: "#b102",
            expected: Expected::Error(ErrorMatcher::Lex("<number>")),
        },
        TestCase {
            name: "nondecimal_errors_2",
            input: "#o7/",
            expected: Expected::Error(ErrorMatcher::IncompleteToken),
        },
        TestCase {
            name: "nondecimal_errors_3",
            input: "#xA/G",
            expected: Expected::Error(ErrorMatcher::Lex("<number>")),
        },
        TestCase {
            name: "nondecimal_errors_4",
            input: "#b#b1",
            expected: Expected::Error(ErrorMatcher::Lex("<number>")),
        },
        TestCase {
            name: "nondecimal_errors_5",
            input: "#i#e#b1",
            expected: Expected::Error(ErrorMatcher::Lex("<number>")),
        },
        TestCase {
            name: "nondecimal_errors_6",
            input: "#b1010foo",
            expected: Expected::Error(ErrorMatcher::Lex("<number>")),
        },
        TestCase {
            name: "nondecimal_errors_7",
            input: "#b101e10",
            expected: Expected::Error(ErrorMatcher::Lex("<number>")),
        },
        TestCase {
            name: "nondecimal_errors_8",
            input: "#x1.2",
            expected: Expected::Error(ErrorMatcher::Lex("<number>")),
        },
        TestCase {
            name: "nondecimal_complex",
            input: "#b1+10i #x1-2i #b+i #o-i #b1@10 #x1+inf.0i #b+inf.0i",
            expected: Expected::Tokens(vec![
                TokenMatcher::Num(
                    "#b1+10i",
                    NumCheck::Radix(NumberRadix::Binary, Box::new(NumCheck::RectInt("1", "+10"))),
                ),
                TokenMatcher::Num(
                    "#x1-2i",
                    NumCheck::Radix(
                        NumberRadix::Hexadecimal,
                        Box::new(NumCheck::RectInt("1", "-2")),
                    ),
                ),
                TokenMatcher::Num(
                    "#b+i",
                    NumCheck::Radix(NumberRadix::Binary, Box::new(NumCheck::RectInt("0", "1"))),
                ),
                TokenMatcher::Num(
                    "#o-i",
                    NumCheck::Radix(NumberRadix::Octal, Box::new(NumCheck::RectInt("0", "-1"))),
                ),
                TokenMatcher::Num(
                    "#b1@10",
                    NumCheck::Radix(NumberRadix::Binary, Box::new(NumCheck::PolarInt("1", "10"))),
                ),
                TokenMatcher::Num(
                    "#x1+inf.0i",
                    NumCheck::Radix(
                        NumberRadix::Hexadecimal,
                        Box::new(NumCheck::RectInfImag("1", InfinityNan::PositiveInfinity)),
                    ),
                ),
                TokenMatcher::Num(
                    "#b+inf.0i",
                    NumCheck::Radix(
                        NumberRadix::Binary,
                        Box::new(NumCheck::RectInfImag("0", InfinityNan::PositiveInfinity)),
                    ),
                ),
            ]),
        },
        TestCase {
            name: "infnan_errors_1",
            input: "+inf.0foo",
            expected: Expected::Error(ErrorMatcher::Lex("<number>")),
        },
        TestCase {
            name: "infnan_errors_2",
            input: "#e+inf.0bar",
            expected: Expected::Error(ErrorMatcher::Lex("<number>")),
        },
        TestCase {
            name: "ambiguous_complex_1",
            input: "1+2",
            expected: Expected::Error(ErrorMatcher::IncompleteToken),
        },
        TestCase {
            name: "ambiguous_complex_2",
            input: "1+2)",
            expected: Expected::Error(ErrorMatcher::Lex("<number>")),
        },
        TestCase {
            name: "ambiguous_complex_3",
            input: "#e1@foo",
            expected: Expected::Error(ErrorMatcher::Lex("<number>")),
        },
        TestCase {
            name: "ambiguous_complex_4",
            input: "#b1@10x",
            expected: Expected::Error(ErrorMatcher::Lex("<number>")),
        },
        TestCase {
            name: "ambiguous_complex_5",
            input: "+inf.0x",
            expected: Expected::Error(ErrorMatcher::Lex("<number>")),
        },
        TestCase {
            name: "ambiguous_complex_6",
            input: "+inf.0i0",
            expected: Expected::Error(ErrorMatcher::Lex("<number>")),
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
            name: "strings_incomplete",
            input: "\"unterminated",
            expected: Expected::Error(ErrorMatcher::Incomplete),
        },
        TestCase {
            name: "strings_invalid_hex",
            input: "\"\\xZZ;\"",
            expected: Expected::Error(ErrorMatcher::Lex("<string>")),
        },
        TestCase {
            name: "strings_incomplete_hex",
            input: "\"\\x",
            expected: Expected::Error(ErrorMatcher::IncompleteToken),
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
    ];

    for case in cases {
        case.run();
    }
}
