pub mod lex;

/// A byte-offset span into the original source.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

/// A syntax object: a value paired with its source span.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Syntax<T> {
    pub span: Span,
    pub value: T,
}

impl<T> Syntax<T> {
    pub fn new(span: Span, value: T) -> Self {
        Self { span, value }
    }
}

/// Radix of a Scheme number literal as specified by `<radix R>`.
///
/// Grammar reference (Formal syntax / `<number>`):
///
/// ```text
/// <radix 2>  ::= #b
/// <radix 8>  ::= #o
/// <radix 10> ::= <empty> | #d
/// <radix 16> ::= #x
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NumberRadix {
    Binary,
    Octal,
    Decimal,
    Hexadecimal,
}

/// Exactness marker of a Scheme number literal.
///
/// ```text
/// <exactness> ::= <empty> | #i | #e
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NumberExactness {
    Exact,
    Inexact,
    /// No explicit `#e`/`#i` prefix; exactness is determined
    /// by the default rules of the report.
    Unspecified,
}

/// The four special infinities / NaNs used by `<infnan>`.
///
/// ```text
/// <infnan> ::= +inf.0 | -inf.0 | +nan.0 | -nan.0
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InfinityNan {
    PositiveInfinity,
    NegativeInfinity,
    PositiveNaN,
    NegativeNaN,
}

/// Finite real-number spellings built from `<ureal R>` and
/// `<decimal 10>`.
///
/// All `spelling` fields are normalized substrings of the original
/// literal, without surrounding whitespace but potentially including
/// an explicit sign.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FiniteRealRepr {
    /// A (possibly signed) integer, e.g. "42", "-7".
    Integer { spelling: String },
    /// A (possibly signed) rational, e.g. "3/4", "-5/16".
    Rational { spelling: String },
    /// A (possibly signed) decimal, e.g. "3.14", "-.5", "1e3".
    Decimal { spelling: String },
}

/// Representation of `<real R>` values.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RealRepr {
    /// A finite real built from `<ureal R>` or `<decimal 10>`.
    Finite(FiniteRealRepr),
    /// One of the four `<infnan>` spellings.
    Infnan(InfinityNan),
}

/// Complex-number structure corresponding to `<complex R>`.
///
/// ```text
/// <complex R> ::= <real R>
///                | <real R> @ <real R>
///                | <real R> + <ureal R> i
///                | <real R> - <ureal R> i
///                | <real R> + i
///                | <real R> - i
///                | <real R> <infnan> i
///                | + <ureal R> i
///                | - <ureal R> i
///                | <infnan> i
///                | + i
///                | - i
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NumberValue {
    /// A purely real number `<real R>`.
    Real(RealRepr),
    /// Rectangular complex form `a+bi` / `a-bi` and related
    /// special cases normalized into explicit real and imaginary
    /// parts.
    Rectangular { real: RealRepr, imag: RealRepr },
    /// Polar complex form `r@theta`.
    Polar {
        magnitude: RealRepr,
        angle: RealRepr,
    },
}

/// Full structural classification of a Scheme number literal.
///
/// This mirrors `<num R> ::= <prefix R> <complex R>`: `radix` and
/// `exactness` capture `<prefix R>`, while `value` is the parsed
/// `<complex R>` structure.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NumberLiteralKind {
    pub radix: NumberRadix,
    pub exactness: NumberExactness,
    pub value: NumberValue,
}

impl NumberLiteralKind {
    /// Convert to a `NumberLiteral` with an empty text field.
    /// The text is filled in later by the lexer driver.
    pub fn into_literal(self) -> NumberLiteral {
        NumberLiteral {
            text: String::new(),
            kind: self,
        }
    }
}

/// A number literal, keeping the original spelling from the source.
#[derive(Clone, Debug, PartialEq)]
pub struct NumberLiteral {
    /// Exact token text, including prefixes/suffixes.
    pub text: String,
    pub kind: NumberLiteralKind,
}

/// Datum syntax as defined in the "External representations" section
/// of `spec/syn.md`.
#[derive(Clone, Debug, PartialEq)]
pub enum Datum {
    Boolean(bool),
    Number(NumberLiteral),
    Character(char),
    String(String),
    Symbol(String),
    ByteVector(Vec<u8>),
    /// Proper and improper lists are represented via pairs.
    Pair(Box<Syntax<Datum>>, Box<Syntax<Datum>>),
    Vector(Vec<Syntax<Datum>>),
    /// A labeled datum: #n=datum
    Labeled(u64, Box<Syntax<Datum>>),
    /// A reference to a previously defined label: #n#
    LabelRef(u64),
}

/// Top-level parse error type. This will grow as the implementation
/// starts enforcing more of `spec/syn.md`.
#[derive(Debug, thiserror::Error)]
pub enum ParseError {
    /// The input ends in the middle of a grammatically valid construct
    /// and more characters are required to decide the result.
    ///
    /// In a REPL, this is the cue to prompt the user for more input
    /// instead of reporting a hard error.
    #[error("input is incomplete; more data required")]
    Incomplete,

    /// The input ends in the middle of a token (e.g., `#\`, `1e+`, `3/`).
    ///
    /// Unlike `Incomplete`, this indicates an incomplete token rather than
    /// an incomplete multi-line construct. In a REPL context, this is
    /// typically a user error rather than a prompt-for-more signal.
    /// In a streaming context, this still means more input is needed.
    #[error("incomplete token; input ends mid-token")]
    IncompleteToken,

    /// A lexical error detected while recognizing a particular
    /// nonterminal (for example, `<string>` or `<identifier>`).
    #[error("lexical error in {nonterminal} at {span:?}: {message}")]
    Lex {
        span: Span,
        nonterminal: &'static str,
        message: String,
    },

    /// A syntactic error detected while parsing a particular
    /// nonterminal (for example, `<datum>` or `<expression>`).
    #[error("syntax error in {nonterminal} at {span:?}: {message}")]
    Syntax {
        span: Span,
        nonterminal: &'static str,
        message: String,
    },

    /// Temporary catch-all while the parser is still a stub.
    #[error("unimplemented parser")]
    Unimplemented,
}

impl ParseError {
    /// Helper for constructing a lexical error.
    pub fn lexical(span: Span, nonterminal: &'static str, message: impl Into<String>) -> Self {
        ParseError::Lex {
            span,
            nonterminal,
            message: message.into(),
        }
    }

    /// Helper for constructing a syntax error.
    pub fn syntax(span: Span, nonterminal: &'static str, message: impl Into<String>) -> Self {
        ParseError::Syntax {
            span,
            nonterminal,
            message: message.into(),
        }
    }
}

/// Parse a single `<datum>` from the given source string.
///
/// Grammar reference: see `spec/syn.md`, section *External representations*,
/// production:
///
/// ```text
/// <datum> ::= <simple datum> | <compound datum>
///           | <label> = <datum> | <label> #
/// ```
///
/// Currently, only the following sub-productions are implemented:
///
/// ```text
/// <simple datum> ::= <boolean> | <number>
///                   | <character> | <string> | <symbol> | <bytevector>
/// <boolean> ::= #t | #f | #true | #false
/// <string> ::= " <string element>* "
/// ```
///
/// That is, `parse_datum` recognizes boolean and string datums; all other
/// inputs return `ParseError::Unimplemented` for now.
pub fn parse_datum(source: &str) -> Result<Syntax<Datum>, ParseError> {
    // `<simple datum> ::= <boolean>`
    if let Some(b) = parse_boolean_datum(source) {
        let leading_ws = source.len() - source.trim_start().len();
        let trimmed = source.trim();
        let span = Span {
            start: leading_ws,
            end: leading_ws + trimmed.len(),
        };
        return Ok(Syntax::new(span, Datum::Boolean(b)));
    }

    // `<simple datum> ::= <string>`
    if let Some(string_syntax) = parse_string_datum(source)? {
        return Ok(string_syntax);
    }

    Err(ParseError::Unimplemented)
}

/// Boolean external representations.
///
/// Grammar reference (Formal syntax / Lexical structure):
///
/// ```text
/// <boolean> ::= #t | #f | #true | #false
/// ```
///
/// This helper implements only that rule, in a case-insensitive way for
/// the alphabetic characters. It also allows surrounding ASCII
/// whitespace, but does not yet understand comments or other
/// `<intertoken space>`.
fn parse_boolean_datum(source: &str) -> Option<bool> {
    let trimmed = source.trim();
    let rest = trimmed.strip_prefix('#')?;
    let lower = rest.to_ascii_lowercase();
    match lower.as_str() {
        "t" | "true" => Some(true),
        "f" | "false" => Some(false),
        _ => None,
    }
}

/// String external representations.
///
/// Grammar reference (Formal syntax / Lexical structure):
///
/// ```text
/// <string> ::= " <string element>* "
///
/// <string element> ::= any character other than " or \
///                     | <mnemonic escape> | \" | \\
///                     | \ <intraline whitespace>* <line ending>
///                       <intraline whitespace>*
///                     | <inline hex escape>
///
/// <mnemonic escape> ::= \a | \b | \t | \n | \r
/// <inline hex escape> ::= \x<hex scalar value>;
/// <hex scalar value> ::= <hex digit>+
/// ```
///
/// This helper implements that grammar for a single `<string>` datum,
/// allowing surrounding whitespace but requiring the entire non-space
/// input to be exactly one string literal.
fn parse_string_datum(source: &str) -> Result<Option<Syntax<Datum>>, ParseError> {
    let leading_ws = source.len() - source.trim_start().len();
    let trimmed = source.trim();

    let overall_span = Span {
        start: leading_ws,
        end: leading_ws + trimmed.len(),
    };

    if trimmed.is_empty() {
        return Ok(None);
    }

    // Must start with opening quote.
    let mut chars = trimmed.char_indices();
    let (first_idx, first_ch) = match chars.next() {
        Some(p) => p,
        None => return Ok(None),
    };
    if first_ch != '"' || first_idx != 0 {
        return Ok(None);
    }

    let mut result = String::new();
    let mut pos = 1; // byte index into `trimmed`, just after opening quote
    let bytes = trimmed.as_bytes();
    let len = bytes.len();
    let mut closing_quote_idx = None;

    while pos < len {
        let ch = trimmed[pos..].chars().next().unwrap();
        let ch_len = ch.len_utf8();

        match ch {
            '"' => {
                // End of string literal.
                closing_quote_idx = Some(pos);
                pos += ch_len;
                break;
            }
            '\\' => {
                // Start of an escape sequence.
                pos += ch_len; // move past '\\'
                if pos >= len {
                    // Nothing after backslash: incomplete escape.
                    return Err(ParseError::Incomplete);
                }

                let next_ch = trimmed[pos..].chars().next().unwrap();
                let next_len = next_ch.len_utf8();

                // <mnemonic escape> ::= \a | \b | \t | \n | \r
                match next_ch {
                    'a' => {
                        result.push('\u{7}');
                        pos += next_len;
                        continue;
                    }
                    'b' => {
                        result.push('\u{8}');
                        pos += next_len;
                        continue;
                    }
                    't' => {
                        result.push('\t');
                        pos += next_len;
                        continue;
                    }
                    'n' => {
                        result.push('\n');
                        pos += next_len;
                        continue;
                    }
                    'r' => {
                        result.push('\r');
                        pos += next_len;
                        continue;
                    }
                    '"' => {
                        // `\"` inside string.
                        result.push('"');
                        pos += next_len;
                        continue;
                    }
                    '\\' => {
                        // `\\` inside string.
                        result.push('\\');
                        pos += next_len;
                        continue;
                    }
                    'x' => {
                        // <inline hex escape> ::= \x<hex scalar value>;
                        pos += next_len; // move past 'x'
                        let mut hex_start = pos;
                        while hex_start < len {
                            let c = trimmed[hex_start..].chars().next().unwrap();
                            if c.is_ascii_hexdigit() {
                                hex_start += c.len_utf8();
                            } else {
                                break;
                            }
                        }

                        if hex_start == pos {
                            // No hex digits.
                            return Err(ParseError::lexical(
                                overall_span,
                                "<string>",
                                "expected hex digits after \\x",
                            ));
                        }

                        if hex_start >= len {
                            return Err(ParseError::Incomplete);
                        }

                        let end_ch = trimmed[hex_start..].chars().next().unwrap();
                        if end_ch != ';' {
                            return Err(ParseError::lexical(
                                overall_span,
                                "<string>",
                                "missing terminating ';' in hex escape",
                            ));
                        }

                        let hex_digits = &trimmed[pos..hex_start];
                        let codepoint = u32::from_str_radix(hex_digits, 16).map_err(|_| {
                            ParseError::lexical(
                                overall_span,
                                "<string>",
                                "invalid hex digits in hex escape",
                            )
                        })?;
                        if let Some(c) = char::from_u32(codepoint) {
                            result.push(c);
                        } else {
                            return Err(ParseError::lexical(
                                overall_span,
                                "<string>",
                                "hex escape is not a valid Unicode scalar value",
                            ));
                        }

                        pos = hex_start + end_ch.len_utf8();
                        continue;
                    }
                    _ => {
                        // Attempt the line-ending escape:
                        // \ <intraline whitespace>* <line ending> <intraline whitespace>*
                        let mut idx = pos;
                        while idx < len {
                            let c = trimmed[idx..].chars().next().unwrap();
                            if c == ' ' || c == '\t' {
                                idx += c.len_utf8();
                            } else {
                                break;
                            }
                        }

                        if idx >= len {
                            return Err(ParseError::Incomplete);
                        }

                        let c = trimmed[idx..].chars().next().unwrap();
                        if c == '\n' || c == '\r' {
                            // Consume the line ending.
                            idx += c.len_utf8();
                            // Handle CRLF specially: we already consumed '\r', check for '\n'.
                            if c == '\r' && idx < len {
                                let c2 = trimmed[idx..].chars().next().unwrap();
                                if c2 == '\n' {
                                    idx += c2.len_utf8();
                                }
                            }

                            // Consume following intraline whitespace.
                            while idx < len {
                                let c2 = trimmed[idx..].chars().next().unwrap();
                                if c2 == ' ' || c2 == '\t' {
                                    idx += c2.len_utf8();
                                } else {
                                    break;
                                }
                            }

                            // The whole backslash + line ending sequence contributes
                            // nothing to the resulting string.
                            pos = idx;
                            continue;
                        }

                        // Unknown escape.
                        return Err(ParseError::lexical(
                            overall_span,
                            "<string>",
                            "unknown escape sequence in string literal",
                        ));
                    }
                }
            }
            '\n' | '\r' => {
                // Newlines are not allowed as raw string characters.
                return Err(ParseError::lexical(
                    overall_span,
                    "<string>",
                    "newline character in string literal",
                ));
            }
            _ => {
                // Any character other than '"' or '\\'.
                result.push(ch);
                pos += ch_len;
            }
        }
    }

    let closing = match closing_quote_idx {
        Some(i) => i,
        None => return Err(ParseError::Incomplete),
    };

    // Ensure only whitespace follows the closing quote in the trimmed input.
    let rest = &trimmed[closing + '"'.len_utf8()..];
    if !rest.chars().all(char::is_whitespace) {
        return Err(ParseError::lexical(
            overall_span,
            "<string>",
            "extra characters after end of string literal",
        ));
    }

    let span = Span {
        start: leading_ws,
        end: leading_ws + closing + '"'.len_utf8(),
    };

    Ok(Some(Syntax::new(span, Datum::String(result))))
}

/// Expression syntax as defined in the "Expressions" section
/// of `spec/syn.md`. This is currently a placeholder and will
/// be fleshed out rule by rule.
#[derive(Clone, Debug, PartialEq)]
pub enum Expr {}

/// Program syntax as defined in the "Programs and definitions"
/// section of `spec/syn.md`. Placeholder for now.
#[derive(Clone, Debug, PartialEq)]
pub struct Program;

/// Library syntax as defined in the "Libraries" section
/// of `spec/syn.md`. Placeholder for now.
#[derive(Clone, Debug, PartialEq)]
pub struct Library;

/// Parse a single `<expression>` from the given source string.
///
/// Grammar reference: see `spec/syn.md`, section *Expressions*.
///
/// Currently this is a stub and always returns
/// `ParseError::Unimplemented`.
pub fn parse_expression(_source: &str) -> Result<Syntax<Expr>, ParseError> {
    Err(ParseError::Unimplemented)
}

/// Parse a `<program>` from the given source string.
///
/// Grammar reference: see `spec/syn.md`, section *Programs and definitions*.
///
/// Currently this is a stub and always returns
/// `ParseError::Unimplemented`.
pub fn parse_program(_source: &str) -> Result<Syntax<Program>, ParseError> {
    Err(ParseError::Unimplemented)
}

/// Parse a `<library>` from the given source string.
///
/// Grammar reference: see `spec/syn.md`, section *Libraries*.
///
/// Currently this is a stub and always returns
/// `ParseError::Unimplemented`.
pub fn parse_library(_source: &str) -> Result<Syntax<Library>, ParseError> {
    Err(ParseError::Unimplemented)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_boolean_datums() {
        let t = parse_datum("#t").unwrap();
        assert!(matches!(t.value, Datum::Boolean(true)));

        let f = parse_datum("#f").unwrap();
        assert!(matches!(f.value, Datum::Boolean(false)));

        let t_long = parse_datum("#true").unwrap();
        assert!(matches!(t_long.value, Datum::Boolean(true)));

        let f_long = parse_datum("#false").unwrap();
        assert!(matches!(f_long.value, Datum::Boolean(false)));

        // Case-insensitive forms.
        let t_upper = parse_datum("#T").unwrap();
        assert!(matches!(t_upper.value, Datum::Boolean(true)));

        let f_mixed = parse_datum("#FaLsE").unwrap();
        assert!(matches!(f_mixed.value, Datum::Boolean(false)));
    }

    #[test]
    fn non_boolean_datum_is_unimplemented_for_now() {
        let err = parse_datum("42").unwrap_err();
        assert!(matches!(err, ParseError::Unimplemented));
    }

    #[test]
    fn parses_simple_strings() {
        let s = parse_datum("\"hello\"").unwrap();
        assert!(matches!(s.value, Datum::String(ref v) if v == "hello"));

        let s_ws = parse_datum("  \"hi\"  ").unwrap();
        assert!(matches!(s_ws.value, Datum::String(ref v) if v == "hi"));
    }

    #[test]
    fn parses_string_escapes() {
        // Scheme string literal: "a\n\t\r\b\a\\\""
        let s = parse_datum(r#""a\n\t\r\b\a\\\"""#).unwrap();
        if let Datum::String(v) = s.value {
            assert_eq!(v, "a\n\t\r\u{8}\u{7}\\\"".to_string());
        } else {
            panic!("expected string datum");
        }

        // Scheme string literal: "\x41;"
        let hex = parse_datum(r#""\x41;""#).unwrap();
        assert!(matches!(hex.value, Datum::String(ref v) if v == "A"));
    }

    #[test]
    fn parses_string_with_line_splice() {
        // Scheme string literal containing a backslash-newline splice.
        let s = parse_datum("\"foo\\\n   bar\"").unwrap();
        assert!(matches!(s.value, Datum::String(ref v) if v == "foobar"));
    }

    #[test]
    fn detects_incomplete_string() {
        let err = parse_datum("\"unterminated").unwrap_err();
        assert!(matches!(err, ParseError::Incomplete));
    }

    #[test]
    fn top_level_parse_stubs_return_unimplemented() {
        let err_expr = parse_expression("(+ 1 2)").unwrap_err();
        assert!(matches!(err_expr, ParseError::Unimplemented));

        let err_prog = parse_program("(program)").unwrap_err();
        assert!(matches!(err_prog, ParseError::Unimplemented));

        let err_lib = parse_library("(define-library (foo))").unwrap_err();
        assert!(matches!(err_lib, ParseError::Unimplemented));
    }
}
