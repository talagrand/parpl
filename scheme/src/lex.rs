use crate::{
    FiniteRealRepr, InfinityNan, NumberExactness, NumberLiteral, NumberLiteralKind, NumberRadix,
    NumberValue, ParseError, RealRepr, Span, Syntax,
};

/// Lexical tokens as defined by `<token>` in `spec/syn.md`.
///
/// Grammar reference (Formal syntax / Lexical structure):
///
/// ```text
/// <token> ::= <identifier> | <boolean> | <number>
///           | <character> | <string>
///           | ( | ) | #( | #u8( | ' | ` | , | ,@ | .
/// ```
#[derive(Clone, Debug, PartialEq)]
pub enum Token {
    /// `<identifier>`
    Identifier(String),
    /// `<boolean>`
    Boolean(bool),
    /// `<number>`
    Number(NumberLiteral),
    /// `<character>`
    Character(char),
    /// `<string>`
    String(String),
    /// `(`
    LParen,
    /// `)`
    RParen,
    /// `#(`
    VectorStart,
    /// `#u8(`
    ByteVectorStart,
    /// `'`
    Quote,
    /// `` ` ``
    Backquote,
    /// `,`
    Comma,
    /// `,@`
    CommaAt,
    /// `.`
    Dot,
}

/// A single token paired with its source span.
pub type SpannedToken = Syntax<Token>;

/// Lex all `<token>`s from the given source string, skipping
/// `<intertoken space>` (whitespace, comments, nested comments,
/// and directives).
///
/// Grammar reference (Formal syntax / Lexical structure):
///
/// ```text
/// <intertoken space> ::= <atmosphere>*
/// <atmosphere> ::= <whitespace> | <comment> | <directive>
///
/// <comment> ::= ; <all subsequent characters up to a line ending
///                or end of file>
/// <nested comment> ::= #| <comment text> |#
/// <directive> ::= #!fold-case | #!no-fold-case
/// ```
///
/// For now, `lex` implements `<intertoken space>` and a subset of
/// `<token>` recognition: inputs that contain only intertoken space
/// yield an empty token list. We are gradually adding `<token>`
/// classifications, currently `<boolean>`, `<character>`, and `<string>`.
pub fn lex(source: &str) -> Result<Vec<SpannedToken>, ParseError> {
    let mut tokens = Vec::new();
    let mut pos = 0usize;
    let len = source.len();

    // Track `#!fold-case` / `#!no-fold-case` directives. This will
    // later influence how identifiers and symbols are recognized.
    let mut _fold_case = false;

    while pos < len {
        // Skip `<intertoken space>` before each token.
        loop {
            if pos >= len {
                return Ok(tokens);
            }

            let ch = match source[pos..].chars().next() {
                Some(c) => c,
                None => return Ok(tokens),
            };

            match ch {
                // <whitespace>
                ' ' | '\t' | '\n' | '\r' => {
                    pos += ch.len_utf8();
                }
                // Line comment: `; ... <line ending or EOF>`
                ';' => {
                    pos += ch.len_utf8();
                    while pos < len {
                        let c = match source[pos..].chars().next() {
                            Some(c) => c,
                            None => break,
                        };
                        pos += c.len_utf8();
                        if c == '\n' || c == '\r' {
                            break;
                        }
                    }
                }
                // Possible nested comment or directive starting with '#'.
                '#' => {
                    let hash_pos = pos;
                    pos += ch.len_utf8();
                    if pos >= len {
                        // Just a solitary '#': leave it for tokenization.
                        pos = hash_pos;
                        break;
                    }

                    let next = source[pos..].chars().next().unwrap();
                    match next {
                        // `<nested comment> ::= #| <comment text> |#`
                        '|' => {
                            pos += next.len_utf8();
                            pos = skip_nested_comment(source, pos)?;
                        }
                        // `<directive> ::= #!fold-case | #!no-fold-case`
                        '!' => {
                            let start = hash_pos;
                            let text = &source[start..];
                            if text.starts_with("#!fold-case") {
                                _fold_case = true;
                                pos = start + "#!fold-case".len();
                            } else if text.starts_with("#!no-fold-case") {
                                _fold_case = false;
                                pos = start + "#!no-fold-case".len();
                            } else {
                                let span = Span { start, end: len };
                                return Err(ParseError::lexical(
                                    span,
                                    "<directive>",
                                    "unknown directive",
                                ));
                            }
                        }
                        _ => {
                            // Not a nested comment or directive; this
                            // begins a real token.
                            pos = hash_pos;
                            break;
                        }
                    }
                }
                _ => {
                    // Start of a real token.
                    break;
                }
            }
        }

        if pos >= len {
            break;
        }

        // Token recognition.
        let ch = source[pos..].chars().next().unwrap();
        match ch {
            '"' => {
                // String literal token.
                //
                // Grammar reference:
                //
                // ```text
                // <string> ::= " <string element>* "
                //
                // <string element> ::= any character other than " or \
                //                     | <mnemonic escape> | \" | \\
                //                     | \\ <intraline whitespace>* <line ending>
                //                       <intraline whitespace>*
                //                     | <inline hex escape>
                // ```

                let start = pos;
                pos += ch.len_utf8(); // skip opening quote

                let mut result = String::new();

                loop {
                    if pos >= len {
                        // Unterminated string.
                        return Err(ParseError::Incomplete);
                    }

                    let ch = source[pos..].chars().next().unwrap();
                    let ch_len = ch.len_utf8();

                    match ch {
                        '"' => {
                            // Closing quote.
                            pos += ch_len;
                            let span = Span { start, end: pos };
                            tokens.push(Syntax::new(span, Token::String(result)));
                            break;
                        }
                        '\\' => {
                            // Start of an escape sequence.
                            pos += ch_len; // move past '\\'
                            if pos >= len {
                                return Err(ParseError::Incomplete);
                            }

                            let next_ch = source[pos..].chars().next().unwrap();
                            let next_len = next_ch.len_utf8();

                            match next_ch {
                                // <mnemonic escape> ::= \\a | \\b | \\t | \\n | \\r
                                'a' => {
                                    result.push('\u{7}');
                                    pos += next_len;
                                }
                                'b' => {
                                    result.push('\u{8}');
                                    pos += next_len;
                                }
                                't' => {
                                    result.push('\t');
                                    pos += next_len;
                                }
                                'n' => {
                                    result.push('\n');
                                    pos += next_len;
                                }
                                'r' => {
                                    result.push('\r');
                                    pos += next_len;
                                }
                                '"' => {
                                    result.push('"');
                                    pos += next_len;
                                }
                                '\\' => {
                                    result.push('\\');
                                    pos += next_len;
                                }
                                'x' | 'X' => {
                                    // <inline hex escape> ::= \\x<hex scalar value>;
                                    pos += next_len; // move past 'x'
                                    let hex_start = pos;
                                    while pos < len {
                                        let c = source[pos..].chars().next().unwrap();
                                        if c.is_ascii_hexdigit() {
                                            pos += c.len_utf8();
                                        } else {
                                            break;
                                        }
                                    }

                                    if pos == hex_start {
                                        let span = Span { start, end: pos };
                                        return Err(ParseError::lexical(
                                            span,
                                            "<string>",
                                            "expected hex digits after \\x",
                                        ));
                                    }

                                    if pos >= len {
                                        return Err(ParseError::Incomplete);
                                    }

                                    let end_ch = source[pos..].chars().next().unwrap();
                                    if end_ch != ';' {
                                        let span = Span { start, end: pos };
                                        return Err(ParseError::lexical(
                                            span,
                                            "<string>",
                                            "missing terminating ';' in hex escape",
                                        ));
                                    }

                                    let hex_digits = &source[hex_start..pos];
                                    let codepoint =
                                        u32::from_str_radix(hex_digits, 16).map_err(|_| {
                                            let span = Span { start, end: pos };
                                            ParseError::lexical(
                                                span,
                                                "<string>",
                                                "invalid hex digits in hex escape",
                                            )
                                        })?;
                                    if let Some(c) = char::from_u32(codepoint) {
                                        result.push(c);
                                    } else {
                                        let span = Span { start, end: pos };
                                        return Err(ParseError::lexical(
                                            span,
                                            "<string>",
                                            "hex escape is not a valid Unicode scalar value",
                                        ));
                                    }

                                    // Consume the ';'.
                                    pos += end_ch.len_utf8();
                                }
                                _ => {
                                    // Attempt the line-ending escape:
                                    // \\ <intraline whitespace>* <line ending>
                                    //    <intraline whitespace>*
                                    let mut idx = pos;
                                    while idx < len {
                                        let c = source[idx..].chars().next().unwrap();
                                        if c == ' ' || c == '\t' {
                                            idx += c.len_utf8();
                                        } else {
                                            break;
                                        }
                                    }

                                    if idx >= len {
                                        return Err(ParseError::Incomplete);
                                    }

                                    let c = source[idx..].chars().next().unwrap();
                                    if c == '\n' || c == '\r' {
                                        // Consume the line ending (including optional LF after CR).
                                        idx += c.len_utf8();
                                        if c == '\r' && idx < len {
                                            let c2 = source[idx..].chars().next().unwrap();
                                            if c2 == '\n' {
                                                idx += c2.len_utf8();
                                            }
                                        }

                                        // Consume following intraline whitespace.
                                        while idx < len {
                                            let c2 = source[idx..].chars().next().unwrap();
                                            if c2 == ' ' || c2 == '\t' {
                                                idx += c2.len_utf8();
                                            } else {
                                                break;
                                            }
                                        }

                                        // Backslash + line ending sequence contributes nothing.
                                        pos = idx;
                                    } else {
                                        let span = Span { start, end: idx };
                                        return Err(ParseError::lexical(
                                            span,
                                            "<string>",
                                            "unknown escape sequence in string literal",
                                        ));
                                    }
                                }
                            }
                        }
                        '\n' | '\r' => {
                            // Newlines are not allowed as raw string characters.
                            let span = Span {
                                start,
                                end: pos + ch_len,
                            };
                            return Err(ParseError::lexical(
                                span,
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
            }
            '+' | '-' | '0'..='9' | '.' => {
                // `<number>` token in decimal radix (R = 10), including
                // both real and complex forms as specified by `<complex 10>`.
                let start = pos;

                // If we start with a '.', require a digit next; otherwise this
                // could be the standalone `.` token or part of an identifier
                // once those are implemented.
                if ch == '.' {
                    let look = pos + ch.len_utf8();
                    if look >= len {
                        return Err(ParseError::Unimplemented);
                    }
                    let next = source[look..].chars().next().unwrap();
                    if !next.is_ascii_digit() {
                        return Err(ParseError::Unimplemented);
                    }
                }

                if let Some((end, literal)) = lex_complex_decimal(source, start)? {
                    let span = Span { start, end };
                    tokens.push(Syntax::new(span, Token::Number(literal)));
                    pos = end;
                    continue;
                } else {
                    // Not a `<number>` starting here; leave to other
                    // token classes (identifiers, etc.) once implemented.
                    return Err(ParseError::Unimplemented);
                }
            }
            '#' => {
                let start = pos;
                pos += ch.len_utf8();
                if pos >= len {
                    // Incomplete `#`-prefixed token (boolean/character/etc.).
                    return Err(ParseError::Incomplete);
                }

                let next = source[pos..].chars().next().unwrap();

                // `<character>` tokens
                //
                // Grammar reference:
                //
                // ```text
                // <character> ::= #\ <any character>
                //                | #\ <character name>
                //                | #\x<hex scalar value>
                //
                // <character name> ::= alarm | backspace | delete
                //                    | escape | newline | null | return | space | tab
                // ```
                if next == '\\' {
                    pos += next.len_utf8();
                    if pos >= len {
                        return Err(ParseError::Incomplete);
                    }

                    let c1 = source[pos..].chars().next().unwrap();
                    let value_char;

                    if c1 == 'x' || c1 == 'X' {
                        // Hex scalar value form: `#\x<hex scalar value>`
                        pos += c1.len_utf8();
                        let hex_start = pos;
                        while pos < len {
                            let c = source[pos..].chars().next().unwrap();
                            if c.is_ascii_hexdigit() {
                                pos += c.len_utf8();
                            } else {
                                break;
                            }
                        }

                        if pos == hex_start {
                            let span = Span { start, end: pos };
                            return Err(ParseError::lexical(
                                span,
                                "<character>",
                                "expected hex digits in character literal",
                            ));
                        }

                        let hex_digits = &source[hex_start..pos];
                        let codepoint = u32::from_str_radix(hex_digits, 16).map_err(|_| {
                            let span = Span { start, end: pos };
                            ParseError::lexical(
                                span,
                                "<character>",
                                "invalid hex digits in character literal",
                            )
                        })?;
                        value_char = match char::from_u32(codepoint) {
                            Some(c) => c,
                            None => {
                                let span = Span { start, end: pos };
                                return Err(ParseError::lexical(
                                    span,
                                    "<character>",
                                    "hex scalar value is not a valid Unicode scalar value",
                                ));
                            }
                        };
                    } else if c1.is_ascii_alphabetic() {
                        // Named character form: `#\\<character name>`
                        let name_start = pos;
                        while pos < len {
                            let c = source[pos..].chars().next().unwrap();
                            if c.is_ascii_alphabetic() {
                                pos += c.len_utf8();
                            } else {
                                break;
                            }
                        }
                        let name = &source[name_start..pos];

                        // If only a single alphabetic character follows `#\\`,
                        // interpret it as the `<any character>` case rather
                        // than a `<character name>`.
                        if name.len() == c1.len_utf8() {
                            value_char = c1;
                        } else {
                            value_char = match name {
                                "alarm" => '\u{7}',
                                "backspace" => '\u{8}',
                                "delete" => '\u{7F}',
                                "escape" => '\u{1B}',
                                "newline" => '\n',
                                "null" => '\0',
                                "return" => '\r',
                                "space" => ' ',
                                "tab" => '\t',
                                _ => {
                                    let span = Span { start, end: pos };
                                    return Err(ParseError::lexical(
                                        span,
                                        "<character>",
                                        "unknown character name",
                                    ));
                                }
                            };
                        }
                    } else {
                        // Single-character form: `#\<any character>`
                        value_char = c1;
                        pos += c1.len_utf8();
                    }

                    // Characters must be terminated by a <delimiter> or
                    // the end of the input. See the note in `syn.md`:
                    // "Identifiers that do not begin with a vertical line are
                    // terminated by a <delimiter> or by the end of the input.
                    // So are dot, numbers, characters, and booleans."
                    if pos < len {
                        let after = source[pos..].chars().next().unwrap();
                        if !is_delimiter(after) {
                            let span = Span { start, end: pos };
                            return Err(ParseError::lexical(
                                span,
                                "<character>",
                                "character literal not followed by a delimiter",
                            ));
                        }
                    }

                    let span = Span { start, end: pos };
                    tokens.push(Syntax::new(span, Token::Character(value_char)));
                    continue;
                }

                // Attempt decimal `<number>` with `<exactness>` / `#d` prefix:
                //
                // ```text
                // <prefix 10> ::= <radix 10> <exactness>
                //               | <exactness> <radix 10>
                // <exactness> ::= <empty> | #i | #e
                // <radix 10> ::= <empty> | #d
                // ```
                if let Some((end, number)) = lex_hash_decimal_number(source, start)? {
                    if end < len {
                        let after = source[end..].chars().next().unwrap();
                        if !is_delimiter(after) {
                            let span = Span { start, end };
                            return Err(ParseError::lexical(
                                span,
                                "<number>",
                                "number literal not followed by a delimiter",
                            ));
                        }
                    }

                    let span = Span { start, end };
                    tokens.push(Syntax::new(span, Token::Number(number)));
                    pos = end;
                    continue;
                }

                // Attempt non-decimal `<number>` with radix prefixes
                // `#b`, `#o`, or `#x` and optional `<exactness>`.
                if let Some((end, number)) = lex_hash_nondecimal_number(source, start)? {
                    let span = Span { start, end };
                    tokens.push(Syntax::new(span, Token::Number(number)));
                    pos = end;
                    continue;
                }

                // `<boolean> ::= #t | #f | #true | #false`
                let word_start = pos;
                while pos < len {
                    let c = source[pos..].chars().next().unwrap();
                    if c.is_ascii_alphabetic() {
                        pos += c.len_utf8();
                    } else {
                        break;
                    }
                }

                let ident = &source[word_start..pos];
                let lower = ident.to_ascii_lowercase();
                let value = match lower.as_str() {
                    "t" | "true" => Some(true),
                    "f" | "false" => Some(false),
                    _ => None,
                };

                if let Some(b) = value {
                    // Booleans are also terminated by a <delimiter> or EOF.
                    if pos < len {
                        let after = source[pos..].chars().next().unwrap();
                        if !is_delimiter(after) {
                            let span = Span { start, end: pos };
                            return Err(ParseError::lexical(
                                span,
                                "<boolean>",
                                "boolean literal not followed by a delimiter",
                            ));
                        }
                    }

                    let span = Span { start, end: pos };
                    tokens.push(Syntax::new(span, Token::Boolean(b)));
                    continue;
                } else {
                    // Not a `<boolean>` or decimal `<number>` with
                    // prefix; other `#`-prefixed tokens (radix-prefixed
                    // numbers for non-decimal R, vectors, bytevectors,
                    // datum comments) are not implemented yet.
                    return Err(ParseError::Unimplemented);
                }
            }
            _ => {
                // Other token classes are not yet implemented.
                return Err(ParseError::Unimplemented);
            }
        }
    }

    Ok(tokens)
}

/// Skip a `<nested comment>` starting just after the initial `#|`.
///
/// Grammar reference:
///
/// ```text
/// <nested comment> ::= #| <comment text> |#
/// ```
///
/// Returns the byte index just after the closing `|#`, or
/// `ParseError::Incomplete` if the input ends before the matching
/// closing delimiter.
fn skip_nested_comment(source: &str, mut pos: usize) -> Result<usize, ParseError> {
    let len = source.len();
    let mut depth = 1usize;

    while pos < len {
        let ch = match source[pos..].chars().next() {
            Some(c) => c,
            None => break,
        };

        if ch == '#' {
            let hash_pos = pos;
            pos += ch.len_utf8();
            if pos < len {
                let next = source[pos..].chars().next().unwrap();
                if next == '|' {
                    // Found a new `#|`.
                    depth += 1;
                    pos += next.len_utf8();
                    continue;
                }
            }
            // Not actually starting a nested comment; just move on.
            pos = hash_pos + ch.len_utf8();
            continue;
        } else if ch == '|' {
            let bar_pos = pos;
            pos += ch.len_utf8();
            if pos < len {
                let next = source[pos..].chars().next().unwrap();
                if next == '#' {
                    // Closing `|#`.
                    depth -= 1;
                    pos += next.len_utf8();
                    if depth == 0 {
                        return Ok(pos);
                    }
                    continue;
                }
            }
            // Not actually closing; just move on.
            pos = bar_pos + ch.len_utf8();
            continue;
        } else {
            pos += ch.len_utf8();
        }
    }

    // Ran out of input before finding a matching `|#`.
    Err(ParseError::Incomplete)
}

/// True if `ch` is a `<delimiter>` character.
///
/// Grammar reference:
///
/// ```text
/// <delimiter> ::= <whitespace> | <vertical line>
///               | ( | ) | " | ;
/// ```
fn is_delimiter(ch: char) -> bool {
    matches!(ch, ' ' | '\t' | '\n' | '\r' | '|' | '(' | ')' | '"' | ';')
}

/// Lex the `<infnan>` body starting at `start`, without any radix or
/// exactness prefixes.
///
/// Grammar reference (Formal syntax / `<number>`):
///
/// ```text
/// <infnan> ::= +inf.0 | -inf.0 | +nan.0 | -nan.0
/// ```
///
/// Alphabetic characters in `<infnan>` are case-insensitive.
fn lex_infnan_body(source: &str, start: usize) -> Option<(usize, InfinityNan)> {
    let s = &source[start..];
    if s.len() < 6 {
        return None;
    }

    // All `<infnan>` spellings are 6 ASCII bytes: sign + 3 letters + ".0".
    let candidate = &s[..6];
    let lower = candidate.to_ascii_lowercase();
    let kind = match lower.as_str() {
        "+inf.0" => InfinityNan::PositiveInfinity,
        "-inf.0" => InfinityNan::NegativeInfinity,
        "+nan.0" => InfinityNan::PositiveNaN,
        "-nan.0" => InfinityNan::NegativeNaN,
        _ => return None,
    };

    Some((start + 6, kind))
}

/// Lex `<sign> <ureal R>` for arbitrary radices `R`, where
/// `<ureal R>` is finite (integer, rational, or, for `R = 10`,
/// a decimal real with optional exponent). This helper delegates
/// to the decimal or non-decimal lexers depending on `radix` and
/// returns the `FiniteRealRepr` together with the end offset.
fn lex_sign_ureal_for_radix(
    source: &str,
    start: usize,
    radix: NumberRadix,
) -> Result<Option<(usize, FiniteRealRepr)>, ParseError> {
    match radix {
        NumberRadix::Decimal => {
            if let Some((end, lit)) = lex_decimal_number(source, start)? {
                match lit.kind.value {
                    NumberValue::Real(RealRepr::Finite(finite)) => Ok(Some((end, finite))),
                    _ => unreachable!("decimal lexer should only produce finite real values"),
                }
            } else {
                Ok(None)
            }
        }
        _ => lex_nondecimal_sign_ureal(source, start, radix),
    }
}

/// Lex a `<complex R>` or `<real R>` starting at `body_start`, with
/// the overall literal beginning at `literal_start` (to include any
/// prefixes in spans and `NumberLiteral.text`). This implements the
/// generic R7RS complex grammar:
///
/// ```text
/// <number>   ::= <num 2> | <num 8>
///              | <num 10> | <num 16>
/// <num R>    ::= <prefix R> <complex R>
/// <complex R> ::= <real R>
///               | <real R> @ <real R>
///               | <real R> + <ureal R> i
///               | <real R> - <ureal R> i
///               | <real R> + i
///               | <real R> - i
///               | <real R> <infnan> i
///               | + <ureal R> i
///               | - <ureal R> i
///               | <infnan> i
///               | + i
///               | - i
/// <real R>   ::= <sign> <ureal R>
///               | <infnan>
/// ```
fn lex_complex_with_radix(
    source: &str,
    literal_start: usize,
    body_start: usize,
    radix: NumberRadix,
    exactness: NumberExactness,
) -> Result<Option<(usize, NumberLiteral)>, ParseError> {
    let len = source.len();
    if body_start >= len {
        return Ok(None);
    }

    let ch = source[body_start..].chars().next().unwrap();

    // Precompute whether the literal body starts with `<infnan>` so we
    // can distinguish `+i`/`-i` from `+inf.0`, `+nan.0`, etc.
    let starts_with_infnan = lex_infnan_body(source, body_start);

    // 1. Pure imaginary `<infnan> i` with no explicit real part.
    if let Some((mid, infnan)) = lex_infnan_body(source, body_start) {
        if mid < len {
            let i_ch = source[mid..].chars().next().unwrap();
            if i_ch == 'i' || i_ch == 'I' {
                let i_end = mid + i_ch.len_utf8();
                if i_end < len {
                    let after = source[i_end..].chars().next().unwrap();
                    if !is_delimiter(after) {
                        let span = Span {
                            start: literal_start,
                            end: i_end,
                        };
                        return Err(ParseError::lexical(
                            span,
                            "<number>",
                            "number literal not followed by a delimiter",
                        ));
                    }
                }

                let real_zero = RealRepr::Finite(FiniteRealRepr::Integer {
                    spelling: "0".to_string(),
                });
                let imag = RealRepr::Infnan(infnan);
                let kind = NumberLiteralKind {
                    radix,
                    exactness,
                    value: NumberValue::Rectangular {
                        real: real_zero,
                        imag,
                    },
                };
                let text = &source[literal_start..i_end];
                let literal = NumberLiteral {
                    text: text.to_string(),
                    kind,
                };
                return Ok(Some((i_end, literal)));
            }
        }
        // If this was plain `<infnan>` without trailing `i`, we will
        // treat it as `<real R>` below.
    }

    // 2. Pure imaginary forms with no explicit real part, but only
    // when the literal does not start with `<infnan>`:
    //
    //   + <ureal R> i
    //   - <ureal R> i
    //   + i
    //   - i
    if (ch == '+' || ch == '-') && starts_with_infnan.is_none() {
        // First try `+<ureal R>i` / `-<ureal R>i` using the shared
        // `<sign> <ureal R>` helper, then fall back to the
        // unit-imaginary `+i` / `-i` cases.
        if let Some((end_ureal, imag_finite)) =
            lex_sign_ureal_for_radix(source, body_start, radix)?
        {
            if end_ureal < len {
                let i_ch = source[end_ureal..].chars().next().unwrap();
                if i_ch == 'i' || i_ch == 'I' {
                    let i_end = end_ureal + i_ch.len_utf8();
                    if i_end < len {
                        let after = source[i_end..].chars().next().unwrap();
                        if !is_delimiter(after) {
                            let span = Span {
                                start: literal_start,
                                end: i_end,
                            };
                            return Err(ParseError::lexical(
                                span,
                                "<number>",
                                "number literal not followed by a delimiter",
                            ));
                        }
                    }

                    let real_zero = RealRepr::Finite(FiniteRealRepr::Integer {
                        spelling: "0".to_string(),
                    });
                    let imag = RealRepr::Finite(imag_finite);
                    let kind = NumberLiteralKind {
                        radix,
                        exactness,
                        value: NumberValue::Rectangular {
                            real: real_zero,
                            imag,
                        },
                    };
                    let text = &source[literal_start..i_end];
                    let literal = NumberLiteral {
                        text: text.to_string(),
                        kind,
                    };
                    return Ok(Some((i_end, literal)));
                }
            }
        }

        // Fallback: unit imaginary `+i` / `-i`.
        let sign_len = ch.len_utf8();
        let after_sign = body_start + sign_len;
        if after_sign < len {
            let i_ch = source[after_sign..].chars().next().unwrap();
            if i_ch == 'i' || i_ch == 'I' {
                let i_end = after_sign + i_ch.len_utf8();
                if i_end < len {
                    let after = source[i_end..].chars().next().unwrap();
                    if !is_delimiter(after) {
                        let span = Span {
                            start: literal_start,
                            end: i_end,
                        };
                        return Err(ParseError::lexical(
                            span,
                            "<number>",
                            "number literal not followed by a delimiter",
                        ));
                    }
                }

                let real_zero = RealRepr::Finite(FiniteRealRepr::Integer {
                    spelling: "0".to_string(),
                });
                let imag_spelling = if ch == '-' { "-1" } else { "1" };
                let imag = RealRepr::Finite(FiniteRealRepr::Integer {
                    spelling: imag_spelling.to_string(),
                });
                let kind = NumberLiteralKind {
                    radix,
                    exactness,
                    value: NumberValue::Rectangular {
                        real: real_zero,
                        imag,
                    },
                };
                let text = &source[literal_start..i_end];
                let literal = NumberLiteral {
                    text: text.to_string(),
                    kind,
                };
                return Ok(Some((i_end, literal)));
            }
        }
    }

    // 3. Parse the leading `<real R>` (finite or `<infnan>`).
    let (real_end, real_repr) = if let Some((end, infnan)) = starts_with_infnan {
        (end, RealRepr::Infnan(infnan))
    } else if let Some((end, finite)) = lex_sign_ureal_for_radix(source, body_start, radix)? {
        (end, RealRepr::Finite(finite))
    } else {
        // Not a `<real R>` at all.
        return Ok(None);
    };

    if real_end >= len {
        // Pure real at end of input.
        let text = &source[literal_start..real_end];
        let kind = NumberLiteralKind {
            radix,
            exactness,
            value: NumberValue::Real(real_repr),
        };
        let literal = NumberLiteral {
            text: text.to_string(),
            kind,
        };
        return Ok(Some((real_end, literal)));
    }

    let tail_ch = source[real_end..].chars().next().unwrap();

    // If the next character is a delimiter, this is a pure real.
    if is_delimiter(tail_ch) {
        let text = &source[literal_start..real_end];
        let kind = NumberLiteralKind {
            radix,
            exactness,
            value: NumberValue::Real(real_repr),
        };
        let literal = NumberLiteral {
            text: text.to_string(),
            kind,
        };
        return Ok(Some((real_end, literal)));
    }

    match tail_ch {
        '@' => {
            // Polar form: `<real R> @ <real R>`.
            let after_at = real_end + tail_ch.len_utf8();
            if after_at >= len {
                return Err(ParseError::Incomplete);
            }

            let (end2, real2_repr) =
                if let Some((e2, infnan2)) = lex_infnan_body(source, after_at) {
                    (e2, RealRepr::Infnan(infnan2))
                } else if let Some((e2, finite2)) =
                    lex_sign_ureal_for_radix(source, after_at, radix)?
                {
                    (e2, RealRepr::Finite(finite2))
                } else {
                    let span = Span {
                        start: literal_start,
                        end: after_at,
                    };
                    return Err(ParseError::lexical(
                        span,
                        "<number>",
                        "invalid polar complex number; expected real after '@'",
                    ));
                };

            if end2 < len {
                let after = source[end2..].chars().next().unwrap();
                if !is_delimiter(after) {
                    let span = Span {
                        start: literal_start,
                        end: end2,
                    };
                    return Err(ParseError::lexical(
                        span,
                        "<number>",
                        "number literal not followed by a delimiter",
                    ));
                }
            }

            let text = &source[literal_start..end2];
            let kind = NumberLiteralKind {
                radix,
                exactness,
                value: NumberValue::Polar {
                    magnitude: real_repr,
                    angle: real2_repr,
                },
            };
            let literal = NumberLiteral {
                text: text.to_string(),
                kind,
            };
            Ok(Some((end2, literal)))
        }
        '+' | '-' => {
            let tail_start = real_end;

            // `<real R> <infnan> i`
            if let Some((mid, infnan_imag)) = lex_infnan_body(source, tail_start) {
                if mid >= len {
                    return Err(ParseError::Incomplete);
                }
                let i_ch = source[mid..].chars().next().unwrap();
                if i_ch == 'i' || i_ch == 'I' {
                    let i_end = mid + i_ch.len_utf8();
                    if i_end < len {
                        let after = source[i_end..].chars().next().unwrap();
                        if !is_delimiter(after) {
                            let span = Span {
                                start: literal_start,
                                end: i_end,
                            };
                            return Err(ParseError::lexical(
                                span,
                                "<number>",
                                "number literal not followed by a delimiter",
                            ));
                        }
                    }

                    let imag = RealRepr::Infnan(infnan_imag);
                    let kind = NumberLiteralKind {
                        radix,
                        exactness,
                        value: NumberValue::Rectangular {
                            real: real_repr,
                            imag,
                        },
                    };
                    let text = &source[literal_start..i_end];
                    let literal = NumberLiteral {
                        text: text.to_string(),
                        kind,
                    };
                    return Ok(Some((i_end, literal)));
                } else {
                    // We saw an `<infnan>` tail but no `i` yet.
                    return Err(ParseError::Incomplete);
                }
            }

            // `<real R> +/- i`
            let sign_len = tail_ch.len_utf8();
            let after_sign = tail_start + sign_len;
            if after_sign < len {
                let i_ch = source[after_sign..].chars().next().unwrap();
                if i_ch == 'i' || i_ch == 'I' {
                    let i_end = after_sign + i_ch.len_utf8();
                    if i_end < len {
                        let after = source[i_end..].chars().next().unwrap();
                        if !is_delimiter(after) {
                            let span = Span {
                                start: literal_start,
                                end: i_end,
                            };
                            return Err(ParseError::lexical(
                                span,
                                "<number>",
                                "number literal not followed by a delimiter",
                            ));
                        }
                    }

                    let imag_spelling = if tail_ch == '-' { "-1" } else { "1" };
                    let imag = RealRepr::Finite(FiniteRealRepr::Integer {
                        spelling: imag_spelling.to_string(),
                    });
                    let kind = NumberLiteralKind {
                        radix,
                        exactness,
                        value: NumberValue::Rectangular {
                            real: real_repr,
                            imag,
                        },
                    };
                    let text = &source[literal_start..i_end];
                    let literal = NumberLiteral {
                        text: text.to_string(),
                        kind,
                    };
                    return Ok(Some((i_end, literal)));
                }
            }

            // `<real R> +/- <ureal R> i`
            if let Some((end_ureal, imag_finite)) =
                lex_sign_ureal_for_radix(source, tail_start, radix)?
            {
                if end_ureal >= len {
                    return Err(ParseError::Incomplete);
                }
                let i_ch = source[end_ureal..].chars().next().unwrap();
                if i_ch == 'i' || i_ch == 'I' {
                    let i_end = end_ureal + i_ch.len_utf8();
                    if i_end < len {
                        let after = source[i_end..].chars().next().unwrap();
                        if !is_delimiter(after) {
                            let span = Span {
                                start: literal_start,
                                end: i_end,
                            };
                            return Err(ParseError::lexical(
                                span,
                                "<number>",
                                "number literal not followed by a delimiter",
                            ));
                        }
                    }

                    let imag = RealRepr::Finite(imag_finite);
                    let kind = NumberLiteralKind {
                        radix,
                        exactness,
                        value: NumberValue::Rectangular {
                            real: real_repr,
                            imag,
                        },
                    };
                    let text = &source[literal_start..i_end];
                    let literal = NumberLiteral {
                        text: text.to_string(),
                        kind,
                    };
                    return Ok(Some((i_end, literal)));
                } else {
                    let span = Span {
                        start: literal_start,
                        end: end_ureal,
                    };
                    return Err(ParseError::lexical(
                        span,
                        "<number>",
                        "number literal not followed by a delimiter",
                    ));
                }
            }

            // No valid complex tail recognized after the real part.
            let span = Span {
                start: literal_start,
                end: real_end,
            };
            Err(ParseError::lexical(
                span,
                "<number>",
                "invalid complex number syntax",
            ))
        }
        _ => {
            // Not a delimiter or complex tail start: malformed number.
            let span = Span {
                start: literal_start,
                end: real_end,
            };
            Err(ParseError::lexical(
                span,
                "<number>",
                "number literal not followed by a delimiter",
            ))
        }
    }
}

/// Lex a decimal `<complex 10>` or `<real 10>` starting at `start` by
/// delegating to the radix-parametric complex helper with `R = 10` and
/// unspecified exactness.
fn lex_complex_decimal(
    source: &str,
    start: usize,
) -> Result<Option<(usize, NumberLiteral)>, ParseError> {
    lex_complex_with_radix(
        source,
        start,
        start,
        NumberRadix::Decimal,
        NumberExactness::Unspecified,
    )
}

/// Lex a decimal `<number>` that begins with one or more `#` prefixes
/// for `<exactness>` and/or `<radix 10>`.
///
/// Grammar reference (Formal syntax / `<number>`):
///
/// ```text
/// <num 10> ::= <prefix 10> <complex 10>
/// <prefix 10> ::= <radix 10> <exactness>
///                | <exactness> <radix 10>
/// <exactness> ::= <empty> | #i | #e
/// <radix 10> ::= <empty> | #d
/// ```
///
/// This helper delegates the `<complex 10>` body, including `<real 10>`,
/// `<infnan>`, rectangular, polar, and pure-imaginary forms, to
/// `lex_complex_decimal`, and then applies the parsed radix/exactness
/// prefixes to the resulting `NumberLiteralKind` while preserving the
/// original token spelling including prefixes.
fn lex_hash_decimal_number(
    source: &str,
    start: usize,
) -> Result<Option<(usize, NumberLiteral)>, ParseError> {
    let len = source.len();
    let mut pos = start;

    if pos >= len || !source[pos..].starts_with('#') {
        return Ok(None);
    }

    let mut radix: Option<NumberRadix> = None;
    let mut exactness: Option<NumberExactness> = None;

    // Consume one or two `#` prefixes consisting only of `d`, `e`, or `i`.
    loop {
        if pos >= len || !source[pos..].starts_with('#') {
            break;
        }
        pos += 1; // skip '#'
        if pos >= len {
            return Err(ParseError::Incomplete);
        }

        let ch = source[pos..].chars().next().unwrap();
        let lower = ch.to_ascii_lowercase();
        pos += ch.len_utf8();

        match lower {
            'd' => {
                if radix.is_some() {
                    let span = Span { start, end: pos };
                    return Err(ParseError::lexical(
                        span,
                        "<number>",
                        "duplicate radix prefix in decimal number",
                    ));
                }
                radix = Some(NumberRadix::Decimal);
            }
            'e' => {
                if exactness.is_some() {
                    let span = Span { start, end: pos };
                    return Err(ParseError::lexical(
                        span,
                        "<number>",
                        "duplicate exactness prefix in decimal number",
                    ));
                }
                exactness = Some(NumberExactness::Exact);
            }
            'i' => {
                if exactness.is_some() {
                    let span = Span { start, end: pos };
                    return Err(ParseError::lexical(
                        span,
                        "<number>",
                        "duplicate exactness prefix in decimal number",
                    ));
                }
                exactness = Some(NumberExactness::Inexact);
            }
            // Any other prefix letter (e.g. `b`, `o`, `x`, `t`, etc.)
            // means this is not a decimal-prefix number; leave it for
            // other handlers (booleans, future radix support, etc.).
            _ => {
                return Ok(None);
            }
        }
    }

    // If we did not recognize any decimal-specific prefixes, this is
    // not a `<prefix 10>`; let other handlers take over.
    if radix.is_none() && exactness.is_none() {
        return Ok(None);
    }

    let radix = radix.unwrap_or(NumberRadix::Decimal);
    let exactness = exactness.unwrap_or(NumberExactness::Unspecified);

    let body_start = pos;
    if body_start >= len {
        return Err(ParseError::Incomplete);
    }

    // Delegate the `<complex 10>` body (including plain reals and
    // `<infnan>`) to the radix-parametric complex helper, starting at
    // `body_start` but using `start` as the literal beginning so the
    // prefixes are included in spans and `text`.
    lex_complex_with_radix(source, start, body_start, radix, exactness)
}

/// Lex a non-decimal `<number>` with radix prefixes `#b`, `#o`, or
/// `#x` and optional `<exactness>` markers `#e` or `#i`.
///
/// Grammar reference (Formal syntax / `<number>`):
///
/// ```text
/// <number> ::= <num 2> | <num 8>
///            | <num 10> | <num 16>
///
/// <num R> ::= <prefix R> <complex R>
///
/// <prefix R> ::= <radix R> <exactness>
///               | <exactness> <radix R>
///
/// <real R> ::= <sign> <ureal R>
///             | <infnan>
///
/// <ureal R> ::= <uinteger R>
///              | <uinteger R> / <uinteger R>
///              | <decimal R>
///
/// <uinteger R> ::= <digit R>+
/// ```
///
/// For `R = 2, 8, 16` there is no `<decimal R>`, so `<ureal R>` is
/// restricted to integers and rationals. This helper recognizes the
/// full `<complex R>` grammar for non-decimal radices, including real,
/// rectangular, polar, pure-imaginary, and `<infnan>`-based forms, and
/// applies the parsed radix and exactness prefixes to the resulting
/// `NumberLiteralKind`.
fn lex_hash_nondecimal_number(
    source: &str,
    start: usize,
) -> Result<Option<(usize, NumberLiteral)>, ParseError> {
    let len = source.len();
    let mut pos = start;

    if pos >= len || !source[pos..].starts_with('#') {
        return Ok(None);
    }

    let mut radix: Option<NumberRadix> = None;
    let mut exactness: Option<NumberExactness> = None;

    // Consume one or two `#` prefixes consisting of a radix (`#b`,
    // `#o`, `#x`) and/or an exactness marker (`#e`, `#i`) in either
    // order.
    loop {
        if pos >= len || !source[pos..].starts_with('#') {
            break;
        }
        pos += 1; // skip '#'
        if pos >= len {
            return Err(ParseError::Incomplete);
        }

        let ch = source[pos..].chars().next().unwrap();
        let lower = ch.to_ascii_lowercase();
        pos += ch.len_utf8();

        match lower {
            'b' => {
                if radix.is_some() {
                    let span = Span { start, end: pos };
                    return Err(ParseError::lexical(
                        span,
                        "<number>",
                        "duplicate radix prefix in non-decimal number",
                    ));
                }
                radix = Some(NumberRadix::Binary);
            }
            'o' => {
                if radix.is_some() {
                    let span = Span { start, end: pos };
                    return Err(ParseError::lexical(
                        span,
                        "<number>",
                        "duplicate radix prefix in non-decimal number",
                    ));
                }
                radix = Some(NumberRadix::Octal);
            }
            'x' => {
                if radix.is_some() {
                    let span = Span { start, end: pos };
                    return Err(ParseError::lexical(
                        span,
                        "<number>",
                        "duplicate radix prefix in non-decimal number",
                    ));
                }
                radix = Some(NumberRadix::Hexadecimal);
            }
            'e' => {
                if exactness.is_some() {
                    let span = Span { start, end: pos };
                    return Err(ParseError::lexical(
                        span,
                        "<number>",
                        "duplicate exactness prefix in non-decimal number",
                    ));
                }
                exactness = Some(NumberExactness::Exact);
            }
            'i' => {
                if exactness.is_some() {
                    let span = Span { start, end: pos };
                    return Err(ParseError::lexical(
                        span,
                        "<number>",
                        "duplicate exactness prefix in non-decimal number",
                    ));
                }
                exactness = Some(NumberExactness::Inexact);
            }
            // Any other prefix letter: if we have already seen a radix,
            // this is an invalid prefix for non-decimal numbers;
            // otherwise, this is not a non-decimal `<number>` and we
            // leave it for other handlers (booleans, decimal numbers,
            // etc.).
            _ => {
                if radix.is_some() {
                    let span = Span { start, end: pos };
                    return Err(ParseError::lexical(
                        span,
                        "<number>",
                        "invalid prefix in non-decimal number",
                    ));
                } else {
                    return Ok(None);
                }
            }
        }
    }

    // If we did not see a non-decimal radix, this is not a `<num 2>`,
    // `<num 8>`, or `<num 16>`.
    let radix = match radix {
        Some(r) => r,
        None => return Ok(None),
    };

    let exactness = exactness.unwrap_or(NumberExactness::Unspecified);

    let body_start = pos;
    if body_start >= len {
        return Err(ParseError::Incomplete);
    }

    // Delegate the `<complex R>` body (including plain reals and
    // `<infnan>`) to the shared radix-parametric helper, starting at
    // `body_start` but treating `start` (the first `#`) as the
    // beginning of the literal for spans and text.
    lex_complex_with_radix(source, start, body_start, radix, exactness)
}

/// Lex `<sign> <ureal R>` for non-decimal radices `R = 2, 8, 16`,
/// where `<ureal R>` is either an integer `<uinteger R>` or a rational
/// `<uinteger R>/<uinteger R>`. The optional sign, if present, is
/// preserved in the resulting `FiniteRealRepr` spelling.
fn lex_nondecimal_sign_ureal(
    source: &str,
    start: usize,
    radix: NumberRadix,
) -> Result<Option<(usize, FiniteRealRepr)>, ParseError> {
    let len = source.len();
    let mut pos = start;

    if pos >= len {
        return Ok(None);
    }

    // Optional sign.
    let first = source[pos..].chars().next().unwrap();
    if first == '+' || first == '-' {
        pos += first.len_utf8();
        if pos >= len {
            // Only a sign: not a number.
            return Ok(None);
        }
    }

    let mut saw_digit = false;

    while pos < len {
        let c = source[pos..].chars().next().unwrap();
        if is_digit_for_radix(c, radix) {
            saw_digit = true;
            pos += c.len_utf8();
        } else {
            break;
        }
    }

    if !saw_digit {
        return Ok(None);
    }

    let mut is_rational = false;

    if pos < len {
        let c = source[pos..].chars().next().unwrap();
        if c == '/' {
            is_rational = true;
            pos += c.len_utf8();
            if pos >= len {
                // E.g. "#b1/" at end of input.
                return Err(ParseError::Incomplete);
            }

            let mut denom_digits = false;
            while pos < len {
                let c2 = source[pos..].chars().next().unwrap();
                if is_digit_for_radix(c2, radix) {
                    denom_digits = true;
                    pos += c2.len_utf8();
                } else {
                    break;
                }
            }

            if !denom_digits {
                let span = Span { start, end: pos };
                return Err(ParseError::lexical(
                    span,
                    "<number>",
                    "invalid rational number; expected digits after '/'",
                ));
            }
        }
    }

    let end = pos;
    let spelling = &source[start..end];
    let finite = if is_rational {
        FiniteRealRepr::Rational {
            spelling: spelling.to_string(),
        }
    } else {
        FiniteRealRepr::Integer {
            spelling: spelling.to_string(),
        }
    };

    Ok(Some((end, finite)))
}

fn is_digit_for_radix(ch: char, radix: NumberRadix) -> bool {
    match radix {
        NumberRadix::Binary => matches!(ch, '0' | '1'),
        NumberRadix::Octal => matches!(ch, '0'..='7'),
        NumberRadix::Decimal => ch.is_ascii_digit(),
        NumberRadix::Hexadecimal => ch.is_ascii_hexdigit(),
    }
}

/// Lex a decimal (radix 10) `<number>` starting at `start`.
///
/// Recognizes the subset of the `<number>` grammar corresponding to
/// real decimal numbers without prefixes:
///
/// ```text
/// <decimal 10> ::= <uinteger 10> <suffix>
///                 | . <digit 10>+ <suffix>
///                 | <digit 10>+ . <digit 10>* <suffix>
///
/// <suffix> ::= <empty>
///            | <exponent marker> <sign> <digit 10>+
///
/// <exponent marker> ::= e
/// <sign> ::= <empty> | + | -
/// ```
///
/// Note: This helper is intentionally limited to radix-10 real
/// numbers (integers, decimals, `3/4` rationals, and exponent
/// forms) without `#b/#o/#d/#x` prefixes or complex numbers
/// (`1+2i`, `+i`, etc.). Prefixes and complex forms for all
/// radices are handled at the `<number>` level by
/// `lex_complex_decimal`, `lex_hash_decimal_number`, and
/// `lex_hash_nondecimal_number`, so the overall `<number>`
/// lexer is R7RS-conformant.
fn lex_decimal_number(
    source: &str,
    start: usize,
) -> Result<Option<(usize, NumberLiteral)>, ParseError> {
    let len = source.len();
    let mut pos = start;

    // Optional sign.
    if pos < len {
        let ch = source[pos..].chars().next().unwrap();
        if ch == '+' || ch == '-' {
            pos += ch.len_utf8();
        }
    }

    if pos >= len {
        // Only a sign, no digits: not a number.
        return Ok(None);
    }

    let mut saw_digit = false;
    let first = source[pos..].chars().next().unwrap();

    if first == '.' {
        // `.digits+` decimal form (no rationals here).
        pos += first.len_utf8();
        if pos >= len {
            return Ok(None);
        }
        while pos < len {
            let c = source[pos..].chars().next().unwrap();
            if c.is_ascii_digit() {
                saw_digit = true;
                pos += c.len_utf8();
            } else {
                break;
            }
        }
        if !saw_digit {
            // No digits after '.'
            return Ok(None);
        }

        // Optional exponent part for `.digits+`.
        if pos < len {
            let c = source[pos..].chars().next().unwrap();
            if c == 'e' || c == 'E' {
                pos += c.len_utf8();
                if pos >= len {
                    // ".5e" at end of input.
                    return Err(ParseError::Incomplete);
                }

                let sign_ch = source[pos..].chars().next().unwrap();
                if sign_ch == '+' || sign_ch == '-' {
                    pos += sign_ch.len_utf8();
                    if pos >= len {
                        // ".5e+" at end of input.
                        return Err(ParseError::Incomplete);
                    }
                }

                let mut exp_digits = false;
                while pos < len {
                    let c2 = source[pos..].chars().next().unwrap();
                    if c2.is_ascii_digit() {
                        exp_digits = true;
                        pos += c2.len_utf8();
                    } else {
                        break;
                    }
                }
                if !exp_digits {
                    // `.5e` or `.5e+` without digits.
                    return Err(ParseError::Incomplete);
                }
            }
        }
    } else if first.is_ascii_digit() {
        // Leading digits of `<uinteger 10>`.
        while pos < len {
            let c = source[pos..].chars().next().unwrap();
            if c.is_ascii_digit() {
                saw_digit = true;
                pos += c.len_utf8();
            } else {
                break;
            }
        }

        // At this point we may have a rational `a/b`, a decimal
        // `a.b`, or a plain integer `a`.
        if pos < len {
            let c = source[pos..].chars().next().unwrap();
            if c == '/' {
                // Potential rational `<uinteger 10> / <uinteger 10>`.
                pos += c.len_utf8();
                if pos >= len {
                    // "3/" at end of input.
                    return Err(ParseError::Incomplete);
                }

                // Denominator must be `<uinteger 10>`.
                let mut denom_digits = false;
                while pos < len {
                    let c2 = source[pos..].chars().next().unwrap();
                    if c2.is_ascii_digit() {
                        denom_digits = true;
                        pos += c2.len_utf8();
                    } else {
                        break;
                    }
                }

                if !denom_digits {
                    // "3/" followed by a non-digit, e.g. "3/x".
                    let span = Span { start, end: pos };
                    return Err(ParseError::lexical(
                        span,
                        "<number>",
                        "invalid rational number; expected digits after '/'",
                    ));
                }

                // Rationals do not allow a decimal point or exponent
                // after the denominator, so we are done here.
            } else if c == '.' {
                // Decimal with fractional part: `digits '.' digits*`.
                pos += c.len_utf8();
                while pos < len {
                    let c2 = source[pos..].chars().next().unwrap();
                    if c2.is_ascii_digit() {
                        pos += c2.len_utf8();
                    } else {
                        break;
                    }
                }

                // Optional exponent part for `digits '.' digits*`.
                if pos < len {
                    let c2 = source[pos..].chars().next().unwrap();
                    if c2 == 'e' || c2 == 'E' {
                        pos += c2.len_utf8();
                        if pos >= len {
                            // "1.e" at end of input.
                            return Err(ParseError::Incomplete);
                        }

                        let sign_ch = source[pos..].chars().next().unwrap();
                        if sign_ch == '+' || sign_ch == '-' {
                            pos += sign_ch.len_utf8();
                            if pos >= len {
                                // "1.e+" at end of input.
                                return Err(ParseError::Incomplete);
                            }
                        }

                        let mut exp_digits = false;
                        while pos < len {
                            let c3 = source[pos..].chars().next().unwrap();
                            if c3.is_ascii_digit() {
                                exp_digits = true;
                                pos += c3.len_utf8();
                            } else {
                                break;
                            }
                        }
                        if !exp_digits {
                            // `1.e` or `1.e+` without digits.
                            return Err(ParseError::Incomplete);
                        }
                    }
                }
            } else if c == 'e' || c == 'E' {
                // Exponent part for pure integer: `digits [eE][sign]digits+`.
                pos += c.len_utf8();
                if pos >= len {
                    // "1e" at end of input.
                    return Err(ParseError::Incomplete);
                }

                let sign_ch = source[pos..].chars().next().unwrap();
                if sign_ch == '+' || sign_ch == '-' {
                    pos += sign_ch.len_utf8();
                    if pos >= len {
                        // "1e+" at end of input.
                        return Err(ParseError::Incomplete);
                    }
                }

                let mut exp_digits = false;
                while pos < len {
                    let c2 = source[pos..].chars().next().unwrap();
                    if c2.is_ascii_digit() {
                        exp_digits = true;
                        pos += c2.len_utf8();
                    } else {
                        break;
                    }
                }
                if !exp_digits {
                    // `1e` or `1e+` without digits.
                    return Err(ParseError::Incomplete);
                }
            }
        }
    } else {
        // Does not look like a decimal number.
        return Ok(None);
    }

    if !saw_digit {
        return Ok(None);
    }

    let text = &source[start..pos];
    let kind = classify_decimal_number(text);
    Ok(Some((
        pos,
        NumberLiteral {
            text: text.to_string(),
            kind,
        },
    )))
}

fn classify_decimal_number(text: &str) -> NumberLiteralKind {
    // For now we only classify radix-10 reals (integers, rationals,
    // and decimals with optional exponents). Prefixes (`#b/#o/#d/#x`
    // and `#e/#i`) are handled at the tokenization layer.
    let radix = NumberRadix::Decimal;
    let exactness = NumberExactness::Unspecified;

    let finite = if text.contains('/') {
        FiniteRealRepr::Rational {
            spelling: text.to_string(),
        }
    } else if text.contains('.') || text.contains('e') || text.contains('E') {
        FiniteRealRepr::Decimal {
            spelling: text.to_string(),
        }
    } else {
        FiniteRealRepr::Integer {
            spelling: text.to_string(),
        }
    };

    NumberLiteralKind {
        radix,
        exactness,
        value: NumberValue::Real(RealRepr::Finite(finite)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lex_is_stub_for_now() {
        // Currently only `<boolean>` is implemented as a real token;
        // other token classes still yield `ParseError::Unimplemented`.
        let err = lex("(foo)").unwrap_err();
        assert!(matches!(err, ParseError::Unimplemented));
    }

    #[test]
    fn lex_only_whitespace_and_comments_produces_no_tokens() {
        let src = "   ; comment here\n  #| nested ; comment |#   ";
        let tokens = lex(src).unwrap();
        assert!(tokens.is_empty());
    }

    #[test]
    fn lex_incomplete_nested_comment_is_incomplete() {
        let err = lex("#| unclosed nested comment").unwrap_err();
        assert!(matches!(err, ParseError::Incomplete));
    }

    #[test]
    fn lex_unknown_directive_is_lex_error() {
        let err = lex("#!unknown-directive").unwrap_err();
        match err {
            ParseError::Lex { nonterminal, .. } => {
                assert_eq!(nonterminal, "<directive>");
            }
            other => panic!("expected lexical error, got: {other:?}"),
        }
    }

    #[test]
    fn lex_fold_case_directives_are_skipped() {
        let src = "#!fold-case\n  #!no-fold-case  ; rest is comment\n";
        let tokens = lex(src).unwrap();
        assert!(tokens.is_empty());
    }

    #[test]
    fn lex_parses_boolean_tokens() {
        // `<boolean> ::= #t | #f | #true | #false`
        let toks = lex("  #t  #FaLsE  #true #FALSE").unwrap();
        assert_eq!(toks.len(), 4);

        assert!(matches!(toks[0].value, Token::Boolean(true)));
        assert!(matches!(toks[1].value, Token::Boolean(false)));
        assert!(matches!(toks[2].value, Token::Boolean(true)));
        assert!(matches!(toks[3].value, Token::Boolean(false)));
    }

    #[test]
    fn lex_parses_character_tokens() {
        // `<character> ::= #\ <any character>
        //                | #\ <character name>
        //                | #\x<hex scalar value>`
        let toks = lex("#\\a #\\space #\\x41").unwrap();
        assert_eq!(toks.len(), 3);

        assert!(matches!(toks[0].value, Token::Character('a')));
        assert!(matches!(toks[1].value, Token::Character(' ')));
        assert!(matches!(toks[2].value, Token::Character('A')));
    }

    #[test]
    fn lex_parses_decimal_number_tokens() {
        let toks = lex("42 -7 3.14 .5 1e3 2.0e-2").unwrap();
        assert_eq!(toks.len(), 6);

        match &toks[0].value {
            Token::Number(n) => {
                assert_eq!(n.text, "42");
                if let NumberLiteralKind {
                    radix: NumberRadix::Decimal,
                    exactness: NumberExactness::Unspecified,
                    value: NumberValue::Real(RealRepr::Finite(FiniteRealRepr::Integer { spelling })),
                } = &n.kind
                {
                    assert_eq!(spelling, "42");
                } else {
                    panic!("unexpected classification for 42: {:#?}", n.kind);
                }
            }
            other => panic!("expected number token, got: {other:?}"),
        }

        match &toks[1].value {
            Token::Number(n) => {
                assert_eq!(n.text, "-7");
                if let NumberLiteralKind {
                    radix: NumberRadix::Decimal,
                    exactness: NumberExactness::Unspecified,
                    value: NumberValue::Real(RealRepr::Finite(FiniteRealRepr::Integer { spelling })),
                } = &n.kind
                {
                    assert_eq!(spelling, "-7");
                } else {
                    panic!("unexpected classification for -7: {:#?}", n.kind);
                }
            }
            other => panic!("expected number token, got: {other:?}"),
        }

        // The remaining forms are classified as decimal reals.
        for tok in toks.iter().skip(2) {
            match &tok.value {
                Token::Number(n) => {
                    if let NumberLiteralKind {
                        radix: NumberRadix::Decimal,
                        exactness: NumberExactness::Unspecified,
                        value:
                            NumberValue::Real(RealRepr::Finite(FiniteRealRepr::Decimal { spelling })),
                    } = &n.kind
                    {
                        assert!(!spelling.is_empty());
                    } else {
                        panic!("unexpected decimal classification: {:#?}", n.kind);
                    }
                }
                other => panic!("expected number token, got: {other:?}"),
            }
        }
    }

    #[test]
    fn lex_incomplete_decimal_number_is_incomplete() {
        let err = lex("1e").unwrap_err();
        assert!(matches!(err, ParseError::Incomplete));

        let err2 = lex("1.0e+").unwrap_err();
        assert!(matches!(err2, ParseError::Incomplete));
    }

    #[test]
    fn lex_decimal_number_requires_delimiter_and_parses_rationals() {
        // Non-delimited decimal: "42foo" should be rejected as a malformed
        // `<number>`.
        let err = lex("42foo").unwrap_err();
        match err {
            ParseError::Lex { nonterminal, .. } => {
                assert_eq!(nonterminal, "<number>");
            }
            other => panic!("expected lexical error in <number>, got: {other:?}"),
        }

        // Decimal rationals `3/4` and `-3/4` are recognized as `<number>`
        // and classified as finite rationals.
        let toks = lex("3/4 -3/4").unwrap();
        assert_eq!(toks.len(), 2);
        for t in &toks {
            match &t.value {
                Token::Number(n) => {
                    assert!(n.text == "3/4" || n.text == "-3/4");
                    if let NumberLiteralKind {
                        radix: NumberRadix::Decimal,
                        exactness: NumberExactness::Unspecified,
                        value:
                            NumberValue::Real(RealRepr::Finite(FiniteRealRepr::Rational { spelling })),
                    } = &n.kind
                    {
                        assert_eq!(spelling, &n.text);
                    } else {
                        panic!("unexpected rational classification: {:#?}", n.kind);
                    }
                }
                other => panic!("expected number token, got: {other:?}"),
            }
        }

        // `3/` at end of input is treated as incomplete.
        let err2 = lex("3/").unwrap_err();
        assert!(matches!(err2, ParseError::Incomplete));

        // `3/x` is a malformed rational.
        let err3 = lex("3/x").unwrap_err();
        match err3 {
            ParseError::Lex { nonterminal, .. } => {
                assert_eq!(nonterminal, "<number>");
            }
            _ => panic!("expected lexical error in <number>"),
        }
    }

    #[test]
    fn lex_parses_decimal_complex_numbers() {
        // Rectangular forms: a+bi, a-bi, with various ureal 10 bodies.
        let toks = lex("1+2i 1-3/4i 1+2.5i 1-1e3i").unwrap();
        assert_eq!(toks.len(), 4);

        // 1+2i
        match &toks[0].value {
            Token::Number(n) => {
                assert_eq!(n.text, "1+2i");
                if let NumberLiteralKind {
                    radix: NumberRadix::Decimal,
                    exactness: NumberExactness::Unspecified,
                    value: NumberValue::Rectangular { real, imag },
                } = &n.kind
                {
                    match real {
                        RealRepr::Finite(FiniteRealRepr::Integer { spelling }) => {
                            assert_eq!(spelling, "1");
                        }
                        other => panic!("unexpected real part for 1+2i: {other:?}"),
                    }
                    match imag {
                        RealRepr::Finite(FiniteRealRepr::Integer { spelling }) => {
                            assert_eq!(spelling, "+2");
                        }
                        other => panic!("unexpected imag part for 1+2i: {other:?}"),
                    }
                } else {
                    panic!("unexpected classification for 1+2i: {:#?}", n.kind);
                }
            }
            other => panic!("expected number token, got: {other:?}"),
        }

        // 1-3/4i
        match &toks[1].value {
            Token::Number(n) => {
                assert_eq!(n.text, "1-3/4i");
                if let NumberLiteralKind {
                    radix: NumberRadix::Decimal,
                    exactness: NumberExactness::Unspecified,
                    value: NumberValue::Rectangular { real, imag },
                } = &n.kind
                {
                    match real {
                        RealRepr::Finite(FiniteRealRepr::Integer { spelling }) => {
                            assert_eq!(spelling, "1");
                        }
                        other => panic!("unexpected real part for 1-3/4i: {other:?}"),
                    }
                    match imag {
                        RealRepr::Finite(FiniteRealRepr::Rational { spelling }) => {
                            assert_eq!(spelling, "-3/4");
                        }
                        other => panic!("unexpected imag part for 1-3/4i: {other:?}"),
                    }
                } else {
                    panic!("unexpected classification for 1-3/4i: {:#?}", n.kind);
                }
            }
            other => panic!("expected number token, got: {other:?}"),
        }

        // 1+2.5i and 1-1e3i: just basic shape checks.
        for (idx, text) in ["1+2.5i", "1-1e3i"].iter().enumerate() {
            match &toks[idx + 2].value {
                Token::Number(n) => {
                    assert_eq!(&n.text, text);
                    if let NumberLiteralKind {
                        radix: NumberRadix::Decimal,
                        exactness: NumberExactness::Unspecified,
                        value: NumberValue::Rectangular { .. },
                    } = &n.kind
                    {
                        // ok
                    } else {
                        panic!("unexpected classification for {text}: {:#?}", n.kind);
                    }
                }
                other => panic!("expected number token, got: {other:?}"),
            }
        }

        // Pure imaginary forms and polar forms.
        let toks2 = lex("+i -i +2i -3/4i 1@2 -3/4@5.0 +inf.0i 1+inf.0i").unwrap();
        assert_eq!(toks2.len(), 8);

        // +i and -i
        for (idx, text, expected_imag) in [(0usize, "+i", "1"), (1usize, "-i", "-1")] {
            match &toks2[idx].value {
                Token::Number(n) => {
                    assert_eq!(n.text, text);
                    if let NumberLiteralKind {
                        radix: NumberRadix::Decimal,
                        exactness: NumberExactness::Unspecified,
                        value: NumberValue::Rectangular { real, imag },
                    } = &n.kind
                    {
                        match real {
                            RealRepr::Finite(FiniteRealRepr::Integer { spelling }) => {
                                assert_eq!(spelling, "0");
                            }
                            other => panic!("unexpected real part for {text}: {other:?}"),
                        }
                        match imag {
                            RealRepr::Finite(FiniteRealRepr::Integer { spelling }) => {
                                assert_eq!(spelling, expected_imag);
                            }
                            other => panic!("unexpected imag part for {text}: {other:?}"),
                        }
                    } else {
                        panic!("unexpected classification for {text}: {:#?}", n.kind);
                    }
                }
                other => panic!("expected number token, got: {other:?}"),
            }
        }

        // +2i and -3/4i
        match &toks2[2].value {
            Token::Number(n) => {
                assert_eq!(n.text, "+2i");
                if let NumberLiteralKind {
                    radix: NumberRadix::Decimal,
                    exactness: NumberExactness::Unspecified,
                    value: NumberValue::Rectangular { real, imag },
                } = &n.kind
                {
                    match real {
                        RealRepr::Finite(FiniteRealRepr::Integer { spelling }) => {
                            assert_eq!(spelling, "0");
                        }
                        other => panic!("unexpected real part for +2i: {other:?}"),
                    }
                    match imag {
                        RealRepr::Finite(FiniteRealRepr::Integer { spelling }) => {
                            assert_eq!(spelling, "+2");
                        }
                        other => panic!("unexpected imag part for +2i: {other:?}"),
                    }
                } else {
                    panic!("unexpected classification for +2i: {:#?}", n.kind);
                }
            }
            other => panic!("expected number token, got: {other:?}"),
        }

        match &toks2[3].value {
            Token::Number(n) => {
                assert_eq!(n.text, "-3/4i");
                if let NumberLiteralKind {
                    radix: NumberRadix::Decimal,
                    exactness: NumberExactness::Unspecified,
                    value: NumberValue::Rectangular { real, imag },
                } = &n.kind
                {
                    match real {
                        RealRepr::Finite(FiniteRealRepr::Integer { spelling }) => {
                            assert_eq!(spelling, "0");
                        }
                        other => panic!("unexpected real part for -3/4i: {other:?}"),
                    }
                    match imag {
                        RealRepr::Finite(FiniteRealRepr::Rational { spelling }) => {
                            assert_eq!(spelling, "-3/4");
                        }
                        other => panic!("unexpected imag part for -3/4i: {other:?}"),
                    }
                } else {
                    panic!("unexpected classification for -3/4i: {:#?}", n.kind);
                }
            }
            other => panic!("expected number token, got: {other:?}"),
        }

        // 1@2 and -3/4@5.0
        match &toks2[4].value {
            Token::Number(n) => {
                assert_eq!(n.text, "1@2");
                if let NumberLiteralKind {
                    radix: NumberRadix::Decimal,
                    exactness: NumberExactness::Unspecified,
                    value: NumberValue::Polar { magnitude, angle },
                } = &n.kind
                {
                    match magnitude {
                        RealRepr::Finite(FiniteRealRepr::Integer { spelling }) => {
                            assert_eq!(spelling, "1");
                        }
                        other => panic!("unexpected magnitude for 1@2: {other:?}"),
                    }
                    match angle {
                        RealRepr::Finite(FiniteRealRepr::Integer { spelling }) => {
                            assert_eq!(spelling, "2");
                        }
                        other => panic!("unexpected angle for 1@2: {other:?}"),
                    }
                } else {
                    panic!("unexpected classification for 1@2: {:#?}", n.kind);
                }
            }
            other => panic!("expected number token, got: {other:?}"),
        }

        match &toks2[5].value {
            Token::Number(n) => {
                assert_eq!(n.text, "-3/4@5.0");
                if let NumberLiteralKind {
                    radix: NumberRadix::Decimal,
                    exactness: NumberExactness::Unspecified,
                    value: NumberValue::Polar { magnitude, angle },
                } = &n.kind
                {
                    match magnitude {
                        RealRepr::Finite(FiniteRealRepr::Rational { spelling }) => {
                            assert_eq!(spelling, "-3/4");
                        }
                        other => panic!("unexpected magnitude for -3/4@5.0: {other:?}"),
                    }
                    match angle {
                        RealRepr::Finite(FiniteRealRepr::Decimal { spelling }) => {
                            assert_eq!(spelling, "5.0");
                        }
                        other => panic!("unexpected angle for -3/4@5.0: {other:?}"),
                    }
                } else {
                    panic!("unexpected classification for -3/4@5.0: {:#?}", n.kind);
                }
            }
            other => panic!("expected number token, got: {other:?}"),
        }

        // +inf.0i and 1+inf.0i
        match &toks2[6].value {
            Token::Number(n) => {
                assert_eq!(n.text, "+inf.0i");
                if let NumberLiteralKind {
                    radix: NumberRadix::Decimal,
                    exactness: NumberExactness::Unspecified,
                    value: NumberValue::Rectangular { real, imag },
                } = &n.kind
                {
                    use InfinityNan::PositiveInfinity;
                    match real {
                        RealRepr::Finite(FiniteRealRepr::Integer { spelling }) => {
                            assert_eq!(spelling, "0");
                        }
                        other => panic!("unexpected real part for +inf.0i: {other:?}"),
                    }
                    match imag {
                        RealRepr::Infnan(k) => {
                            assert_eq!(*k, PositiveInfinity);
                        }
                        other => panic!("unexpected imag part for +inf.0i: {other:?}"),
                    }
                } else {
                    panic!("unexpected classification for +inf.0i: {:#?}", n.kind);
                }
            }
            other => panic!("expected number token, got: {other:?}"),
        }

        match &toks2[7].value {
            Token::Number(n) => {
                assert_eq!(n.text, "1+inf.0i");
                if let NumberLiteralKind {
                    radix: NumberRadix::Decimal,
                    exactness: NumberExactness::Unspecified,
                    value: NumberValue::Rectangular { real, imag },
                } = &n.kind
                {
                    use InfinityNan::PositiveInfinity;
                    match real {
                        RealRepr::Finite(FiniteRealRepr::Integer { spelling }) => {
                            assert_eq!(spelling, "1");
                        }
                        other => panic!("unexpected real part for 1+inf.0i: {other:?}"),
                    }
                    match imag {
                        RealRepr::Infnan(k) => {
                            assert_eq!(*k, PositiveInfinity);
                        }
                        other => panic!("unexpected imag part for 1+inf.0i: {other:?}"),
                    }
                } else {
                    panic!("unexpected classification for 1+inf.0i: {:#?}", n.kind);
                }
            }
            other => panic!("expected number token, got: {other:?}"),
        }
    }

    #[test]
    fn lex_parses_prefixed_decimal_numbers() {
        // `<num 10>` with `<prefix 10>` using `#d`, `#e`, `#i`.
        let toks = lex("#d42 #e3.0 #i-5/6 #d#e1 #e#d2").unwrap();
        assert_eq!(toks.len(), 5);

        // #d42 → integer 42, radix 10, unspecified exactness.
        match &toks[0].value {
            Token::Number(n) => {
                assert_eq!(n.text, "#d42");
                if let NumberLiteralKind {
                    radix: NumberRadix::Decimal,
                    exactness: NumberExactness::Unspecified,
                    value: NumberValue::Real(RealRepr::Finite(FiniteRealRepr::Integer { spelling })),
                } = &n.kind
                {
                    assert_eq!(spelling, "42");
                } else {
                    panic!("unexpected classification for #d42: {:#?}", n.kind);
                }
            }
            other => panic!("expected number token, got: {other:?}"),
        }

        // #e3.0 → decimal 3.0, radix 10, exact.
        match &toks[1].value {
            Token::Number(n) => {
                assert_eq!(n.text, "#e3.0");
                if let NumberLiteralKind {
                    radix: NumberRadix::Decimal,
                    exactness: NumberExactness::Exact,
                    value: NumberValue::Real(RealRepr::Finite(FiniteRealRepr::Decimal { spelling })),
                } = &n.kind
                {
                    assert_eq!(spelling, "3.0");
                } else {
                    panic!("unexpected classification for #e3.0: {:#?}", n.kind);
                }
            }
            other => panic!("expected number token, got: {other:?}"),
        }

        // #i-5/6 → inexact rational -5/6, radix 10.
        match &toks[2].value {
            Token::Number(n) => {
                assert_eq!(n.text, "#i-5/6");
                if let NumberLiteralKind {
                    radix: NumberRadix::Decimal,
                    exactness: NumberExactness::Inexact,
                    value:
                        NumberValue::Real(RealRepr::Finite(FiniteRealRepr::Rational { spelling })),
                } = &n.kind
                {
                    assert_eq!(spelling, "-5/6");
                } else {
                    panic!("unexpected classification for #i-5/6: {:#?}", n.kind);
                }
            }
            other => panic!("expected number token, got: {other:?}"),
        }

        // #d#e1 and #e#d2 both combine radix and exactness prefixes
        // in either order.
        for (idx, expected_text, expected_spelling) in
            [(3usize, "#d#e1", "1"), (4usize, "#e#d2", "2")]
        {
            match &toks[idx].value {
                Token::Number(n) => {
                    assert_eq!(n.text, expected_text);
                    if let NumberLiteralKind {
                        radix: NumberRadix::Decimal,
                        exactness: NumberExactness::Exact,
                        value:
                            NumberValue::Real(RealRepr::Finite(FiniteRealRepr::Integer { spelling })),
                    } = &n.kind
                    {
                        assert_eq!(spelling, expected_spelling);
                    } else {
                        panic!(
                            "unexpected classification for {expected_text}: {:#?}",
                            n.kind
                        );
                    }
                }
                other => panic!("expected number token, got: {other:?}"),
            }
        }
    }

    #[test]
    fn lex_parses_prefixed_decimal_complex_numbers() {
        // `<num 10>` complex forms with `<prefix 10>` using `#d`, `#e`, `#i`.
        let toks = lex("#d1+2i #e1-3/4i #i+2i #e1@2 #d+inf.0i #e1+inf.0i").unwrap();
        assert_eq!(toks.len(), 6);

        // #d1+2i → rectangular complex with unspecified exactness.
        match &toks[0].value {
            Token::Number(n) => {
                assert_eq!(n.text, "#d1+2i");
                if let NumberLiteralKind {
                    radix: NumberRadix::Decimal,
                    exactness: NumberExactness::Unspecified,
                    value: NumberValue::Rectangular { real, imag },
                } = &n.kind
                {
                    match real {
                        RealRepr::Finite(FiniteRealRepr::Integer { spelling }) => {
                            assert_eq!(spelling, "1");
                        }
                        other => panic!("unexpected real part for #d1+2i: {other:?}"),
                    }
                    match imag {
                        RealRepr::Finite(FiniteRealRepr::Integer { spelling }) => {
                            assert_eq!(spelling, "+2");
                        }
                        other => panic!("unexpected imag part for #d1+2i: {other:?}"),
                    }
                } else {
                    panic!("unexpected classification for #d1+2i: {:#?}", n.kind);
                }
            }
            other => panic!("expected number token, got: {other:?}"),
        }

        // #e1-3/4i → exact rectangular complex with rational imaginary part.
        match &toks[1].value {
            Token::Number(n) => {
                assert_eq!(n.text, "#e1-3/4i");
                if let NumberLiteralKind {
                    radix: NumberRadix::Decimal,
                    exactness: NumberExactness::Exact,
                    value: NumberValue::Rectangular { real, imag },
                } = &n.kind
                {
                    match real {
                        RealRepr::Finite(FiniteRealRepr::Integer { spelling }) => {
                            assert_eq!(spelling, "1");
                        }
                        other => panic!("unexpected real part for #e1-3/4i: {other:?}"),
                    }
                    match imag {
                        RealRepr::Finite(FiniteRealRepr::Rational { spelling }) => {
                            assert_eq!(spelling, "-3/4");
                        }
                        other => panic!("unexpected imag part for #e1-3/4i: {other:?}"),
                    }
                } else {
                    panic!("unexpected classification for #e1-3/4i: {:#?}", n.kind);
                }
            }
            other => panic!("expected number token, got: {other:?}"),
        }

        // #i+2i → inexact pure imaginary.
        match &toks[2].value {
            Token::Number(n) => {
                assert_eq!(n.text, "#i+2i");
                if let NumberLiteralKind {
                    radix: NumberRadix::Decimal,
                    exactness: NumberExactness::Inexact,
                    value: NumberValue::Rectangular { real, imag },
                } = &n.kind
                {
                    match real {
                        RealRepr::Finite(FiniteRealRepr::Integer { spelling }) => {
                            assert_eq!(spelling, "0");
                        }
                        other => panic!("unexpected real part for #i+2i: {other:?}"),
                    }
                    match imag {
                        RealRepr::Finite(FiniteRealRepr::Integer { spelling }) => {
                            assert_eq!(spelling, "+2");
                        }
                        other => panic!("unexpected imag part for #i+2i: {other:?}"),
                    }
                } else {
                    panic!("unexpected classification for #i+2i: {:#?}", n.kind);
                }
            }
            other => panic!("expected number token, got: {other:?}"),
        }

        // #e1@2 → exact polar complex.
        match &toks[3].value {
            Token::Number(n) => {
                assert_eq!(n.text, "#e1@2");
                if let NumberLiteralKind {
                    radix: NumberRadix::Decimal,
                    exactness: NumberExactness::Exact,
                    value: NumberValue::Polar { magnitude, angle },
                } = &n.kind
                {
                    match magnitude {
                        RealRepr::Finite(FiniteRealRepr::Integer { spelling }) => {
                            assert_eq!(spelling, "1");
                        }
                        other => panic!("unexpected magnitude for #e1@2: {other:?}"),
                    }
                    match angle {
                        RealRepr::Finite(FiniteRealRepr::Integer { spelling }) => {
                            assert_eq!(spelling, "2");
                        }
                        other => panic!("unexpected angle for #e1@2: {other:?}"),
                    }
                } else {
                    panic!("unexpected classification for #e1@2: {:#?}", n.kind);
                }
            }
            other => panic!("expected number token, got: {other:?}"),
        }

        // #d+inf.0i and #e1+inf.0i → rectangular with `<infnan>` imaginary part.
        for (idx, expected_text, expect_real) in
            [(4usize, "#d+inf.0i", "0"), (5usize, "#e1+inf.0i", "1")]
        {
            match &toks[idx].value {
                Token::Number(n) => {
                    assert_eq!(n.text, expected_text);
                    if let NumberLiteralKind {
                        radix: NumberRadix::Decimal,
                        value: NumberValue::Rectangular { real, imag },
                        ..
                    } = &n.kind
                    {
                        use InfinityNan::PositiveInfinity;
                        match real {
                            RealRepr::Finite(FiniteRealRepr::Integer { spelling }) => {
                                assert_eq!(spelling, expect_real);
                            }
                            other => panic!("unexpected real part for {expected_text}: {other:?}"),
                        }
                        match imag {
                            RealRepr::Infnan(k) => {
                                assert_eq!(*k, PositiveInfinity);
                            }
                            other => panic!("unexpected imag part for {expected_text}: {other:?}"),
                        }
                    } else {
                        panic!(
                            "unexpected classification for {expected_text}: {:#?}",
                            n.kind
                        );
                    }
                }
                other => panic!("expected number token, got: {other:?}"),
            }
        }
    }

    #[test]
    fn lex_prefixed_decimal_number_errors() {
        // Duplicate radix prefix: #d#d1.
        let err = lex("#d#d1").unwrap_err();
        match err {
            ParseError::Lex { nonterminal, .. } => {
                assert_eq!(nonterminal, "<number>");
            }
            other => panic!("expected lexical error in <number>, got: {other:?}"),
        }

        // Duplicate exactness prefix: #e#i1.
        let err2 = lex("#e#i1").unwrap_err();
        match err2 {
            ParseError::Lex { nonterminal, .. } => {
                assert_eq!(nonterminal, "<number>");
            }
            other => panic!("expected lexical error in <number>, got: {other:?}"),
        }

        // Prefixed decimal numbers must be followed by a <delimiter>.
        let err3 = lex("#d42foo").unwrap_err();
        match err3 {
            ParseError::Lex { nonterminal, .. } => {
                assert_eq!(nonterminal, "<number>");
            }
            other => panic!("expected lexical error in <number>, got: {other:?}"),
        }

        // Incomplete prefix with no number body.
        let err4 = lex("#d").unwrap_err();
        assert!(matches!(err4, ParseError::Incomplete));
    }

    #[test]
    fn lex_infnan_numbers_plain_and_prefixed() {
        // Plain `<infnan>` without prefixes.
        let toks = lex("+inf.0 -inf.0 +nan.0 -nan.0").unwrap();
        assert_eq!(toks.len(), 4);

        let kinds: Vec<_> = toks
            .iter()
            .map(|t| match &t.value {
                Token::Number(n) => &n.kind,
                other => panic!("expected number token, got: {other:?}"),
            })
            .collect();

        use InfinityNan::*;

        let expect = [
            ("+inf.0", PositiveInfinity),
            ("-inf.0", NegativeInfinity),
            ("+nan.0", PositiveNaN),
            ("-nan.0", NegativeNaN),
        ];

        for (i, (text, kind)) in expect.iter().enumerate() {
            assert_eq!(
                match &toks[i].value {
                    Token::Number(n) => n.text.as_str(),
                    _ => unreachable!(),
                },
                *text
            );
            if let NumberLiteralKind {
                radix: NumberRadix::Decimal,
                exactness: NumberExactness::Unspecified,
                value: NumberValue::Real(RealRepr::Infnan(k)),
            } = kinds[i]
            {
                assert_eq!(k, kind);
            } else {
                panic!(
                    "unexpected infnan classification for {text}: {:#?}",
                    kinds[i]
                );
            }
        }

        // Prefixed `<infnan>` with exactness and non-decimal radices.
        let toks2 = lex("#e+inf.0 #i-nan.0 #b+inf.0 #x-nan.0 #b#e+inf.0 #i#x-nan.0").unwrap();
        assert_eq!(toks2.len(), 6);

        // #e+inf.0 → exact decimal +inf.0.
        match &toks2[0].value {
            Token::Number(n) => {
                assert_eq!(n.text, "#e+inf.0");
                if let NumberLiteralKind {
                    radix: NumberRadix::Decimal,
                    exactness: NumberExactness::Exact,
                    value: NumberValue::Real(RealRepr::Infnan(k)),
                } = &n.kind
                {
                    assert_eq!(*k, PositiveInfinity);
                } else {
                    panic!("unexpected classification for #e+inf.0: {:#?}", n.kind);
                }
            }
            other => panic!("expected number token, got: {other:?}"),
        }

        // #i-nan.0 → inexact decimal -nan.0.
        match &toks2[1].value {
            Token::Number(n) => {
                assert_eq!(n.text, "#i-nan.0");
                if let NumberLiteralKind {
                    radix: NumberRadix::Decimal,
                    exactness: NumberExactness::Inexact,
                    value: NumberValue::Real(RealRepr::Infnan(k)),
                } = &n.kind
                {
                    assert_eq!(*k, NegativeNaN);
                } else {
                    panic!("unexpected classification for #i-nan.0: {:#?}", n.kind);
                }
            }
            other => panic!("expected number token, got: {other:?}"),
        }

        // #b+inf.0 → binary +inf.0, unspecified exactness.
        match &toks2[2].value {
            Token::Number(n) => {
                assert_eq!(n.text, "#b+inf.0");
                if let NumberLiteralKind {
                    radix: NumberRadix::Binary,
                    exactness: NumberExactness::Unspecified,
                    value: NumberValue::Real(RealRepr::Infnan(k)),
                } = &n.kind
                {
                    assert_eq!(*k, PositiveInfinity);
                } else {
                    panic!("unexpected classification for #b+inf.0: {:#?}", n.kind);
                }
            }
            other => panic!("expected number token, got: {other:?}"),
        }

        // #x-nan.0 → hexadecimal -nan.0, unspecified exactness.
        match &toks2[3].value {
            Token::Number(n) => {
                assert_eq!(n.text, "#x-nan.0");
                if let NumberLiteralKind {
                    radix: NumberRadix::Hexadecimal,
                    exactness: NumberExactness::Unspecified,
                    value: NumberValue::Real(RealRepr::Infnan(k)),
                } = &n.kind
                {
                    assert_eq!(*k, NegativeNaN);
                } else {
                    panic!("unexpected classification for #x-nan.0: {:#?}", n.kind);
                }
            }
            other => panic!("expected number token, got: {other:?}"),
        }

        // #b#e+inf.0 → exact binary +inf.0.
        match &toks2[4].value {
            Token::Number(n) => {
                assert_eq!(n.text, "#b#e+inf.0");
                if let NumberLiteralKind {
                    radix: NumberRadix::Binary,
                    exactness: NumberExactness::Exact,
                    value: NumberValue::Real(RealRepr::Infnan(k)),
                } = &n.kind
                {
                    assert_eq!(*k, PositiveInfinity);
                } else {
                    panic!("unexpected classification for #b#e+inf.0: {:#?}", n.kind);
                }
            }
            other => panic!("expected number token, got: {other:?}"),
        }

        // #i#x-nan.0 → inexact hexadecimal -nan.0.
        match &toks2[5].value {
            Token::Number(n) => {
                assert_eq!(n.text, "#i#x-nan.0");
                if let NumberLiteralKind {
                    radix: NumberRadix::Hexadecimal,
                    exactness: NumberExactness::Inexact,
                    value: NumberValue::Real(RealRepr::Infnan(k)),
                } = &n.kind
                {
                    assert_eq!(*k, NegativeNaN);
                } else {
                    panic!("unexpected classification for #i#x-nan.0: {:#?}", n.kind);
                }
            }
            other => panic!("expected number token, got: {other:?}"),
        }
    }

    #[test]
    fn lex_parses_nondecimal_number_tokens() {
        // `<num 2>`, `<num 8>`, `<num 16>` integers and rationals with
        // optional `<exactness>` prefixes.
        let toks = lex("#b1010 #o77 #x1f #b101/11 #xA/F #b#e1 #i#o7").unwrap();
        assert_eq!(toks.len(), 7);

        // #b1010 → binary integer 1010.
        match &toks[0].value {
            Token::Number(n) => {
                assert_eq!(n.text, "#b1010");
                if let NumberLiteralKind {
                    radix: NumberRadix::Binary,
                    exactness: NumberExactness::Unspecified,
                    value: NumberValue::Real(RealRepr::Finite(FiniteRealRepr::Integer { spelling })),
                } = &n.kind
                {
                    assert_eq!(spelling, "1010");
                } else {
                    panic!("unexpected classification for #b1010: {:#?}", n.kind);
                }
            }
            other => panic!("expected number token, got: {other:?}"),
        }

        // #o77 → octal integer 77.
        match &toks[1].value {
            Token::Number(n) => {
                assert_eq!(n.text, "#o77");
                if let NumberLiteralKind {
                    radix: NumberRadix::Octal,
                    exactness: NumberExactness::Unspecified,
                    value: NumberValue::Real(RealRepr::Finite(FiniteRealRepr::Integer { spelling })),
                } = &n.kind
                {
                    assert_eq!(spelling, "77");
                } else {
                    panic!("unexpected classification for #o77: {:#?}", n.kind);
                }
            }
            other => panic!("expected number token, got: {other:?}"),
        }

        // #x1f → hexadecimal integer 1f.
        match &toks[2].value {
            Token::Number(n) => {
                assert_eq!(n.text, "#x1f");
                if let NumberLiteralKind {
                    radix: NumberRadix::Hexadecimal,
                    exactness: NumberExactness::Unspecified,
                    value: NumberValue::Real(RealRepr::Finite(FiniteRealRepr::Integer { spelling })),
                } = &n.kind
                {
                    assert_eq!(spelling, "1f");
                } else {
                    panic!("unexpected classification for #x1f: {:#?}", n.kind);
                }
            }
            other => panic!("expected number token, got: {other:?}"),
        }

        // #b101/11 → binary rational 101/11.
        match &toks[3].value {
            Token::Number(n) => {
                assert_eq!(n.text, "#b101/11");
                if let NumberLiteralKind {
                    radix: NumberRadix::Binary,
                    exactness: NumberExactness::Unspecified,
                    value:
                        NumberValue::Real(RealRepr::Finite(FiniteRealRepr::Rational { spelling })),
                } = &n.kind
                {
                    assert_eq!(spelling, "101/11");
                } else {
                    panic!("unexpected classification for #b101/11: {:#?}", n.kind);
                }
            }
            other => panic!("expected number token, got: {other:?}"),
        }

        // #xA/F → hexadecimal rational A/F.
        match &toks[4].value {
            Token::Number(n) => {
                assert_eq!(n.text, "#xA/F");
                if let NumberLiteralKind {
                    radix: NumberRadix::Hexadecimal,
                    exactness: NumberExactness::Unspecified,
                    value:
                        NumberValue::Real(RealRepr::Finite(FiniteRealRepr::Rational { spelling })),
                } = &n.kind
                {
                    assert_eq!(spelling, "A/F");
                } else {
                    panic!("unexpected classification for #xA/F: {:#?}", n.kind);
                }
            }
            other => panic!("expected number token, got: {other:?}"),
        }

        // #b#e1 → exact binary integer.
        match &toks[5].value {
            Token::Number(n) => {
                assert_eq!(n.text, "#b#e1");
                if let NumberLiteralKind {
                    radix: NumberRadix::Binary,
                    exactness: NumberExactness::Exact,
                    value: NumberValue::Real(RealRepr::Finite(FiniteRealRepr::Integer { spelling })),
                } = &n.kind
                {
                    assert_eq!(spelling, "1");
                } else {
                    panic!("unexpected classification for #b#e1: {:#?}", n.kind);
                }
            }
            other => panic!("expected number token, got: {other:?}"),
        }

        // #i#o7 → inexact octal integer.
        match &toks[6].value {
            Token::Number(n) => {
                assert_eq!(n.text, "#i#o7");
                if let NumberLiteralKind {
                    radix: NumberRadix::Octal,
                    exactness: NumberExactness::Inexact,
                    value: NumberValue::Real(RealRepr::Finite(FiniteRealRepr::Integer { spelling })),
                } = &n.kind
                {
                    assert_eq!(spelling, "7");
                } else {
                    panic!("unexpected classification for #i#o7: {:#?}", n.kind);
                }
            }
            other => panic!("expected number token, got: {other:?}"),
        }
    }

    #[test]
    fn lex_nondecimal_number_errors_and_complex_placeholders() {
        // Invalid digit for radix: #b102.
        let err = lex("#b102").unwrap_err();
        match err {
            ParseError::Lex { nonterminal, .. } => {
                assert_eq!(nonterminal, "<number>");
            }
            other => panic!("expected lexical error in <number>, got: {other:?}"),
        }

        // Incomplete rational: #o7/.
        let err2 = lex("#o7/").unwrap_err();
        assert!(matches!(err2, ParseError::Incomplete));

        // Malformed rational denominator: #xA/G.
        let err3 = lex("#xA/G").unwrap_err();
        match err3 {
            ParseError::Lex { nonterminal, .. } => {
                assert_eq!(nonterminal, "<number>");
            }
            other => panic!("expected lexical error in <number>, got: {other:?}"),
        }

        // Duplicate radix prefix in non-decimal numbers: #b#b1.
        let err4 = lex("#b#b1").unwrap_err();
        match err4 {
            ParseError::Lex { nonterminal, .. } => {
                assert_eq!(nonterminal, "<number>");
            }
            other => panic!("expected lexical error in <number>, got: {other:?}"),
        }

        // Duplicate exactness prefix: #i#e#b1.
        let err5 = lex("#i#e#b1").unwrap_err();
        match err5 {
            ParseError::Lex { nonterminal, .. } => {
                assert_eq!(nonterminal, "<number>");
            }
            other => panic!("expected lexical error in <number>, got: {other:?}"),
        }

        // Non-decimal complex forms are now supported.
        let toks = lex("#b1+10i #x1-2i #b+i #o-i #b1@10 #x1+inf.0i #b+inf.0i").unwrap();
        assert_eq!(toks.len(), 7);

        // #b1+10i → rectangular complex in binary.
        match &toks[0].value {
            Token::Number(n) => {
                assert_eq!(n.text, "#b1+10i");
                if let NumberLiteralKind {
                    radix: NumberRadix::Binary,
                    value: NumberValue::Rectangular { real, imag },
                    ..
                } = &n.kind
                {
                    match real {
                        RealRepr::Finite(FiniteRealRepr::Integer { spelling }) => {
                            assert_eq!(spelling, "1");
                        }
                        other => panic!("unexpected real part for #b1+10i: {other:?}"),
                    }
                    match imag {
                        RealRepr::Finite(FiniteRealRepr::Integer { spelling }) => {
                            assert_eq!(spelling, "+10");
                        }
                        other => panic!("unexpected imag part for #b1+10i: {other:?}"),
                    }
                } else {
                    panic!("unexpected classification for #b1+10i: {:#?}", n.kind);
                }
            }
            other => panic!("expected number token, got: {other:?}"),
        }

        // #x1-2i → rectangular complex in hexadecimal.
        match &toks[1].value {
            Token::Number(n) => {
                assert_eq!(n.text, "#x1-2i");
                if let NumberLiteralKind {
                    radix: NumberRadix::Hexadecimal,
                    value: NumberValue::Rectangular { real, imag },
                    ..
                } = &n.kind
                {
                    match real {
                        RealRepr::Finite(FiniteRealRepr::Integer { spelling }) => {
                            assert_eq!(spelling, "1");
                        }
                        other => panic!("unexpected real part for #x1-2i: {other:?}"),
                    }
                    match imag {
                        RealRepr::Finite(FiniteRealRepr::Integer { spelling }) => {
                            assert_eq!(spelling, "-2");
                        }
                        other => panic!("unexpected imag part for #x1-2i: {other:?}"),
                    }
                } else {
                    panic!("unexpected classification for #x1-2i: {:#?}", n.kind);
                }
            }
            other => panic!("expected number token, got: {other:?}"),
        }

        // #b+i and #o-i → pure imaginary with unit magnitude.
        for (idx, expected_text, expected_imag, expected_radix) in [
            (2usize, "#b+i", "1", NumberRadix::Binary),
            (3usize, "#o-i", "-1", NumberRadix::Octal),
        ] {
            match &toks[idx].value {
                Token::Number(n) => {
                    assert_eq!(n.text, expected_text);
                    if let NumberLiteralKind {
                        radix,
                        value: NumberValue::Rectangular { real, imag },
                        ..
                    } = &n.kind
                    {
                        assert_eq!(*radix, expected_radix);
                        match real {
                            RealRepr::Finite(FiniteRealRepr::Integer { spelling }) => {
                                assert_eq!(spelling, "0");
                            }
                            other => panic!("unexpected real part for {expected_text}: {other:?}"),
                        }
                        match imag {
                            RealRepr::Finite(FiniteRealRepr::Integer { spelling }) => {
                                assert_eq!(spelling, expected_imag);
                            }
                            other => panic!("unexpected imag part for {expected_text}: {other:?}"),
                        }
                    } else {
                        panic!(
                            "unexpected classification for {expected_text}: {:#?}",
                            n.kind
                        );
                    }
                }
                other => panic!("expected number token, got: {other:?}"),
            }
        }

        // #b1@10 → polar complex in binary.
        match &toks[4].value {
            Token::Number(n) => {
                assert_eq!(n.text, "#b1@10");
                if let NumberLiteralKind {
                    radix: NumberRadix::Binary,
                    value: NumberValue::Polar { magnitude, angle },
                    ..
                } = &n.kind
                {
                    match magnitude {
                        RealRepr::Finite(FiniteRealRepr::Integer { spelling }) => {
                            assert_eq!(spelling, "1");
                        }
                        other => panic!("unexpected magnitude for #b1@10: {other:?}"),
                    }
                    match angle {
                        RealRepr::Finite(FiniteRealRepr::Integer { spelling }) => {
                            assert_eq!(spelling, "10");
                        }
                        other => panic!("unexpected angle for #b1@10: {other:?}"),
                    }
                } else {
                    panic!("unexpected classification for #b1@10: {:#?}", n.kind);
                }
            }
            other => panic!("expected number token, got: {other:?}"),
        }

        // #x1+inf.0i and #b+inf.0i → non-decimal `<infnan>` complexes.
        for (idx, expected_text, expected_radix, expect_real) in [
            (5usize, "#x1+inf.0i", NumberRadix::Hexadecimal, "1"),
            (6usize, "#b+inf.0i", NumberRadix::Binary, "0"),
        ] {
            match &toks[idx].value {
                Token::Number(n) => {
                    assert_eq!(n.text, expected_text);
                    if let NumberLiteralKind {
                        radix,
                        value: NumberValue::Rectangular { real, imag },
                        ..
                    } = &n.kind
                    {
                        use InfinityNan::PositiveInfinity;
                        assert_eq!(*radix, expected_radix);
                        match real {
                            RealRepr::Finite(FiniteRealRepr::Integer { spelling }) => {
                                assert_eq!(spelling, expect_real);
                            }
                            other => panic!("unexpected real part for {expected_text}: {other:?}"),
                        }
                        match imag {
                            RealRepr::Infnan(k) => {
                                assert_eq!(*k, PositiveInfinity);
                            }
                            other => panic!("unexpected imag part for {expected_text}: {other:?}"),
                        }
                    } else {
                        panic!(
                            "unexpected classification for {expected_text}: {:#?}",
                            n.kind
                        );
                    }
                }
                other => panic!("expected number token, got: {other:?}"),
            }
        }
    }

    #[test]
    fn lex_infnan_errors_and_complex_placeholders() {
        // Non-delimited `<infnan>` should be a lexical error.
        let err = lex("+inf.0foo").unwrap_err();
        match err {
            ParseError::Lex { nonterminal, .. } => {
                assert_eq!(nonterminal, "<number>");
            }
            other => panic!("expected lexical error in <number>, got: {other:?}"),
        }

        let err2 = lex("#e+inf.0bar").unwrap_err();
        match err2 {
            ParseError::Lex { nonterminal, .. } => {
                assert_eq!(nonterminal, "<number>");
            }
            other => panic!("expected lexical error in <number>, got: {other:?}"),
        }
        // Decimal `<infnan>` complex forms are now supported, while
        // non-decimal ones remain unimplemented.
        let toks = lex("+inf.0i").unwrap();
        assert_eq!(toks.len(), 1);
        match &toks[0].value {
            Token::Number(n) => {
                assert_eq!(n.text, "+inf.0i");
                if let NumberLiteralKind {
                    radix: NumberRadix::Decimal,
                    exactness: NumberExactness::Unspecified,
                    value: NumberValue::Rectangular { real, imag },
                } = &n.kind
                {
                    use InfinityNan::PositiveInfinity;
                    match real {
                        RealRepr::Finite(FiniteRealRepr::Integer { spelling }) => {
                            assert_eq!(spelling, "0");
                        }
                        other => panic!("unexpected real part for +inf.0i: {other:?}"),
                    }
                    match imag {
                        RealRepr::Infnan(k) => {
                            assert_eq!(*k, PositiveInfinity);
                        }
                        other => panic!("unexpected imag part for +inf.0i: {other:?}"),
                    }
                } else {
                    panic!("unexpected classification for +inf.0i: {:#?}", n.kind);
                }
            }
            other => panic!("expected number token, got: {other:?}"),
        }

        // Non-decimal `<infnan>` complexes are now supported.
        let toks2 = lex("#b+inf.0i").unwrap();
        assert_eq!(toks2.len(), 1);
        match &toks2[0].value {
            Token::Number(n) => {
                assert_eq!(n.text, "#b+inf.0i");
                if let NumberLiteralKind {
                    radix: NumberRadix::Binary,
                    exactness: NumberExactness::Unspecified,
                    value: NumberValue::Rectangular { real, imag },
                } = &n.kind
                {
                    use InfinityNan::PositiveInfinity;
                    match real {
                        RealRepr::Finite(FiniteRealRepr::Integer { spelling }) => {
                            assert_eq!(spelling, "0");
                        }
                        other => panic!("unexpected real part for #b+inf.0i: {other:?}"),
                    }
                    match imag {
                        RealRepr::Infnan(k) => {
                            assert_eq!(*k, PositiveInfinity);
                        }
                        other => panic!("unexpected imag part for #b+inf.0i: {other:?}"),
                    }
                } else {
                    panic!("unexpected classification for #b+inf.0i: {:#?}", n.kind);
                }
            }
            other => panic!("expected number token, got: {other:?}"),
        }
    }

    #[test]
    fn lex_parses_string_tokens_simple_and_escapes() {
        // Simple string and mnemonic/hex escapes.
        let toks = lex("  \"hi\"  \"a\\n\\t\\r\\b\\a\\\\\\\"\"  \"\\x41;\"").unwrap();
        assert_eq!(toks.len(), 3);

        assert!(matches!(toks[0].value, Token::String(ref v) if v == "hi"));
        assert!(matches!(toks[1].value, Token::String(ref v) if v == "a\n\t\r\u{8}\u{7}\\\""));
        assert!(matches!(toks[2].value, Token::String(ref v) if v == "A"));
    }

    #[test]
    fn lex_parses_string_with_line_splice() {
        // Backslash-newline splice should disappear from the resulting string.
        let toks = lex("\"foo\\\n   bar\"").unwrap();
        assert_eq!(toks.len(), 1);
        assert!(matches!(toks[0].value, Token::String(ref v) if v == "foobar"));
    }

    #[test]
    fn lex_incomplete_string_is_incomplete() {
        let err = lex("\"unterminated").unwrap_err();
        assert!(matches!(err, ParseError::Incomplete));
    }

    #[test]
    fn lex_invalid_string_hex_escape_is_lex_error() {
        let err = lex("\"\\xZZ;\"").unwrap_err();
        match err {
            ParseError::Lex { nonterminal, .. } => {
                assert_eq!(nonterminal, "<string>");
            }
            other => panic!("expected lexical error in <string>, got: {other:?}"),
        }
    }
}
