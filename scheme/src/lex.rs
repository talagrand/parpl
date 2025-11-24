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
    /// `#;` (datum comment prefix)
    ///
    /// Note: This is a deviation from R7RS, which treats `#; <datum>` as
    /// intertoken space. Since the lexer cannot parse `<datum>`, it yields
    /// this token so the parser can perform the skipping.
    DatumComment,
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
/// classifications, currently `<boolean>`, `<character>`, `<string>`, and `<number>`.
pub fn lex(source: &str) -> Result<Vec<SpannedToken>, ParseError> {
    let mut tokens = Vec::new();
    let mut pos = 0usize;
    let len = source.len();

    // Track `#!fold-case` / `#!no-fold-case` directives.
    //
    // R7RS-DEVIATION: Although we recognize these directives
    // lexically, we deliberately ignore their semantics for now and
    // keep the reader case-sensitive with ASCII-only identifiers.
    // This errs on the side of rejecting some valid programs rather
    // than accepting invalid ones.
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
        let start = pos;

        if let Some((end, token)) = lex_string(source, start)? {
            tokens.push(Syntax::new(Span { start, end }, token));
            pos = end;
            continue;
        }

        if let Some((end, token)) = lex_character(source, start)? {
            tokens.push(Syntax::new(Span { start, end }, token));
            pos = end;
            continue;
        }

        if let Some((end, token)) = lex_boolean(source, start)? {
            tokens.push(Syntax::new(Span { start, end }, token));
            pos = end;
            continue;
        }

        if let Some((end, literal)) = lex_prefixed_number(source, start)? {
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
            tokens.push(Syntax::new(Span { start, end }, Token::Number(literal)));
            pos = end;
            continue;
        }

        let ch = source[pos..].chars().next().unwrap();
        match ch {
            '(' => {
                let end = pos + ch.len_utf8();
                tokens.push(Syntax::new(Span { start, end }, Token::LParen));
                pos = end;
                continue;
            }
            ')' => {
                let end = pos + ch.len_utf8();
                tokens.push(Syntax::new(Span { start, end }, Token::RParen));
                pos = end;
                continue;
            }
            '\'' => {
                let end = pos + ch.len_utf8();
                tokens.push(Syntax::new(Span { start, end }, Token::Quote));
                pos = end;
                continue;
            }
            '`' => {
                let end = pos + ch.len_utf8();
                tokens.push(Syntax::new(Span { start, end }, Token::Backquote));
                pos = end;
                continue;
            }
            ',' => {
                let comma_end = pos + ch.len_utf8();
                let mut end = comma_end;
                if comma_end < len {
                    let next = source[comma_end..].chars().next().unwrap();
                    if next == '@' {
                        end = comma_end + next.len_utf8();
                        tokens.push(Syntax::new(Span { start, end }, Token::CommaAt));
                        pos = end;
                        continue;
                    }
                }
                tokens.push(Syntax::new(Span { start, end }, Token::Comma));
                pos = end;
                continue;
            }
            '#' => {
                let hash_end = pos + ch.len_utf8();
                if hash_end < len {
                    let next = source[hash_end..].chars().next().unwrap();
                    if next == '(' {
                        let end = hash_end + next.len_utf8();
                        tokens.push(Syntax::new(Span { start, end }, Token::VectorStart));
                        pos = end;
                        continue;
                    } else if next == ';' {
                        // R7RS-DEVIATION: #; is technically a comment and should be skipped by the lexer.
                        // However, skipping it requires parsing a full datum, which is not possible in the lexer.
                        // We return it as a token so the parser can handle the skipping.
                        // For now, we report Unimplemented as requested.
                        return Err(ParseError::Unimplemented);
                    } else if next == 'u' || next == 'U' {
                        // Possible `#u8(` bytevector prefix.
                        let mut p = hash_end + next.len_utf8();
                        if p < len {
                            let c2 = source[p..].chars().next().unwrap();
                            if c2 == '8' {
                                p += c2.len_utf8();
                                if p < len {
                                    let c3 = source[p..].chars().next().unwrap();
                                    if c3 == '(' {
                                        let end = p + c3.len_utf8();
                                        tokens.push(Syntax::new(
                                            Span { start, end },
                                            Token::ByteVectorStart,
                                        ));
                                        pos = end;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
                // Other `#`-prefixed tokens (e.g. datum comments) are not
                // implemented yet at the lexical layer.
                return Err(ParseError::Unimplemented);
            }
            '+' | '-' | '0'..='9' => {
                // `<number>` token in decimal radix (R = 10), including
                // both real and complex forms as specified by `<complex 10>`.
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
            '.' => {
                // Either a decimal `<number>` starting with `.`, or the
                // standalone `.` punctuation token.
                let look = pos + ch.len_utf8();
                if look < len {
                    let next = source[look..].chars().next().unwrap();
                    if next.is_ascii_digit() {
                        if let Some((end, literal)) = lex_complex_decimal(source, start)? {
                            let span = Span { start, end };
                            tokens.push(Syntax::new(span, Token::Number(literal)));
                            pos = end;
                            continue;
                        } else {
                            return Err(ParseError::Unimplemented);
                        }
                    }
                }
                // Treat as `.` token.
                let end = look;
                tokens.push(Syntax::new(Span { start, end }, Token::Dot));
                pos = end;
                continue;
            }
            _ => {
                // Other token classes (identifiers, etc.) are not yet implemented.
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
fn ensure_delimiter(
    source: &str,
    pos: usize,
    start: usize,
    context: &'static str,
) -> Result<(), ParseError> {
    if pos < source.len() {
        let after = source[pos..].chars().next().unwrap();
        if !is_delimiter(after) {
            let span = Span { start, end: pos };
            return Err(ParseError::lexical(
                span,
                context,
                "literal not followed by a delimiter",
            ));
        }
    }
    Ok(())
}

fn lex_real_repr(
    source: &str,
    start: usize,
    radix: NumberRadix,
) -> Result<Option<(usize, RealRepr)>, ParseError> {
    if let Some((end, infnan)) = lex_infnan_body(source, start) {
        return Ok(Some((end, RealRepr::Infnan(infnan))));
    }

    if let Some((end, finite)) = lex_sign_ureal_for_radix(source, start, radix)? {
        return Ok(Some((end, RealRepr::Finite(finite))));
    }

    Ok(None)
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

    // 1. Try to parse the first component as a real number.
    // This covers `<real R>`, the real part of `<real R> @ <real R>`,
    // and the real part of `<real R> +/- ... i`.
    // It also covers the imaginary part of `+ <ureal R> i` if we consider
    // the leading `+` as part of the number.
    let first_attempt = lex_real_repr(source, body_start, radix)?;

    if let Some((end1, repr1)) = first_attempt {
        // We successfully parsed something that looks like a real number.
        // Now check what follows.

        if end1 >= len {
            // End of input. It's a real number.
            let text = &source[literal_start..end1];
            let kind = NumberLiteralKind {
                radix,
                exactness,
                value: NumberValue::Real(repr1),
            };
            return Ok(Some((
                end1,
                NumberLiteral {
                    text: text.to_string(),
                    kind,
                },
            )));
        }

        let next_ch = source[end1..].chars().next().unwrap();

        if is_delimiter(next_ch) {
            // It's a real number.
            let text = &source[literal_start..end1];
            let kind = NumberLiteralKind {
                radix,
                exactness,
                value: NumberValue::Real(repr1),
            };
            return Ok(Some((
                end1,
                NumberLiteral {
                    text: text.to_string(),
                    kind,
                },
            )));
        }

        match next_ch {
            'i' | 'I' => {
                // It was actually a pure imaginary number: `<real R> i`
                // e.g. `+inf.0i`, `+5i` (if `+5` was parsed as real).
                let i_end = end1 + next_ch.len_utf8();
                ensure_delimiter(source, i_end, literal_start, "<number>")?;

                let real_zero = RealRepr::Finite(FiniteRealRepr::Integer {
                    spelling: "0".to_string(),
                });
                let kind = NumberLiteralKind {
                    radix,
                    exactness,
                    value: NumberValue::Rectangular {
                        real: real_zero,
                        imag: repr1,
                    },
                };
                let text = &source[literal_start..i_end];
                return Ok(Some((
                    i_end,
                    NumberLiteral {
                        text: text.to_string(),
                        kind,
                    },
                )));
            }
            '@' => {
                // Polar: `<real R> @ <real R>`
                let start2 = end1 + next_ch.len_utf8();
                if let Some((end2, repr2)) = lex_real_repr(source, start2, radix)? {
                    ensure_delimiter(source, end2, literal_start, "<number>")?;
                    let kind = NumberLiteralKind {
                        radix,
                        exactness,
                        value: NumberValue::Polar {
                            magnitude: repr1,
                            angle: repr2,
                        },
                    };
                    let text = &source[literal_start..end2];
                    return Ok(Some((
                        end2,
                        NumberLiteral {
                            text: text.to_string(),
                            kind,
                        },
                    )));
                } else {
                    let span = Span {
                        start: literal_start,
                        end: start2,
                    };
                    return Err(ParseError::lexical(
                        span,
                        "<number>",
                        "expected real after '@'",
                    ));
                }
            }
            '+' | '-' => {
                // Rectangular: `<real R> + ... i` or `<real R> - ... i`
                // The `+` or `-` starts the imaginary part.

                // 1. Try to parse the imaginary part as a real number (including the sign).
                // This covers `1+2i` (parsing `+2`) and `1+inf.0i` (parsing `+inf.0`).
                if let Some((end2, repr2)) = lex_real_repr(source, end1, radix)? {
                    if end2 >= len {
                        // We parsed the second number but hit EOF. We need an 'i' to complete
                        // the complex number, so this is incomplete.
                        return Err(ParseError::Incomplete);
                    }

                    let ch2 = source[end2..].chars().next().unwrap();
                    if ch2 == 'i' || ch2 == 'I' {
                        let i_end = end2 + ch2.len_utf8();
                        ensure_delimiter(source, i_end, literal_start, "<number>")?;

                        let kind = NumberLiteralKind {
                            radix,
                            exactness,
                            value: NumberValue::Rectangular {
                                real: repr1,
                                imag: repr2,
                            },
                        };
                        let text = &source[literal_start..i_end];
                        return Ok(Some((
                            i_end,
                            NumberLiteral {
                                text: text.to_string(),
                                kind,
                            },
                        )));
                    }

                    // If we parsed a number but it wasn't followed by 'i',
                    // e.g. `1+2` or `1+inf.0`, this is invalid complex syntax.
                    let span = Span {
                        start: literal_start,
                        end: end2,
                    };
                    return Err(ParseError::lexical(
                        span,
                        "<number>",
                        "missing 'i' in complex number",
                    ));
                }

                // 2. If that failed, check for `+i` / `-i` (implicit 1).
                let sign_len = next_ch.len_utf8();
                let after_sign = end1 + sign_len;

                if after_sign < len {
                    let after_sign_ch = source[after_sign..].chars().next().unwrap();
                    if after_sign_ch == 'i' || after_sign_ch == 'I' {
                        let i_end = after_sign + after_sign_ch.len_utf8();
                        ensure_delimiter(source, i_end, literal_start, "<number>")?;

                        let imag_spelling = if next_ch == '-' { "-1" } else { "1" };
                        let imag = RealRepr::Finite(FiniteRealRepr::Integer {
                            spelling: imag_spelling.to_string(),
                        });

                        let kind = NumberLiteralKind {
                            radix,
                            exactness,
                            value: NumberValue::Rectangular { real: repr1, imag },
                        };
                        let text = &source[literal_start..i_end];
                        return Ok(Some((
                            i_end,
                            NumberLiteral {
                                text: text.to_string(),
                                kind,
                            },
                        )));
                    }
                }

                // If neither worked, it's an error.
                let span = Span {
                    start: literal_start,
                    end: after_sign,
                };
                return Err(ParseError::lexical(
                    span,
                    "<number>",
                    "invalid imaginary part",
                ));
            }
            _ => {
                // Some other character. Error.
                let span = Span {
                    start: literal_start,
                    end: end1,
                };
                return Err(ParseError::lexical(
                    span,
                    "<number>",
                    "number literal not followed by a delimiter",
                ));
            }
        }
    }

    // If `lex_real_repr` failed, we might still have `+i` or `-i` (unit imaginary)
    // which `lex_real_repr` doesn't handle (it expects digits or infnan).
    let ch = source[body_start..].chars().next().unwrap();
    if ch == '+' || ch == '-' {
        let sign_len = ch.len_utf8();
        let after_sign = body_start + sign_len;
        if after_sign < len {
            let i_ch = source[after_sign..].chars().next().unwrap();
            if i_ch == 'i' || i_ch == 'I' {
                let i_end = after_sign + i_ch.len_utf8();
                ensure_delimiter(source, i_end, literal_start, "<number>")?;

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
                return Ok(Some((
                    i_end,
                    NumberLiteral {
                        text: text.to_string(),
                        kind,
                    },
                )));
            }
        }
    }

    Ok(None)
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

/// Lex a `<number>` with optional radix and exactness prefixes.
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
/// <radix 2>  ::= #b
/// <radix 8>  ::= #o
/// <radix 10> ::= <empty> | #d
/// <radix 16> ::= #x
/// <exactness> ::= <empty> | #i | #e
/// ```
///
/// This helper unifies the handling of decimal and non-decimal prefixes.
/// It parses any valid combination of `#<radix>` and `#<exactness>`,
/// defaults to decimal/unspecified if both are omitted, and then
/// delegates the body to `lex_complex_with_radix`.
///
/// When called from `lex`, this runs after `lex_boolean` and
/// `lex_character`, so an initial `#` that is not followed by a
/// radix or exactness marker causes this function to return `Ok(None)`
/// and allow other `#`-prefixed token classes to claim the input.
/// Once at least one `<prefix R>` component has been seen, any further
/// `#<unknown>` sequence is reported as a `<number>` lexical error in
/// accordance with the `<prefix R>` grammar.
fn lex_prefixed_number(
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

    // Consume one or two `#` prefixes.
    loop {
        if pos >= len || !source[pos..].starts_with('#') {
            break;
        }
        // Peek at the character after `#`.
        let hash_pos = pos;
        let after_hash = hash_pos + 1;
        if after_hash >= len {
            // `#` at end of input is incomplete, but we let the
            // outer loop or specific handlers deal with solitary `#`
            // if it's not a valid prefix.
            // However, if we already parsed a prefix, `#` at EOF is incomplete.
            if radix.is_some() || exactness.is_some() {
                return Err(ParseError::Incomplete);
            } else {
                // No prefixes yet, just `#` at EOF.
                return Ok(None);
            }
        }

        let ch = source[after_hash..].chars().next().unwrap();
        let lower = ch.to_ascii_lowercase();
        let prefix_len = 1 + ch.len_utf8(); // '#' + char

        match lower {
            'b' | 'o' | 'd' | 'x' => {
                if radix.is_some() {
                    let span = Span {
                        start,
                        end: pos + prefix_len,
                    };
                    return Err(ParseError::lexical(
                        span,
                        "<number>",
                        "duplicate radix prefix",
                    ));
                }
                radix = Some(match lower {
                    'b' => NumberRadix::Binary,
                    'o' => NumberRadix::Octal,
                    'd' => NumberRadix::Decimal,
                    'x' => NumberRadix::Hexadecimal,
                    _ => unreachable!(),
                });
                pos += prefix_len;
            }
            'e' | 'i' => {
                if exactness.is_some() {
                    let span = Span {
                        start,
                        end: pos + prefix_len,
                    };
                    return Err(ParseError::lexical(
                        span,
                        "<number>",
                        "duplicate exactness prefix",
                    ));
                }
                exactness = Some(match lower {
                    'e' => NumberExactness::Exact,
                    'i' => NumberExactness::Inexact,
                    _ => unreachable!(),
                });
                pos += prefix_len;
            }
            _ => {
                // Any other character after `#`.
                // If we have already seen a radix or exactness prefix,
                // then this `#<unknown>` sequence is invalid in a `<number>`
                // and we report a lexical error for `<prefix R>`.
                //
                // If no prefixes have been seen yet, this `#` is not part
                // of a `<number>` prefix at all; we return `Ok(None)` so
                // that other `#`-prefixed tokens (such as `<boolean>` or
                // `<character>`) can handle it.
                if radix.is_some() || exactness.is_some() {
                    let span = Span {
                        start,
                        end: pos + prefix_len,
                    };
                    return Err(ParseError::lexical(
                        span,
                        "<number>",
                        "invalid prefix in number",
                    ));
                } else {
                    // No prefixes seen yet. This `#` is not for us.
                    return Ok(None);
                }
            }
        }
    }

    // If we parsed no prefixes, this is not a prefixed number.
    if radix.is_none() && exactness.is_none() {
        return Ok(None);
    }

    let radix = radix.unwrap_or(NumberRadix::Decimal);
    let exactness = exactness.unwrap_or(NumberExactness::Unspecified);

    let body_start = pos;
    if body_start >= len {
        return Err(ParseError::Incomplete);
    }

    // Delegate the body to the generic complex helper.
    lex_complex_with_radix(source, start, body_start, radix, exactness)
}

/// Lex a `<string>` token starting at `start`.
///
/// Grammar reference (Formal syntax / `<string>`):
///
/// ```text
/// <string> ::= " <string element>* "
/// ```
///
/// This helper implements the R7RS escape and line-splicing rules,
/// including mnemonic escapes (`\n`, `\t`, etc.), `\x...;` hex escapes,
/// and backslash-newline splices, and reports lexical errors using
/// the `<string>` nonterminal.
fn lex_string(source: &str, start: usize) -> Result<Option<(usize, Token)>, ParseError> {
    let len = source.len();
    let mut pos = start;

    if pos >= len || !source[pos..].starts_with('"') {
        return Ok(None);
    }

    pos += 1; // skip opening quote
    let mut result = String::new();

    loop {
        if pos >= len {
            return Err(ParseError::Incomplete);
        }

        let ch = source[pos..].chars().next().unwrap();
        let ch_len = ch.len_utf8();

        match ch {
            '"' => {
                pos += ch_len;
                return Ok(Some((pos, Token::String(result))));
            }
            '\\' => {
                pos += ch_len;
                if pos >= len {
                    return Err(ParseError::Incomplete);
                }

                let next_ch = source[pos..].chars().next().unwrap();
                let next_len = next_ch.len_utf8();

                match next_ch {
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
                        pos += next_len;
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
                        let codepoint = u32::from_str_radix(hex_digits, 16).map_err(|_| {
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
                        pos += end_ch.len_utf8();
                    }
                    _ => {
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
                            idx += c.len_utf8();
                            if c == '\r' && idx < len {
                                let c2 = source[idx..].chars().next().unwrap();
                                if c2 == '\n' {
                                    idx += c2.len_utf8();
                                }
                            }
                            while idx < len {
                                let c2 = source[idx..].chars().next().unwrap();
                                if c2 == ' ' || c2 == '\t' {
                                    idx += c2.len_utf8();
                                } else {
                                    break;
                                }
                            }
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
                result.push(ch);
                pos += ch_len;
            }
        }
    }
}

/// Lex a `<character>` token starting at `start`.
///
/// Grammar reference (Formal syntax / `<character>`):
///
/// ```text
/// <character> ::= #\\ <any character>
///               | #\\ <character name>
///               | #\\x<hex scalar value>
/// ```
///
/// This helper accepts the R7RS named characters and `#\\x` hex
/// scalar values and reports lexical errors using the `<character>`
/// nonterminal.
fn lex_character(source: &str, start: usize) -> Result<Option<(usize, Token)>, ParseError> {
    let len = source.len();
    let mut pos = start;

    if pos >= len || !source[pos..].starts_with("#\\") {
        return Ok(None);
    }
    pos += 2; // skip "#\"

    if pos >= len {
        return Err(ParseError::Incomplete);
    }

    let c1 = source[pos..].chars().next().unwrap();
    let value_char;

    if c1 == 'x' || c1 == 'X' {
        let hex_start = pos + c1.len_utf8();
        let mut hex_pos = hex_start;
        while hex_pos < len {
            let c = source[hex_pos..].chars().next().unwrap();
            if c.is_ascii_hexdigit() {
                hex_pos += c.len_utf8();
            } else {
                break;
            }
        }

        if hex_pos > hex_start {
            let hex_digits = &source[hex_start..hex_pos];
            let codepoint = u32::from_str_radix(hex_digits, 16).map_err(|_| {
                let span = Span {
                    start,
                    end: hex_pos,
                };
                ParseError::lexical(
                    span,
                    "<character>",
                    "invalid hex digits in character literal",
                )
            })?;
            value_char = match char::from_u32(codepoint) {
                Some(c) => c,
                None => {
                    let span = Span {
                        start,
                        end: hex_pos,
                    };
                    return Err(ParseError::lexical(
                        span,
                        "<character>",
                        "hex scalar value is not a valid Unicode scalar value",
                    ));
                }
            };
            pos = hex_pos;
        } else {
            // No hex digits, treat as character 'x' or 'X'
            value_char = c1;
            pos += c1.len_utf8();
        }
    } else if c1.is_ascii_alphabetic() {
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
        value_char = c1;
        pos += c1.len_utf8();
    }

    ensure_delimiter(source, pos, start, "<character>")?;

    Ok(Some((pos, Token::Character(value_char))))
}

/// Lex a `<boolean>` token starting at `start`.
///
/// Grammar reference (Formal syntax / `<boolean>`):
///
/// ```text
/// <boolean> ::= #t | #f | #true | #false
/// ```
///
/// This helper is consulted before `<number>` prefix handling so that
/// `#t` / `#f` and their long forms are always recognized as booleans.
fn lex_boolean(source: &str, start: usize) -> Result<Option<(usize, Token)>, ParseError> {
    let len = source.len();
    let mut pos = start;

    if pos >= len || !source[pos..].starts_with('#') {
        return Ok(None);
    }

    let after_hash = pos + 1;
    if after_hash >= len {
        return Ok(None);
    }

    let c = source[after_hash..].chars().next().unwrap();
    let lower_c = c.to_ascii_lowercase();
    if lower_c != 't' && lower_c != 'f' {
        return Ok(None);
    }

    let word_start = after_hash;
    pos = word_start;
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
        ensure_delimiter(source, pos, start, "<boolean>")?;
        Ok(Some((pos, Token::Boolean(b))))
    } else {
        Ok(None)
    }
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
/// `lex_complex_decimal` for unprefixed decimal numbers and by
/// `lex_prefixed_number`/`lex_complex_with_radix` for prefixed
/// forms, so the overall `<number>` lexer is R7RS-conformant.
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
        Unimplemented,
        Incomplete,
        Lex(&'static str), // nonterminal
    }

    enum TokenMatcher {
        Bool(bool),
        Char(char),
        Str(&'static str),
        LParen,
        RParen,
        Quote,
        Backquote,
        Comma,
        CommaAt,
        Dot,
        VectorStart,
        ByteVectorStart,
        Num(&'static str, NumCheck),
    }

    enum NumCheck {
        Any, // Just check text
        Int(&'static str),
        Dec(&'static str),
        Rat(&'static str),
        RectInt(&'static str, &'static str), // real int, imag int
        RectRat(&'static str, &'static str), // real int, imag rat
        PolarInt(&'static str, &'static str), // mag int, ang int
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
                    for (i, (tok, matcher)) in tokens.iter().zip(expected_tokens.iter()).enumerate()
                    {
                        matcher.check(&tok.value, self.name, i);
                    }
                }
                Expected::Error(matcher) => {
                    let err =
                        result.expect_err(&format!("{}: expected error, got tokens", self.name));
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
                (ErrorMatcher::Unimplemented, ParseError::Unimplemented) => {}
                (ErrorMatcher::Incomplete, ParseError::Incomplete) => {}
                (
                    ErrorMatcher::Lex(nt),
                    ParseError::Lex { nonterminal, .. },
                ) => {
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
                Self::Unimplemented => write!(f, "Unimplemented"),
                Self::Incomplete => write!(f, "Incomplete"),
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
                (TokenMatcher::LParen, Token::LParen) => {}
                (TokenMatcher::RParen, Token::RParen) => {}
                (TokenMatcher::Quote, Token::Quote) => {}
                (TokenMatcher::Backquote, Token::Backquote) => {}
                (TokenMatcher::Comma, Token::Comma) => {}
                (TokenMatcher::CommaAt, Token::CommaAt) => {}
                (TokenMatcher::Dot, Token::Dot) => {}
                (TokenMatcher::VectorStart, Token::VectorStart) => {}
                (TokenMatcher::ByteVectorStart, Token::ByteVectorStart) => {}
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
                Self::LParen => write!(f, "LParen"),
                Self::RParen => write!(f, "RParen"),
                Self::Quote => write!(f, "Quote"),
                Self::Backquote => write!(f, "Backquote"),
                Self::Comma => write!(f, "Comma"),
                Self::CommaAt => write!(f, "CommaAt"),
                Self::Dot => write!(f, "Dot"),
                Self::VectorStart => write!(f, "VectorStart"),
                Self::ByteVectorStart => write!(f, "ByteVectorStart"),
                Self::Num(s, _) => f.debug_tuple("Num").field(s).finish(),
            }
        }
    }

    impl NumCheck {
        fn verify(&self, kind: &NumberLiteralKind, test_name: &str, index: usize) {
            match self {
                NumCheck::Any => {}
                NumCheck::Int(s) => {
                    if let NumberValue::Real(RealRepr::Finite(FiniteRealRepr::Integer {
                        spelling,
                    })) = &kind.value
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
                    if let NumberValue::Real(RealRepr::Finite(FiniteRealRepr::Decimal {
                        spelling,
                    })) = &kind.value
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
                    if let NumberValue::Real(RealRepr::Finite(FiniteRealRepr::Rational {
                        spelling,
                    })) = &kind.value
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
                name: "stub_unimplemented",
                input: "(foo)",
                expected: Expected::Error(ErrorMatcher::Unimplemented),
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
                input: "( ) ' ` , ,@ . #(",
                expected: Expected::Tokens(vec![
                    TokenMatcher::LParen,
                    TokenMatcher::RParen,
                    TokenMatcher::Quote,
                    TokenMatcher::Backquote,
                    TokenMatcher::Comma,
                    TokenMatcher::CommaAt,
                    TokenMatcher::Dot,
                    TokenMatcher::VectorStart,
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
                expected: Expected::Error(ErrorMatcher::Incomplete),
            },
            TestCase {
                name: "incomplete_decimal_2",
                input: "1.0e+",
                expected: Expected::Error(ErrorMatcher::Incomplete),
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
                expected: Expected::Error(ErrorMatcher::Incomplete),
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
                expected: Expected::Error(ErrorMatcher::Incomplete),
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
                expected: Expected::Error(ErrorMatcher::Incomplete),
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
                        NumCheck::Radix(
                            NumberRadix::Binary,
                            Box::new(NumCheck::RectInt("1", "+10")),
                        ),
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
                        NumCheck::Radix(
                            NumberRadix::Binary,
                            Box::new(NumCheck::PolarInt("1", "10")),
                        ),
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
                expected: Expected::Error(ErrorMatcher::Incomplete),
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
                name: "datum_comment",
                input: "#; (foo)",
                expected: Expected::Error(ErrorMatcher::Unimplemented),
            },
        ];

        for case in cases {
            case.run();
        }
    }
}
