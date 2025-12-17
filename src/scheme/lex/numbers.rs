use crate::scheme::lex::{
    FiniteRealKind, FiniteRealMagnitude, NumberExactness, NumberLiteral, NumberLiteralKind,
    NumberRadix, NumberValue, PResult, RealMagnitude, RealRepr, Sign, WinnowInput,
    utils::{
        InputExt, cut_lex_error_token, ensure_delimiter, is_delimiter, lex_error, winnow_backtrack,
        winnow_incomplete_token,
    },
};
use winnow::{
    Parser,
    ascii::{Caseless, digit1},
    combinator::alt,
    error::{ContextError, ErrMode},
    stream::Stream,
    token::take_while,
};

/// Parse `+i` or `-i` (unit imaginary), returning the sign character on success.
///
/// Grammar reference (`syn.tex`, `<complex R>` production):
///
/// ```text
/// <complex R> ::= ...
///               | + i
///               | - i
///               | <real R> + i
///               | <real R> - i
///               | ...
/// ```
///
/// This helper handles the `+ i` / `- i` suffix in those productions, used:
/// 1. After parsing a real part: `<real R> + i` or `<real R> - i`
/// 2. Standalone: `+ i` or `- i` (with implicit zero real part)
///
/// On success, consumes the sign and `i` characters and returns the sign.
/// On failure (not `+i`/`-i`), returns `None` without consuming input.
fn try_parse_unit_imaginary<'i>(input: &mut WinnowInput<'i>) -> PResult<Option<char>> {
    let mut probe = *input;
    let Some(sign_ch) = probe.eat_if(|c| c == '+' || c == '-') else {
        return Ok(None);
    };
    if probe.eat_if(|c| c == 'i' || c == 'I').is_some() {
        // Must be followed by delimiter or EOF for this to be `+i` / `-i`.
        // If not, it could be an identifier like `+if`, so return None.
        if probe.peek_token().is_some_and(|ch| !is_delimiter(ch)) {
            return Ok(None);
        }
        *input = probe;
        Ok(Some(sign_ch))
    } else {
        Ok(None)
    }
}

/// Canonical `<suffix>` parser for decimal numbers.
///
/// Grammar reference (Formal syntax / `<number>`):
///
/// ```text
/// <suffix> ::= <empty>
///            | <exponent marker> <sign> <digit 10>+
///
/// <exponent marker> ::= e
///
/// <sign> ::= <empty> | + | -
/// ```
///
/// This helper consumes the suffix text (if any).
/// Returns `Ok(())` if no exponent marker is present (the `<empty>` case)
/// or if a complete exponent suffix was parsed successfully.
fn parse_exponent_suffix<'i>(input: &mut WinnowInput<'i>) -> PResult<()> {
    let Some(_) = input.eat_if(|c| c == 'e' || c == 'E') else {
        return Ok(());
    };

    let sign_or_digit = input.peek_or_incomplete_token()?;
    if sign_or_digit == '+' || sign_or_digit == '-' {
        let _ = input.next_token();
        let _ = input.peek_or_incomplete_token()?;
    }

    let _: &str = cut_lex_error_token(digit1, "<number>").parse_next(input)?;

    Ok(())
}

/// Canonical `<real R>` parser.
///
/// Grammar reference (Formal syntax / `<number>`):
///
/// ```text
/// <real R> ::= <sign> <ureal R>
///            | <infnan>
/// ```
///
/// This first tries `<infnan>` and, on backtrack,
/// falls back to `<sign> <ureal R>`.
fn lex_real_repr<'i>(input: &mut WinnowInput<'i>, radix: NumberRadix) -> PResult<RealRepr<'i>> {
    // Check for sign
    let sign_ch = input.eat_if(|c| c == '+' || c == '-');
    let sign = match sign_ch {
        Some('-') => Some(Sign::Negative),
        Some('+') => Some(Sign::Positive),
        None => None,
        _ => unreachable!("eat_if only returns '+' or '-'"),
    };

    // Check for inf/nan
    // Must start with i/I or n/N (after sign)
    // Note: if no explicit sign, can't be infnan (grammar: +inf.0 | -inf.0 ...)
    if sign.is_some() {
        if let Some(c) = input.peek_token() {
            match c {
                'i' | 'I' => {
                    let mut probe = *input;
                    let res: Result<&str, ErrMode<ContextError>> =
                        Caseless("inf.0").parse_next(&mut probe);
                    if res.is_ok() {
                        *input = probe;
                        return Ok(RealRepr {
                            sign,
                            magnitude: RealMagnitude::Infinity,
                        });
                    }
                }
                'n' | 'N' => {
                    let mut probe = *input;
                    let res: Result<&str, ErrMode<ContextError>> =
                        Caseless("nan.0").parse_next(&mut probe);
                    if res.is_ok() {
                        *input = probe;
                        return Ok(RealRepr {
                            sign,
                            magnitude: RealMagnitude::NaN,
                        });
                    }
                }
                _ => {}
            }
        }
    }

    // Not infnan. Try ureal (signless).
    match lex_ureal(input, radix) {
        Ok(finite) => Ok(RealRepr {
            sign,
            magnitude: RealMagnitude::Finite(finite),
        }),
        Err(e) => Err(e),
    }
}

/// Canonical `<complex R>` / `<real R>` parser.
///
/// This implements the R7RS number grammar for a fixed radix `R`,
/// including real, rectangular, polar, and pure-imaginary cases:
///
/// ```text
/// <number>   ::= <num 2> | <num 8>
///              | <num 10> | <num 16>
/// <num R>    ::= <prefix R> <complex R>
///
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
///
/// <real R> ::= <sign> <ureal R>
///            | <infnan>
/// ```
///
/// The `<ureal R>` production is implemented by `lex_ureal`, which
/// handles all radixes uniformly (with decimal-specific forms like
/// `.digits` and exponents enabled only for radix 10).
fn lex_complex_with_radix<'i>(
    input: &mut WinnowInput<'i>,
    radix: NumberRadix,
    exactness: NumberExactness,
) -> PResult<NumberLiteral<'i>> {
    let start_state = *input;

    // 1. Try to parse the first component as `<real R>`.
    match lex_real_repr(input, radix) {
        Ok(repr1) => {
            // End of input or delimiter after `<real R>`: it's a real number.
            let next_ch = match input.peek_token() {
                None => {
                    return Ok(NumberLiteralKind {
                        radix,
                        exactness,
                        value: NumberValue::Real(repr1),
                    }
                    .into_literal());
                }
                Some(ch) if is_delimiter(ch) => {
                    return Ok(NumberLiteralKind {
                        radix,
                        exactness,
                        value: NumberValue::Real(repr1),
                    }
                    .into_literal());
                }
                Some(ch) => ch,
            };

            match next_ch {
                'i' | 'I' => {
                    // Pure imaginary without an explicit real part:
                    // `+<ureal R> i`, `-<ureal R> i`, or `<infnan> i`.
                    //
                    // The R7RS grammar does *not* allow bare `2i` (no sign),
                    // so we only accept this branch when the parsed `<real R>`
                    // carried an explicit sign or is an `<infnan>`.
                    let allow_pure_imag = repr1.sign.is_some();

                    if !allow_pure_imag {
                        return lex_error("<number>");
                    }

                    let mut probe = *input;
                    let _ = probe.next_token(); // consume 'i' / 'I'
                    ensure_delimiter(&mut probe, "<number>")?;

                    *input = probe;
                    return Ok(NumberLiteralKind {
                        radix,
                        exactness,
                        value: NumberValue::Rectangular {
                            real: int_repr("0"),
                            imag: repr1,
                        },
                    }
                    .into_literal());
                }
                '@' => {
                    // Polar: `<real R> @ <real R>`.
                    let mut probe = *input;
                    let _ = probe.next_token(); // consume '@'
                    let repr2 =
                        cut_lex_error_token(|i: &mut _| lex_real_repr(i, radix), "<number>")
                            .parse_next(&mut probe)?;

                    ensure_delimiter(&mut probe, "<number>")?;
                    *input = probe;
                    return Ok(NumberLiteralKind {
                        radix,
                        exactness,
                        value: NumberValue::Polar {
                            magnitude: repr1,
                            angle: repr2,
                        },
                    }
                    .into_literal());
                }
                '+' | '-' => {
                    // Rectangular cases.
                    //
                    // In `syn.tex`, these appear as:
                    // - `<real R> + <ureal R> i` / `<real R> - <ureal R> i`
                    // - `<real R> + i` / `<real R> - i`
                    // - `<real R> <infnan> i` (e.g. `1+inf.0i`)
                    //
                    // Implementation detail: once we see a `+`/`-`, we attempt to parse the
                    // remainder using `lex_real_repr` starting at that sign. This yields a
                    // signed `RealRepr` which represents either:
                    // - `+/- <ureal R>` (the operator supplies the sign), or
                    // - `<infnan>` (whose sign is part of the token).
                    let mut probe = *input;
                    match lex_real_repr(&mut probe, radix) {
                        Ok(repr2) => {
                            cut_lex_error_token(alt(('i', 'I')), "<number>")
                                .parse_next(&mut probe)?;
                            ensure_delimiter(&mut probe, "<number>")?;
                            *input = probe;
                            return Ok(NumberLiteralKind {
                                radix,
                                exactness,
                                value: NumberValue::Rectangular {
                                    real: repr1,
                                    imag: repr2,
                                },
                            }
                            .into_literal());
                        }
                        Err(ErrMode::Backtrack(_)) => {
                            // Fall back to `+i` / `-i` (implicit 1).
                            probe = *input;
                            if let Some(sign_ch) = try_parse_unit_imaginary(&mut probe)? {
                                let imag = signed_int_repr(
                                    if sign_ch == '-' {
                                        Sign::Negative
                                    } else {
                                        Sign::Positive
                                    },
                                    "1",
                                );
                                *input = probe;
                                return Ok(NumberLiteralKind {
                                    radix,
                                    exactness,
                                    value: NumberValue::Rectangular { real: repr1, imag },
                                }
                                .into_literal());
                            }
                            return lex_error("<number>");
                        }
                        Err(e) => return Err(e),
                    }
                }
                _ => {
                    // Some other character after `<real R>`.
                    return lex_error("<number>");
                }
            }
        }
        Err(ErrMode::Backtrack(_)) => {
            // No `<real R>` here; reset and try `+i` / `-i` (unit imaginary).
            *input = start_state;
        }
        Err(e) => return Err(e),
    }

    // Handle `+i` / `-i` without an explicit real part.
    if let Some(sign_ch) = try_parse_unit_imaginary(input)? {
        let imag = signed_int_repr(
            if sign_ch == '-' {
                Sign::Negative
            } else {
                Sign::Positive
            },
            "1",
        );
        return Ok(NumberLiteralKind {
            radix,
            exactness,
            value: NumberValue::Rectangular {
                real: int_repr("0"),
                imag,
            },
        }
        .into_literal());
    }

    winnow_backtrack()
}

/// Canonical `<number>` parser for decimal radix (`<num 10>`).
///
/// This is a thin wrapper around `lex_complex_with_radix` with
/// `R = 10` and unspecified exactness.
pub(crate) fn lex_complex_decimal<'i>(input: &mut WinnowInput<'i>) -> PResult<NumberLiteral<'i>> {
    lex_complex_with_radix(input, 10, NumberExactness::Unspecified)
}

/// Canonical `<number>` parser for prefixed numbers.
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
///              | <exactness> <radix R>
///
/// <exactness> ::= <empty> | #i | #e
///
/// <radix 2> ::= #b
/// <radix 8> ::= #o
/// <radix 10> ::= <empty> | #d
/// <radix 16> ::= #x
/// ```
///
/// This helper parses one or more radix/exactness prefixes and then
/// delegates to `lex_complex_with_radix` for the `<complex R>` part.
pub(crate) fn lex_prefixed_number<'i>(input: &mut WinnowInput<'i>) -> PResult<NumberLiteral<'i>> {
    let mut probe = *input;

    let mut radix: Option<NumberRadix> = None;
    let mut exactness: Option<NumberExactness> = None;
    let mut saw_prefix = false;

    while probe.peek_token() == Some('#') {
        let _ = probe.next_token(); // consume '#'
        let after_hash = match probe.peek_token() {
            Some(c) => c,
            None => {
                if radix.is_some() || exactness.is_some() {
                    // Already saw a prefix like `#b`, then another `#` at EOF.
                    return winnow_incomplete_token();
                } else {
                    return winnow_backtrack();
                }
            }
        };

        saw_prefix = true;
        let lower = after_hash.to_ascii_lowercase();
        let _ = probe.next_token(); // consume the prefix character

        match lower {
            'b' | 'o' | 'd' | 'x' => {
                if radix.is_some() {
                    return lex_error("<number>");
                }
                radix = Some(match lower {
                    'b' => 2,
                    'o' => 8,
                    'd' => 10,
                    'x' => 16,
                    _ => return lex_error("<number>"),
                });
            }
            'e' | 'i' => {
                if exactness.is_some() {
                    return lex_error("<number>");
                }
                exactness = Some(match lower {
                    'e' => NumberExactness::Exact,
                    'i' => NumberExactness::Inexact,
                    _ => return lex_error("<number>"),
                });
            }
            _ => {
                if radix.is_some() || exactness.is_some() {
                    return lex_error("<number>");
                } else {
                    return winnow_backtrack();
                }
            }
        }
    }

    if !saw_prefix {
        return winnow_backtrack();
    }

    let radix_value = radix.unwrap_or(10);
    let exactness_value = exactness.unwrap_or(NumberExactness::Unspecified);

    let _ = probe.peek_or_incomplete_token()?;

    match lex_complex_with_radix(&mut probe, radix_value, exactness_value) {
        Ok(literal) => {
            *input = probe;
            Ok(literal)
        }
        Err(e) => Err(e),
    }
}

/// Canonical `<ureal R>` parser.
///
/// Grammar reference (Formal syntax / `<number>`):
///
/// ```text
/// <ureal R> ::= <uinteger R>
///              | <uinteger R> / <uinteger R>
///              | <decimal R>
///
/// <decimal 10> ::= <uinteger 10> <suffix>
///                 | . <digit 10>+ <suffix>
///                 | <digit 10>+ . <digit 10>* <suffix>
/// ```
///
/// Note: There are no `<decimal 2>`, `<decimal 8>`, or `<decimal 16>`
/// productions, so decimal points and exponents are only valid for
/// radix 10. This function handles all radixes uniformly, with the
/// decimal-specific forms enabled only when `radix == Decimal`.
fn lex_ureal<'i>(
    input: &mut WinnowInput<'i>,
    radix: NumberRadix,
) -> PResult<FiniteRealMagnitude<'i>> {
    let is_decimal = radix == 10;
    let first = input.peek_or_backtrack()?;

    let (kind, slice) = (move |input: &mut WinnowInput<'i>| -> PResult<FiniteRealKind> {
        // Decimal-only: `.digits+` form (e.g., `.5`, `.123e4`).
        if is_decimal && first == '.' {
            let _ = input.next_token();

            if input.peek_token().is_none() {
                return winnow_backtrack();
            }

            let digits = take_while(0.., |c: char| c.is_ascii_digit()).parse_next(input)?;
            let saw_digit = !digits.is_empty();
            if !saw_digit {
                return winnow_backtrack();
            }

            parse_exponent_suffix(input)?;
            return Ok(FiniteRealKind::Decimal);
        }

        // Common case: starts with digit(s).
        let digits = take_while(0.., |c| is_digit_for_radix(c, radix)).parse_next(input)?;
        let saw_digit = !digits.is_empty();
        if !saw_digit {
            return winnow_backtrack();
        }

        // Check what follows the integer part.
        match input.peek_token() {
            // Rational: `<uinteger R> / <uinteger R>` (all radixes).
            Some('/') => {
                let _ = input.next_token();

                let _ = cut_lex_error_token(
                    take_while(1.., |c| is_digit_for_radix(c, radix)),
                    "<number>",
                )
                .parse_next(input)?;
                Ok(FiniteRealKind::Rational)
            }

            // Decimal-only: `digits.digits*` with optional exponent.
            Some('.') if is_decimal => {
                let _ = input.next_token();
                let _ = take_while(0.., |c: char| c.is_ascii_digit()).parse_next(input)?;
                parse_exponent_suffix(input)?;
                Ok(FiniteRealKind::Decimal)
            }

            // Decimal-only: integer with exponent (e.g., `1e10`).
            Some('e' | 'E') if is_decimal => {
                parse_exponent_suffix(input)?;
                Ok(FiniteRealKind::Decimal)
            }

            // Plain integer.
            _ => Ok(FiniteRealKind::Integer),
        }
    })
    .with_taken()
    .parse_next(input)?;

    Ok(FiniteRealMagnitude {
        kind,
        spelling: slice,
    })
}

fn is_digit_for_radix(ch: char, radix: NumberRadix) -> bool {
    match radix {
        2 => matches!(ch, '0' | '1'),
        8 => matches!(ch, '0'..='7'),
        10 => ch.is_ascii_digit(),
        16 => ch.is_ascii_hexdigit(),
        _ => false,
    }
}

/// Create an integer `RealRepr` from a spelling string.
pub(crate) fn int_repr(spelling: &str) -> RealRepr<'_> {
    RealRepr {
        sign: None,
        magnitude: RealMagnitude::Finite(FiniteRealMagnitude {
            kind: FiniteRealKind::Integer,
            spelling,
        }),
    }
}

pub(crate) fn signed_int_repr(sign: Sign, digits: &str) -> RealRepr<'_> {
    RealRepr {
        sign: Some(sign),
        magnitude: RealMagnitude::Finite(FiniteRealMagnitude {
            kind: FiniteRealKind::Integer,
            spelling: digits,
        }),
    }
}
