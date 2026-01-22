use crate::{
    common::{Span, Syntax},
    scheme::lex::{
        FoldCaseMode, Input, PResult, SpannedToken, Token,
        utils::{
            InputExt, backtrack, cut_lex_error_token, ensure_delimiter, incomplete, is_delimiter,
            lex_error,
        },
    },
};
use std::borrow::Cow;
use unicase::UniCase;
use winnow::{
    Parser,
    ascii::{Caseless, hex_digit1},
    combinator::alt,
    error::{ContextError, ErrMode, StrContext},
    stream::{Location, Stream},
    token::take_while,
};

// --- Identifier character classification ---
//
// The R7RS spec allows Unicode characters with specific general categories
// in identifiers, but explicitly permits implementations to choose which
// additional Unicode characters they support. Rust's stdlib doesn't expose
// Unicode general categories directly, but we can approximate using the
// available methods.
//
// We therefore implement a conservative, but still conforming, choice of
// additional Unicode identifier characters. See design notes for
// details of what is and is not accepted.
//
// Allowed categories per R7RS:
//   Lu, Ll, Lt, Lm, Lo - Letters (covered by is_alphabetic())
//   Mn, Mc, Me - Marks (NOT in subsequent initial, Mc/Me not in initial)
//   Nd, Nl, No - Numbers (Nd not in initial)
//   Pd, Pc, Po, Sc, Sm, Sk, So - Punctuation/Symbols
//   Co - Private Use
//   U+200C, U+200D - Zero-width joiner/non-joiner
//
// Rust stdlib limitations - we can only detect:
//   - is_alphabetic() → Lu, Ll, Lt, Lm, Lo, Nl
//   - is_numeric() → Nd, Nl, No
//
// We CANNOT detect: Mn, Mc, Me, Pd, Pc, Po, Sc, Sm, Sk, So, Co.
//
// Consequence: We reject some valid R7RS identifiers (those using marks,
// symbols, or private-use characters) but never accept invalid ones.
//
// U+200C (ZWNJ) and U+200D (ZWJ) are handled explicitly below as
// <subsequent> characters, because both R7RS and Unicode UAX #31 call
// them out as necessary for correct spelling in some scripts.

/// Check if a character is an ASCII `<letter>`.
#[inline]
fn is_ascii_letter(ch: char) -> bool {
    ch.is_ascii_alphabetic()
}

/// Check if a character is an ASCII `<special initial>`.
///
/// ```text
/// <special initial> ::= ! | $ | % | & | * | / | : | < | =
///                     | > | ? | ^ | _ | ~
/// ```
#[inline]
fn is_special_initial(ch: char) -> bool {
    matches!(
        ch,
        '!' | '$' | '%' | '&' | '*' | '/' | ':' | '<' | '=' | '>' | '?' | '^' | '_' | '~'
    )
}

/// Check if a character is an ASCII `<initial>`.
///
/// ```text
/// <initial> ::= <letter> | <special initial>
/// ```
#[inline]
fn is_ascii_initial(ch: char) -> bool {
    is_ascii_letter(ch) || is_special_initial(ch)
}

/// Check if a character is a Unicode character valid as an identifier initial.
///
/// Per R7RS, Unicode characters with categories Lu, Ll, Lt, Lm, Lo, Mn, Nl, No,
/// Pd, Pc, Po, Sc, Sm, Sk, So, Co are allowed, but NOT Nd, Mc, Me as initial.
///
/// We use `is_alphabetic()` which covers Lu, Ll, Lt, Lm, Lo, Nl.
/// This is conservative - we reject valid chars we can't verify.
#[inline]
fn is_unicode_initial(ch: char) -> bool {
    // Must be non-ASCII (ASCII handled separately)
    !ch.is_ascii() && ch.is_alphabetic()
}

/// Check if a character is valid as `<initial>` (first char of identifier).
#[inline]
fn is_initial(ch: char) -> bool {
    is_ascii_initial(ch) || is_unicode_initial(ch)
}

/// Check if a character is an ASCII `<digit>`.
#[inline]
fn is_ascii_digit_char(ch: char) -> bool {
    ch.is_ascii_digit()
}

/// Check if a character is a `<special subsequent>`.
///
/// ```text
/// <special subsequent> ::= <explicit sign> | . | @
/// ```
#[inline]
fn is_special_subsequent(ch: char) -> bool {
    matches!(ch, '+' | '-' | '.' | '@')
}

/// Check if a character is valid as `<subsequent>`.
///
/// ```text
/// <subsequent> ::= <initial> | <digit> | <special subsequent>
/// ```
///
/// For Unicode, we allow is_alphanumeric() which includes Nd (digits), and
/// we also treat U+200C (ZWNJ) and U+200D (ZWJ) as valid subsequent
/// characters. R7RS and Unicode UAX #31 both permit these format controls
/// inside identifiers to support correct spelling in scripts such as
/// Persian and Hindi.
#[inline]
fn is_subsequent(ch: char) -> bool {
    is_initial(ch)
        || is_ascii_digit_char(ch)
        || is_special_subsequent(ch)
        || (!ch.is_ascii() && ch.is_alphanumeric())
        || matches!(ch, '\u{200C}' | '\u{200D}')
}

/// Check if a character is a `<sign subsequent>`.
///
/// ```text
/// <sign subsequent> ::= <initial> | <explicit sign> | @
/// ```
#[inline]
fn is_sign_subsequent(ch: char) -> bool {
    is_initial(ch) || matches!(ch, '+' | '-' | '@')
}

/// Check if a character is a `<dot subsequent>`.
///
/// ```text
/// <dot subsequent> ::= <sign subsequent> | .
/// ```
#[inline]
pub(crate) fn is_dot_subsequent(ch: char) -> bool {
    is_sign_subsequent(ch) || ch == '.'
}

/// Fast-path for consuming identifier subsequent characters.
///
/// This bypasses winnow's generic `take_while` machinery by directly
/// iterating over the input string. For pure-ASCII identifiers (the
/// common case), this avoids UTF-8 decoding overhead.
///
/// Returns the slice of subsequent characters consumed.
#[inline]
#[expect(clippy::indexing_slicing, clippy::string_slice)]
fn take_subsequent<'i>(input: &mut Input<'i>) -> &'i str {
    let slice = input.as_ref();
    let bytes = slice.as_bytes();

    let mut len = 0;
    while len < bytes.len() {
        let b = bytes[len];
        // Fast ASCII check - avoid char decoding overhead
        if b < 128 {
            if is_subsequent(b as char) {
                len += 1;
            } else {
                break;
            }
        } else {
            // Non-ASCII: decode UTF-8 and check
            // This is the slow path, but rare in practice
            let remaining = &slice[len..];
            if let Some(ch) = remaining.chars().next() {
                if is_subsequent(ch) {
                    len += ch.len_utf8();
                } else {
                    break;
                }
            } else {
                break;
            }
        }
    }

    // Advance input by len bytes
    let result = &slice[..len];
    // Use winnow's Stream trait to advance
    let _ = input.next_slice(len);

    result
}

/// Parse a hex escape inside a vertical-line delimited identifier.
/// The leading `\x` has been consumed; parse `<hex digits>;`.
fn lex_identifier_hex_escape<'i>(input: &mut Input<'i>) -> PResult<char> {
    let digits = cut_lex_error_token(hex_digit1, "<identifier>").parse_next(input)?;
    let _ = cut_lex_error_token(';', "<identifier>").parse_next(input)?;

    let codepoint = u32::from_str_radix(digits, 16).map_err(|_| {
        let mut ctx = ContextError::new();
        ctx.push(StrContext::Label("<identifier>"));
        ErrMode::Cut(ctx)
    })?;

    char::from_u32(codepoint).ok_or_else(|| {
        let mut ctx = ContextError::new();
        ctx.push(StrContext::Label("<identifier>"));
        ErrMode::Cut(ctx)
    })
}

/// Parse a `<symbol element>` inside a vertical-line delimited identifier.
///
/// ```text
/// <symbol element> ::= any character other than <vertical line> or \
///                    | <inline hex escape> | <mnemonic escape> | \|
/// ```
fn lex_symbol_element<'i>(input: &mut Input<'i>) -> PResult<Option<char>> {
    let ch = input.peek_or_incomplete()?;

    match ch {
        '|' => Ok(None), // End of symbol - don't consume
        '\\' => {
            let _ = input.next_token();
            let escape_ch = input.next_or_incomplete()?;
            match escape_ch {
                'x' | 'X' => Ok(Some(lex_identifier_hex_escape(input)?)),
                'a' => Ok(Some('\u{7}')),
                'b' => Ok(Some('\u{8}')),
                't' => Ok(Some('\t')),
                'n' => Ok(Some('\n')),
                'r' => Ok(Some('\r')),
                '|' => Ok(Some('|')),
                _ => lex_error("<identifier>"),
            }
        }
        _ => {
            let _ = input.next_token();
            Ok(Some(ch))
        }
    }
}

/// Parse a vertical-line delimited identifier: `|<symbol element>*|`.
/// The opening `|` has already been consumed.
fn lex_vertical_line_identifier<'i>(input: &mut Input<'i>) -> PResult<Cow<'i, str>> {
    // Fast path: consume characters that don't need escaping
    let simple_part = take_while(0.., |c| c != '|' && c != '\\').parse_next(input)?;

    match input.peek_token() {
        Some('|') => {
            // No escapes encountered, just the closing delimiter
            let _ = input.next_token();
            Ok(Cow::Borrowed(simple_part))
        }
        Some('\\') => {
            // Encountered an escape sequence; switch to owned string building
            let mut result = String::from(simple_part);

            while let Some(ch) = lex_symbol_element(input)? {
                result.push(ch);
            }

            // Consume the closing `|`
            if !input.eat('|') {
                return incomplete();
            }

            Ok(Cow::Owned(result))
        }
        _ => incomplete(),
    }
}

/// Parse the content of a `<peculiar identifier>` (without consuming it into a string).
/// This function just validates and advances the input.
///
/// ```text
/// <peculiar identifier> ::= <explicit sign>
///                         | <explicit sign> <sign subsequent> <subsequent>*
///                         | <explicit sign> . <dot subsequent> <subsequent>*
///                         | . <dot subsequent> <subsequent>*
/// ```
///
/// IMPORTANT: This must NOT match `+i`, `-i`, or `<infnan>` which are numbers.
/// We handle this by checking for these cases and backtracking.
fn lex_peculiar_identifier_content<'i>(input: &mut Input<'i>) -> PResult<()> {
    let start = *input;
    let first = input.peek_or_backtrack()?;

    match first {
        '+' | '-' => {
            let _ = input.next_token();

            // Check what follows
            match input.peek_token() {
                None => Ok(()), // Just `+` or `-` alone - valid peculiar identifier
                Some(ch) if is_delimiter(ch) => Ok(()), // `+` or `-` followed by delimiter - valid
                Some('.') => {
                    // `<explicit sign> . <dot subsequent> <subsequent>*`
                    let _ = input.next_token();

                    // Must have <dot subsequent>
                    let ds = input.peek_or_backtrack().map_err(|_| {
                        *input = start;
                        ErrMode::Backtrack(ContextError::new())
                    })?;

                    if !is_dot_subsequent(ds) {
                        *input = start;
                        return backtrack();
                    }
                    let _ = input.next_token();

                    // Consume remaining <subsequent>*
                    let _ = take_subsequent(input);
                    Ok(())
                }
                Some(ch) if is_sign_subsequent(ch) => {
                    // Check for `+i`, `-i` which are numbers, not identifiers
                    if (ch == 'i' || ch == 'I')
                        && input
                            .peek_token()
                            .map(|c| c == 'i' || c == 'I')
                            .unwrap_or(false)
                    {
                        // Peek ahead after the 'i'
                        let mut probe = *input;
                        let _ = probe.next_token(); // consume 'i'
                        match probe.peek_token() {
                            None => {
                                // This is `+i` or `-i` - a number, not identifier
                                *input = start;
                                return backtrack();
                            }
                            Some(c) if is_delimiter(c) => {
                                // This is `+i` or `-i` - a number, not identifier
                                *input = start;
                                return backtrack();
                            }
                            _ => {
                                // Something follows - could be `+if` etc., valid identifier
                            }
                        }
                    }

                    // Check for infnan: +inf.0, -inf.0, +nan.0, -nan.0
                    if ch == 'i' || ch == 'I' || ch == 'n' || ch == 'N' {
                        let mut probe = *input;
                        let res: Result<&str, ErrMode<ContextError>> =
                            alt((Caseless("inf.0"), Caseless("nan.0"))).parse_next(&mut probe);
                        if res.is_ok() {
                            // Check if followed by delimiter
                            match probe.peek_token() {
                                None => {
                                    // This is infnan - a number
                                    *input = start;
                                    return backtrack();
                                }
                                Some(c) if is_delimiter(c) => {
                                    // This is infnan - a number
                                    *input = start;
                                    return backtrack();
                                }
                                _ => {
                                    // Something follows - continue as identifier
                                }
                            }
                        }
                    }

                    // `<explicit sign> <sign subsequent> <subsequent>*`
                    let _ = input.next_token();

                    // Consume remaining <subsequent>*
                    let _ = take_subsequent(input);
                    Ok(())
                }
                _ => {
                    // Invalid character after sign
                    *input = start;
                    backtrack()
                }
            }
        }
        '.' => {
            // `. <dot subsequent> <subsequent>*`
            let _ = input.next_token();

            // Must have <dot subsequent>
            let ds = input.peek_or_backtrack().map_err(|_| {
                *input = start;
                ErrMode::Backtrack(ContextError::new())
            })?;

            if !is_dot_subsequent(ds) {
                *input = start;
                return backtrack();
            }

            // Check for `...` which is a valid peculiar identifier
            // but also check it's not just `.` followed by a number
            if ds == '.' {
                // Continue - this could be `...` or `..<subsequent>*`
            }

            let _ = input.next_token();

            // Consume remaining <subsequent>*
            let _ = take_subsequent(input);
            Ok(())
        }
        _ => backtrack(),
    }
}

/// Canonical `<identifier>` parser.
///
/// Grammar reference:
///
/// ```text
/// <identifier> ::= <initial> <subsequent>*
///                 | <vertical line> <symbol element>* <vertical line>
///                 | <peculiar identifier>
/// ```
///
/// # Performance Note
///
/// This parser uses a manual `take_subsequent` loop that bypasses winnow's
/// generic `take_while` machinery. This provides ~12% faster parsing than
/// the naive `take_while(0.., is_subsequent)` approach for identifier-heavy
/// code, because it avoids the overhead of winnow's generic iterator.
pub fn lex_identifier<'i>(
    input: &mut Input<'i>,
    fold_case_mode: FoldCaseMode,
) -> PResult<SpannedToken<'i>> {
    let start = input.current_token_start();

    let first = input.peek_or_backtrack()?;

    let name: Cow<'i, str> = match first {
        // Vertical-line delimited identifier
        '|' => {
            let _ = input.next_token();
            lex_vertical_line_identifier(input)?
        }
        // Regular identifier: <initial> <subsequent>*
        ch if is_initial(ch) => {
            let slice = take_subsequent(input);
            Cow::Borrowed(slice)
        }
        // Peculiar identifier (starts with +, -, or .)
        '+' | '-' | '.' => {
            let slice = lex_peculiar_identifier_content.take().parse_next(input)?;
            Cow::Borrowed(slice)
        }
        _ => return backtrack(),
    };

    // Identifiers not starting with `|` must be followed by delimiter or EOF
    if first != '|' {
        ensure_delimiter(input, "<identifier>")?;
    }

    let final_name: Cow<'i, str> = if matches!(fold_case_mode, FoldCaseMode::Off) {
        name
    } else {
        // Apply full Unicode case folding via `unicase`. This follows
        // Unicode CaseFolding.txt (C/F mappings) and matches the
        // intent of R7RS `string-foldcase` for identifiers.
        let folded: String = UniCase::new(name.as_ref()).to_folded_case();
        Cow::Owned(folded)
    };

    let end = input.current_token_start();
    Ok(Syntax::new(
        Span { start, end },
        Token::Identifier(final_name),
    ))
}
