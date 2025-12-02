use crate::{
    ast::{Span, Syntax},
    lex::{
        PResult, SpannedToken, Token, WinnowInput,
        utils::{
            InputExt, cut_lex_error_token, ensure_delimiter, lex_error, winnow_backtrack,
            winnow_incomplete,
        },
    },
};
use winnow::{
    Parser,
    ascii::{hex_digit1, line_ending, space0},
    combinator::{alt, cut_err, preceded},
    error::{ContextError, ErrMode, StrContext},
    stream::{Location, Stream},
    token::{literal, take_while},
};

/// Look up a named character (case-sensitive).
///
/// R7RS §7.1.1: "Case is significant in ... <character name>"
fn named_character(name: &str) -> Option<char> {
    Some(match name {
        "alarm" => '\u{7}',
        "backspace" => '\u{8}',
        "delete" => '\u{7F}',
        "escape" => '\u{1B}',
        "newline" => '\n',
        "null" => '\0',
        "return" => '\r',
        "space" => ' ',
        "tab" => '\t',
        _ => return None,
    })
}

/// Canonical `<string element>` parser used by `<string>`.
///
/// Grammar reference (Formal syntax / `<string>`):
///
/// ```text
/// <string> ::= " <string element>* "
///
/// <string element> ::= any character other than " or \
///                     | <mnemonic escape> | \" | \\
///                     | \ <intraline whitespace>* <line ending>
///                       <intraline whitespace>*
///                     | <inline hex escape>
/// ```
///
/// This function assumes the opening `"` has already been consumed
/// and stops just before the closing `"`.
fn lex_string_body<'i>(input: &mut WinnowInput<'i>) -> PResult<std::borrow::Cow<'i, str>> {
    let is_not_string_terminator = |c| c != '"' && c != '\\' && c != '\n' && c != '\r';

    // Fast path: consume literal text.
    // Strings cannot contain raw newlines, so we stop at them too.
    let simple_part = take_while(0.., is_not_string_terminator).parse_next(input)?;

    match input.peek_or_incomplete()? {
        '"' => {
            // No escapes encountered, just the closing quote
            Ok(std::borrow::Cow::Borrowed(simple_part))
        }
        '\\' => {
            // Encountered an escape sequence; switch to owned string building
            let mut result = String::from(simple_part);

            loop {
                // We are at a backslash or just finished a chunk.
                // If we are at a backslash, handle escape.
                if input.peek_token() == Some('\\') {
                    let _ = input.next_token();
                    if let Some(c) = lex_string_escape(input)? {
                        result.push(c);
                    }
                } else {
                    // Consume next chunk of literal text
                    let chunk: &str =
                        take_while(0.., is_not_string_terminator).parse_next(input)?;
                    result.push_str(chunk);
                }

                match input.peek_or_incomplete()? {
                    '"' => break,
                    '\\' => continue, // Loop back to handle escape
                    '\n' | '\r' => return lex_error("<string>"),
                    _ => continue, // Continue to consume next chunk
                }
            }
            Ok(std::borrow::Cow::Owned(result))
        }
        '\n' | '\r' => lex_error("<string>"),
        _ => unreachable!("take_while stops at quote, backslash, or newline"),
    }
}

/// Parse the body of a hex escape sequence: `<hex digits>;`.
/// The leading `x` has already been consumed.
fn lex_hex_escape<'i>(input: &mut WinnowInput<'i>) -> PResult<char> {
    let digits = cut_lex_error_token(hex_digit1, "<string>").parse_next(input)?;
    let _ = cut_lex_error_token(';', "<string>").parse_next(input)?;

    let codepoint = u32::from_str_radix(digits, 16).map_err(|_| {
        // This should be rare given hex_digit1, but handles overflow
        let mut ctx = ContextError::new();
        ctx.push(StrContext::Label("<string>"));
        ErrMode::Cut(ctx)
    })?;

    char::from_u32(codepoint).ok_or_else(|| {
        // Invalid unicode scalar value
        let mut ctx = ContextError::new();
        ctx.push(StrContext::Label("<string>"));
        ErrMode::Cut(ctx)
    })
}

/// Parse a single string escape sequence (after the backslash).
fn lex_string_escape<'i>(input: &mut WinnowInput<'i>) -> PResult<Option<char>> {
    alt((
        // Hex escape: \x...;
        preceded(alt(('x', 'X')), lex_hex_escape).map(Some),
        // Line splice: \ ... \n ... (contributes nothing to string)
        lex_line_splice.map(|_| None),
        // Simple escapes
        alt((
            'a'.value(Some('\u{7}')),
            'b'.value(Some('\u{8}')),
            't'.value(Some('\t')),
            'n'.value(Some('\n')),
            'r'.value(Some('\r')),
            '"'.value(Some('"')),
            '\\'.value(Some('\\')),
        )),
    ))
    .parse_next(input)
}

/// Canonical `<string>` parser.
///
/// Grammar reference (Formal syntax / `<string>`):
///
/// ```text
/// <string> ::= " <string element>* "
/// ```
///
/// The `<string element>` production itself is implemented by
/// `lex_string_body`.
pub(crate) fn lex_string<'i>(input: &mut WinnowInput<'i>) -> PResult<SpannedToken<'i>> {
    let start = input.current_token_start();

    if !input.eat('"') {
        return winnow_backtrack();
    }

    let value = lex_string_body(input)?;

    match input.next_token() {
        Some('"') => {}
        None => return winnow_incomplete(),
        _ => return lex_error("<string>"),
    }

    let end = input.current_token_start();
    Ok(Syntax::new(Span { start, end }, Token::String(value)))
}

/// Canonical `<character>` parser.
///
/// Grammar reference (Formal syntax / `<character>`):
///
/// ```text
/// <character> ::= #\ <any character>
///               | #\ <character name>
///               | #\x<hex scalar value>
///
/// <character name> ::= alarm | backspace | delete
///                    | escape | newline | null | return | space | tab
/// ```
///
/// This helper accepts the R7RS named characters and `#\x` hex
/// scalar values and reports lexical errors using the `<character>`
/// nonterminal.
pub(crate) fn lex_character<'i>(input: &mut WinnowInput<'i>) -> PResult<SpannedToken<'i>> {
    let start = input.current_token_start();

    // 1. Match prefix "#\"
    literal("#\\").parse_next(input)?;

    // 2. Match body
    let value_char = cut_err(alt((
        // Hex scalar value: x<hex>
        // Note: We must NOT cut here, because `#\x` is a valid literal char 'x'.
        preceded(alt(('x', 'X')), hex_digit1).verify_map(|digits| {
            u32::from_str_radix(digits, 16)
                .ok()
                .and_then(char::from_u32)
        }),
        // Named character
        take_while(1.., |c: char| c.is_ascii_alphabetic()).verify_map(named_character),
        // Any character
        |i: &mut WinnowInput<'i>| i.next_or_incomplete_token(),
    )))
    .parse_next(input)?;

    // 3. Enforce delimiter after the `<character>` token.
    ensure_delimiter(input, "<character>")?;

    let end = input.current_token_start();
    Ok(Syntax::new(
        Span { start, end },
        Token::Character(value_char),
    ))
}

/// Parse a line splice: `\ <ws> <line ending> <ws>`.
pub(crate) fn lex_line_splice<'i>(input: &mut WinnowInput<'i>) -> PResult<()> {
    let _: &str = space0.parse_next(input)?;
    let _: &str = line_ending.parse_next(input)?;
    let _: &str = space0.parse_next(input)?;
    Ok(())
}
