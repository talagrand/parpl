use crate::{
    ast::{Span, Syntax},
    lex::{
        PResult, SpannedToken, Token, WinnowInput,
        utils::{
            InputExt, cut_lex_error_token, ensure_delimiter, lex_error, winnow_backtrack,
            winnow_incomplete, winnow_incomplete_token,
        },
    },
};
use winnow::{
    Parser,
    ascii::{hex_digit1, line_ending, space0},
    combinator::{alt, preceded},
    error::{ContextError, ErrMode, StrContext},
    stream::{Location, Stream},
    token::take_while,
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
fn lex_string_body<'i>(input: &mut WinnowInput<'i>) -> PResult<String> {
    let mut result = String::new();

    loop {
        // Fast path: consume literal text.
        // Strings cannot contain raw newlines, so we stop at them too.
        let chunk: &str = take_while(0.., |c| c != '"' && c != '\\' && c != '\n' && c != '\r')
            .parse_next(input)?;
        result.push_str(chunk);

        match input.peek_or_incomplete()? {
            '"' => break,
            '\\' => {
                let _ = input.next_token();
                if let Some(c) = lex_string_escape(input)? {
                    result.push(c);
                }
            }
            '\n' | '\r' => return lex_error("<string>"),
            _ => unreachable!("take_while stops at quote, backslash, or newline"),
        }
    }

    Ok(result)
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
pub(crate) fn lex_string<'i>(input: &mut WinnowInput<'i>) -> PResult<SpannedToken> {
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
pub(crate) fn lex_character<'i>(input: &mut WinnowInput<'i>) -> PResult<SpannedToken> {
    let start = input.current_token_start();

    // Expect leading "#\" prefix using lookahead so that we don't
    // consume input on mismatch (for example, `#t` / `#f` booleans).
    let mut probe = *input;
    match (probe.next_token(), probe.peek_token()) {
        (Some('#'), Some('\\')) => {
            // Commit the prefix on the real input.
            let _ = input.next_token();
            let _ = input.next_token();
        }
        // `#` at end-of-input followed by missing `\\` is an
        // incomplete `<character>` token.
        (Some('#'), None) => return winnow_incomplete_token(),
        _ => return winnow_backtrack(),
    }

    // At least one character must follow `#\`.
    let c1 = input.next_or_incomplete_token()?;

    let value_char = if c1.eq_ignore_ascii_case(&'x') {
        // Potential `#\x<hex scalar value>` form.
        let mut probe = *input;
        if let Ok(digits) = hex_digit1::<_, ContextError>.parse_next(&mut probe) {
            let Some(codepoint) = u32::from_str_radix(digits, 16)
                .ok()
                .and_then(char::from_u32)
            else {
                return lex_error("<character>");
            };
            *input = probe;
            codepoint
        } else {
            c1 // No hex digits: literal 'x' / 'X'
        }
    } else if c1.is_ascii_alphabetic() {
        // Possible named character like `space`, `newline`, etc.
        let mut name = String::new();
        name.push(c1);
        input.eat_while(&mut name, |c| c.is_ascii_alphabetic());

        if name.len() == c1.len_utf8() {
            c1 // Single alphabetic character like `#\a`
        } else {
            match named_character(&name) {
                Some(ch) => ch,
                None => return lex_error("<character>"),
            }
        }
    } else {
        c1 // Any other single character after `#\`
    };

    // Enforce delimiter after the `<character>` token.
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
