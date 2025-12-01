use crate::{
    ast::{Span, Syntax},
    lex::{
        PResult, SpannedToken, Token, WinnowInput,
        identifiers::is_dot_subsequent,
        utils::{InputExt, winnow_backtrack},
    },
};
use winnow::stream::{Location, Stream};

/// Canonical punctuation parser using `winnow`.
///
/// Grammar reference (spec/syn.md / `<token>`):
///
/// ```text
/// ( | ) | #( | #u8( | ' | ` | , | ,@ | .
/// ```
pub fn lex_punctuation<'i>(input: &mut WinnowInput<'i>) -> PResult<SpannedToken> {
    let start = input.current_token_start();

    let ch = input.peek_or_backtrack()?;

    let token = match ch {
        '(' => {
            let _ = input.next_token();
            Token::LParen
        }
        ')' => {
            let _ = input.next_token();
            Token::RParen
        }
        '\'' => {
            let _ = input.next_token();
            Token::Quote
        }
        '`' => {
            let _ = input.next_token();
            Token::Backquote
        }
        ',' => {
            let _ = input.next_token();
            if input.eat('@') {
                Token::CommaAt
            } else {
                Token::Comma
            }
        }
        '#' => {
            let _ = input.next_token();
            match input.peek_token() {
                Some('(') => {
                    let _ = input.next_token();
                    Token::VectorStart
                }
                Some('u' | 'U') => {
                    let _ = input.next_token();
                    if input.eat('8') && input.eat('(') {
                        Token::ByteVectorStart
                    } else {
                        return winnow_backtrack();
                    }
                }
                Some(';') => {
                    // Datum comment prefix - emit token for parser to handle
                    let _ = input.next_token();
                    Token::DatumComment
                }
                Some(c) if c.is_ascii_digit() => {
                    // Label definition `#n=` or reference `#n#`
                    let mut probe = *input;
                    let mut text = String::new();
                    if probe.eat_while(&mut text, |c| c.is_ascii_digit()) > 0 {
                        match probe.peek_token() {
                            Some('=') => {
                                let _ = probe.next_token();
                                *input = probe;
                                let n = text.parse::<u64>().unwrap(); // Safe because we only ate digits
                                Token::LabelDef(n)
                            }
                            Some('#') => {
                                let _ = probe.next_token();
                                *input = probe;
                                let n = text.parse::<u64>().unwrap();
                                Token::LabelRef(n)
                            }
                            _ => return winnow_backtrack(),
                        }
                    } else {
                        return winnow_backtrack();
                    }
                }
                _ => {
                    // Let other `#`-prefixed tokens handle this.
                    return winnow_backtrack();
                }
            }
        }
        '.' => {
            // If `.` is followed by a digit, treat this as the
            // start of a decimal number and let the numeric
            // lexers claim it instead of producing a `.` token.
            // If `.` is followed by another `.`, it could be `...` (identifier).
            let mut probe = *input;
            let _ = probe.next_token(); // consume '.'
            match probe.peek_token() {
                Some(c) if c.is_ascii_digit() => {
                    // Decimal number like `.5`
                    return winnow_backtrack();
                }
                Some('.') => {
                    // Could be `...` - let identifier parser handle it
                    return winnow_backtrack();
                }
                Some(c) if is_dot_subsequent(c) => {
                    // Could be `.foo` - let identifier parser handle it
                    return winnow_backtrack();
                }
                _ => {
                    // Just a single `.` - this is Token::Dot
                }
            }

            let _ = input.next_token();
            Token::Dot
        }
        _ => return winnow_backtrack(),
    };

    let end = input.current_token_start();
    Ok(Syntax::new(Span { start, end }, token))
}
