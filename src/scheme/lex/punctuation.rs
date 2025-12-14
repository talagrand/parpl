use crate::scheme::{
    ast::{Span, Syntax},
    lex::{
        PResult, SpannedToken, Token, WinnowInput,
        identifiers::is_dot_subsequent,
        utils::{InputExt, lex_error, winnow_backtrack, winnow_incomplete_token},
    },
};
use winnow::{
    Parser,
    ascii::digit1,
    error::ContextError,
    stream::{Location, Stream},
};

/// Canonical punctuation parser.
///
/// Grammar reference (`syn.tex` / `<token>`):
///
/// ```text
/// ( | ) | #( | #u8( | ' | ` | , | ,@ | .
/// ```
pub fn lex_punctuation<'i>(input: &mut WinnowInput<'i>) -> PResult<SpannedToken<'i>> {
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
            // Use a probe so we only commit to `input` once we've
            // identified a concrete punctuation token. This allows
            // other `#`-prefixed constructs (such as `#!` directives)
            // to backtrack cleanly to other lexers.
            let mut probe = *input;
            let _ = probe.next_token(); // consume '#'
            match probe.peek_token() {
                Some('(') => {
                    // Vector start: commit "#(".
                    let _ = input.next_token();
                    let _ = input.next_token();
                    Token::VectorStart
                }
                Some('u' | 'U') => {
                    // Possible bytevector start: "#u8(".
                    let _ = input.next_token(); // '#'
                    let _ = input.next_token(); // 'u' or 'U'
                    if input.eat('8') && input.eat('(') {
                        Token::ByteVectorStart
                    } else {
                        return winnow_backtrack();
                    }
                }
                Some(';') => {
                    // Datum comment prefix - emit token for parser to handle.
                    let _ = input.next_token(); // '#'
                    let _ = input.next_token(); // ';'
                    Token::DatumComment
                }
                Some(c) if c.is_ascii_digit() => {
                    // Label definition `#n=` or reference `#n#`.
                    let mut label_probe = probe;
                    if let Ok(digits) = digit1::<_, ContextError>.parse_next(&mut label_probe) {
                        match label_probe.peek_token() {
                            Some('=') => {
                                let _ = label_probe.next_token();
                                *input = label_probe;
                                let n = digits.parse::<u64>().unwrap(); // Safe because we only ate digits
                                Token::LabelDef(n)
                            }
                            Some('#') => {
                                let _ = label_probe.next_token();
                                *input = label_probe;
                                let n = digits.parse::<u64>().unwrap();
                                Token::LabelRef(n)
                            }
                            None => return winnow_incomplete_token(),
                            _ => return lex_error("label definition or reference"),
                        }
                    } else {
                        return winnow_backtrack();
                    }
                }
                Some('!') => {
                    // `#!` starts a directive; let the directive lexer handle it.
                    return winnow_backtrack();
                }
                None => return winnow_incomplete_token(),
                _ => {
                    // No other valid tokens start with `#`.
                    return lex_error("punctuation");
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
