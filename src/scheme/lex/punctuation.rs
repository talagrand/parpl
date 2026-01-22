use crate::common::{Span, Syntax};
use crate::scheme::lex::{
    Input, PResult, SpannedToken, Token,
    identifiers::is_dot_subsequent,
    utils::{InputExt, backtrack, incomplete_token, lex_error},
};
use winnow::{
    Parser,
    ascii::digit1,
    error::ContextError,
    stream::{Location, Stream},
};

/// Parser for `#`-prefixed punctuation tokens.
///
/// This handles:
/// - `#(` - vector start
/// - `#u8(` - bytevector start
/// - `#;` - datum comment
/// - `#n=` - label definition
/// - `#n#` - label reference
///
/// Simple punctuation (`(`, `)`, `'`, `` ` ``, `,`, `,@`) is handled
/// directly by the first-character dispatcher for efficiency.
pub fn lex_hash_punctuation<'i>(input: &mut Input<'i>) -> PResult<SpannedToken<'i>> {
    let start = input.current_token_start();

    // Use a probe so we only commit to `input` once we've identified
    // a concrete punctuation token. This allows other `#`-prefixed
    // constructs (such as `#!` directives) to backtrack cleanly.
    let mut probe = *input;

    if !probe.eat('#') {
        return backtrack();
    }

    let token = match probe.peek_token() {
        Some('(') => {
            // Vector start: "#("
            let _ = probe.next_token();
            Token::VectorStart
        }
        Some('u' | 'U') => {
            // Possible bytevector start: "#u8("
            let _ = probe.next_token(); // 'u' or 'U'
            if probe.eat('8') && probe.eat('(') {
                Token::ByteVectorStart
            } else {
                return backtrack();
            }
        }
        Some(';') => {
            // Datum comment prefix - emit token for parser to handle.
            let _ = probe.next_token();
            Token::DatumComment
        }
        Some(c) if c.is_ascii_digit() => {
            // Label definition `#n=` or reference `#n#`.
            if let Ok(digits) = digit1::<_, ContextError>.parse_next(&mut probe) {
                match probe.peek_token() {
                    Some('=') => {
                        let _ = probe.next_token();
                        let n = match digits.parse::<u64>() {
                            Ok(n) => n,
                            Err(_) => return lex_error("label definition or reference"),
                        };
                        Token::LabelDef(n)
                    }
                    Some('#') => {
                        let _ = probe.next_token();
                        let n = match digits.parse::<u64>() {
                            Ok(n) => n,
                            Err(_) => return lex_error("label definition or reference"),
                        };
                        Token::LabelRef(n)
                    }
                    None => return incomplete_token(),
                    _ => return lex_error("label definition or reference"),
                }
            } else {
                return backtrack();
            }
        }
        Some('!') => {
            // `#!` starts a directive; let the directive lexer handle it.
            return backtrack();
        }
        None => return incomplete_token(),
        _ => {
            // No other valid punctuation tokens start with `#`.
            // Don't error here - let other parsers try (e.g., booleans, numbers).
            return backtrack();
        }
    };

    // Commit the probe's progress to the real input.
    *input = probe;
    let end = input.current_token_start();
    Ok(Syntax::new(Span { start, end }, token))
}

/// Parser for lone `.` (dot) token.
///
/// This is called as a fallback after the identifier parser fails,
/// since `.` can start identifiers like `...` or `.foo`.
///
/// Returns `Token::Dot` only if `.` is followed by a delimiter or EOF.
pub fn lex_dot<'i>(input: &mut Input<'i>) -> PResult<SpannedToken<'i>> {
    let start = input.current_token_start();

    if !input.eat('.') {
        return backtrack();
    }

    // Check what follows - if it could continue an identifier or number, backtrack
    match input.peek_token() {
        Some(c) if c.is_ascii_digit() => {
            // Decimal number like `.5` - should have been caught by number parser
            return backtrack();
        }
        Some('.') => {
            // Could be `...` - should have been caught by identifier parser
            return backtrack();
        }
        Some(c) if is_dot_subsequent(c) => {
            // Could be `.foo` - should have been caught by identifier parser
            return backtrack();
        }
        _ => {
            // Lone `.` followed by delimiter or EOF
        }
    }

    let end = input.current_token_start();
    Ok(Syntax::new(Span { start, end }, Token::Dot))
}

/// Fast-path helper for simple single-character punctuation tokens.
///
/// This is used by the first-character dispatch in the lexer to avoid
/// the overhead of the full `lex_punctuation` parser for common tokens.
#[inline]
pub(crate) fn simple_punct<'i>(
    input: &mut Input<'i>,
    start: usize,
    token: Token<'i>,
) -> SpannedToken<'i> {
    let _ = input.next_token();
    let end = input.current_token_start();
    Syntax::new(Span { start, end }, token)
}
