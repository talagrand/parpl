use winnow::{
    Parser,
    ascii::Caseless,
    error::{ContextError, ErrMode},
    stream::{Location, Stream},
};

use super::{
    PResult, SpannedToken, Token, WinnowInput,
    utils::{InputExt, ensure_delimiter, winnow_backtrack},
};
use crate::ast::{Span, Syntax};

/// Lex a `<boolean>` token using a `WinnowInput`.
///
/// Grammar reference (Formal syntax / `<boolean>`):
///
/// ```text
/// <boolean> ::= #t | #f | #true | #false
/// ```
///
/// This helper is consulted before `<number>` prefix handling so that
/// `#t` / `#f` and their long forms are always recognized as booleans.
pub fn lex_boolean<'i>(input: &mut WinnowInput<'i>) -> PResult<SpannedToken> {
    let start = input.current_token_start();
    let mut probe = *input;

    if !probe.eat('#') {
        return winnow_backtrack();
    }

    let value = match probe.next_token() {
        Some('t') | Some('T') => {
            // Check for optional "rue"
            let _: Result<&str, ErrMode<ContextError>> = Caseless("rue").parse_next(&mut probe);
            true
        }
        Some('f') | Some('F') => {
            // Check for optional "alse"
            let _: Result<&str, ErrMode<ContextError>> = Caseless("alse").parse_next(&mut probe);
            false
        }
        _ => return winnow_backtrack(),
    };

    // Enforce delimiter: the next character, if any, must be a
    // `<delimiter>`; otherwise this is a `<boolean>` lexical error.
    ensure_delimiter(&mut probe, "<boolean>")?;

    // Commit the successfully parsed boolean by updating the real
    // input cursor to the probe's position.
    *input = probe;
    let end = input.current_token_start();
    Ok(Syntax::new(Span { start, end }, Token::Boolean(value)))
}
