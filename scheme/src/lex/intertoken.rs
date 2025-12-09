use crate::lex::{
    FoldCaseMode, PResult, WinnowInput,
    utils::{InputExt, cut_lex_error_token, ensure_delimiter, winnow_backtrack},
};
use winnow::{
    Parser,
    ascii::{Caseless, line_ending, till_line_ending},
    combinator::{alt, opt},
    stream::Stream,
    token::take_while,
};

/// Canonical `<intertoken space>` parser.
///
/// This parser consumes zero or more `<atmosphere>` elements:
/// whitespace, line comments, and nested comments.
///
/// It returns `true` if at least one comment (line or nested) was
/// encountered while consuming intertoken space, and `false` otherwise.
///
/// Uses a manual loop for efficiency with `take_while` for the fast paths.
pub fn lex_intertoken<'i>(input: &mut WinnowInput<'i>) -> PResult<bool> {
    let mut saw_comment = false;

    loop {
        // Fast path: consume runs of whitespace at once
        let _: &str =
            take_while(0.., |c| matches!(c, ' ' | '\t' | '\n' | '\r')).parse_next(input)?;

        let Some(ch) = input.peek_token() else {
            return Ok(saw_comment);
        };

        match ch {
            // Line comment: `; ... <line ending or EOF>`
            ';' => {
                let _ = input.next_token();
                let _: &str = till_line_ending.parse_next(input)?;
                // Consume the line ending if present
                let _: Option<&str> = opt(line_ending).parse_next(input)?;
                saw_comment = true;
            }
            // Possible nested comment starting with '#'.
            '#' => {
                // Peek at the next character to decide.
                let mut probe = *input;
                let _ = probe.next_token(); // consume '#'

                match probe.peek_token() {
                    // Nested comment `#| ... |#`.
                    Some('|') => {
                        // Commit both characters and parse the rest
                        let _ = input.next_token();
                        let _ = input.next_token();
                        lex_nested_comment_body(input)?;
                        saw_comment = true;
                    }
                    _ => {
                        // Not a nested comment or directive; this
                        // begins a real token.
                        return Ok(saw_comment);
                    }
                }
            }
            _ => {
                // Start of a real token.
                return Ok(saw_comment);
            }
        }
    }
}

/// Parse a `<directive>` token starting at `#!`.
///
/// Returns `FoldCaseMode::On` for `#!fold-case` and `FoldCaseMode::Off`
/// for `#!no-fold-case`. Unknown directives are reported as `<directive>`
/// lexical errors, and the span is anchored to the `#!` prefix so that
/// errors like `#!unknown-directive` highlight just the directive marker.
#[cold]
pub(crate) fn lex_directive<'i>(input: &mut WinnowInput<'i>) -> PResult<FoldCaseMode> {
    // First, look ahead to see if we have a `#!` prefix.
    // Use a probe so we can backtrack cleanly for non-directive tokens
    // such as `#(`, `#\`, etc.
    let mut probe = *input;
    if !probe.eat('#') {
        return winnow_backtrack();
    }
    if !probe.eat('!') {
        return winnow_backtrack();
    }

    // From here on, parse against `probe`, but always commit its
    // progress back into `input` before returning. This ensures that
    // lexical errors report spans that extend past the `#!` prefix
    // (e.g., `#!unknown-directive` hits the `<directive>` handler)
    // while still allowing other lexers to backtrack cleanly when
    // the `#!` prefix is absent.
    let parser = alt((
        Caseless("fold-case").value(FoldCaseMode::On),
        Caseless("no-fold-case").value(FoldCaseMode::Off),
    ));
    let mode = match cut_lex_error_token(parser, "<directive>").parse_next(&mut probe) {
        Ok(m) => m,
        Err(e) => {
            *input = probe;
            return Err(e);
        }
    };
    if let Err(e) = ensure_delimiter(&mut probe, "<directive>") {
        *input = probe;
        return Err(e);
    }
    *input = probe;
    Ok(mode)
}

/// Parse the body of a nested comment after `#|` has been consumed.
///
/// Grammar reference (Formal syntax / Lexical structure):
///
/// ```text
/// <nested comment> ::= #| <comment text>
///                       <comment cont>* |#
///
/// <comment cont> ::= <nested comment> <comment text>
/// ```
fn lex_nested_comment_body<'i>(input: &mut WinnowInput<'i>) -> PResult<()> {
    let mut depth = 1usize;

    loop {
        let ch = input.next_or_incomplete()?;

        match ch {
            '#' if input.eat('|') => depth += 1,
            '|' if input.eat('#') => {
                depth -= 1;
                if depth == 0 {
                    return Ok(());
                }
            }
            _ => {}
        }
    }
}
