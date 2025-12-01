use crate::lex::{
    PResult, WinnowInput,
    utils::{InputExt, cut_lex_error_token, ensure_delimiter},
};
use winnow::{
    Parser,
    ascii::{line_ending, till_line_ending},
    combinator::{alt, opt},
    stream::Stream,
    token::{literal, take_while},
};

/// Canonical `<intertoken space>` parser using `winnow`.
///
/// This parser consumes zero or more `<atmosphere>` elements:
/// whitespace, line comments, nested comments, and directives.
///
/// Uses a manual loop for efficiency with `take_while` for the fast paths.
pub fn lex_intertoken<'i>(input: &mut WinnowInput<'i>) -> PResult<()> {
    loop {
        // Fast path: consume runs of whitespace at once
        let _: &str =
            take_while(0.., |c| matches!(c, ' ' | '\t' | '\n' | '\r')).parse_next(input)?;

        let Some(ch) = input.peek_token() else {
            return Ok(());
        };

        match ch {
            // Line comment: `; ... <line ending or EOF>`
            ';' => {
                let _ = input.next_token();
                let _: &str = till_line_ending.parse_next(input)?;
                // Consume the line ending if present
                let _: Option<&str> = opt(line_ending).parse_next(input)?;
            }
            // Possible nested comment or directive starting with '#'.
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
                    }
                    // Directives starting with `#!`.
                    Some('!') => {
                        // Commit both characters and parse the directive
                        let _ = input.next_token();
                        let _ = input.next_token();
                        lex_directive_body(input)?;
                    }
                    _ => {
                        // Not a nested comment or directive; this
                        // begins a real token.
                        return Ok(());
                    }
                }
            }
            _ => {
                // Start of a real token.
                return Ok(());
            }
        }
    }
}

/// Parse a `<directive>` word after `#!` has been consumed.
///
/// Grammar reference (spec/syn.md / Lexical structure):
///
/// ```text
/// <directive> ::= #!fold-case | #!no-fold-case
/// ```
///
/// NOTE: We validate these directives but ignore their semantics.
/// See R7RS-DEVIATION comment in `lex_winnow`.
#[cold]
fn lex_directive_body<'i>(input: &mut WinnowInput<'i>) -> PResult<()> {
    cut_lex_error_token(
        alt((literal("fold-case"), literal("no-fold-case"))),
        "<directive>",
    )
    .parse_next(input)?;
    ensure_delimiter(input, "<directive>")
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
