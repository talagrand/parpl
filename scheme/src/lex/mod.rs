use crate::{
    ParseError,
    ast::{NumberLiteral, Span, Syntax},
    lex::{
        boolean::lex_boolean,
        identifiers::lex_identifier,
        intertoken::lex_intertoken,
        numbers::{lex_complex_decimal, lex_prefixed_number},
        punctuation::lex_punctuation,
        strings::{lex_character, lex_string},
        utils::winnow_err_to_parse_error,
    },
};
use winnow::{
    error::{ContextError, ErrMode},
    stream::{Location, Stream},
};

pub mod boolean;
pub mod identifiers;
pub mod intertoken;
pub mod numbers;
pub mod punctuation;
pub mod strings;
#[cfg(test)]
mod tests;
pub mod utils;

// Internal input and result types used by the lexer implementation.
pub type WinnowInput<'i> = winnow::stream::LocatingSlice<winnow::stream::Str<'i>>;
pub type PResult<O> = Result<O, ErrMode<ContextError>>;

/// Lexical tokens as defined by `<token>` in `syn.tex`, plus internal tokens
/// to support other R7RS constructs.
///
/// Grammar reference (Formal syntax / Lexical structure):
///
/// ```text
/// <token> ::= <identifier> | <boolean> | <number>
///           | <character> | <string>
///           | ( | ) | #( | #u8( | ' | ` | , | ,@ | .
/// ```
///
/// **Internal tokens:**
/// - `DatumComment` (`#;`) supports R7RS datum comments (handled by the parser).
/// - `LabelDef` (`#n=`) and `LabelRef` (`#n#`) support R7RS shared structure labels.
#[derive(Clone, Debug, PartialEq)]
pub enum Token {
    /// `<identifier>`
    Identifier(String),
    /// `<boolean>`
    Boolean(bool),
    /// `<number>`
    Number(NumberLiteral),
    /// `<character>`
    Character(char),
    /// `<string>`
    String(String),
    /// `(`
    LParen,
    /// `)`
    RParen,
    /// `#(`
    VectorStart,
    /// `#u8(`
    ByteVectorStart,
    /// `'`
    Quote,
    /// `` ` ``
    Backquote,
    /// `,`
    Comma,
    /// `,@`
    CommaAt,
    /// `.`
    Dot,
    /// `#;` (datum comment prefix)
    ///
    /// R7RS-DEVIATION: Datum comments handled at parser level, not lexer.
    /// See R7RS-DEVIATIONS.md §3 for full details.
    ///
    /// R7RS treats `#; <datum>` as intertoken space (i.e., the lexer should
    /// skip the `#;` and the following datum). However, determining what
    /// constitutes a `<datum>` requires a full parser—the lexer alone cannot
    /// know where the datum ends.
    ///
    /// Our approach: The lexer emits `Token::DatumComment` when it sees `#;`,
    /// and the parser is responsible for consuming and discarding the next
    /// datum. This keeps the lexer simple and context-free.
    DatumComment,
    /// `#n=` (label definition)
    LabelDef(u64),
    /// `#n#` (label reference)
    LabelRef(u64),
}

/// A single token paired with its source span.
pub type SpannedToken = Syntax<Token>;

/// Lex all `<token>`s from the given source string, skipping
/// `<intertoken space>` (whitespace, comments, nested comments,
/// and directives).
///
/// This function recognizes all standard R7RS tokens. It also produces tokens
/// for constructs that R7RS defines as part of `<comment>` or `<datum>`
/// (datum comments, labels) to facilitate parser-level handling.
///
/// **Deviations from R7RS:**
/// - **Unicode:** Identifier support is conservative (see `R7RS-DEVIATIONS.md`).
/// - **Fold-case:** `#!fold-case` directives are ignored.
/// - **Datum comments:** Handled at parser level (emitted as `Token::DatumComment`).
///
/// Grammar reference (Formal syntax / Lexical structure):
///
/// ```text
/// <intertoken space> ::= <atmosphere>*
/// <atmosphere> ::= <whitespace> | <comment> | <directive>
///
/// <comment> ::= ; <all subsequent characters up to a line ending
///                or end of file>
/// <nested comment> ::= #| <comment text> |#
/// <directive> ::= #!fold-case | #!no-fold-case
/// ```
pub fn lex(source: &str) -> Result<Vec<SpannedToken>, ParseError> {
    let mut tokens = Vec::new();
    let mut input = WinnowInput::new(source);

    // R7RS-DEVIATION: Fold-case directives recognized but ignored.
    // See R7RS-DEVIATIONS.md §2 for full details.
    //
    // We recognize `#!fold-case` / `#!no-fold-case` directives lexically
    // (and validate them), but deliberately ignore their semantics.
    // The reader remains case-sensitive throughout. Identifiers `FOO`
    // and `foo` are treated as distinct.

    while let Some(token) = token_with_span(&mut input, source)? {
        tokens.push(token);
    }

    Ok(tokens)
}

/// Lex a single token from the input stream, returning `Ok(None)` at EOF.
/// This driver delegates to the canonical `lex_*` parsers.
fn token_with_span<'i>(
    input: &mut WinnowInput<'i>,
    source: &'i str,
) -> Result<Option<SpannedToken>, ParseError> {
    let len = source.len();

    // Skip `<intertoken space>` before each token.
    let start_before = input.current_token_start();
    let fallback_span_before = Span {
        start: start_before,
        end: len,
    };

    match lex_intertoken(input) {
        Ok(()) => {}
        Err(ErrMode::Incomplete(_)) => return Err(ParseError::Incomplete),
        Err(e) => return Err(winnow_err_to_parse_error(e, fallback_span_before)),
    }

    let start = input.current_token_start();
    if input.peek_token().is_none() {
        return Ok(None);
    }

    let fallback_span = Span { start, end: len };

    // 1. Strings.
    match lex_string(input) {
        Ok(spanned) => return Ok(Some(spanned)),
        Err(ErrMode::Backtrack(_)) => {}
        Err(e) => return Err(winnow_err_to_parse_error(e, fallback_span)),
    }

    // 2. Characters.
    match lex_character(input) {
        Ok(spanned) => return Ok(Some(spanned)),
        Err(ErrMode::Backtrack(_)) => {}
        Err(e) => return Err(winnow_err_to_parse_error(e, fallback_span)),
    }

    // 3. Booleans.
    match lex_boolean(input) {
        Ok(spanned) => return Ok(Some(spanned)),
        Err(ErrMode::Backtrack(_)) => {}
        Err(e) => return Err(winnow_err_to_parse_error(e, fallback_span)),
    }

    // 4. Prefixed numbers (`#b`, `#x`, `#e`, `#i`, ...).
    match lex_prefixed_number(input) {
        Ok(mut literal) => {
            let end = input.current_token_start();
            literal.text = source[start..end].to_string();
            let span = Span { start, end };
            return Ok(Some(Syntax::new(span, Token::Number(literal))));
        }
        Err(ErrMode::Backtrack(_)) => {}
        Err(ErrMode::Incomplete(_)) => return Err(ParseError::Incomplete),
        Err(e) => return Err(winnow_err_to_parse_error(e, fallback_span)),
    }

    // 5. Punctuation: parens, quotes, `#(`, `#u8(`, `.`, etc.
    match lex_punctuation(input) {
        Ok(spanned) => return Ok(Some(spanned)),
        Err(ErrMode::Backtrack(_)) => {}
        Err(e) => return Err(winnow_err_to_parse_error(e, fallback_span)),
    }

    // 6. Decimal `<number>` tokens (no prefixes), including complex forms.
    let ch = match input.peek_token() {
        Some(c) => c,
        None => return Ok(None),
    };
    match ch {
        '+' | '-' | '0'..='9' | '.' => {
            match lex_complex_decimal(input) {
                Ok(mut literal) => {
                    let end = input.current_token_start();
                    literal.text = source[start..end].to_string();
                    let span = Span { start, end };
                    return Ok(Some(Syntax::new(span, Token::Number(literal))));
                }
                Err(ErrMode::Backtrack(_)) => {
                    // Not a `<number>` starting here; try as identifier
                    // (e.g., `+` or `-` alone, or peculiar identifiers)
                }
                Err(ErrMode::Incomplete(_)) => return Err(ParseError::Incomplete),
                Err(e) => return Err(winnow_err_to_parse_error(e, fallback_span)),
            }
        }
        _ => {}
    }

    // 7. Identifiers (including peculiar identifiers like `+`, `-`, `...`).
    match lex_identifier(input) {
        Ok(spanned) => return Ok(Some(spanned)),
        Err(ErrMode::Backtrack(_)) => {}
        Err(ErrMode::Incomplete(_)) => return Err(ParseError::Incomplete),
        Err(e) => return Err(winnow_err_to_parse_error(e, fallback_span)),
    }

    // No token matched - this is an error
    Err(ParseError::lexical(
        fallback_span,
        "<token>",
        format!("unexpected character: {:?}", ch),
    ))
}
