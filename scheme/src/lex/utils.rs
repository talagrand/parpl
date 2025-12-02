use crate::{
    ParseError,
    ast::Span,
    lex::{PResult, WinnowInput},
};
use winnow::{
    Parser,
    error::{ContextError, ErrMode, Needed, StrContext},
    stream::Stream,
};

// --- Idiomatic helper trait for cleaner character consumption ---

/// Extension trait providing idiomatic helpers for the lexer input stream.
///
/// These methods reduce boilerplate for common lexer patterns while
/// maintaining zero-cost abstractions (they inline to the same code
/// as the manual versions).
pub trait InputExt {
    /// Consume the next character if it matches `expected`, returning `true`.
    /// Returns `false` without consuming if it doesn't match or at EOF.
    fn eat(&mut self, expected: char) -> bool;

    /// Consume the next character if it matches the predicate.
    /// Returns `Some(char)` if consumed, `None` otherwise.
    fn eat_if(&mut self, predicate: impl FnOnce(char) -> bool) -> Option<char>;

    /// Peek at the next character, returning an incomplete error if at EOF.
    /// Use for REPL-continuable constructs (strings, nested comments).
    fn peek_or_incomplete(&mut self) -> PResult<char>;

    /// Peek at the next character, returning an incomplete-token error if at EOF.
    /// Use for mid-token EOF (e.g., after `#\`, `1e+`, `3/`).
    fn peek_or_incomplete_token(&mut self) -> PResult<char>;

    /// Peek at the next character, returning a backtrack error if at EOF.
    fn peek_or_backtrack(&mut self) -> PResult<char>;

    /// Consume and return the next character, returning an incomplete error if at EOF.
    /// Use for REPL-continuable constructs (strings, nested comments).
    fn next_or_incomplete(&mut self) -> PResult<char>;

    /// Consume and return the next character, returning an incomplete-token error if at EOF.
    /// Use for mid-token EOF (e.g., after `#\`).
    fn next_or_incomplete_token(&mut self) -> PResult<char>;
}

impl InputExt for WinnowInput<'_> {
    #[inline]
    fn eat(&mut self, expected: char) -> bool {
        if self.peek_token() == Some(expected) {
            let _ = self.next_token();
            true
        } else {
            false
        }
    }

    #[inline]
    fn eat_if(&mut self, predicate: impl FnOnce(char) -> bool) -> Option<char> {
        match self.peek_token() {
            Some(c) if predicate(c) => {
                let _ = self.next_token();
                Some(c)
            }
            _ => None,
        }
    }

    #[inline]
    fn peek_or_incomplete(&mut self) -> PResult<char> {
        self.peek_token()
            .ok_or(ErrMode::Incomplete(Needed::Unknown))
    }

    #[inline]
    fn peek_or_incomplete_token(&mut self) -> PResult<char> {
        self.peek_token().ok_or_else(|| {
            let mut ctx = ContextError::new();
            ctx.push(StrContext::Label(INCOMPLETE_TOKEN_LABEL));
            ErrMode::Cut(ctx)
        })
    }

    #[inline]
    fn peek_or_backtrack(&mut self) -> PResult<char> {
        self.peek_token()
            .ok_or_else(|| ErrMode::Backtrack(ContextError::new()))
    }

    #[inline]
    fn next_or_incomplete(&mut self) -> PResult<char> {
        self.next_token()
            .ok_or(ErrMode::Incomplete(Needed::Unknown))
    }

    #[inline]
    fn next_or_incomplete_token(&mut self) -> PResult<char> {
        self.next_token().ok_or_else(|| {
            let mut ctx = ContextError::new();
            ctx.push(StrContext::Label(INCOMPLETE_TOKEN_LABEL));
            ErrMode::Cut(ctx)
        })
    }
}

/// Sentinel label used to distinguish `IncompleteToken` from `Incomplete`.
const INCOMPLETE_TOKEN_LABEL: &str = "__incomplete_token__";

pub fn winnow_err_to_parse_error(err: ErrMode<ContextError>, fallback_span: Span) -> ParseError {
    match err {
        ErrMode::Incomplete(_) => ParseError::Incomplete,
        ErrMode::Cut(e) | ErrMode::Backtrack(e) => {
            // Check for the special incomplete-token sentinel.
            for ctx in e.context() {
                if let StrContext::Label(INCOMPLETE_TOKEN_LABEL) = ctx {
                    return ParseError::IncompleteToken;
                }
            }

            // Try to recover the most specific nonterminal label from the
            // `ContextError`. If none is present, fall back to a generic
            // `<token>` context.
            let mut nonterminal = "<token>";
            for ctx in e.context() {
                if let StrContext::Label(label) = ctx {
                    nonterminal = label;
                }
            }

            // For now, we do not yet plumb precise spans from `LocatingSlice`.
            // During the full migration we will replace `fallback_span` with
            // spans derived from `with_span` and the input location.
            ParseError::lexical(fallback_span, nonterminal, e.to_string())
        }
    }
}

/// Helper to produce a recoverable backtrack error with empty context.
pub fn winnow_backtrack<O>() -> PResult<O> {
    Err(ErrMode::Backtrack(ContextError::new()))
}

/// Helper to produce an incomplete input error (REPL should prompt for more).
#[allow(dead_code)]
pub fn winnow_incomplete<O>() -> PResult<O> {
    Err(ErrMode::Incomplete(Needed::Unknown))
}

/// Helper to produce an incomplete token error (mid-token EOF).
///
/// This indicates the input ended in the middle of a token (e.g., `#\`,
/// `1e+`, `3/`). In a REPL, this is typically a user error rather than a
/// prompt-for-more signal.
pub fn winnow_incomplete_token<O>() -> PResult<O> {
    let mut ctx = ContextError::new();
    ctx.push(StrContext::Label(INCOMPLETE_TOKEN_LABEL));
    Err(ErrMode::Cut(ctx))
}

/// Wraps a parser to convert Backtrack errors into Cut errors with a specific label.
/// If the input is empty (EOF), it returns the special IncompleteToken error instead.
pub fn cut_lex_error_token<'i, O, P>(
    mut parser: P,
    nonterminal: &'static str,
) -> impl Parser<WinnowInput<'i>, O, ErrMode<ContextError>>
where
    P: Parser<WinnowInput<'i>, O, ErrMode<ContextError>>,
{
    move |input: &mut WinnowInput<'i>| {
        parser.parse_next(input).map_err(|e| match e {
            ErrMode::Backtrack(_) => {
                if input.is_empty() {
                    let mut ctx = ContextError::new();
                    ctx.push(StrContext::Label(INCOMPLETE_TOKEN_LABEL));
                    ErrMode::Cut(ctx)
                } else {
                    let mut ctx = ContextError::new();
                    ctx.push(StrContext::Label(nonterminal));
                    ErrMode::Cut(ctx)
                }
            }
            _ => e,
        })
    }
}

/// Helper to produce a lexical error for a given nonterminal.
pub fn lex_error<O>(nonterminal: &'static str) -> PResult<O> {
    let mut ctx = ContextError::new();
    ctx.push(StrContext::Label(nonterminal));
    Err(ErrMode::Cut(ctx))
}

/// True if `ch` is a `<delimiter>` character.
///
/// Grammar reference:
///
/// ```text
/// <delimiter> ::= <whitespace> | <vertical line>
///               | ( | ) | " | ;
/// ```
pub(crate) fn is_delimiter(ch: char) -> bool {
    matches!(ch, ' ' | '\t' | '\n' | '\r' | '|' | '(' | ')' | '"' | ';')
}

/// Ensure the next character is a delimiter (or EOF).
///
/// Many tokens in Scheme must be followed by a delimiter. This helper
/// checks that condition and returns an error with the given nonterminal
/// label if violated.
#[inline]
pub(crate) fn ensure_delimiter<'i>(
    input: &mut WinnowInput<'i>,
    nonterminal: &'static str,
) -> PResult<()> {
    if input.peek_token().is_some_and(|ch| !is_delimiter(ch)) {
        return lex_error(nonterminal);
    }
    Ok(())
}
