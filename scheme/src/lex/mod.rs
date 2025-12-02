use crate::{
    ParseError,
    ast::{Span, Syntax},
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
use std::borrow::Cow;
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

/// Radix of a Scheme number literal as specified by `<radix R>`.
///
/// Grammar reference (Formal syntax / `<number>`):
///
/// ```text
/// <radix 2>  ::= #b
/// <radix 8>  ::= #o
/// <radix 10> ::= <empty> | #d
/// <radix 16> ::= #x
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NumberRadix {
    Binary,
    Octal,
    Decimal,
    Hexadecimal,
}

/// Exactness marker of a Scheme number literal.
///
/// ```text
/// <exactness> ::= <empty> | #i | #e
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NumberExactness {
    Exact,
    Inexact,
    /// No explicit `#e`/`#i` prefix; exactness is determined
    /// by the default rules of the report.
    Unspecified,
}

/// The four special infinities / NaNs used by `<infnan>`.
///
/// ```text
/// <infnan> ::= +inf.0 | -inf.0 | +nan.0 | -nan.0
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InfinityNan {
    PositiveInfinity,
    NegativeInfinity,
    PositiveNaN,
    NegativeNaN,
}

/// Finite real-number spellings built from `<ureal R>` and
/// `<decimal 10>`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FiniteRealKind {
    /// A (possibly signed) integer, e.g. "42", "-7".
    Integer,
    /// A (possibly signed) rational, e.g. "3/4", "-5/16".
    Rational,
    /// A (possibly signed) decimal, e.g. "3.14", "-.5", "1e3".
    Decimal,
}

// --- Lexer-specific Number Representations (Zero-Copy) ---

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteReal<'a> {
    pub kind: FiniteRealKind,
    pub spelling: &'a str,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RealRepr<'a> {
    Finite(FiniteReal<'a>),
    Infnan(InfinityNan),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NumberValue<'a> {
    Real(RealRepr<'a>),
    Rectangular {
        real: RealRepr<'a>,
        imag: RealRepr<'a>,
    },
    Polar {
        magnitude: RealRepr<'a>,
        angle: RealRepr<'a>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NumberLiteralKind<'a> {
    pub radix: NumberRadix,
    pub exactness: NumberExactness,
    pub value: NumberValue<'a>,
}

impl<'a> NumberLiteralKind<'a> {
    pub fn into_literal(self) -> NumberLiteral<'a> {
        NumberLiteral {
            text: "",
            kind: self,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct NumberLiteral<'a> {
    pub text: &'a str,
    pub kind: NumberLiteralKind<'a>,
}

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
pub enum Token<'a> {
    /// `<identifier>`
    Identifier(Cow<'a, str>),
    /// `<boolean>`
    Boolean(bool),
    /// `<number>`
    Number(NumberLiteral<'a>),
    /// `<character>`
    Character(char),
    /// `<string>`
    String(Cow<'a, str>),
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
pub type SpannedToken<'a> = Syntax<Token<'a>>;

/// An iterator over tokens in the source string.
pub struct Lexer<'i> {
    input: WinnowInput<'i>,
    source: &'i str,
}

impl<'i> Lexer<'i> {
    /// Map a winnow error into a `ParseError` with a span derived
    /// from the given token start and the current input offset.
    fn map_lex_error(&mut self, start: usize, err: ErrMode<ContextError>) -> ParseError {
        let end = self.input.current_token_start();
        let end = if end > start { end } else { start + 1 };
        let span = Span { start, end };
        winnow_err_to_parse_error(err, span)
    }

    /// Run a lexing parser starting at `start`, mapping backtrack to
    /// `Ok(None)` and other errors into `ParseError`.
    fn run_lex<O, F>(&mut self, start: usize, parser: F) -> Result<Option<O>, ParseError>
    where
        F: FnOnce(&mut WinnowInput<'i>) -> PResult<O>,
    {
        match parser(&mut self.input) {
            Ok(output) => Ok(Some(output)),
            Err(ErrMode::Backtrack(_)) => Ok(None),
            Err(e) => Err(self.map_lex_error(start, e)),
        }
    }

    /// Create a new lexer for the given source string.
    pub fn new(source: &'i str) -> Self {
        Self {
            input: WinnowInput::new(source),
            source,
        }
    }

    /// Lex a single token from the input stream, returning `Ok(None)` at EOF.
    /// This driver delegates to the canonical `lex_*` parsers.
    fn token_with_span(&mut self) -> Result<Option<SpannedToken<'i>>, ParseError> {
        // Skip `<intertoken space>` before each token.
        let start_before = self.input.current_token_start();

        // `lex_intertoken` should not backtrack; if it does, treat it
        // as "no intertoken space" and continue.
        self.run_lex(start_before, lex_intertoken)?;

        let start = self.input.current_token_start();
        if self.input.peek_token().is_none() {
            return Ok(None);
        }

        // 1. Strings.
        if let Some(spanned) = self.run_lex(start, lex_string)? {
            return Ok(Some(spanned));
        }

        // 2. Characters.
        if let Some(spanned) = self.run_lex(start, lex_character)? {
            return Ok(Some(spanned));
        }

        // 3. Booleans.
        if let Some(spanned) = self.run_lex(start, lex_boolean)? {
            return Ok(Some(spanned));
        }

        // 4. Prefixed numbers (`#b`, `#x`, `#e`, `#i`, ...).
        // Note: lex_boolean must come before this because #t/#f could be mistaken
        // for hex digits if we aren't careful, though lex_prefixed_number looks for
        // specific radix prefixes.
        if let Some(mut literal) = self.run_lex(start, lex_prefixed_number)? {
            let end = self.input.current_token_start();
            literal.text = &self.source[start..end];
            let span = Span { start, end };
            return Ok(Some(Syntax::new(span, Token::Number(literal))));
        }

        // 5. Punctuation: parens, quotes, `#(`, `#u8(`, `.`, etc.
        if let Some(spanned) = self.run_lex(start, lex_punctuation)? {
            return Ok(Some(spanned));
        }

        // 6. Decimal `<number>` tokens (no prefixes), including complex forms.
        let ch = match self.input.peek_token() {
            Some(c) => c,
            None => return Ok(None),
        };
        match ch {
            '+' | '-' | '0'..='9' | '.' => {
                // Not a `<number>` starting here; try as identifier
                // (e.g., `+` or `-` alone, or peculiar identifiers).
                if let Some(mut literal) = self.run_lex(start, lex_complex_decimal)? {
                    let end = self.input.current_token_start();
                    literal.text = &self.source[start..end];
                    let span = Span { start, end };
                    return Ok(Some(Syntax::new(span, Token::Number(literal))));
                }
            }
            _ => {}
        }

        // 7. Identifiers (including peculiar identifiers like `+`, `-`, `...`).
        if let Some(spanned) = self.run_lex(start, lex_identifier)? {
            return Ok(Some(spanned));
        }

        // No token matched - this is an error
        let end = start.saturating_add(ch.len_utf8()).min(self.source.len());
        let span = Span { start, end };

        Err(ParseError::lexical(
            span,
            "<token>",
            format!("unexpected character: {:?}", ch),
        ))
    }
}

impl<'i> Iterator for Lexer<'i> {
    type Item = Result<SpannedToken<'i>, ParseError>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.token_with_span() {
            Ok(Some(token)) => Some(Ok(token)),
            Ok(None) => None,
            Err(e) => Some(Err(e)),
        }
    }
}

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
pub fn lex(source: &str) -> Lexer<'_> {
    Lexer::new(source)
}
