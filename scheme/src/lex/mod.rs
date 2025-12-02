use crate::{
    ParseError,
    ast::{self, FiniteRealKind, InfinityNan, NumberExactness, NumberRadix, Span, Syntax},
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

impl<'a> From<FiniteReal<'a>> for ast::RealRepr {
    fn from(lex: FiniteReal<'a>) -> Self {
        ast::RealRepr::Finite {
            kind: lex.kind,
            spelling: lex.spelling.to_string(),
        }
    }
}

impl<'a> From<RealRepr<'a>> for ast::RealRepr {
    fn from(lex: RealRepr<'a>) -> Self {
        match lex {
            RealRepr::Finite(f) => f.into(),
            RealRepr::Infnan(i) => ast::RealRepr::Infnan(i),
        }
    }
}

impl<'a> From<NumberValue<'a>> for ast::NumberValue {
    fn from(lex: NumberValue<'a>) -> Self {
        match lex {
            NumberValue::Real(r) => ast::NumberValue::Real(r.into()),
            NumberValue::Rectangular { real, imag } => ast::NumberValue::Rectangular {
                real: real.into(),
                imag: imag.into(),
            },
            NumberValue::Polar { magnitude, angle } => ast::NumberValue::Polar {
                magnitude: magnitude.into(),
                angle: angle.into(),
            },
        }
    }
}

impl<'a> From<NumberLiteralKind<'a>> for ast::NumberLiteralKind {
    fn from(lex: NumberLiteralKind<'a>) -> Self {
        ast::NumberLiteralKind {
            radix: lex.radix,
            exactness: lex.exactness,
            value: lex.value.into(),
        }
    }
}

impl<'a> From<NumberLiteral<'a>> for ast::NumberLiteral {
    fn from(lex: NumberLiteral<'a>) -> Self {
        ast::NumberLiteral {
            text: lex.text.to_string(),
            kind: lex.kind.into(),
        }
    }
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
        let len = self.source.len();

        // Skip `<intertoken space>` before each token.
        let start_before = self.input.current_token_start();
        let fallback_span_before = Span {
            start: start_before,
            end: len,
        };

        match lex_intertoken(&mut self.input) {
            Ok(()) => {}
            Err(ErrMode::Incomplete(_)) => return Err(ParseError::Incomplete),
            Err(e) => return Err(winnow_err_to_parse_error(e, fallback_span_before)),
        }

        let start = self.input.current_token_start();
        if self.input.peek_token().is_none() {
            return Ok(None);
        }

        let fallback_span = Span { start, end: len };

        // 1. Strings.
        match lex_string(&mut self.input) {
            Ok(spanned) => return Ok(Some(spanned)),
            Err(ErrMode::Backtrack(_)) => {}
            Err(e) => return Err(winnow_err_to_parse_error(e, fallback_span)),
        }

        // 2. Characters.
        match lex_character(&mut self.input) {
            Ok(spanned) => return Ok(Some(spanned)),
            Err(ErrMode::Backtrack(_)) => {}
            Err(e) => return Err(winnow_err_to_parse_error(e, fallback_span)),
        }

        // 3. Booleans.
        match lex_boolean(&mut self.input) {
            Ok(spanned) => return Ok(Some(spanned)),
            Err(ErrMode::Backtrack(_)) => {}
            Err(e) => return Err(winnow_err_to_parse_error(e, fallback_span)),
        }

        // 4. Prefixed numbers (`#b`, `#x`, `#e`, `#i`, ...).
        match lex_prefixed_number(&mut self.input) {
            Ok(mut literal) => {
                let end = self.input.current_token_start();
                literal.text = &self.source[start..end];
                let span = Span { start, end };
                return Ok(Some(Syntax::new(span, Token::Number(literal))));
            }
            Err(ErrMode::Backtrack(_)) => {}
            Err(ErrMode::Incomplete(_)) => return Err(ParseError::Incomplete),
            Err(e) => return Err(winnow_err_to_parse_error(e, fallback_span)),
        }

        // 5. Punctuation: parens, quotes, `#(`, `#u8(`, `.`, etc.
        match lex_punctuation(&mut self.input) {
            Ok(spanned) => return Ok(Some(spanned)),
            Err(ErrMode::Backtrack(_)) => {}
            Err(e) => return Err(winnow_err_to_parse_error(e, fallback_span)),
        }

        // 6. Decimal `<number>` tokens (no prefixes), including complex forms.
        let ch = match self.input.peek_token() {
            Some(c) => c,
            None => return Ok(None),
        };
        match ch {
            '+' | '-' | '0'..='9' | '.' => {
                match lex_complex_decimal(&mut self.input) {
                    Ok(mut literal) => {
                        let end = self.input.current_token_start();
                        literal.text = &self.source[start..end];
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
        match lex_identifier(&mut self.input) {
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
