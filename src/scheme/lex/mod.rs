use crate::common::{Span, Syntax};
use crate::scheme::{
    ParseError, Unsupported,
    lex::{
        boolean::lex_boolean,
        identifiers::lex_identifier,
        intertoken::lex_intertoken,
        numbers::{lex_complex_decimal, lex_prefixed_number, try_fast_decimal_integer},
        punctuation::{lex_dot, lex_hash_punctuation, simple_punct},
        strings::{lex_character, lex_string},
        utils::{INCOMPLETE_TOKEN_LABEL, InputExt},
    },
};
use std::borrow::Cow;
use winnow::{
    error::{ContextError, ErrMode, StrContext},
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
pub type Input<'i> = winnow::stream::LocatingSlice<winnow::stream::Str<'i>>;
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
/// Radix base for a Scheme number literal.
///
/// Invariant: only 2, 8, 10, or 16.
pub type NumberRadix = u32;

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

/// Sign prefix used by `<sign>`.
///
/// Note: we track whether a sign was explicitly present separately
/// in `RealRepr`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Sign {
    Positive,
    Negative,
}

/// Finite real-number spellings built from `<ureal R>` and
/// `<decimal 10>`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FiniteRealKind {
    /// An integer, e.g. "42".
    Integer,
    /// A rational, e.g. "3/4".
    Rational,
    /// A decimal, e.g. "3.14", ".5", "1e3".
    Decimal,
}

// --- Lexer-specific Number Representations (Zero-Copy) ---

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteRealMagnitude<'a> {
    pub kind: FiniteRealKind,
    /// Signless spelling of the finite real.
    ///
    /// Invariant: never includes a leading '+' or '-'.
    pub spelling: &'a str,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RealMagnitude<'a> {
    Finite(FiniteRealMagnitude<'a>),
    Infinity,
    NaN,
}

/// Signed real-number representation used inside complex numbers.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RealRepr<'a> {
    /// Explicit sign from the source (`+` / `-`).
    ///
    /// - `None` means no explicit sign was present (implicit positive).
    /// - `Some(Sign::Positive)` means an explicit `+` was present.
    /// - `Some(Sign::Negative)` means an explicit `-` was present.
    ///
    /// Invariant: if `magnitude` is `Infinity` or `NaN`, then `sign.is_some()`.
    pub sign: Option<Sign>,
    pub magnitude: RealMagnitude<'a>,
}

impl<'a> RealRepr<'a> {
    /// Returns the effective sign, treating an omitted sign as `+`.
    pub fn effective_sign(&self) -> Sign {
        self.sign.unwrap_or(Sign::Positive)
    }
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

/// Fold-case mode for identifiers and named character literals.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum FoldCaseMode {
    /// Case-folding disabled (R7RS `#!no-fold-case`).
    Off,
    /// Case-folding enabled (R7RS `#!fold-case`).
    On,
}

/// Configuration options for the lexer.
///
/// This controls whether fold-case directives are honored semantically
/// and whether comments are accepted or rejected.
#[derive(Copy, Clone, Default, Debug, PartialEq, Eq)]
pub struct LexConfig {
    /// If true, fold-case directives are rejected as
    /// `Unsupported::FoldCaseDirectives` and identifiers and character
    /// names are always case-sensitive.
    ///
    /// When false (the default), `#!fold-case` / `#!no-fold-case`
    /// directives are allowed and can toggle the internal
    /// `FoldCaseMode`, which in turn controls whether identifiers and
    /// named character literals are case-folded.
    pub reject_fold_case: bool,

    /// If true, any comment (line comment `;`, nested comment `#| |#`, or
    /// datum comment `#;`) is rejected with `Unsupported::Comments`.
    ///
    /// When false (the default), comments are treated according to the
    /// normal R7RS rules: line and nested comments are part of
    /// `<intertoken space>`, and datum comments emit `Token::DatumComment`
    /// for higher layers to interpret.
    pub reject_comments: bool,
}

/// A single token paired with its source span.
pub type SpannedToken<'a> = Syntax<Token<'a>>;

/// An iterator over tokens in the source string.
pub struct Lexer<'i> {
    input: Input<'i>,
    source: &'i str,
    /// Current fold-case mode for identifiers and character names.
    fold_case_mode: FoldCaseMode,
    /// Static configuration for this lexer instance.
    config: LexConfig,
}

impl<'i> Lexer<'i> {
    /// Map a winnow error into a `ParseError` with a span derived
    /// from the given token start and the current input offset.
    #[inline]
    fn map_lex_error(&mut self, start: usize, err: ErrMode<ContextError>) -> ParseError {
        let end = self.input.current_token_start();
        let end = if end > start { end } else { start + 1 };
        let span = Span { start, end };

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

                ParseError::lexical(span, nonterminal, e.to_string())
            }
        }
    }

    /// Run a lexing parser starting at `start`, mapping backtrack to
    /// `Ok(None)` and other errors into `ParseError`.
    fn run_lex<O, F>(&mut self, start: usize, parser: F) -> Result<Option<O>, ParseError>
    where
        F: FnOnce(&mut Input<'i>) -> PResult<O>,
    {
        match parser(&mut self.input) {
            Ok(output) => Ok(Some(output)),
            Err(ErrMode::Backtrack(_)) => Ok(None),
            Err(e) => Err(self.map_lex_error(start, e)),
        }
    }

    /// Create a new lexer for the given source string with default
    /// configuration.
    #[inline]
    pub fn new(source: &'i str) -> Self {
        Self::with_config(source, LexConfig::default())
    }

    /// Create a new lexer for the given source string and configuration.
    #[inline]
    pub fn with_config(source: &'i str, config: LexConfig) -> Self {
        Self {
            input: Input::new(source),
            source,
            fold_case_mode: FoldCaseMode::Off,
            config,
        }
    }

    /// Lex a single token from the input stream, returning `Ok(None)` at EOF.
    /// This driver uses first-character dispatch for efficiency, then delegates to the canonical lex_* parsers.
    fn token_with_span(&mut self) -> Result<Option<SpannedToken<'i>>, ParseError> {
        // Skip `<intertoken space>` before each token.
        let start_before = self.input.current_token_start();

        // `lex_intertoken` should not backtrack; if it does, treat it
        // as "no intertoken space" and continue.
        let saw_comment = self.run_lex(start_before, lex_intertoken)?.unwrap_or(false);

        if self.config.reject_comments && saw_comment {
            let end = self.input.current_token_start();
            let span = Span {
                start: start_before,
                end,
            };
            return Err(ParseError::unsupported(span, Unsupported::Comments));
        }

        let start = self.input.current_token_start();
        let ch = match self.input.peek_token() {
            Some(c) => c,
            None => return Ok(None),
        };

        let fold_mode = if self.config.reject_fold_case {
            FoldCaseMode::Off
        } else {
            self.fold_case_mode
        };

        // First-character dispatch to eliminate backtracking overhead.
        // At authoring time, this optimization provided ~40% performance
        // improvement by avoiding sequential parser attempts.
        match ch {
            // Strings: only `"` can start a string.
            '"' => {
                if let Some(spanned) = self.run_lex(start, lex_string)? {
                    return Ok(Some(spanned));
                }
            }

            // Simple punctuation: single-character tokens.
            '(' => return Ok(Some(simple_punct(&mut self.input, start, Token::LParen))),
            ')' => return Ok(Some(simple_punct(&mut self.input, start, Token::RParen))),
            '\'' => return Ok(Some(simple_punct(&mut self.input, start, Token::Quote))),
            '`' => return Ok(Some(simple_punct(&mut self.input, start, Token::Backquote))),
            ',' => {
                let _ = self.input.next_token();
                let tok = if self.input.eat('@') {
                    Token::CommaAt
                } else {
                    Token::Comma
                };
                let end = self.input.current_token_start();
                return Ok(Some(Syntax::new(Span { start, end }, tok)));
            }

            // Hash-prefixed tokens: #t, #f, #\, #(, #u8(, #b, #o, #x, #d, #e, #i, #;, #n=, #n#, #!
            '#' => {
                // Characters: #\
                if let Some(spanned) =
                    self.run_lex(start, |input| lex_character(input, fold_mode))?
                {
                    return Ok(Some(spanned));
                }

                // Booleans: #t, #f, #true, #false
                if let Some(spanned) = self.run_lex(start, lex_boolean)? {
                    return Ok(Some(spanned));
                }

                // Prefixed numbers: #b, #o, #x, #d, #e, #i
                if let Some(mut literal) = self.run_lex(start, lex_prefixed_number)? {
                    let end = self.input.current_token_start();
                    #[expect(
                        clippy::string_slice,
                        reason = "LocatingSlice offsets are valid UTF-8 boundaries"
                    )]
                    {
                        literal.text = &self.source[start..end];
                    }
                    let span = Span { start, end };
                    return Ok(Some(Syntax::new(span, Token::Number(literal))));
                }

                // Hash punctuation: #(, #u8(, #;, #n=, #n#
                if let Some(spanned) = self.run_lex(start, lex_hash_punctuation)? {
                    if self.config.reject_comments && spanned.value == Token::DatumComment {
                        return Err(ParseError::unsupported(spanned.span, Unsupported::Comments));
                    }
                    return Ok(Some(spanned));
                }

                // Fold-case directives: #!fold-case, #!no-fold-case
                if let Some(mode) = self.run_lex(start, intertoken::lex_directive)? {
                    let end = self.input.current_token_start();
                    let span = Span { start, end };

                    if self.config.reject_fold_case {
                        return Err(ParseError::unsupported(
                            span,
                            Unsupported::FoldCaseDirectives,
                        ));
                    }

                    self.fold_case_mode = mode;
                    return self.token_with_span();
                }
            }

            // Digits: always a number.
            // Fast-path: simple decimal integers (e.g., 42, 123) are very common.
            // Skip the full parser machinery when we can identify them directly.
            // At authoring time, this optimization provided ~5% performance
            // improvement on parsing a 1K Scheme program.
            '0'..='9' => {
                // Try fast-path for simple decimal integers first.
                if let Some(Some(literal)) = self.run_lex(start, try_fast_decimal_integer)? {
                    let end = self.input.current_token_start();
                    let span = Span { start, end };
                    return Ok(Some(Syntax::new(span, Token::Number(literal))));
                }
                // Fall back to full number parser for complex cases.
                if let Some(mut literal) = self.run_lex(start, lex_complex_decimal)? {
                    let end = self.input.current_token_start();
                    #[expect(
                        clippy::string_slice,
                        reason = "LocatingSlice offsets are valid UTF-8 boundaries"
                    )]
                    {
                        literal.text = &self.source[start..end];
                    }
                    let span = Span { start, end };
                    return Ok(Some(Syntax::new(span, Token::Number(literal))));
                }
            }

            // Sign or dot: could be number or identifier.
            '+' | '-' | '.' => {
                // Try number first (more common in arithmetic expressions).
                if let Some(mut literal) = self.run_lex(start, lex_complex_decimal)? {
                    let end = self.input.current_token_start();
                    #[expect(
                        clippy::string_slice,
                        reason = "LocatingSlice offsets are valid UTF-8 boundaries"
                    )]
                    {
                        literal.text = &self.source[start..end];
                    }
                    let span = Span { start, end };
                    return Ok(Some(Syntax::new(span, Token::Number(literal))));
                }

                // Fall through to identifier (handles +, -, ..., .foo, etc.)
                if let Some(spanned) =
                    self.run_lex(start, |input| lex_identifier(input, fold_mode))?
                {
                    return Ok(Some(spanned));
                }

                // Special case: lone `.` is Token::Dot
                if ch == '.'
                    && let Some(spanned) = self.run_lex(start, lex_dot)?
                {
                    return Ok(Some(spanned));
                }
            }

            // Everything else: identifier.
            _ => {
                if let Some(spanned) =
                    self.run_lex(start, |input| lex_identifier(input, fold_mode))?
                {
                    return Ok(Some(spanned));
                }
            }
        }

        // No token matched - this is an error
        let end = start.saturating_add(ch.len_utf8()).min(self.source.len());
        let span = Span { start, end };

        Err(ParseError::lexical(
            span,
            "<token>",
            format!("unexpected character: {ch:?}"),
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
/// `<intertoken space>` (whitespace, line comments, and nested comments).
///
/// This function recognizes all standard R7RS tokens. It also produces
/// additional tokens for constructs that the spec treats as part of
/// `<comment>` or `<datum>` so that higher layers can implement the
/// prescribed semantics:
///
/// - `Token::DatumComment` for `#;`, which `TokenStream` can consume while
///   recursively skipping the following datum, making datum comments
///   effectively intertoken space to callers.
///
/// Fold-case directives `#!fold-case` / `#!no-fold-case` are never emitted
/// as tokens. They are recognized after `<intertoken space>` and treated as
/// additional intertoken space, updating the internal `FoldCaseMode` when
/// `LexConfig::reject_fold_case` is false. The lexer applies fold-case
/// semantics to identifiers and named character literals based on this
/// mode.
///
/// Unicode identifier support remains conservative (see design notes for details).
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
/// Convenience constructor using the default `LexConfig`.
#[inline]
pub fn lex(source: &str) -> Lexer<'_> {
    Lexer::new(source)
}

/// Construct a lexer with an explicit `LexConfig`.
#[inline]
pub fn lex_with_config(source: &str, config: LexConfig) -> Lexer<'_> {
    Lexer::with_config(source, config)
}
