use crate::{
    FiniteRealRepr, InfinityNan, NumberExactness, NumberLiteral, NumberLiteralKind, NumberRadix,
    NumberValue, ParseError, RealRepr, Span, Syntax,
};
use winnow::Parser;
use winnow::ascii::{Caseless, hex_digit1, line_ending, space0, till_line_ending};
use winnow::combinator::{alt, opt, preceded};
use winnow::error::{ContextError, ErrMode, Needed, StrContext};
use winnow::stream::{Location, Stream};
use winnow::token::{literal, take_while};

// Internal types and helpers to support the `winnow`-based lexer.
type WinnowInput<'i> = winnow::stream::LocatingSlice<winnow::stream::Str<'i>>;
type PResult<O> = Result<O, ErrMode<ContextError>>;

// --- Idiomatic helper trait for cleaner character consumption ---

/// Extension trait providing idiomatic helpers for `WinnowInput`.
///
/// These methods reduce boilerplate for common lexer patterns while
/// maintaining zero-cost abstractions (they inline to the same code
/// as the manual versions).
trait InputExt {
    /// Consume the next character if it matches `expected`, returning `true`.
    /// Returns `false` without consuming if it doesn't match or at EOF.
    fn eat(&mut self, expected: char) -> bool;

    /// Consume the next character if it matches the predicate.
    /// Returns `Some(char)` if consumed, `None` otherwise.
    fn eat_if(&mut self, predicate: impl FnOnce(char) -> bool) -> Option<char>;

    /// Consume characters while the predicate holds, pushing them to `buf`.
    /// Returns the number of characters consumed.
    fn eat_while(&mut self, buf: &mut String, predicate: impl Fn(char) -> bool) -> usize;

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
    fn eat_while(&mut self, buf: &mut String, predicate: impl Fn(char) -> bool) -> usize {
        let mut count = 0;
        while let Some(c) = self.peek_token() {
            if predicate(c) {
                buf.push(c);
                let _ = self.next_token();
                count += 1;
            } else {
                break;
            }
        }
        count
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

fn winnow_err_to_parse_error(err: ErrMode<ContextError>, fallback_span: Span) -> ParseError {
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
fn winnow_backtrack<O>() -> PResult<O> {
    Err(ErrMode::Backtrack(ContextError::new()))
}

/// Helper to produce an incomplete input error (REPL should prompt for more).
#[allow(dead_code)]
fn winnow_incomplete<O>() -> PResult<O> {
    Err(ErrMode::Incomplete(Needed::Unknown))
}

/// Helper to produce an incomplete token error (mid-token EOF).
///
/// Unlike `winnow_incomplete`, this indicates the input ended in the middle
/// of a token (e.g., `#\`, `1e+`, `3/`). In a REPL, this is typically a user
/// error rather than a prompt-for-more signal.
fn winnow_incomplete_token<O>() -> PResult<O> {
    let mut ctx = ContextError::new();
    ctx.push(StrContext::Label(INCOMPLETE_TOKEN_LABEL));
    Err(ErrMode::Cut(ctx))
}

/// Wraps a parser to convert Backtrack errors into Cut errors with a specific label.
/// If the input is empty (EOF), it returns the special IncompleteToken error instead.
fn cut_lex_error_token<'i, O, P>(
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
fn lex_error<O>(nonterminal: &'static str) -> PResult<O> {
    let mut ctx = ContextError::new();
    ctx.push(StrContext::Label(nonterminal));
    Err(ErrMode::Cut(ctx))
}

/// Parse `+i` or `-i` (unit imaginary), returning the sign character on success.
///
/// Grammar reference (spec/syn.md, `<complex R>` production):
///
/// ```text
/// <complex R> ::= ...
///               | + i
///               | - i
///               | <real R> + i
///               | <real R> - i
///               | ...
/// ```
///
/// This helper handles the `+ i` / `- i` suffix in those productions, used:
/// 1. After parsing a real part: `<real R> + i` or `<real R> - i`
/// 2. Standalone: `+ i` or `- i` (with implicit zero real part)
///
/// On success, consumes the sign and `i` characters and returns the sign.
/// On failure (not `+i`/`-i`), returns `None` without consuming input.
fn try_parse_unit_imaginary<'i>(input: &mut WinnowInput<'i>) -> PResult<Option<char>> {
    let mut probe = *input;
    let Some(sign_ch) = probe.eat_if(|c| c == '+' || c == '-') else {
        return Ok(None);
    };
    if probe.eat_if(|c| c == 'i' || c == 'I').is_some() {
        ensure_delimiter(&mut probe, "<number>")?;
        *input = probe;
        Ok(Some(sign_ch))
    } else {
        Ok(None)
    }
}

/// Canonical `<suffix>` parser for decimal numbers.
///
/// Grammar reference (Formal syntax / `<number>`):
///
/// ```text
/// <suffix> ::= <empty>
///            | <exponent marker> <sign> <digit 10>+
///
/// <exponent marker> ::= e
///
/// <sign> ::= <empty> | + | -
/// ```
///
/// This helper appends the matched suffix text (if any) to `text`.
/// Returns `Ok(())` if no exponent marker is present (the `<empty>` case)
/// or if a complete exponent suffix was parsed successfully.
fn parse_exponent_suffix<'i>(input: &mut WinnowInput<'i>, text: &mut String) -> PResult<()> {
    let Some(e) = input.eat_if(|c| c == 'e' || c == 'E') else {
        return Ok(());
    };
    text.push(e);

    let sign_or_digit = input.peek_or_incomplete_token()?;
    if sign_or_digit == '+' || sign_or_digit == '-' {
        text.push(sign_or_digit);
        let _ = input.next_token();
        let _ = input.peek_or_incomplete_token()?;
    }

    if input.eat_while(text, |c| c.is_ascii_digit()) == 0 {
        return winnow_incomplete_token();
    }

    Ok(())
}

/// Lexical tokens as defined by `<token>` in `spec/syn.md`.
///
/// Grammar reference (Formal syntax / Lexical structure):
///
/// ```text
/// <token> ::= <identifier> | <boolean> | <number>
///           | <character> | <string>
///           | ( | ) | #( | #u8( | ' | ` | , | ,@ | .
/// ```
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
    /// Note: This is a deviation from R7RS, which treats `#; <datum>` as
    /// intertoken space. Since the lexer cannot parse `<datum>`, it yields
    /// this token so the parser can perform the skipping.
    DatumComment,
}

/// A single token paired with its source span.
pub type SpannedToken = Syntax<Token>;

/// Lex all `<token>`s from the given source string, skipping
/// `<intertoken space>` (whitespace, comments, nested comments,
/// and directives).
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
///
/// For now, `lex` implements `<intertoken space>` and a subset of
/// `<token>` recognition: inputs that contain only intertoken space
/// yield an empty token list. We are gradually adding `<token>`
/// classifications, currently `<boolean>`, `<character>`, `<string>`, and `<number>`.
pub fn lex(source: &str) -> Result<Vec<SpannedToken>, ParseError> {
    lex_winnow(source)
}
/// Canonical `<intertoken space>` parser using `winnow`.
///
/// This parser consumes zero or more `<atmosphere>` elements:
/// whitespace, line comments, nested comments, and directives.
///
/// Uses a manual loop for efficiency with `take_while` for the fast paths.
fn lex_intertoken<'i>(input: &mut WinnowInput<'i>) -> PResult<()> {
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

/// Parse a directive word after `#!` has been consumed.
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

/// Canonical punctuation parser using `winnow`.
fn lex_punctuation<'i>(input: &mut WinnowInput<'i>) -> PResult<SpannedToken> {
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
            let _ = input.next_token();
            match input.peek_token() {
                Some('(') => {
                    let _ = input.next_token();
                    Token::VectorStart
                }
                Some('u' | 'U') => {
                    let _ = input.next_token();
                    if input.eat('8') && input.eat('(') {
                        Token::ByteVectorStart
                    } else {
                        return winnow_backtrack();
                    }
                }
                _ => {
                    // Let other `#`-prefixed tokens handle this.
                    return winnow_backtrack();
                }
            }
        }
        '.' => {
            // If `.` is followed by a digit, treat this as the
            // start of a decimal number and let the numeric
            // lexers claim it instead of producing a `.` token.
            let mut probe = *input;
            let _ = probe.next_token(); // consume '.'
            if probe.peek_token().is_some_and(|c| c.is_ascii_digit()) {
                return winnow_backtrack();
            }

            let _ = input.next_token();
            Token::Dot
        }
        _ => return winnow_backtrack(),
    };

    let end = input.current_token_start();
    Ok(Syntax::new(Span { start, end }, token))
}

/// Lex a single token using a `WinnowInput`, returning `Ok(None)` at EOF.
/// This driver now uses the canonical `lex_*` parsers directly.
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
                    Ok(Some(Syntax::new(span, Token::Number(literal))))
                }
                Err(ErrMode::Backtrack(_)) => {
                    // Not a `<number>` starting here; leave to other
                    // token classes (identifiers, etc.) once implemented.
                    Err(ParseError::Unimplemented)
                }
                Err(ErrMode::Incomplete(_)) => Err(ParseError::Incomplete),
                Err(e) => Err(winnow_err_to_parse_error(e, fallback_span)),
            }
        }
        _ => {
            // Other token classes (identifiers, etc.) are not yet implemented.
            Err(ParseError::Unimplemented)
        }
    }
}

/// `winnow`-driven lexer entry point used by `lex`.
fn lex_winnow(source: &str) -> Result<Vec<SpannedToken>, ParseError> {
    let mut tokens = Vec::new();
    let mut input = WinnowInput::new(source);

    // R7RS-DEVIATION: We recognize `#!fold-case` / `#!no-fold-case`
    // directives lexically (and validate them), but deliberately
    // ignore their semantics. This keeps the reader case-sensitive
    // with ASCII-only identifiers, erring on the side of rejecting
    // some valid programs rather than accepting invalid ones.

    while let Some(token) = token_with_span(&mut input, source)? {
        tokens.push(token);
    }

    Ok(tokens)
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

/// True if `ch` is a `<delimiter>` character.
///
/// Grammar reference:
///
/// ```text
/// <delimiter> ::= <whitespace> | <vertical line>
///               | ( | ) | " | ;
/// ```
fn is_delimiter(ch: char) -> bool {
    matches!(ch, ' ' | '\t' | '\n' | '\r' | '|' | '(' | ')' | '"' | ';')
}

/// Ensure the next character is a delimiter (or EOF).
///
/// Many tokens in Scheme must be followed by a delimiter. This helper
/// checks that condition and returns an error with the given nonterminal
/// label if violated.
#[inline]
fn ensure_delimiter<'i>(input: &mut WinnowInput<'i>, nonterminal: &'static str) -> PResult<()> {
    if input.peek_token().is_some_and(|ch| !is_delimiter(ch)) {
        return lex_error(nonterminal);
    }
    Ok(())
}

/// Create an integer `RealRepr` from a spelling string.
fn int_repr(spelling: &str) -> RealRepr {
    RealRepr::Finite(FiniteRealRepr::Integer {
        spelling: spelling.to_string(),
    })
}

/// Look up a named character (case-insensitive).
fn named_character(name: &str) -> Option<char> {
    Some(match () {
        _ if name.eq_ignore_ascii_case("alarm") => '\u{7}',
        _ if name.eq_ignore_ascii_case("backspace") => '\u{8}',
        _ if name.eq_ignore_ascii_case("delete") => '\u{7F}',
        _ if name.eq_ignore_ascii_case("escape") => '\u{1B}',
        _ if name.eq_ignore_ascii_case("newline") => '\n',
        _ if name.eq_ignore_ascii_case("null") => '\0',
        _ if name.eq_ignore_ascii_case("return") => '\r',
        _ if name.eq_ignore_ascii_case("space") => ' ',
        _ if name.eq_ignore_ascii_case("tab") => '\t',
        _ => return None,
    })
}

/// Canonical `<infnan>` parser using `winnow`.
///
/// Grammar reference (Formal syntax / `<number>`):
///
/// ```text
/// <infnan> ::= +inf.0 | -inf.0 | +nan.0 | -nan.0
/// ```
///
/// Alphabetic characters are treated case-insensitively. Any mismatch or
/// incomplete spelling results in a recoverable backtrack so other number
/// forms can claim the input.
fn lex_infnan<'i>(input: &mut WinnowInput<'i>) -> PResult<InfinityNan> {
    alt((
        Caseless("+inf.0").value(InfinityNan::PositiveInfinity),
        Caseless("-inf.0").value(InfinityNan::NegativeInfinity),
        Caseless("+nan.0").value(InfinityNan::PositiveNaN),
        Caseless("-nan.0").value(InfinityNan::NegativeNaN),
    ))
    .parse_next(input)
}

/// Parse `<sign> <ureal R>` for a given radix.
///
/// Grammar reference (Formal syntax / `<number>`):
///
/// ```text
/// <real R> ::= <sign> <ureal R>
///            | <infnan>
///
/// <sign> ::= <empty> | + | -
/// ```
///
/// This parses an optional sign followed by `<ureal R>` via `lex_ureal`.
fn lex_sign_ureal_for_radix<'i>(
    input: &mut WinnowInput<'i>,
    radix: NumberRadix,
) -> PResult<FiniteRealRepr> {
    let mut probe = *input;
    let sign = probe.eat_if(|ch| ch == '+' || ch == '-');

    match lex_ureal(&mut probe, radix) {
        Ok(mut finite) => {
            if let Some(s) = sign {
                match &mut finite {
                    FiniteRealRepr::Integer { spelling }
                    | FiniteRealRepr::Rational { spelling }
                    | FiniteRealRepr::Decimal { spelling } => {
                        spelling.insert(0, s);
                    }
                }
            }
            *input = probe;
            Ok(finite)
        }
        Err(e) => Err(e),
    }
}

/// Canonical `<real R>` parser using `winnow`.
///
/// Grammar reference (Formal syntax / `<number>`):
///
/// ```text
/// <real R> ::= <sign> <ureal R>
///            | <infnan>
/// ```
///
/// This first tries `<infnan>` via `lex_infnan` and, on backtrack,
/// falls back to `<sign> <ureal R>` via `lex_sign_ureal_for_radix`.
fn lex_real_repr<'i>(input: &mut WinnowInput<'i>, radix: NumberRadix) -> PResult<RealRepr> {
    let start_state = *input;

    // Try `<infnan>` first.
    match lex_infnan(input) {
        Ok(infnan) => return Ok(RealRepr::Infnan(infnan)),
        Err(ErrMode::Backtrack(_)) => {
            // Not an `<infnan>`; reset and try `<sign> <ureal R>`.
            *input = start_state;
        }
        Err(e) => return Err(e),
    }

    // `<sign> <ureal R>`.
    lex_sign_ureal_for_radix(input, radix).map(RealRepr::Finite)
}

/// Canonical `<complex R>` / `<real R>` parser using `winnow`.
///
/// This implements the R7RS number grammar for a fixed radix `R`,
/// including real, rectangular, polar, and pure-imaginary cases:
///
/// ```text
/// <number>   ::= <num 2> | <num 8>
///              | <num 10> | <num 16>
/// <num R>    ::= <prefix R> <complex R>
///
/// <complex R> ::= <real R>
///                | <real R> @ <real R>
///                | <real R> + <ureal R> i
///                | <real R> - <ureal R> i
///                | <real R> + i
///                | <real R> - i
///                | <real R> <infnan> i
///                | + <ureal R> i
///                | - <ureal R> i
///                | <infnan> i
///                | + i
///                | - i
///
/// <real R> ::= <sign> <ureal R>
///            | <infnan>
/// ```
///
/// The `<ureal R>` production is implemented by `lex_ureal`, which
/// handles all radixes uniformly (with decimal-specific forms like
/// `.digits` and exponents enabled only for radix 10).
fn lex_complex_with_radix<'i>(
    input: &mut WinnowInput<'i>,
    radix: NumberRadix,
    exactness: NumberExactness,
) -> PResult<NumberLiteral> {
    let start_state = *input;

    // Helper to construct NumberLiteral with the current radix and exactness.
    let make_literal = |value: NumberValue| {
        NumberLiteralKind {
            radix,
            exactness,
            value,
        }
        .into_literal()
    };

    // 1. Try to parse the first component as `<real R>`.
    match lex_real_repr(input, radix) {
        Ok(repr1) => {
            // End of input or delimiter after `<real R>`: it's a real number.
            let next_ch = match input.peek_token() {
                None => return Ok(make_literal(NumberValue::Real(repr1))),
                Some(ch) if is_delimiter(ch) => return Ok(make_literal(NumberValue::Real(repr1))),
                Some(ch) => ch,
            };

            match next_ch {
                'i' | 'I' => {
                    // Pure imaginary: `<real R> i`.
                    let mut probe = *input;
                    let _ = probe.next_token(); // consume 'i' / 'I'
                    ensure_delimiter(&mut probe, "<number>")?;

                    *input = probe;
                    return Ok(make_literal(NumberValue::Rectangular {
                        real: int_repr("0"),
                        imag: repr1,
                    }));
                }
                '@' => {
                    // Polar: `<real R> @ <real R>`.
                    let mut probe = *input;
                    let _ = probe.next_token(); // consume '@'
                    let repr2 =
                        cut_lex_error_token(|i: &mut _| lex_real_repr(i, radix), "<number>")
                            .parse_next(&mut probe)?;

                    ensure_delimiter(&mut probe, "<number>")?;
                    *input = probe;
                    return Ok(make_literal(NumberValue::Polar {
                        magnitude: repr1,
                        angle: repr2,
                    }));
                }
                '+' | '-' => {
                    // Rectangular: `<real R> +/- <ureal R> i` or `<real R> +/- i`.
                    let mut probe = *input;
                    match lex_real_repr(&mut probe, radix) {
                        Ok(repr2) => {
                            cut_lex_error_token(alt(('i', 'I')), "<number>").parse_next(&mut probe)?;
                            ensure_delimiter(&mut probe, "<number>")?;
                            *input = probe;
                            return Ok(make_literal(NumberValue::Rectangular {
                                real: repr1,
                                imag: repr2,
                            }));
                        }
                        Err(ErrMode::Backtrack(_)) => {
                            // Fall back to `+i` / `-i` (implicit 1).
                            if let Some(sign_ch) = try_parse_unit_imaginary(&mut probe)? {
                                let imag = int_repr(if sign_ch == '-' { "-1" } else { "1" });
                                *input = probe;
                                return Ok(make_literal(NumberValue::Rectangular {
                                    real: repr1,
                                    imag,
                                }));
                            }
                            return lex_error("<number>");
                        }
                        Err(e) => return Err(e),
                    }
                }
                _ => {
                    // Some other character after `<real R>`.
                    return lex_error("<number>");
                }
            }
        }
        Err(ErrMode::Backtrack(_)) => {
            // No `<real R>` here; reset and try `+i` / `-i` (unit imaginary).
            *input = start_state;
        }
        Err(e) => return Err(e),
    }

    // Handle `+i` / `-i` without an explicit real part.
    if let Some(sign_ch) = try_parse_unit_imaginary(input)? {
        let imag = int_repr(if sign_ch == '-' { "-1" } else { "1" });
        return Ok(make_literal(NumberValue::Rectangular {
            real: int_repr("0"),
            imag,
        }));
    }

    winnow_backtrack()
}

/// Canonical `<number>` parser for decimal radix (`<num 10>`).
///
/// This is a thin wrapper around `lex_complex_with_radix` with
/// `R = 10` and unspecified exactness.
fn lex_complex_decimal<'i>(input: &mut WinnowInput<'i>) -> PResult<NumberLiteral> {
    lex_complex_with_radix(input, NumberRadix::Decimal, NumberExactness::Unspecified)
}

/// Canonical `<number>` parser for prefixed numbers.
///
/// Grammar reference (Formal syntax / `<number>`):
///
/// ```text
/// <number> ::= <num 2> | <num 8>
///            | <num 10> | <num 16>
///
/// <num R> ::= <prefix R> <complex R>
///
/// <prefix R> ::= <radix R> <exactness>
///              | <exactness> <radix R>
///
/// <exactness> ::= <empty> | #i | #e
///
/// <radix 2> ::= #b
/// <radix 8> ::= #o
/// <radix 10> ::= <empty> | #d
/// <radix 16> ::= #x
/// ```
///
/// This helper parses one or more radix/exactness prefixes and then
/// delegates to `lex_complex_with_radix` for the `<complex R>` part.
fn lex_prefixed_number<'i>(input: &mut WinnowInput<'i>) -> PResult<NumberLiteral> {
    let mut probe = *input;

    let mut radix: Option<NumberRadix> = None;
    let mut exactness: Option<NumberExactness> = None;
    let mut saw_prefix = false;

    while probe.peek_token() == Some('#') {
        let _ = probe.next_token(); // consume '#'
        let after_hash = match probe.peek_token() {
            Some(c) => c,
            None => {
                if radix.is_some() || exactness.is_some() {
                    // Already saw a prefix like `#b`, then another `#` at EOF.
                    return winnow_incomplete_token();
                } else {
                    return winnow_backtrack();
                }
            }
        };

        saw_prefix = true;
        let lower = after_hash.to_ascii_lowercase();
        let _ = probe.next_token(); // consume the prefix character

        match lower {
            'b' | 'o' | 'd' | 'x' => {
                if radix.is_some() {
                    return lex_error("<number>");
                }
                radix = Some(match lower {
                    'b' => NumberRadix::Binary,
                    'o' => NumberRadix::Octal,
                    'd' => NumberRadix::Decimal,
                    'x' => NumberRadix::Hexadecimal,
                    _ => return lex_error("<number>"),
                });
            }
            'e' | 'i' => {
                if exactness.is_some() {
                    return lex_error("<number>");
                }
                exactness = Some(match lower {
                    'e' => NumberExactness::Exact,
                    'i' => NumberExactness::Inexact,
                    _ => return lex_error("<number>"),
                });
            }
            _ => {
                if radix.is_some() || exactness.is_some() {
                    return lex_error("<number>");
                } else {
                    return winnow_backtrack();
                }
            }
        }
    }

    if !saw_prefix {
        return winnow_backtrack();
    }

    let radix_value = radix.unwrap_or(NumberRadix::Decimal);
    let exactness_value = exactness.unwrap_or(NumberExactness::Unspecified);

    let _ = probe.peek_or_incomplete_token()?;

    match lex_complex_with_radix(&mut probe, radix_value, exactness_value) {
        Ok(literal) => {
            *input = probe;
            Ok(literal)
        }
        Err(e) => Err(e),
    }
}

/// Canonical `<string element>` parser used by `<string>`.
///
/// Grammar reference (Formal syntax / `<string>`):
///
/// ```text
/// <string> ::= " <string element>* "
///
/// <string element> ::= any character other than " or \
///                     | <mnemonic escape> | \" | \\
///                     | \ <intraline whitespace>* <line ending>
///                       <intraline whitespace>*
///                     | <inline hex escape>
/// ```
///
/// This function assumes the opening `"` has already been consumed
/// and stops just before the closing `"`.
fn lex_string_body<'i>(input: &mut WinnowInput<'i>) -> PResult<String> {
    let mut result = String::new();

    loop {
        // Fast path: consume literal text.
        // Strings cannot contain raw newlines, so we stop at them too.
        let chunk: &str = take_while(0.., |c| c != '"' && c != '\\' && c != '\n' && c != '\r')
            .parse_next(input)?;
        result.push_str(chunk);

        match input.peek_or_incomplete()? {
            '"' => break,
            '\\' => {
                let _ = input.next_token();
                if let Some(c) = lex_string_escape(input)? {
                    result.push(c);
                }
            }
            '\n' | '\r' => return lex_error("<string>"),
            _ => unreachable!("take_while stops at quote, backslash, or newline"),
        }
    }

    Ok(result)
}

/// Parse the body of a hex escape sequence: `<hex digits>;`.
/// The leading `x` has already been consumed.
fn lex_hex_escape<'i>(input: &mut WinnowInput<'i>) -> PResult<char> {
    let digits = cut_lex_error_token(hex_digit1, "<string>").parse_next(input)?;
    let _ = cut_lex_error_token(';', "<string>").parse_next(input)?;

    let codepoint = u32::from_str_radix(digits, 16).map_err(|_| {
        // This should be rare given hex_digit1, but handles overflow
        let mut ctx = ContextError::new();
        ctx.push(StrContext::Label("<string>"));
        ErrMode::Cut(ctx)
    })?;

    char::from_u32(codepoint).ok_or_else(|| {
        // Invalid unicode scalar value
        let mut ctx = ContextError::new();
        ctx.push(StrContext::Label("<string>"));
        ErrMode::Cut(ctx)
    })
}

/// Parse a line splice: `\ <ws> <line ending> <ws>`.
fn lex_line_splice<'i>(input: &mut WinnowInput<'i>) -> PResult<()> {
    let _: &str = space0.parse_next(input)?;
    let _: &str = line_ending.parse_next(input)?;
    let _: &str = space0.parse_next(input)?;
    Ok(())
}

/// Parse a single string escape sequence (after the backslash).
fn lex_string_escape<'i>(input: &mut WinnowInput<'i>) -> PResult<Option<char>> {
    alt((
        // Hex escape: \x...;
        preceded(alt(('x', 'X')), lex_hex_escape).map(Some),
        // Line splice: \ ... \n ... (contributes nothing to string)
        lex_line_splice.map(|_| None),
        // Simple escapes
        alt((
            'a'.value(Some('\u{7}')),
            'b'.value(Some('\u{8}')),
            't'.value(Some('\t')),
            'n'.value(Some('\n')),
            'r'.value(Some('\r')),
            '"'.value(Some('"')),
            '\\'.value(Some('\\')),
        )),
    ))
    .parse_next(input)
}

/// Canonical `<string>` parser using `winnow`.
///
/// Grammar reference (Formal syntax / `<string>`):
///
/// ```text
/// <string> ::= " <string element>* "
/// ```
///
/// The `<string element>` production itself is implemented by
/// `lex_string_body`.
fn lex_string<'i>(input: &mut WinnowInput<'i>) -> PResult<SpannedToken> {
    let start = input.current_token_start();

    if !input.eat('"') {
        return winnow_backtrack();
    }

    let value = lex_string_body(input)?;

    match input.next_token() {
        Some('"') => {}
        None => return winnow_incomplete(),
        _ => return lex_error("<string>"),
    }

    let end = input.current_token_start();
    Ok(Syntax::new(Span { start, end }, Token::String(value)))
}

/// Canonical `<character>` parser using `winnow`.
///
/// Grammar reference (Formal syntax / `<character>`):
///
/// ```text
/// <character> ::= #\ <any character>
///               | #\ <character name>
///               | #\x<hex scalar value>
///
/// <character name> ::= alarm | backspace | delete
///                    | escape | newline | null | return | space | tab
/// ```
///
/// This helper accepts the R7RS named characters and `#\x` hex
/// scalar values and reports lexical errors using the `<character>`
/// nonterminal.
fn lex_character<'i>(input: &mut WinnowInput<'i>) -> PResult<SpannedToken> {
    let start = input.current_token_start();

    // Expect leading "#\" prefix using lookahead so that we don't
    // consume input on mismatch (for example, `#t` / `#f` booleans).
    let mut probe = *input;
    match (probe.next_token(), probe.peek_token()) {
        (Some('#'), Some('\\')) => {
            // Commit the prefix on the real input.
            let _ = input.next_token();
            let _ = input.next_token();
        }
        // `#` at end-of-input followed by missing `\\` is an
        // incomplete `<character>` token.
        (Some('#'), None) => return winnow_incomplete_token(),
        _ => return winnow_backtrack(),
    }

    // At least one character must follow `#\`.
    let c1 = input.next_or_incomplete_token()?;

    let value_char = if c1.eq_ignore_ascii_case(&'x') {
        // Potential `#\x<hex scalar value>` form.
        let mut probe = *input;
        if let Ok(digits) = hex_digit1::<_, ContextError>.parse_next(&mut probe) {
            let Some(codepoint) = u32::from_str_radix(digits, 16)
                .ok()
                .and_then(char::from_u32)
            else {
                return lex_error("<character>");
            };
            *input = probe;
            codepoint
        } else {
            c1 // No hex digits: literal 'x' / 'X'
        }
    } else if c1.is_ascii_alphabetic() {
        // Possible named character like `space`, `newline`, etc.
        let mut name = String::new();
        name.push(c1);
        input.eat_while(&mut name, |c| c.is_ascii_alphabetic());

        if name.len() == c1.len_utf8() {
            c1 // Single alphabetic character like `#\a`
        } else {
            match named_character(&name) {
                Some(ch) => ch,
                None => return lex_error("<character>"),
            }
        }
    } else {
        c1 // Any other single character after `#\`
    };

    // Enforce delimiter after the `<character>` token.
    ensure_delimiter(input, "<character>")?;

    let end = input.current_token_start();
    Ok(Syntax::new(
        Span { start, end },
        Token::Character(value_char),
    ))
}

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
fn lex_boolean<'i>(input: &mut WinnowInput<'i>) -> PResult<SpannedToken> {
    let start = input.current_token_start();

    // Use a probing cursor so that we only commit to a `<boolean>`
    // token when the full spelling matches `#t`, `#f`, `#true`, or
    // `#false` with a proper delimiter. On mismatch, we backtrack
    // without consuming any input so other `#`-prefixed token kinds
    // can claim the sequence.
    let mut probe = *input;

    let value = match alt::<_, _, ContextError, _>((
        Caseless("#true").value(true),
        Caseless("#false").value(false),
        Caseless("#t").value(true),
        Caseless("#f").value(false),
    ))
    .parse_next(&mut probe)
    {
        Ok(v) => v,
        Err(_) => return winnow_backtrack(),
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

/// Canonical `<ureal R>` parser using `winnow`.
///
/// Grammar reference (Formal syntax / `<number>`):
///
/// ```text
/// <ureal R> ::= <uinteger R>
///              | <uinteger R> / <uinteger R>
///              | <decimal R>
///
/// <decimal 10> ::= <uinteger 10> <suffix>
///                 | . <digit 10>+ <suffix>
///                 | <digit 10>+ . <digit 10>* <suffix>
/// ```
///
/// Note: There are no `<decimal 2>`, `<decimal 8>`, or `<decimal 16>`
/// productions, so decimal points and exponents are only valid for
/// radix 10. This function handles all radixes uniformly, with the
/// decimal-specific forms enabled only when `radix == Decimal`.
fn lex_ureal<'i>(input: &mut WinnowInput<'i>, radix: NumberRadix) -> PResult<FiniteRealRepr> {
    let mut probe = *input;
    let mut text = String::new();
    let is_decimal = radix == NumberRadix::Decimal;

    let first = probe.peek_or_backtrack()?;

    // Decimal-only: `.digits+` form (e.g., `.5`, `.123e4`).
    if is_decimal && first == '.' {
        text.push(first);
        let _ = probe.next_token();

        if probe.peek_token().is_none() {
            return winnow_backtrack();
        }

        let saw_digit = probe.eat_while(&mut text, |c| c.is_ascii_digit()) > 0;
        if !saw_digit {
            return winnow_backtrack();
        }

        parse_exponent_suffix(&mut probe, &mut text)?;

        *input = probe;
        return Ok(FiniteRealRepr::Decimal { spelling: text });
    }

    // Common case: starts with digit(s).
    let saw_digit = probe.eat_while(&mut text, |c| is_digit_for_radix(c, radix)) > 0;
    if !saw_digit {
        return winnow_backtrack();
    }

    // Check what follows the integer part.
    match probe.peek_token() {
        // Rational: `<uinteger R> / <uinteger R>` (all radixes).
        Some('/') => {
            text.push('/');
            let _ = probe.next_token();

            let digits = cut_lex_error_token(
                take_while(1.., |c| is_digit_for_radix(c, radix)),
                "<number>",
            )
            .parse_next(&mut probe)?;
            text.push_str(digits);

            *input = probe;
            Ok(FiniteRealRepr::Rational { spelling: text })
        }

        // Decimal-only: `digits.digits*` with optional exponent.
        Some('.') if is_decimal => {
            text.push('.');
            let _ = probe.next_token();
            probe.eat_while(&mut text, |c| c.is_ascii_digit());
            parse_exponent_suffix(&mut probe, &mut text)?;

            *input = probe;
            Ok(FiniteRealRepr::Decimal { spelling: text })
        }

        // Decimal-only: integer with exponent (e.g., `1e10`).
        Some('e' | 'E') if is_decimal => {
            parse_exponent_suffix(&mut probe, &mut text)?;

            *input = probe;
            Ok(FiniteRealRepr::Decimal { spelling: text })
        }

        // Plain integer.
        _ => {
            *input = probe;
            Ok(FiniteRealRepr::Integer { spelling: text })
        }
    }
}

fn is_digit_for_radix(ch: char, radix: NumberRadix) -> bool {
    match radix {
        NumberRadix::Binary => matches!(ch, '0' | '1'),
        NumberRadix::Octal => matches!(ch, '0'..='7'),
        NumberRadix::Decimal => ch.is_ascii_digit(),
        NumberRadix::Hexadecimal => ch.is_ascii_hexdigit(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // --- Test Infrastructure ---

    struct TestCase {
        name: &'static str,
        input: &'static str,
        expected: Expected,
    }

    enum Expected {
        Tokens(Vec<TokenMatcher>),
        Error(ErrorMatcher),
        Empty,
    }

    enum ErrorMatcher {
        Unimplemented,
        Incomplete,
        IncompleteToken,
        Lex(&'static str), // nonterminal
    }

    enum TokenMatcher {
        Bool(bool),
        Char(char),
        Str(&'static str),
        LParen,
        RParen,
        Quote,
        Backquote,
        Comma,
        CommaAt,
        Dot,
        VectorStart,
        ByteVectorStart,
        Num(&'static str, NumCheck),
    }

    enum NumCheck {
        Any, // Just check text
        Int(&'static str),
        Dec(&'static str),
        Rat(&'static str),
        RectInt(&'static str, &'static str), // real int, imag int
        RectRat(&'static str, &'static str), // real int, imag rat
        PolarInt(&'static str, &'static str), // mag int, ang int
        PolarRatDec(&'static str, &'static str), // mag rat, ang dec
        Inf(InfinityNan),
        RectInfImag(&'static str, InfinityNan), // real int, imag inf

        // Wrappers
        Exact(Box<NumCheck>),
        Inexact(Box<NumCheck>),
        Radix(NumberRadix, Box<NumCheck>),
    }

    impl TestCase {
        fn run(&self) {
            let result = lex(self.input);
            match &self.expected {
                Expected::Tokens(expected_tokens) => {
                    let tokens = result.unwrap_or_else(|e| {
                        panic!("{}: expected tokens, got error {:?}", self.name, e)
                    });
                    assert_eq!(
                        tokens.len(),
                        expected_tokens.len(),
                        "{}: token count mismatch",
                        self.name
                    );
                    for (i, (tok, matcher)) in tokens.iter().zip(expected_tokens.iter()).enumerate()
                    {
                        matcher.check(&tok.value, self.name, i);
                    }
                }
                Expected::Error(matcher) => {
                    let err =
                        result.expect_err(&format!("{}: expected error, got tokens", self.name));
                    matcher.check(&err, self.name);
                }
                Expected::Empty => {
                    let tokens = result.unwrap_or_else(|e| {
                        panic!("{}: expected success, got error {:?}", self.name, e)
                    });
                    assert!(tokens.is_empty(), "{}: expected empty tokens", self.name);
                }
            }
        }
    }

    impl ErrorMatcher {
        fn check(&self, err: &ParseError, test_name: &str) {
            match (self, err) {
                (ErrorMatcher::Unimplemented, ParseError::Unimplemented) => {}
                (ErrorMatcher::Incomplete, ParseError::Incomplete) => {}
                (ErrorMatcher::IncompleteToken, ParseError::IncompleteToken) => {}
                (ErrorMatcher::Lex(nt), ParseError::Lex { nonterminal, .. }) => {
                    assert_eq!(nt, nonterminal, "{}: error nonterminal mismatch", test_name);
                }
                _ => panic!(
                    "{}: error mismatch. Expected {:?}, got {:?}",
                    test_name, self, err
                ),
            }
        }
    }

    impl std::fmt::Debug for ErrorMatcher {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                Self::Unimplemented => write!(f, "Unimplemented"),
                Self::Incomplete => write!(f, "Incomplete"),
                Self::IncompleteToken => write!(f, "IncompleteToken"),
                Self::Lex(arg0) => f.debug_tuple("Lex").field(arg0).finish(),
            }
        }
    }

    impl TokenMatcher {
        fn check(&self, token: &Token, test_name: &str, index: usize) {
            match (self, token) {
                (TokenMatcher::Bool(e), Token::Boolean(a)) => {
                    assert_eq!(e, a, "{}: token {} mismatch", test_name, index)
                }
                (TokenMatcher::Char(e), Token::Character(a)) => {
                    assert_eq!(e, a, "{}: token {} mismatch", test_name, index)
                }
                (TokenMatcher::Str(e), Token::String(a)) => {
                    assert_eq!(e, a, "{}: token {} mismatch", test_name, index)
                }
                (TokenMatcher::LParen, Token::LParen) => {}
                (TokenMatcher::RParen, Token::RParen) => {}
                (TokenMatcher::Quote, Token::Quote) => {}
                (TokenMatcher::Backquote, Token::Backquote) => {}
                (TokenMatcher::Comma, Token::Comma) => {}
                (TokenMatcher::CommaAt, Token::CommaAt) => {}
                (TokenMatcher::Dot, Token::Dot) => {}
                (TokenMatcher::VectorStart, Token::VectorStart) => {}
                (TokenMatcher::ByteVectorStart, Token::ByteVectorStart) => {}
                (TokenMatcher::Num(text, check), Token::Number(n)) => {
                    assert_eq!(
                        text, &n.text,
                        "{}: token {} text mismatch",
                        test_name, index
                    );
                    check.verify(&n.kind, test_name, index);
                }
                _ => panic!(
                    "{}: token {} type mismatch. Expected {:?}, got {:?}",
                    test_name, index, self, token
                ),
            }
        }
    }

    impl std::fmt::Debug for TokenMatcher {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                Self::Bool(b) => f.debug_tuple("Bool").field(b).finish(),
                Self::Char(c) => f.debug_tuple("Char").field(c).finish(),
                Self::Str(s) => f.debug_tuple("Str").field(s).finish(),
                Self::LParen => write!(f, "LParen"),
                Self::RParen => write!(f, "RParen"),
                Self::Quote => write!(f, "Quote"),
                Self::Backquote => write!(f, "Backquote"),
                Self::Comma => write!(f, "Comma"),
                Self::CommaAt => write!(f, "CommaAt"),
                Self::Dot => write!(f, "Dot"),
                Self::VectorStart => write!(f, "VectorStart"),
                Self::ByteVectorStart => write!(f, "ByteVectorStart"),
                Self::Num(s, _) => f.debug_tuple("Num").field(s).finish(),
            }
        }
    }

    impl NumCheck {
        fn verify(&self, kind: &NumberLiteralKind, test_name: &str, index: usize) {
            match self {
                NumCheck::Any => {}
                NumCheck::Int(s) => {
                    if let NumberValue::Real(RealRepr::Finite(FiniteRealRepr::Integer {
                        spelling,
                    })) = &kind.value
                    {
                        assert_eq!(
                            spelling, s,
                            "{}: token {} integer spelling mismatch",
                            test_name, index
                        );
                    } else {
                        panic!(
                            "{}: token {} expected Integer, got {:?}",
                            test_name, index, kind
                        );
                    }
                }
                NumCheck::Dec(s) => {
                    if let NumberValue::Real(RealRepr::Finite(FiniteRealRepr::Decimal {
                        spelling,
                    })) = &kind.value
                    {
                        assert_eq!(
                            spelling, s,
                            "{}: token {} decimal spelling mismatch",
                            test_name, index
                        );
                    } else {
                        panic!(
                            "{}: token {} expected Decimal, got {:?}",
                            test_name, index, kind
                        );
                    }
                }
                NumCheck::Rat(s) => {
                    if let NumberValue::Real(RealRepr::Finite(FiniteRealRepr::Rational {
                        spelling,
                    })) = &kind.value
                    {
                        assert_eq!(
                            spelling, s,
                            "{}: token {} rational spelling mismatch",
                            test_name, index
                        );
                    } else {
                        panic!(
                            "{}: token {} expected Rational, got {:?}",
                            test_name, index, kind
                        );
                    }
                }
                NumCheck::RectInt(r, i) => {
                    if let NumberValue::Rectangular { real, imag } = &kind.value {
                        match real {
                            RealRepr::Finite(FiniteRealRepr::Integer { spelling }) => {
                                assert_eq!(spelling, r)
                            }
                            _ => {
                                panic!("{}: token {} expected Integer real part", test_name, index)
                            }
                        }
                        match imag {
                            RealRepr::Finite(FiniteRealRepr::Integer { spelling }) => {
                                assert_eq!(spelling, i)
                            }
                            _ => {
                                panic!("{}: token {} expected Integer imag part", test_name, index)
                            }
                        }
                    } else {
                        panic!("{}: token {} expected Rectangular", test_name, index);
                    }
                }
                NumCheck::RectRat(r, i) => {
                    if let NumberValue::Rectangular { real, imag } = &kind.value {
                        match real {
                            RealRepr::Finite(FiniteRealRepr::Integer { spelling }) => {
                                assert_eq!(spelling, r)
                            }
                            _ => {
                                panic!("{}: token {} expected Integer real part", test_name, index)
                            }
                        }
                        match imag {
                            RealRepr::Finite(FiniteRealRepr::Rational { spelling }) => {
                                assert_eq!(spelling, i)
                            }
                            _ => {
                                panic!("{}: token {} expected Rational imag part", test_name, index)
                            }
                        }
                    } else {
                        panic!("{}: token {} expected Rectangular", test_name, index);
                    }
                }
                NumCheck::PolarInt(m, a) => {
                    if let NumberValue::Polar { magnitude, angle } = &kind.value {
                        match magnitude {
                            RealRepr::Finite(FiniteRealRepr::Integer { spelling }) => {
                                assert_eq!(spelling, m)
                            }
                            _ => {
                                panic!("{}: token {} expected Integer magnitude", test_name, index)
                            }
                        }
                        match angle {
                            RealRepr::Finite(FiniteRealRepr::Integer { spelling }) => {
                                assert_eq!(spelling, a)
                            }
                            _ => panic!("{}: token {} expected Integer angle", test_name, index),
                        }
                    } else {
                        panic!("{}: token {} expected Polar", test_name, index);
                    }
                }
                NumCheck::PolarRatDec(m, a) => {
                    if let NumberValue::Polar { magnitude, angle } = &kind.value {
                        match magnitude {
                            RealRepr::Finite(FiniteRealRepr::Rational { spelling }) => {
                                assert_eq!(spelling, m)
                            }
                            _ => {
                                panic!("{}: token {} expected Rational magnitude", test_name, index)
                            }
                        }
                        match angle {
                            RealRepr::Finite(FiniteRealRepr::Decimal { spelling }) => {
                                assert_eq!(spelling, a)
                            }
                            _ => panic!("{}: token {} expected Decimal angle", test_name, index),
                        }
                    } else {
                        panic!("{}: token {} expected Polar", test_name, index);
                    }
                }
                NumCheck::Inf(k) => {
                    if let NumberValue::Real(RealRepr::Infnan(val)) = &kind.value {
                        assert_eq!(val, k, "{}: token {} infnan mismatch", test_name, index);
                    } else {
                        panic!("{}: token {} expected Infnan", test_name, index);
                    }
                }
                NumCheck::RectInfImag(r, k) => {
                    if let NumberValue::Rectangular { real, imag } = &kind.value {
                        match real {
                            RealRepr::Finite(FiniteRealRepr::Integer { spelling }) => {
                                assert_eq!(spelling, r)
                            }
                            _ => {
                                panic!("{}: token {} expected Integer real part", test_name, index)
                            }
                        }
                        match imag {
                            RealRepr::Infnan(val) => assert_eq!(val, k),
                            _ => panic!("{}: token {} expected Infnan imag part", test_name, index),
                        }
                    } else {
                        panic!("{}: token {} expected Rectangular", test_name, index);
                    }
                }
                NumCheck::Exact(inner) => {
                    assert_eq!(
                        kind.exactness,
                        NumberExactness::Exact,
                        "{}: token {} expected Exact",
                        test_name,
                        index
                    );
                    inner.verify(kind, test_name, index);
                }
                NumCheck::Inexact(inner) => {
                    assert_eq!(
                        kind.exactness,
                        NumberExactness::Inexact,
                        "{}: token {} expected Inexact",
                        test_name,
                        index
                    );
                    inner.verify(kind, test_name, index);
                }
                NumCheck::Radix(r, inner) => {
                    assert_eq!(
                        kind.radix, *r,
                        "{}: token {} radix mismatch",
                        test_name, index
                    );
                    inner.verify(kind, test_name, index);
                }
            }
        }
    }

    // --- Tests ---

    #[test]
    fn run_all_tests() {
        let cases = vec![
            TestCase {
                name: "stub_unimplemented",
                input: "(foo)",
                expected: Expected::Error(ErrorMatcher::Unimplemented),
            },
            TestCase {
                name: "whitespace_comments",
                input: "   ; comment here\n  #| nested ; comment |#   ",
                expected: Expected::Empty,
            },
            TestCase {
                name: "incomplete_nested_comment",
                input: "#| unclosed nested comment",
                expected: Expected::Error(ErrorMatcher::Incomplete),
            },
            TestCase {
                name: "incomplete_character_prefix",
                input: r#"#\"#,
                expected: Expected::Error(ErrorMatcher::IncompleteToken),
            },
            TestCase {
                name: "incomplete_hash_only",
                input: "#",
                expected: Expected::Error(ErrorMatcher::IncompleteToken),
            },
            TestCase {
                name: "incomplete_double_prefix",
                input: "#b#",
                expected: Expected::Error(ErrorMatcher::IncompleteToken),
            },
            TestCase {
                name: "unknown_directive",
                input: "#!unknown-directive",
                expected: Expected::Error(ErrorMatcher::Lex("<directive>")),
            },
            TestCase {
                name: "fold_case_directives",
                input: "#!fold-case\n  #!no-fold-case  ; rest is comment\n",
                expected: Expected::Empty,
            },
            TestCase {
                name: "directive_requires_delimiter_1",
                input: "#!fold-caseX",
                expected: Expected::Error(ErrorMatcher::Lex("<directive>")),
            },
            TestCase {
                name: "directive_requires_delimiter_2",
                input: "#!no-fold-caseX",
                expected: Expected::Error(ErrorMatcher::Lex("<directive>")),
            },
            TestCase {
                name: "boolean_tokens",
                input: "  #t  #FaLsE  #true #FALSE",
                expected: Expected::Tokens(vec![
                    TokenMatcher::Bool(true),
                    TokenMatcher::Bool(false),
                    TokenMatcher::Bool(true),
                    TokenMatcher::Bool(false),
                ]),
            },
            TestCase {
                name: "character_tokens",
                input: "#\\a #\\space #\\x41",
                expected: Expected::Tokens(vec![
                    TokenMatcher::Char('a'),
                    TokenMatcher::Char(' '),
                    TokenMatcher::Char('A'),
                ]),
            },
            TestCase {
                name: "punctuation_tokens",
                input: "( ) ' ` , ,@ . #(",
                expected: Expected::Tokens(vec![
                    TokenMatcher::LParen,
                    TokenMatcher::RParen,
                    TokenMatcher::Quote,
                    TokenMatcher::Backquote,
                    TokenMatcher::Comma,
                    TokenMatcher::CommaAt,
                    TokenMatcher::Dot,
                    TokenMatcher::VectorStart,
                ]),
            },
            TestCase {
                name: "bytevector_start",
                input: "#u8(",
                expected: Expected::Tokens(vec![TokenMatcher::ByteVectorStart]),
            },
            TestCase {
                name: "decimal_numbers",
                input: "42 -7 3.14 .5 1e3 2.0e-2",
                expected: Expected::Tokens(vec![
                    TokenMatcher::Num("42", NumCheck::Int("42")),
                    TokenMatcher::Num("-7", NumCheck::Int("-7")),
                    TokenMatcher::Num("3.14", NumCheck::Dec("3.14")),
                    TokenMatcher::Num(".5", NumCheck::Dec(".5")),
                    TokenMatcher::Num("1e3", NumCheck::Dec("1e3")),
                    TokenMatcher::Num("2.0e-2", NumCheck::Dec("2.0e-2")),
                ]),
            },
            TestCase {
                name: "incomplete_decimal_1",
                input: "1e",
                expected: Expected::Error(ErrorMatcher::IncompleteToken),
            },
            TestCase {
                name: "incomplete_decimal_2",
                input: "1.0e+",
                expected: Expected::Error(ErrorMatcher::IncompleteToken),
            },
            TestCase {
                name: "malformed_number_suffix",
                input: "42foo",
                expected: Expected::Error(ErrorMatcher::Lex("<number>")),
            },
            TestCase {
                name: "rationals",
                input: "3/4 -3/4",
                expected: Expected::Tokens(vec![
                    TokenMatcher::Num("3/4", NumCheck::Rat("3/4")),
                    TokenMatcher::Num("-3/4", NumCheck::Rat("-3/4")),
                ]),
            },
            TestCase {
                name: "incomplete_rational",
                input: "3/",
                expected: Expected::Error(ErrorMatcher::IncompleteToken),
            },
            TestCase {
                name: "malformed_rational_1",
                input: "3/x",
                expected: Expected::Error(ErrorMatcher::Lex("<number>")),
            },
            TestCase {
                name: "malformed_rational_2",
                input: "1/2/3",
                expected: Expected::Error(ErrorMatcher::Lex("<number>")),
            },
            TestCase {
                name: "invalid_hex_literal",
                input: "0x1",
                expected: Expected::Error(ErrorMatcher::Lex("<number>")),
            },
            TestCase {
                name: "decimal_complex",
                input: "1+2i 1-3/4i 1+2.5i 1-1e3i",
                expected: Expected::Tokens(vec![
                    TokenMatcher::Num("1+2i", NumCheck::RectInt("1", "+2")),
                    TokenMatcher::Num("1-3/4i", NumCheck::RectRat("1", "-3/4")),
                    TokenMatcher::Num("1+2.5i", NumCheck::Any),
                    TokenMatcher::Num("1-1e3i", NumCheck::Any),
                ]),
            },
            TestCase {
                name: "pure_imaginary_and_polar",
                input: "+i -i +2i -3/4i 1@2 -3/4@5.0 +inf.0i 1+inf.0i",
                expected: Expected::Tokens(vec![
                    TokenMatcher::Num("+i", NumCheck::RectInt("0", "1")),
                    TokenMatcher::Num("-i", NumCheck::RectInt("0", "-1")),
                    TokenMatcher::Num("+2i", NumCheck::RectInt("0", "+2")),
                    TokenMatcher::Num("-3/4i", NumCheck::RectRat("0", "-3/4")),
                    TokenMatcher::Num("1@2", NumCheck::PolarInt("1", "2")),
                    TokenMatcher::Num("-3/4@5.0", NumCheck::PolarRatDec("-3/4", "5.0")),
                    TokenMatcher::Num(
                        "+inf.0i",
                        NumCheck::RectInfImag("0", InfinityNan::PositiveInfinity),
                    ),
                    TokenMatcher::Num(
                        "1+inf.0i",
                        NumCheck::RectInfImag("1", InfinityNan::PositiveInfinity),
                    ),
                ]),
            },
            TestCase {
                name: "prefixed_decimal",
                input: "#d42 #e3.0 #i-5/6 #d#e1 #e#d2",
                expected: Expected::Tokens(vec![
                    TokenMatcher::Num("#d42", NumCheck::Int("42")),
                    TokenMatcher::Num("#e3.0", NumCheck::Exact(Box::new(NumCheck::Dec("3.0")))),
                    TokenMatcher::Num("#i-5/6", NumCheck::Inexact(Box::new(NumCheck::Rat("-5/6")))),
                    TokenMatcher::Num("#d#e1", NumCheck::Exact(Box::new(NumCheck::Int("1")))),
                    TokenMatcher::Num("#e#d2", NumCheck::Exact(Box::new(NumCheck::Int("2")))),
                ]),
            },
            TestCase {
                name: "prefixed_complex",
                input: "#d1+2i #e1-3/4i #i+2i #e1-1e3i #d+inf.0i #e1+inf.0i",
                expected: Expected::Tokens(vec![
                    TokenMatcher::Num("#d1+2i", NumCheck::RectInt("1", "+2")),
                    TokenMatcher::Num(
                        "#e1-3/4i",
                        NumCheck::Exact(Box::new(NumCheck::RectRat("1", "-3/4"))),
                    ),
                    TokenMatcher::Num("#i+2i", NumCheck::Inexact(Box::new(NumCheck::Any))),
                    TokenMatcher::Num("#e1-1e3i", NumCheck::Exact(Box::new(NumCheck::Any))),
                    TokenMatcher::Num(
                        "#d+inf.0i",
                        NumCheck::RectInfImag("0", InfinityNan::PositiveInfinity),
                    ),
                    TokenMatcher::Num(
                        "#e1+inf.0i",
                        NumCheck::Exact(Box::new(NumCheck::RectInfImag(
                            "1",
                            InfinityNan::PositiveInfinity,
                        ))),
                    ),
                ]),
            },
            TestCase {
                name: "prefixed_polar",
                input: "#e1@2 #d-3/4@5.0 #b+inf.0@1 -3/4@5.0",
                expected: Expected::Tokens(vec![
                    TokenMatcher::Num(
                        "#e1@2",
                        NumCheck::Exact(Box::new(NumCheck::PolarInt("1", "2"))),
                    ),
                    TokenMatcher::Num("#d-3/4@5.0", NumCheck::PolarRatDec("-3/4", "5.0")),
                    TokenMatcher::Num(
                        "#b+inf.0@1",
                        NumCheck::Radix(NumberRadix::Binary, Box::new(NumCheck::Any)),
                    ), // Simplified check
                    TokenMatcher::Num("-3/4@5.0", NumCheck::PolarRatDec("-3/4", "5.0")),
                ]),
            },
            TestCase {
                name: "prefixed_errors_1",
                input: "#d#d1",
                expected: Expected::Error(ErrorMatcher::Lex("<number>")),
            },
            TestCase {
                name: "prefixed_errors_2",
                input: "#e#i1",
                expected: Expected::Error(ErrorMatcher::Lex("<number>")),
            },
            TestCase {
                name: "prefixed_errors_3",
                input: "#d42foo",
                expected: Expected::Error(ErrorMatcher::Lex("<number>")),
            },
            TestCase {
                name: "prefixed_errors_4",
                input: "#d",
                expected: Expected::Error(ErrorMatcher::IncompleteToken),
            },
            TestCase {
                name: "infnan_plain",
                input: "+inf.0 -inf.0 +nan.0 -nan.0",
                expected: Expected::Tokens(vec![
                    TokenMatcher::Num("+inf.0", NumCheck::Inf(InfinityNan::PositiveInfinity)),
                    TokenMatcher::Num("-inf.0", NumCheck::Inf(InfinityNan::NegativeInfinity)),
                    TokenMatcher::Num("+nan.0", NumCheck::Inf(InfinityNan::PositiveNaN)),
                    TokenMatcher::Num("-nan.0", NumCheck::Inf(InfinityNan::NegativeNaN)),
                ]),
            },
            TestCase {
                name: "infnan_prefixed",
                input: "#e+inf.0 #i-nan.0 #b+inf.0 #x-nan.0 #b#e+inf.0 #i#x-nan.0",
                expected: Expected::Tokens(vec![
                    TokenMatcher::Num(
                        "#e+inf.0",
                        NumCheck::Exact(Box::new(NumCheck::Inf(InfinityNan::PositiveInfinity))),
                    ),
                    TokenMatcher::Num(
                        "#i-nan.0",
                        NumCheck::Inexact(Box::new(NumCheck::Inf(InfinityNan::NegativeNaN))),
                    ),
                    TokenMatcher::Num(
                        "#b+inf.0",
                        NumCheck::Radix(
                            NumberRadix::Binary,
                            Box::new(NumCheck::Inf(InfinityNan::PositiveInfinity)),
                        ),
                    ),
                    TokenMatcher::Num(
                        "#x-nan.0",
                        NumCheck::Radix(
                            NumberRadix::Hexadecimal,
                            Box::new(NumCheck::Inf(InfinityNan::NegativeNaN)),
                        ),
                    ),
                    TokenMatcher::Num(
                        "#b#e+inf.0",
                        NumCheck::Exact(Box::new(NumCheck::Radix(
                            NumberRadix::Binary,
                            Box::new(NumCheck::Inf(InfinityNan::PositiveInfinity)),
                        ))),
                    ),
                    TokenMatcher::Num(
                        "#i#x-nan.0",
                        NumCheck::Inexact(Box::new(NumCheck::Radix(
                            NumberRadix::Hexadecimal,
                            Box::new(NumCheck::Inf(InfinityNan::NegativeNaN)),
                        ))),
                    ),
                ]),
            },
            TestCase {
                name: "nondecimal_numbers",
                input: "#b1010 #o77 #x1f #b101/11 #xA/F #b#e1 #i#o7",
                expected: Expected::Tokens(vec![
                    TokenMatcher::Num(
                        "#b1010",
                        NumCheck::Radix(NumberRadix::Binary, Box::new(NumCheck::Int("1010"))),
                    ),
                    TokenMatcher::Num(
                        "#o77",
                        NumCheck::Radix(NumberRadix::Octal, Box::new(NumCheck::Int("77"))),
                    ),
                    TokenMatcher::Num(
                        "#x1f",
                        NumCheck::Radix(NumberRadix::Hexadecimal, Box::new(NumCheck::Int("1f"))),
                    ),
                    TokenMatcher::Num(
                        "#b101/11",
                        NumCheck::Radix(NumberRadix::Binary, Box::new(NumCheck::Rat("101/11"))),
                    ),
                    TokenMatcher::Num(
                        "#xA/F",
                        NumCheck::Radix(NumberRadix::Hexadecimal, Box::new(NumCheck::Rat("A/F"))),
                    ),
                    TokenMatcher::Num(
                        "#b#e1",
                        NumCheck::Exact(Box::new(NumCheck::Radix(
                            NumberRadix::Binary,
                            Box::new(NumCheck::Int("1")),
                        ))),
                    ),
                    TokenMatcher::Num(
                        "#i#o7",
                        NumCheck::Inexact(Box::new(NumCheck::Radix(
                            NumberRadix::Octal,
                            Box::new(NumCheck::Int("7")),
                        ))),
                    ),
                ]),
            },
            TestCase {
                name: "nondecimal_errors_1",
                input: "#b102",
                expected: Expected::Error(ErrorMatcher::Lex("<number>")),
            },
            TestCase {
                name: "nondecimal_errors_2",
                input: "#o7/",
                expected: Expected::Error(ErrorMatcher::IncompleteToken),
            },
            TestCase {
                name: "nondecimal_errors_3",
                input: "#xA/G",
                expected: Expected::Error(ErrorMatcher::Lex("<number>")),
            },
            TestCase {
                name: "nondecimal_errors_4",
                input: "#b#b1",
                expected: Expected::Error(ErrorMatcher::Lex("<number>")),
            },
            TestCase {
                name: "nondecimal_errors_5",
                input: "#i#e#b1",
                expected: Expected::Error(ErrorMatcher::Lex("<number>")),
            },
            TestCase {
                name: "nondecimal_errors_6",
                input: "#b1010foo",
                expected: Expected::Error(ErrorMatcher::Lex("<number>")),
            },
            TestCase {
                name: "nondecimal_errors_7",
                input: "#b101e10",
                expected: Expected::Error(ErrorMatcher::Lex("<number>")),
            },
            TestCase {
                name: "nondecimal_errors_8",
                input: "#x1.2",
                expected: Expected::Error(ErrorMatcher::Lex("<number>")),
            },
            TestCase {
                name: "nondecimal_complex",
                input: "#b1+10i #x1-2i #b+i #o-i #b1@10 #x1+inf.0i #b+inf.0i",
                expected: Expected::Tokens(vec![
                    TokenMatcher::Num(
                        "#b1+10i",
                        NumCheck::Radix(
                            NumberRadix::Binary,
                            Box::new(NumCheck::RectInt("1", "+10")),
                        ),
                    ),
                    TokenMatcher::Num(
                        "#x1-2i",
                        NumCheck::Radix(
                            NumberRadix::Hexadecimal,
                            Box::new(NumCheck::RectInt("1", "-2")),
                        ),
                    ),
                    TokenMatcher::Num(
                        "#b+i",
                        NumCheck::Radix(NumberRadix::Binary, Box::new(NumCheck::RectInt("0", "1"))),
                    ),
                    TokenMatcher::Num(
                        "#o-i",
                        NumCheck::Radix(NumberRadix::Octal, Box::new(NumCheck::RectInt("0", "-1"))),
                    ),
                    TokenMatcher::Num(
                        "#b1@10",
                        NumCheck::Radix(
                            NumberRadix::Binary,
                            Box::new(NumCheck::PolarInt("1", "10")),
                        ),
                    ),
                    TokenMatcher::Num(
                        "#x1+inf.0i",
                        NumCheck::Radix(
                            NumberRadix::Hexadecimal,
                            Box::new(NumCheck::RectInfImag("1", InfinityNan::PositiveInfinity)),
                        ),
                    ),
                    TokenMatcher::Num(
                        "#b+inf.0i",
                        NumCheck::Radix(
                            NumberRadix::Binary,
                            Box::new(NumCheck::RectInfImag("0", InfinityNan::PositiveInfinity)),
                        ),
                    ),
                ]),
            },
            TestCase {
                name: "infnan_errors_1",
                input: "+inf.0foo",
                expected: Expected::Error(ErrorMatcher::Lex("<number>")),
            },
            TestCase {
                name: "infnan_errors_2",
                input: "#e+inf.0bar",
                expected: Expected::Error(ErrorMatcher::Lex("<number>")),
            },
            TestCase {
                name: "ambiguous_complex_1",
                input: "1+2",
                expected: Expected::Error(ErrorMatcher::IncompleteToken),
            },
            TestCase {
                name: "ambiguous_complex_2",
                input: "1+2)",
                expected: Expected::Error(ErrorMatcher::Lex("<number>")),
            },
            TestCase {
                name: "ambiguous_complex_3",
                input: "#e1@foo",
                expected: Expected::Error(ErrorMatcher::Lex("<number>")),
            },
            TestCase {
                name: "ambiguous_complex_4",
                input: "#b1@10x",
                expected: Expected::Error(ErrorMatcher::Lex("<number>")),
            },
            TestCase {
                name: "ambiguous_complex_5",
                input: "+inf.0x",
                expected: Expected::Error(ErrorMatcher::Lex("<number>")),
            },
            TestCase {
                name: "ambiguous_complex_6",
                input: "+inf.0i0",
                expected: Expected::Error(ErrorMatcher::Lex("<number>")),
            },
            TestCase {
                name: "strings_simple",
                input: "  \"hi\"  \"a\\n\\t\\r\\b\\a\\\\\\\"\"  \"\\x41;\"",
                expected: Expected::Tokens(vec![
                    TokenMatcher::Str("hi"),
                    TokenMatcher::Str("a\n\t\r\u{8}\u{7}\\\""),
                    TokenMatcher::Str("A"),
                ]),
            },
            TestCase {
                name: "strings_splice",
                input: "\"foo\\\n   bar\"",
                expected: Expected::Tokens(vec![TokenMatcher::Str("foobar")]),
            },
            TestCase {
                name: "strings_incomplete",
                input: "\"unterminated",
                expected: Expected::Error(ErrorMatcher::Incomplete),
            },
            TestCase {
                name: "strings_invalid_hex",
                input: "\"\\xZZ;\"",
                expected: Expected::Error(ErrorMatcher::Lex("<string>")),
            },
            TestCase {
                name: "strings_incomplete_hex",
                input: "\"\\x",
                expected: Expected::Error(ErrorMatcher::IncompleteToken),
            },
            TestCase {
                name: "datum_comment",
                input: "#; (foo)",
                expected: Expected::Error(ErrorMatcher::Unimplemented),
            },
        ];

        for case in cases {
            case.run();
        }
    }
}
