use crate::{
    FiniteRealRepr, InfinityNan, NumberExactness, NumberLiteral, NumberLiteralKind, NumberRadix,
    NumberValue, ParseError, RealRepr, Span, Syntax,
};
use winnow::Parser;
use winnow::error::{ContextError, ErrMode, Needed, StrContext};
use winnow::stream::{Location, Stream};
use winnow::token::{any, take, take_while};

// Internal types and helpers to support the `winnow`-based lexer.
type WinnowInput<'i> = winnow::stream::LocatingSlice<winnow::stream::Str<'i>>;
type PResult<O> = Result<O, ErrMode<ContextError>>;
type WinnowInnerError = ContextError;

#[allow(dead_code)]
fn winnow_err_to_parse_error(err: ErrMode<WinnowInnerError>, fallback_span: Span) -> ParseError {
    match err {
        ErrMode::Incomplete(_) => ParseError::Incomplete,
        ErrMode::Cut(e) | ErrMode::Backtrack(e) => {
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
fn lex_intertoken<'i>(input: &mut WinnowInput<'i>, fold_case: &mut bool) -> PResult<()> {
    loop {
        let Some(ch) = input.peek_token() else {
            return Ok(());
        };

        match ch {
            // <whitespace>
            ' ' | '\t' | '\n' | '\r' => {
                let _ = input.next_token();
            }
            // Line comment: `; ... <line ending or EOF>`
            ';' => {
                let _ = input.next_token();
                while let Some(c) = input.next_token() {
                    if c == '\n' || c == '\r' {
                        break;
                    }
                }
            }
            // Possible nested comment or directive starting with '#'.
            '#' => {
                // Use a cloned cursor for lookahead so we don't
                // consume `#` unless we recognize a comment or
                // directive.
                let mut probe = input.clone();
                let _ = probe.next_token(); // consume '#'

                match probe.peek_token() {
                    // Nested comment `#| ... |#`.
                    Some('|') => {
                        // Commit `#|` on the real input.
                        let _ = input.next_token();
                        let _ = input.next_token();
                        lex_nested_comment(input)?;
                        continue;
                    }
                    // Directives starting with `#!`.
                    Some('!') => {
                        let _ = probe.next_token(); // consume '!'
                        let directive_start = probe.clone();

                        // Helper to test whether the stream from
                        // `start` begins with `word`.
                        let matches_word = |mut s: WinnowInput<'i>, word: &str| {
                            for expected in word.chars() {
                                match s.next_token() {
                                    Some(c) if c == expected => {}
                                    _ => return false,
                                }
                            }
                            true
                        };

                        // Helper to enforce the R7RS rule that a
                        // <directive> must be followed by a
                        // <delimiter> or EOF.
                        let check_directive_delimiter = |mut s: WinnowInput<'i>, word: &str| {
                            for _ in word.chars() {
                                let _ = s.next_token();
                            }
                            if let Some(ch) = s.peek_token() {
                                if !is_delimiter(ch) {
                                    let mut ctx = ContextError::new();
                                    ctx.push(StrContext::Label("<directive>"));
                                    return Err(ErrMode::Cut(ctx));
                                }
                            }
                            Ok(())
                        };

                        if matches_word(directive_start, "fold-case") {
                            check_directive_delimiter(directive_start, "fold-case")?;
                            // Consume `#!fold-case` on the real input.
                            for _ in 0..(2 + "fold-case".chars().count()) {
                                let _ = input.next_token();
                            }
                            *fold_case = true;
                            continue;
                        }

                        if matches_word(directive_start, "no-fold-case") {
                            check_directive_delimiter(directive_start, "no-fold-case")?;
                            // Consume `#!no-fold-case` on the real input.
                            for _ in 0..(2 + "no-fold-case".chars().count()) {
                                let _ = input.next_token();
                            }
                            *fold_case = false;
                            continue;
                        }

                        // Any other `#!...` sequence is an unknown directive.
                        let mut ctx = ContextError::new();
                        ctx.push(StrContext::Label("<directive>"));
                        return Err(ErrMode::Cut(ctx));
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

/// Canonical punctuation parser using `winnow`.
fn lex_punctuation<'i>(input: &mut WinnowInput<'i>) -> PResult<SpannedToken> {
    let start = input.current_token_start();

    let ch = match input.peek_token() {
        Some(c) => c,
        None => return winnow_backtrack(),
    };

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
            if let Some('@') = input.peek_token() {
                let _ = input.next_token();
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
                Some('u') | Some('U') => {
                    let _ = input.next_token();
                    if let Some('8') = input.peek_token() {
                        let _ = input.next_token();
                        if let Some('(') = input.peek_token() {
                            let _ = input.next_token();
                            Token::ByteVectorStart
                        } else {
                            return winnow_backtrack();
                        }
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
            let mut probe = input.clone();
            let _ = probe.next_token(); // consume '.'
            if let Some(next) = probe.peek_token() {
                if next.is_ascii_digit() {
                    return winnow_backtrack();
                }
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
    fold_case: &mut bool,
) -> Result<Option<SpannedToken>, ParseError> {
    let len = source.len();

    // Skip `<intertoken space>` before each token.
    let start_before = input.current_token_start();
    let fallback_span_before = Span {
        start: start_before,
        end: len,
    };

    match lex_intertoken(input, fold_case) {
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
            let text = &source[start..end];
            literal.text = text.to_string();
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
    let ch = input.peek_token().unwrap();
    match ch {
        '+' | '-' | '0'..='9' | '.' => {
            match lex_complex_decimal(input) {
                Ok(mut literal) => {
                    let end = input.current_token_start();
                    let text = &source[start..end];
                    literal.text = text.to_string();
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

    // Track `#!fold-case` / `#!no-fold-case` directives.
    //
    // R7RS-DEVIATION: Although we recognize these directives
    // lexically, we deliberately ignore their semantics for now and
    // keep the reader case-sensitive with ASCII-only identifiers.
    // This errs on the side of rejecting some valid programs rather
    // than accepting invalid ones.
    let mut fold_case = false;

    loop {
        match token_with_span(&mut input, source, &mut fold_case)? {
            Some(token) => tokens.push(token),
            None => break,
        }
    }

    Ok(tokens)
}

/// Canonical `<nested comment>` parser using `winnow`.
///
/// Grammar reference (Formal syntax / Lexical structure):
///
/// ```text
/// <comment> ::= ; <all subsequent characters up to a line ending>
///             | <nested comment>
///             | #; <intertoken space> <datum>
///
/// <nested comment> ::= #| <comment text>
///                       <comment cont>* |#
///
/// <comment cont> ::= <nested comment> <comment text>
/// ```
///
/// This helper assumes the initial `#|` has already been consumed and
/// stops after the matching closing `|#`, supporting arbitrary nesting.
fn lex_nested_comment<'i>(input: &mut WinnowInput<'i>) -> PResult<()> {
    let mut depth = 1usize;

    loop {
        let ch = match input.next_token() {
            Some(c) => c,
            None => return Err(ErrMode::Incomplete(Needed::Unknown)),
        };

        if ch == '#' {
            if let Some('|') = input.peek_token() {
                let _ = input.next_token();
                depth += 1;
                continue;
            }
        } else if ch == '|' {
            if let Some('#') = input.peek_token() {
                let _ = input.next_token();
                depth -= 1;
                if depth == 0 {
                    return Ok(());
                }
                continue;
            }
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
    // All `<infnan>` spellings are 6 ASCII bytes: sign + 3 letters + ".0".
    // We simply grab 6 characters and compare against the four allowed
    // spellings, case-insensitively, just like the old helper.
    let candidate_res: PResult<&str> = take(6usize).parse_next(input);
    let candidate = match candidate_res {
        Ok(s) => s,
        Err(_) => return winnow_backtrack(),
    };

    let lower = candidate.to_ascii_lowercase();
    let kind = match lower.as_str() {
        "+inf.0" => InfinityNan::PositiveInfinity,
        "-inf.0" => InfinityNan::NegativeInfinity,
        "+nan.0" => InfinityNan::PositiveNaN,
        "-nan.0" => InfinityNan::NegativeNaN,
        _ => return winnow_backtrack(),
    };

    Ok(kind)
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
/// For `R = 10`, this delegates to `lex_decimal_number` and projects
/// out a `FiniteRealRepr`; for other radices it parses an optional
/// `<sign>` followed by `lex_nondecimal_ureal`.
fn lex_sign_ureal_for_radix<'i>(
    input: &mut WinnowInput<'i>,
    radix: NumberRadix,
) -> PResult<FiniteRealRepr> {
    match radix {
        NumberRadix::Decimal => {
            // Delegate to the canonical decimal lexer and project out
            // the finite real representation.
            let mut probe = *input;
            let literal = match lex_decimal_number(&mut probe) {
                Ok(lit) => lit,
                Err(e) => return Err(e),
            };

            let kind = literal.kind;
            match kind.value {
                NumberValue::Real(RealRepr::Finite(finite)) => {
                    *input = probe;
                    Ok(finite)
                }
                _ => unreachable!("decimal lexer should only produce finite real values"),
            }
        }
        _ => {
            // Optional sign followed by `<ureal R>`.
            let mut probe = *input;
            let mut sign: Option<char> = None;
            if let Some(ch) = probe.peek_token() {
                if ch == '+' || ch == '-' {
                    sign = Some(ch);
                    let _ = probe.next_token();
                }
            }

            match lex_nondecimal_ureal(&mut probe, radix) {
                Ok(mut finite) => {
                    if let Some(s) = sign {
                        match &mut finite {
                            FiniteRealRepr::Integer { spelling }
                            | FiniteRealRepr::Rational { spelling } => {
                                spelling.insert(0, s);
                            }
                            FiniteRealRepr::Decimal { .. } => {
                                // Non-decimal `<ureal R>` never produces decimals.
                            }
                        }
                    }
                    *input = probe;
                    Ok(finite)
                }
                Err(e) => Err(e),
            }
        }
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
/// The `<ureal R>` and `<decimal 10>` productions are implemented
/// by `lex_nondecimal_ureal` and `lex_decimal_number` respectively.
fn lex_complex_with_radix<'i>(
    input: &mut WinnowInput<'i>,
    radix: NumberRadix,
    exactness: NumberExactness,
) -> PResult<NumberLiteral> {
    let start_state = *input;

    // 1. Try to parse the first component as `<real R>`.
    match lex_real_repr(input, radix) {
        Ok(repr1) => {
            match input.peek_token() {
                None => {
                    // End of input: it's a real number.
                    let kind = NumberLiteralKind {
                        radix,
                        exactness,
                        value: NumberValue::Real(repr1),
                    };
                    return Ok(NumberLiteral {
                        text: String::new(),
                        kind,
                    });
                }
                Some(next_ch) if is_delimiter(next_ch) => {
                    // Delimiter after `<real R>`: also a real number.
                    let kind = NumberLiteralKind {
                        radix,
                        exactness,
                        value: NumberValue::Real(repr1),
                    };
                    return Ok(NumberLiteral {
                        text: String::new(),
                        kind,
                    });
                }
                Some(next_ch) => match next_ch {
                    'i' | 'I' => {
                        // Pure imaginary: `<real R> i`.
                        let mut probe = *input;
                        let _ = probe.next_token(); // consume 'i' / 'I'
                        lex_ensure_number_delimiter(&mut probe)?;

                        let real_zero = RealRepr::Finite(FiniteRealRepr::Integer {
                            spelling: "0".to_string(),
                        });
                        let kind = NumberLiteralKind {
                            radix,
                            exactness,
                            value: NumberValue::Rectangular {
                                real: real_zero,
                                imag: repr1,
                            },
                        };
                        *input = probe;
                        return Ok(NumberLiteral {
                            text: String::new(),
                            kind,
                        });
                    }
                    '@' => {
                        // Polar: `<real R> @ <real R>`.
                        let mut probe = *input;
                        let _ = probe.next_token(); // consume '@'
                        match lex_real_repr(&mut probe, radix) {
                            Ok(repr2) => {
                                lex_ensure_number_delimiter(&mut probe)?;
                                let kind = NumberLiteralKind {
                                    radix,
                                    exactness,
                                    value: NumberValue::Polar {
                                        magnitude: repr1,
                                        angle: repr2,
                                    },
                                };
                                *input = probe;
                                return Ok(NumberLiteral {
                                    text: String::new(),
                                    kind,
                                });
                            }
                            Err(ErrMode::Backtrack(_)) => return lex_number_error(),
                            Err(e) => return Err(e),
                        }
                    }
                    '+' | '-' => {
                        // Rectangular: `<real R> +/- <ureal R> i` or `<real R> +/- i`.
                        let mut probe = *input;
                        match lex_real_repr(&mut probe, radix) {
                            Ok(repr2) => {
                                match probe.peek_token() {
                                    None => {
                                        // Parsed the second number but hit EOF before 'i'.
                                        return Err(ErrMode::Incomplete(Needed::Unknown));
                                    }
                                    Some(ch2) if ch2 == 'i' || ch2 == 'I' => {
                                        let _ = probe.next_token();
                                        lex_ensure_number_delimiter(&mut probe)?;
                                        let kind = NumberLiteralKind {
                                            radix,
                                            exactness,
                                            value: NumberValue::Rectangular {
                                                real: repr1,
                                                imag: repr2,
                                            },
                                        };
                                        *input = probe;
                                        return Ok(NumberLiteral {
                                            text: String::new(),
                                            kind,
                                        });
                                    }
                                    _ => {
                                        // Parsed a second real but it wasn't followed by 'i'.
                                        return lex_number_error();
                                    }
                                }
                            }
                            Err(ErrMode::Backtrack(_)) => {
                                // Fall back to `+i` / `-i` (implicit 1).
                                let mut probe2 = *input;
                                let sign_ch = match probe2.peek_token() {
                                    Some(c) => c,
                                    None => return winnow_backtrack(),
                                };
                                let _ = probe2.next_token(); // consume '+' / '-'
                                match probe2.peek_token() {
                                    Some('i') | Some('I') => {
                                        let _ = probe2.next_token();
                                        lex_ensure_number_delimiter(&mut probe2)?;

                                        let imag_spelling = if sign_ch == '-' { "-1" } else { "1" };
                                        let imag = RealRepr::Finite(FiniteRealRepr::Integer {
                                            spelling: imag_spelling.to_string(),
                                        });
                                        let kind = NumberLiteralKind {
                                            radix,
                                            exactness,
                                            value: NumberValue::Rectangular { real: repr1, imag },
                                        };
                                        *input = probe2;
                                        return Ok(NumberLiteral {
                                            text: String::new(),
                                            kind,
                                        });
                                    }
                                    _ => return lex_number_error(),
                                }
                            }
                            Err(e) => return Err(e),
                        }
                    }
                    _ => {
                        // Some other character after `<real R>`.
                        return lex_number_error();
                    }
                },
            }
        }
        Err(ErrMode::Backtrack(_)) => {
            // No `<real R>` here; reset and try `+i` / `-i` (unit imaginary).
            *input = start_state;
        }
        Err(e) => return Err(e),
    }

    // Handle `+i` / `-i` without an explicit real part.
    let mut probe = *input;
    let ch = match probe.peek_token() {
        Some(c) => c,
        None => return winnow_backtrack(),
    };

    if ch != '+' && ch != '-' {
        return winnow_backtrack();
    }

    let sign_ch = ch;
    let _ = probe.next_token(); // consume '+' / '-'
    match probe.peek_token() {
        Some('i') | Some('I') => {
            let _ = probe.next_token();
            lex_ensure_number_delimiter(&mut probe)?;

            let real_zero = RealRepr::Finite(FiniteRealRepr::Integer {
                spelling: "0".to_string(),
            });
            let imag_spelling = if sign_ch == '-' { "-1" } else { "1" };
            let imag = RealRepr::Finite(FiniteRealRepr::Integer {
                spelling: imag_spelling.to_string(),
            });

            let kind = NumberLiteralKind {
                radix,
                exactness,
                value: NumberValue::Rectangular {
                    real: real_zero,
                    imag,
                },
            };
            *input = probe;
            return Ok(NumberLiteral {
                text: String::new(),
                kind,
            });
        }
        _ => return winnow_backtrack(),
    }
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

    loop {
        let ch0 = match probe.peek_token() {
            Some(c) => c,
            None => break,
        };

        if ch0 != '#' {
            break;
        }

        let _ = probe.next_token(); // consume '#'
        let after_hash = match probe.peek_token() {
            Some(c) => c,
            None => {
                if radix.is_some() || exactness.is_some() {
                    return Err(ErrMode::Incomplete(Needed::Unknown));
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
                    return lex_number_error();
                }
                radix = Some(match lower {
                    'b' => NumberRadix::Binary,
                    'o' => NumberRadix::Octal,
                    'd' => NumberRadix::Decimal,
                    'x' => NumberRadix::Hexadecimal,
                    _ => unreachable!(),
                });
            }
            'e' | 'i' => {
                if exactness.is_some() {
                    return lex_number_error();
                }
                exactness = Some(match lower {
                    'e' => NumberExactness::Exact,
                    'i' => NumberExactness::Inexact,
                    _ => unreachable!(),
                });
            }
            _ => {
                if radix.is_some() || exactness.is_some() {
                    return lex_number_error();
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

    if probe.peek_token().is_none() {
        return Err(ErrMode::Incomplete(Needed::Unknown));
    }

    match lex_complex_with_radix(&mut probe, radix_value, exactness_value) {
        Ok(literal) => {
            *input = probe;
            Ok(literal)
        }
        Err(e) => Err(e),
    }
}

/// Internal helper to report `<string>` lexical errors.
fn lex_string_error<O>() -> PResult<O> {
    let mut ctx = ContextError::new();
    ctx.push(StrContext::Label("<string>"));
    Err(ErrMode::Cut(ctx))
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
        let ch = match input.peek_token() {
            Some(c) => c,
            None => return Err(ErrMode::Incomplete(Needed::Unknown)),
        };

        match ch {
            '"' => break,
            '\\' => {
                let _ = input.next_token();
                let next = match input.peek_token() {
                    Some(c) => c,
                    None => return Err(ErrMode::Incomplete(Needed::Unknown)),
                };

                match next {
                    'a' => {
                        let _ = input.next_token();
                        result.push('\u{7}');
                    }
                    'b' => {
                        let _ = input.next_token();
                        result.push('\u{8}');
                    }
                    't' => {
                        let _ = input.next_token();
                        result.push('\t');
                    }
                    'n' => {
                        let _ = input.next_token();
                        result.push('\n');
                    }
                    'r' => {
                        let _ = input.next_token();
                        result.push('\r');
                    }
                    '"' => {
                        let _ = input.next_token();
                        result.push('"');
                    }
                    '\\' => {
                        let _ = input.next_token();
                        result.push('\\');
                    }
                    'x' | 'X' => {
                        let _ = input.next_token();
                        let mut hex_digits = String::new();
                        while let Some(c) = input.peek_token() {
                            if c.is_ascii_hexdigit() {
                                hex_digits.push(c);
                                let _ = input.next_token();
                            } else {
                                break;
                            }
                        }

                        if hex_digits.is_empty() {
                            return lex_string_error();
                        }

                        let end_ch = match input.peek_token() {
                            Some(c) => c,
                            None => return Err(ErrMode::Incomplete(Needed::Unknown)),
                        };

                        if end_ch != ';' {
                            return lex_string_error();
                        }

                        let _ = input.next_token();

                        let codepoint = match u32::from_str_radix(&hex_digits, 16) {
                            Ok(v) => v,
                            Err(_) => return lex_string_error(),
                        };

                        match char::from_u32(codepoint) {
                            Some(c) => result.push(c),
                            None => return lex_string_error(),
                        }
                    }
                    _ => {
                        // Possible line splice: backslash, optional spaces/tabs,
                        // then a line ending and more spaces/tabs.
                        loop {
                            match input.peek_token() {
                                Some(' ' | '\t') => {
                                    let _ = input.next_token();
                                }
                                _ => break,
                            }
                        }

                        let nl = match input.peek_token() {
                            Some(c) => c,
                            None => return Err(ErrMode::Incomplete(Needed::Unknown)),
                        };

                        if nl == '\n' || nl == '\r' {
                            let first = nl;
                            let _ = input.next_token();
                            if first == '\r' {
                                if let Some('\n') = input.peek_token() {
                                    let _ = input.next_token();
                                }
                            }
                            // Skip following spaces/tabs on the next line.
                            loop {
                                match input.peek_token() {
                                    Some(' ' | '\t') => {
                                        let _ = input.next_token();
                                    }
                                    _ => break,
                                }
                            }
                        } else {
                            return lex_string_error();
                        }
                    }
                }
            }
            '\n' | '\r' => {
                return lex_string_error();
            }
            _ => {
                let _ = input.next_token();
                result.push(ch);
            }
        }
    }

    Ok(result)
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

    match input.peek_token() {
        Some('"') => {
            let _ = input.next_token();
        }
        _ => return winnow_backtrack(),
    }

    let value = lex_string_body(input)?;

    match input.next_token() {
        Some('"') => {}
        None => return Err(ErrMode::Incomplete(Needed::Unknown)),
        _ => return lex_string_error(),
    }

    let end = input.current_token_start();
    Ok(Syntax::new(Span { start, end }, Token::String(value)))
}

/// Internal helper to report `<character>` lexical errors.
fn lex_character_error<O>() -> PResult<O> {
    let mut ctx = ContextError::new();
    ctx.push(StrContext::Label("<character>"));
    Err(ErrMode::Cut(ctx))
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
    let mut probe = input.clone();
    match (probe.next_token(), probe.peek_token()) {
        (Some('#'), Some('\\')) => {
            // Commit the prefix on the real input.
            let _ = input.next_token();
            let _ = input.next_token();
        }
        // `#` at end-of-input followed by missing `\\` is an
        // incomplete `<character>` token.
        (Some('#'), None) => return Err(ErrMode::Incomplete(Needed::Unknown)),
        _ => return winnow_backtrack(),
    }

    // At least one character must follow `#\`.
    let c1: char = any.parse_next(input)?;

    let value_char = if c1 == 'x' || c1 == 'X' {
        // Potential `#\x<hex scalar value>` form.
        let mut hex_digits = String::new();
        while let Some(c) = input.peek_token() {
            if c.is_ascii_hexdigit() {
                hex_digits.push(c);
                let _ = input.next_token();
            } else {
                break;
            }
        }

        if !hex_digits.is_empty() {
            let codepoint = match u32::from_str_radix(&hex_digits, 16) {
                Ok(v) => v,
                Err(_) => return lex_character_error(),
            };

            match char::from_u32(codepoint) {
                Some(ch) => ch,
                None => return lex_character_error(),
            }
        } else {
            // No hex digits: treat as the literal character 'x' / 'X'.
            c1
        }
    } else if c1.is_ascii_alphabetic() {
        // Possible named character like `space`, `newline`, etc.
        let mut name = String::new();
        name.push(c1);
        while let Some(c) = input.peek_token() {
            if c.is_ascii_alphabetic() {
                name.push(c);
                let _ = input.next_token();
            } else {
                break;
            }
        }

        if name.len() == c1.len_utf8() {
            // Single alphabetic character like `#\a`.
            c1
        } else {
            match name.as_str() {
                "alarm" => '\u{7}',
                "backspace" => '\u{8}',
                "delete" => '\u{7F}',
                "escape" => '\u{1B}',
                "newline" => '\n',
                "null" => '\0',
                "return" => '\r',
                "space" => ' ',
                "tab" => '\t',
                _ => return lex_character_error(),
            }
        }
    } else {
        // Any other single character after `#\`.
        c1
    };

    // Enforce delimiter after the `<character>` token.
    if let Some(ch) = input.peek_token() {
        if !is_delimiter(ch) {
            return lex_character_error();
        }
    }

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

    match probe.peek_token() {
        Some('#') => {
            let _ = probe.next_token();
        }
        _ => return winnow_backtrack(),
    }

    // Bare `#` at EOF is treated as "no boolean here" rather than an
    // incomplete token, matching the previous semantics.
    if probe.peek_token().is_none() {
        return winnow_backtrack();
    }

    // Parse 1+ alphabetic characters for the boolean identifier.
    let ident_res: PResult<&str> =
        take_while(1.., |c: char| c.is_ascii_alphabetic()).parse_next(&mut probe);
    let ident = match ident_res {
        Ok(s) => s,
        Err(ErrMode::Backtrack(_)) | Err(ErrMode::Incomplete(_)) => {
            return winnow_backtrack();
        }
        Err(e) => return Err(e),
    };

    let lower = ident.to_ascii_lowercase();
    let value = match lower.as_str() {
        "t" | "true" => true,
        "f" | "false" => false,
        // Any other spelling (e.g. "foo") is not a boolean; backtrack
        // so that other `#`-prefixed token kinds can claim the input.
        _ => return winnow_backtrack(),
    };

    // Enforce delimiter: the next character, if any, must be a
    // `<delimiter>`; otherwise this is a `<boolean>` lexical error.
    if let Some(ch) = probe.peek_token() {
        if !is_delimiter(ch) {
            let mut ctx = ContextError::new();
            ctx.push(StrContext::Label("<boolean>"));
            return Err(ErrMode::Cut(ctx));
        }
    }

    // Commit the successfully parsed boolean by updating the real
    // input cursor to the probe's position.
    *input = probe;
    let end = input.current_token_start();
    Ok(Syntax::new(Span { start, end }, Token::Boolean(value)))
}

/// Canonical non-decimal `<ureal R>` parser using `winnow`.
///
/// Grammar reference (Formal syntax / `<number>`):
///
/// ```text
/// <ureal R> ::= <uinteger R>
///              | <uinteger R> / <uinteger R>
///              | <decimal R>
/// ```
///
/// This helper implements the `<uinteger R>` and
/// `<uinteger R> / <uinteger R>` alternatives for `R = 2, 8, 16`,
/// without any leading sign. The caller is responsible for handling
/// the optional `<sign>` and delimiter checks at the `<real R>` /
/// `<number>` level; the `<decimal 10>` case is handled separately
/// by `lex_decimal_number`.
fn lex_nondecimal_ureal<'i>(
    input: &mut WinnowInput<'i>,
    radix: NumberRadix,
) -> PResult<FiniteRealRepr> {
    let mut probe = *input;
    let mut text = String::new();
    let mut saw_digit = false;

    // `<uinteger R>` numerator: at least one digit.
    while let Some(c) = probe.peek_token() {
        if is_digit_for_radix(c, radix) {
            saw_digit = true;
            text.push(c);
            let _ = probe.next_token();
        } else {
            break;
        }
    }

    if !saw_digit {
        return winnow_backtrack();
    }

    let mut is_rational = false;

    // Optional `/ <uinteger R>` denominator.
    if let Some(c) = probe.peek_token() {
        if c == '/' {
            is_rational = true;
            text.push(c);
            let _ = probe.next_token();

            if probe.peek_token().is_none() {
                // E.g. "#b1/" at end of input.
                return Err(ErrMode::Incomplete(Needed::Unknown));
            }

            let mut denom_digits = false;
            while let Some(c2) = probe.peek_token() {
                if is_digit_for_radix(c2, radix) {
                    denom_digits = true;
                    text.push(c2);
                    let _ = probe.next_token();
                } else {
                    break;
                }
            }

            if !denom_digits {
                // "3/" followed by a non-digit, e.g. "3/x".
                return lex_number_error();
            }
        }
    }

    let finite = if is_rational {
        FiniteRealRepr::Rational {
            spelling: text.clone(),
        }
    } else {
        FiniteRealRepr::Integer {
            spelling: text.clone(),
        }
    };

    *input = probe;
    Ok(finite)
}

fn is_digit_for_radix(ch: char, radix: NumberRadix) -> bool {
    match radix {
        NumberRadix::Binary => matches!(ch, '0' | '1'),
        NumberRadix::Octal => matches!(ch, '0'..='7'),
        NumberRadix::Decimal => ch.is_ascii_digit(),
        NumberRadix::Hexadecimal => ch.is_ascii_hexdigit(),
    }
}

/// Internal helper to report `<number>` lexical errors.
fn lex_number_error<O>() -> PResult<O> {
    let mut ctx = ContextError::new();
    ctx.push(StrContext::Label("<number>"));
    Err(ErrMode::Cut(ctx))
}

fn lex_ensure_number_delimiter<'i>(input: &mut WinnowInput<'i>) -> PResult<()> {
    if let Some(ch) = input.peek_token() {
        if !is_delimiter(ch) {
            return lex_number_error();
        }
    }
    Ok(())
}

/// Canonical `<decimal 10>` parser using `winnow`.
///
/// Recognizes the subset of the `<number>` grammar corresponding to
/// real decimal numbers without prefixes:
///
/// ```text
/// <decimal 10> ::= <uinteger 10> <suffix>
///                 | . <digit 10>+ <suffix>
///                 | <digit 10>+ . <digit 10>* <suffix>
///
/// <suffix> ::= <empty>
///            | <exponent marker> <sign> <digit 10>+
///
/// <exponent marker> ::= e
/// <sign> ::= <empty> | + | -
/// ```
///
/// Note: This helper is intentionally limited to radix-10 real
/// components; radix and exactness prefixes are handled at the
/// `<prefix R>` / `lex_prefixed_number` layer.
fn lex_decimal_number<'i>(input: &mut WinnowInput<'i>) -> PResult<NumberLiteral> {
    // Work on a copy so we can backtrack cleanly if this
    // does not match a decimal number at all.
    let mut probe = *input;
    let mut text = String::new();
    let mut saw_digit = false;

    // Optional sign.
    if let Some(ch) = probe.peek_token() {
        if ch == '+' || ch == '-' {
            text.push(ch);
            let _ = probe.next_token();
        }
    }

    let first = match probe.peek_token() {
        Some(c) => c,
        None => return winnow_backtrack(),
    };

    if first == '.' {
        // `.digits+` decimal form (no rationals here).
        text.push(first);
        let _ = probe.next_token();

        // Only '.' (or sign + '.') is not a decimal number.
        if probe.peek_token().is_none() {
            return winnow_backtrack();
        }

        while let Some(c) = probe.peek_token() {
            if c.is_ascii_digit() {
                saw_digit = true;
                text.push(c);
                let _ = probe.next_token();
            } else {
                break;
            }
        }
        if !saw_digit {
            // No digits after '.'
            return winnow_backtrack();
        }

        // Optional exponent part for `.digits+`.
        if let Some(c) = probe.peek_token() {
            if c == 'e' || c == 'E' {
                text.push(c);
                let _ = probe.next_token();

                let sign_or_digit = match probe.peek_token() {
                    Some(ch) => ch,
                    None => return Err(ErrMode::Incomplete(Needed::Unknown)),
                };

                if sign_or_digit == '+' || sign_or_digit == '-' {
                    text.push(sign_or_digit);
                    let _ = probe.next_token();
                    if probe.peek_token().is_none() {
                        return Err(ErrMode::Incomplete(Needed::Unknown));
                    }
                }

                let mut exp_digits = false;
                while let Some(c2) = probe.peek_token() {
                    if c2.is_ascii_digit() {
                        exp_digits = true;
                        text.push(c2);
                        let _ = probe.next_token();
                    } else {
                        break;
                    }
                }
                if !exp_digits {
                    return Err(ErrMode::Incomplete(Needed::Unknown));
                }
            }
        }
    } else if first.is_ascii_digit() {
        // Leading digits of `<uinteger 10>`.
        while let Some(c) = probe.peek_token() {
            if c.is_ascii_digit() {
                saw_digit = true;
                text.push(c);
                let _ = probe.next_token();
            } else {
                break;
            }
        }

        // At this point we may have a rational `a/b`, a decimal
        // `a.b`, or a plain integer `a`.
        if let Some(c) = probe.peek_token() {
            if c == '/' {
                // Potential rational `<uinteger 10> / <uinteger 10>`.
                text.push(c);
                let _ = probe.next_token();
                if probe.peek_token().is_none() {
                    // "3/" at end of input.
                    return Err(ErrMode::Incomplete(Needed::Unknown));
                }

                // Denominator must be `<uinteger 10>`.
                let mut denom_digits = false;
                while let Some(c2) = probe.peek_token() {
                    if c2.is_ascii_digit() {
                        denom_digits = true;
                        text.push(c2);
                        let _ = probe.next_token();
                    } else {
                        break;
                    }
                }

                if !denom_digits {
                    // "3/" followed by a non-digit, e.g. "3/x".
                    return lex_number_error();
                }

                // Rationals do not allow a decimal point or exponent
                // after the denominator, so we are done here.
            } else if c == '.' {
                // Decimal with fractional part: `digits '.' digits*`.
                text.push(c);
                let _ = probe.next_token();
                while let Some(c2) = probe.peek_token() {
                    if c2.is_ascii_digit() {
                        text.push(c2);
                        let _ = probe.next_token();
                    } else {
                        break;
                    }
                }

                // Optional exponent part for `digits '.' digits*`.
                if let Some(c2) = probe.peek_token() {
                    if c2 == 'e' || c2 == 'E' {
                        text.push(c2);
                        let _ = probe.next_token();
                        if probe.peek_token().is_none() {
                            return Err(ErrMode::Incomplete(Needed::Unknown));
                        }

                        let sign_ch = probe.peek_token().unwrap();
                        if sign_ch == '+' || sign_ch == '-' {
                            text.push(sign_ch);
                            let _ = probe.next_token();
                            if probe.peek_token().is_none() {
                                return Err(ErrMode::Incomplete(Needed::Unknown));
                            }
                        }

                        let mut exp_digits = false;
                        while let Some(c3) = probe.peek_token() {
                            if c3.is_ascii_digit() {
                                exp_digits = true;
                                text.push(c3);
                                let _ = probe.next_token();
                            } else {
                                break;
                            }
                        }
                        if !exp_digits {
                            return Err(ErrMode::Incomplete(Needed::Unknown));
                        }
                    }
                }
            } else if c == 'e' || c == 'E' {
                // Exponent part for pure integer: `digits [eE][sign]digits+`.
                text.push(c);
                let _ = probe.next_token();
                if probe.peek_token().is_none() {
                    return Err(ErrMode::Incomplete(Needed::Unknown));
                }

                let sign_ch = probe.peek_token().unwrap();
                if sign_ch == '+' || sign_ch == '-' {
                    text.push(sign_ch);
                    let _ = probe.next_token();
                    if probe.peek_token().is_none() {
                        return Err(ErrMode::Incomplete(Needed::Unknown));
                    }
                }

                let mut exp_digits = false;
                while let Some(c2) = probe.peek_token() {
                    if c2.is_ascii_digit() {
                        exp_digits = true;
                        text.push(c2);
                        let _ = probe.next_token();
                    } else {
                        break;
                    }
                }
                if !exp_digits {
                    return Err(ErrMode::Incomplete(Needed::Unknown));
                }
            }
        }
    } else {
        // Does not look like a decimal number.
        return winnow_backtrack();
    }

    if !saw_digit {
        return winnow_backtrack();
    }

    let kind = classify_decimal_number(&text);
    *input = probe;
    Ok(NumberLiteral { text, kind })
}

fn classify_decimal_number(text: &str) -> NumberLiteralKind {
    // For now we only classify radix-10 reals (integers, rationals,
    // and decimals with optional exponents). Prefixes (`#b/#o/#d/#x`
    // and `#e/#i`) are handled at the tokenization layer.
    let radix = NumberRadix::Decimal;
    let exactness = NumberExactness::Unspecified;

    let finite = if text.contains('/') {
        FiniteRealRepr::Rational {
            spelling: text.to_string(),
        }
    } else if text.contains('.') || text.contains('e') || text.contains('E') {
        FiniteRealRepr::Decimal {
            spelling: text.to_string(),
        }
    } else {
        FiniteRealRepr::Integer {
            spelling: text.to_string(),
        }
    };

    NumberLiteralKind {
        radix,
        exactness,
        value: NumberValue::Real(RealRepr::Finite(finite)),
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
                expected: Expected::Error(ErrorMatcher::Incomplete),
            },
            TestCase {
                name: "incomplete_decimal_2",
                input: "1.0e+",
                expected: Expected::Error(ErrorMatcher::Incomplete),
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
                expected: Expected::Error(ErrorMatcher::Incomplete),
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
                expected: Expected::Error(ErrorMatcher::Incomplete),
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
                expected: Expected::Error(ErrorMatcher::Incomplete),
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
                expected: Expected::Error(ErrorMatcher::Incomplete),
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
