use crate::{
    common::{Interner, Span},
    scheme::{
        ParseError, Unsupported,
        datumtraits::{DatumWriter, SchemeNumberOps},
        lex::{self, FiniteRealKind, NumberExactness, SpannedToken, Token},
    },
};

// Datum enum removed. Use generic DatumWriter.

// ============================================================================
// Token Stream with Datum Comment Handling
// ============================================================================

/// A token stream that handles `#;` datum comments at the parser level.
///
/// Uses inline peeking instead of `std::iter::Peekable` for better performance.
/// The standard library's `Peekable` wrapper introduces overhead through double
/// `Option` wrapping (`Option<Option<T>>`), closure-based `get_or_insert_with`,
/// and generic abstraction boundaries that inhibit cross-function inlining.
/// At authoring time, this inline peeking approach was responsible for ~9%
/// performance improvement on parsing a 1K Scheme program.
pub struct TokenStream<'i> {
    lexer: lex::Lexer<'i>,
    /// Peeked token, if any. Avoids `Peekable` wrapper overhead.
    peeked: Option<Result<SpannedToken<'i>, ParseError>>,
}

const DEFAULT_MAX_DEPTH: u32 = 64;

impl<'i> TokenStream<'i> {
    /// Create a new token stream from lexed tokens.
    #[inline]
    pub fn new(lexer: lex::Lexer<'i>) -> Self {
        Self {
            lexer,
            peeked: None,
        }
    }

    /// Lex source and create a token stream.
    #[inline]
    pub fn from_source(source: &'i str) -> Self {
        Self::new(lex::lex(source))
    }

    /// Internal: ensure we have a peeked token (or None at EOF).
    #[inline]
    fn fill_peek(&mut self) {
        if self.peeked.is_none() {
            self.peeked = self.lexer.next();
        }
    }

    /// Internal: peek at the raw next token without consuming.
    #[inline]
    fn raw_peek(&mut self) -> Option<&Result<SpannedToken<'i>, ParseError>> {
        self.fill_peek();
        self.peeked.as_ref()
    }

    /// Internal: consume the peeked token.
    #[inline]
    fn raw_next(&mut self) -> Option<Result<SpannedToken<'i>, ParseError>> {
        self.fill_peek();
        self.peeked.take()
    }

    /// Peek at the next token without consuming it, skipping intertoken
    /// space such as datum comments, with an explicit maximum depth
    /// used when skipping comments.
    fn peek_with_max_depth(&mut self, depth: u32) -> Result<Option<&SpannedToken<'i>>, ParseError> {
        self.consume_intertoken_space_with_max_depth(depth)?;
        match self.raw_peek() {
            Some(Ok(token)) => Ok(Some(token)),
            Some(Err(e)) => Err(e.clone()),
            None => Ok(None),
        }
    }

    /// Public peek that uses the default maximum depth when skipping
    /// comments.
    #[inline]
    pub fn peek(&mut self) -> Result<Option<&SpannedToken<'i>>, ParseError> {
        self.peek_with_max_depth(DEFAULT_MAX_DEPTH)
    }

    /// Peek at the next token's value without consuming it, skipping
    /// intertoken space, with an explicit maximum depth.
    #[inline]
    fn peek_token_value_with_max_depth(
        &mut self,
        depth: u32,
    ) -> Result<Option<&Token<'i>>, ParseError> {
        Ok(self.peek_with_max_depth(depth)?.map(|st| &st.value))
    }

    /// Public peek of the token value using the default depth.
    #[inline]
    pub fn peek_token_value(&mut self) -> Result<Option<&Token<'i>>, ParseError> {
        self.peek_token_value_with_max_depth(DEFAULT_MAX_DEPTH)
    }

    /// Consume and return the next token, skipping intertoken space,
    /// with an explicit maximum depth used when skipping comments.
    fn next_token_with_max_depth(
        &mut self,
        depth: u32,
    ) -> Result<Option<SpannedToken<'i>>, ParseError> {
        self.consume_intertoken_space_with_max_depth(depth)?;
        match self.raw_next() {
            Some(Ok(token)) => Ok(Some(token)),
            Some(Err(e)) => Err(e),
            None => Ok(None),
        }
    }

    /// Public `next_token` that uses the default maximum depth when
    /// skipping comments.
    #[inline]
    pub fn next_token(&mut self) -> Result<Option<SpannedToken<'i>>, ParseError> {
        self.next_token_with_max_depth(DEFAULT_MAX_DEPTH)
    }

    /// Check if the stream is exhausted (no more tokens after skipping comments).
    pub fn is_empty(&mut self) -> bool {
        matches!(self.peek(), Ok(None))
    }

    /// Consume any leading `<intertoken space>` tokens (currently datum
    /// comments; fold-case directives are handled in the lexer) by
    /// skipping over their tokens, with an explicit maximum depth used
    /// when skipping the commented datums.
    fn consume_intertoken_space_with_max_depth(&mut self, depth: u32) -> Result<(), ParseError> {
        loop {
            let span = match self.raw_peek() {
                Some(Ok(token)) => match token.value {
                    Token::DatumComment => Some(token.span),
                    _ => None,
                },
                Some(Err(e)) => return Err(e.clone()),
                None => None,
            };

            match span {
                Some(span) => {
                    if depth == 0 {
                        return Err(ParseError::unsupported(span, Unsupported::DepthLimit));
                    }
                    let _ = self.raw_next(); // consume #;
                    // Skip the commented datum at one level deeper.
                    self.skip_one_datum_with_max_depth(depth - 1)?;
                }
                None => break,
            }
        }
        Ok(())
    }

    /// Skip exactly one datum from the current position.
    ///
    /// This is a simplified datum skipper that handles:
    /// - Simple tokens (identifiers, numbers, strings, characters, booleans)
    /// - Lists: `(` ... `)` with proper nesting
    /// - Vectors: `#(` ... `)` with proper nesting
    /// - Bytevectors: `#u8(` ... `)`
    /// - Quoted forms: `'datum`, `` `datum``, `,datum`, `,@datum`
    /// - Nested datum comments: `#; datum` within the skipped datum
    ///
    /// If the stream is empty or starts with an unexpected token (like `)`),
    /// this is a no-op (the parser will report the error).
    fn skip_one_datum_with_max_depth(&mut self, depth: u32) -> Result<(), ParseError> {
        // First, skip any leading datum comments within this datum.
        self.consume_intertoken_space_with_max_depth(depth)?;
        let (span, token_type) = {
            let token = match self.raw_peek() {
                Some(Ok(token)) => token,
                Some(Err(e)) => return Err(e.clone()),
                None => return Ok(()),
            };
            (token.span, token.value.clone())
        };

        if depth == 0 {
            return Err(ParseError::unsupported(span, Unsupported::DepthLimit));
        }

        match token_type {
            // Simple datums: just consume the token
            Token::Boolean(_)
            | Token::Number(_)
            | Token::Character(_)
            | Token::String(_)
            | Token::Identifier(_) => {
                let _ = self.raw_next();
            }

            // List or dotted list
            Token::LParen => {
                let _ = self.raw_next(); // consume (
                self.skip_list_contents_with_max_depth(depth - 1)?;
            }

            // Vector
            Token::VectorStart => {
                let _ = self.raw_next(); // consume #(
                self.skip_list_contents_with_max_depth(depth - 1)?;
            }

            // Bytevector
            Token::ByteVectorStart => {
                let _ = self.raw_next(); // consume #u8(
                self.skip_list_contents_with_max_depth(depth - 1)?;
            }

            // Abbreviations: quote, quasiquote, unquote, unquote-splicing
            Token::Quote | Token::Backquote | Token::Comma | Token::CommaAt => {
                let _ = self.raw_next(); // consume the prefix
                self.skip_one_datum_with_max_depth(depth - 1)?; // skip the following datum
            }

            // Labels
            Token::LabelDef(_) => {
                let _ = self.raw_next(); // consume #n=
                self.skip_one_datum_with_max_depth(depth - 1)?; // skip the following datum
            }
            Token::LabelRef(_) => {
                let _ = self.raw_next(); // consume #n#
            }

            // Nested datum comment - already handled by consume_intertoken_space, but
            // handle explicitly just in case.
            Token::DatumComment => {
                let _ = self.raw_next();
                self.skip_one_datum_with_max_depth(depth - 1)?;
            }

            // Unexpected tokens - leave for parser to handle
            Token::RParen | Token::Dot => {
                // Don't consume - this will be an error in the parser
            }
        }
        Ok(())
    }

    #[expect(dead_code)]
    fn skip_one_datum(&mut self) -> Result<(), ParseError> {
        self.skip_one_datum_with_max_depth(DEFAULT_MAX_DEPTH)
    }

    /// Skip contents of a list/vector until the closing `)`.
    fn skip_list_contents_with_max_depth(&mut self, depth: u32) -> Result<(), ParseError> {
        loop {
            self.consume_intertoken_space_with_max_depth(depth)?;

            let token_type = match self.raw_peek() {
                Some(Ok(token)) => token.value.clone(),
                Some(Err(e)) => return Err(e.clone()),
                None => return Ok(()),
            };

            match token_type {
                Token::RParen => {
                    let _ = self.raw_next(); // consume )
                    return Ok(());
                }
                Token::Dot => {
                    // Dotted list: skip the dot and the final datum
                    let _ = self.raw_next(); // consume .
                    self.skip_one_datum_with_max_depth(depth - 1)?;
                    // Now expect )
                    self.consume_intertoken_space_with_max_depth(depth)?;
                    if let Some(Ok(token)) = self.raw_peek()
                        && matches!(token.value, Token::RParen)
                    {
                        let _ = self.raw_next();
                    }
                    return Ok(());
                }
                _ => {
                    self.skip_one_datum_with_max_depth(depth - 1)?;
                }
            }
        }
    }

    #[expect(dead_code)]
    fn skip_list_contents(&mut self) -> Result<(), ParseError> {
        self.skip_list_contents_with_max_depth(DEFAULT_MAX_DEPTH)
    }

    /// Parse a single `<datum>` from the token stream.
    ///
    /// Grammar reference (`syn.tex` / External representations):
    ///
    /// ```text
    /// <datum> ::= <simple datum> | <compound datum>
    ///           | <label> = <datum> | <label> #
    /// ```
    ///
    /// This consumes tokens from the stream to form a complete datum,
    /// covering the currently implemented `<simple datum>` and
    /// `<compound datum>` alternatives plus label forms (`#n=` / `#n#`).
    pub fn parse_datum<W: DatumWriter>(
        &mut self,
        writer: &mut W,
    ) -> Result<(W::Output, Span), ParseError> {
        self.parse_datum_with_max_depth(writer, DEFAULT_MAX_DEPTH)
    }

    pub fn parse_datum_with_max_depth<W: DatumWriter>(
        &mut self,
        writer: &mut W,
        depth: u32,
    ) -> Result<(W::Output, Span), ParseError> {
        let token = self
            .next_token_with_max_depth(depth)?
            .ok_or(ParseError::Incomplete)?;
        let span = token.span;

        if depth == 0 {
            return Err(ParseError::unsupported(span, Unsupported::DepthLimit));
        }

        match token.value {
            Token::Boolean(b) => writer
                .bool(b, span)
                .map(|d| (d, span))
                .map_err(|e| ParseError::WriterError(format!("{e:?}"))),
            Token::Number(n) => {
                let num = W::N::from_literal(&n, span)?;
                writer
                    .number(num, span)
                    .map(|d| (d, span))
                    .map_err(|e| ParseError::WriterError(format!("{e:?}")))
            }
            Token::Character(c) => writer
                .char(c, span)
                .map(|d| (d, span))
                .map_err(|e| ParseError::WriterError(format!("{e:?}"))),
            Token::String(s) => {
                let id = writer.interner().intern(&s);
                writer
                    .string(id, span)
                    .map(|d| (d, span))
                    .map_err(|e| ParseError::WriterError(format!("{e:?}")))
            }
            Token::Identifier(s) => {
                let id = writer.interner().intern(&s);
                writer
                    .symbol(id, span)
                    .map(|d| (d, span))
                    .map_err(|e| ParseError::WriterError(format!("{e:?}")))
            }
            Token::LParen => self.parse_list_with_max_depth(writer, span, depth),
            Token::VectorStart => self.parse_vector_with_max_depth(writer, span, depth),
            Token::ByteVectorStart => self.parse_bytevector_with_max_depth(writer, span, depth),
            Token::Quote => self.parse_abbreviation_with_max_depth(writer, "quote", span, depth),
            Token::Backquote => {
                self.parse_abbreviation_with_max_depth(writer, "quasiquote", span, depth)
            }
            Token::Comma => self.parse_abbreviation_with_max_depth(writer, "unquote", span, depth),
            Token::CommaAt => {
                self.parse_abbreviation_with_max_depth(writer, "unquote-splicing", span, depth)
            }

            Token::LabelDef(n) => {
                let (datum, datum_span) = self.parse_datum_with_max_depth(writer, depth - 1)?;
                let full_span = span.merge(datum_span);
                writer
                    .labeled(n, datum, full_span)
                    .map(|d| (d, full_span))
                    .map_err(|e| ParseError::WriterError(format!("{e:?}")))
            }
            Token::LabelRef(n) => writer
                .label_ref(n, span)
                .map(|d| (d, span))
                .map_err(|e| ParseError::WriterError(format!("{e:?}"))),

            // Invalid start of datum
            Token::RParen | Token::Dot => Err(ParseError::syntax(
                span,
                "<datum>",
                format!("unexpected token {:?}", token.value),
            )),

            Token::DatumComment => unreachable!("TokenStream skips datum comments"),
        }
    }

    /// Parse a `<list>` (proper or improper) once the opening `(` has been consumed.
    ///
    /// Grammar reference (`syn.tex` / External representations):
    ///
    /// ```text
    /// <list> ::= ( <datum>* )
    ///          | ( <datum>+ . <datum> )
    /// ```
    fn parse_list_with_max_depth<W: DatumWriter>(
        &mut self,
        writer: &mut W,
        start_span: Span,
        depth: u32,
    ) -> Result<(W::Output, Span), ParseError> {
        if depth == 0 {
            return Err(ParseError::unsupported(start_span, Unsupported::DepthLimit));
        }

        let mut elements = Vec::new();
        let mut tail = None;
        let end_span;

        loop {
            // Check for end of list or dot
            match self.peek_token_value_with_max_depth(depth)? {
                Some(Token::RParen) => {
                    let token = self
                        .next_token_with_max_depth(depth)?
                        .ok_or(ParseError::Incomplete)?;
                    end_span = token.span;
                    break;
                }
                Some(Token::Dot) => {
                    if elements.is_empty() {
                        let span = self
                            .peek_with_max_depth(depth)?
                            .ok_or(ParseError::Incomplete)?
                            .span;
                        return Err(ParseError::syntax(
                            span,
                            "<list>",
                            "unexpected dot at start of list",
                        ));
                    }
                    self.next_token_with_max_depth(depth)?; // consume dot
                    let (tail_datum, _) = self.parse_datum_with_max_depth(writer, depth - 1)?;
                    tail = Some(tail_datum);

                    // Expect RParen
                    match self.next_token_with_max_depth(depth)? {
                        Some(token) if matches!(token.value, Token::RParen) => {
                            end_span = token.span;
                            break;
                        }
                        Some(token) => {
                            return Err(ParseError::syntax(
                                token.span,
                                "<list>",
                                "expected ')' after dotted list tail",
                            ));
                        }
                        None => return Err(ParseError::Incomplete),
                    }
                }
                None => return Err(ParseError::Incomplete),
                _ => {
                    elements.push(self.parse_datum_with_max_depth(writer, depth - 1)?.0);
                }
            }
        }

        let span = start_span.merge(end_span);
        if let Some(tail) = tail {
            writer
                .improper_list(elements, tail, span)
                .map(|d| (d, span))
                .map_err(|e| ParseError::WriterError(format!("{e:?}")))
        } else {
            writer
                .list(elements, span)
                .map(|d| (d, span))
                .map_err(|e| ParseError::WriterError(format!("{e:?}")))
        }
    }

    /// Parse a `<vector>` once the `#(` prefix has been consumed.
    ///
    /// Grammar reference (`syn.tex` / External representations):
    ///
    /// ```text
    /// <vector> ::= #( <datum>* )
    /// ```
    fn parse_vector_with_max_depth<W: DatumWriter>(
        &mut self,
        writer: &mut W,
        start_span: Span,
        depth: u32,
    ) -> Result<(W::Output, Span), ParseError> {
        if depth == 0 {
            return Err(ParseError::unsupported(start_span, Unsupported::DepthLimit));
        }

        let mut elements = Vec::new();
        let end_span;

        loop {
            match self.peek_token_value_with_max_depth(depth)? {
                Some(Token::RParen) => {
                    let token = self
                        .next_token_with_max_depth(depth)?
                        .ok_or(ParseError::Incomplete)?;
                    end_span = token.span;
                    break;
                }
                None => return Err(ParseError::Incomplete),
                _ => {
                    elements.push(self.parse_datum_with_max_depth(writer, depth - 1)?.0);
                }
            }
        }

        let span = start_span.merge(end_span);
        writer
            .vector(elements, span)
            .map(|d| (d, span))
            .map_err(|e| ParseError::WriterError(format!("{e:?}")))
    }

    /// Parse an `<abbreviation>` (quote, quasiquote, unquote variants).
    ///
    /// Grammar reference (`syn.tex` / External representations):
    ///
    /// ```text
    /// <abbreviation> ::= <abbrev prefix> <datum>
    /// <abbrev prefix> ::= ' | ` | , | ,@
    /// ```
    ///
    /// Each abbreviation expands into its desugared list form (e.g., `'x` ⇒ `(quote x)`).
    fn parse_abbreviation_with_max_depth<W: DatumWriter>(
        &mut self,
        writer: &mut W,
        name: &str,
        start_span: Span,
        depth: u32,
    ) -> Result<(W::Output, Span), ParseError> {
        if depth == 0 {
            return Err(ParseError::unsupported(start_span, Unsupported::DepthLimit));
        }

        let (datum, datum_span) = self.parse_datum_with_max_depth(writer, depth - 1)?;
        let span = start_span.merge(datum_span);

        let sym_id = writer.interner().intern(name);
        let sym = writer
            .symbol(sym_id, start_span)
            .map_err(|e| ParseError::WriterError(format!("{e:?}")))?;

        // Build (name datum)
        writer
            .list([sym, datum], span)
            .map(|d| (d, span))
            .map_err(|e| ParseError::WriterError(format!("{e:?}")))
    }

    /// Parse a `<bytevector>` datum once the `#u8(` prefix has been consumed.
    ///
    /// Grammar reference (`syn.tex` / External representations):
    ///
    /// ```text
    /// <bytevector> ::= #u8( <byte>* )
    /// <byte> ::= any exact integer between 0 and 255
    /// ```
    fn parse_bytevector_with_max_depth<W: DatumWriter>(
        &mut self,
        writer: &mut W,
        start_span: Span,
        depth: u32,
    ) -> Result<(W::Output, Span), ParseError> {
        if depth == 0 {
            return Err(ParseError::unsupported(start_span, Unsupported::DepthLimit));
        }

        let mut elements = Vec::new();
        let end_span;

        loop {
            match self.peek_token_value_with_max_depth(depth)? {
                Some(Token::RParen) => {
                    let token = self
                        .next_token_with_max_depth(depth)?
                        .ok_or(ParseError::Incomplete)?;
                    end_span = token.span;
                    break;
                }
                None => return Err(ParseError::Incomplete),
                _ => {
                    // Bytevectors must contain exact integers in the closed range [0, 255].
                    // Parse `<byte>` directly from the token stream so this does not depend on
                    // any particular number backend.
                    let token = self
                        .next_token_with_max_depth(depth)?
                        .ok_or(ParseError::Incomplete)?;

                    let value = match token.value {
                        Token::Number(lit) => number_literal_to_byte(&lit),
                        _ => None,
                    };

                    if let Some(value) = value {
                        elements.push(value);
                    } else {
                        return Err(ParseError::syntax(
                            token.span,
                            "<bytevector>",
                            "expected exact integer 0-255",
                        ));
                    }
                }
            }
        }

        let span = start_span.merge(end_span);
        writer
            .bytevector(&elements, span)
            .map(|d| (d, span))
            .map_err(|e| ParseError::WriterError(format!("{e:?}")))
    }
}

/// Attempt to interpret `literal` as a `<byte>` value (exact integer 0-255).
fn number_literal_to_byte(literal: &lex::NumberLiteral<'_>) -> Option<u8> {
    match literal.kind.exactness {
        NumberExactness::Inexact => return None,
        NumberExactness::Exact | NumberExactness::Unspecified => {}
    }

    let radix = literal.kind.radix;

    match &literal.kind.value {
        lex::NumberValue::Real(real) => match &real.magnitude {
            lex::RealMagnitude::Finite(lex::FiniteRealMagnitude {
                kind: FiniteRealKind::Integer,
                spelling,
            }) => {
                let value = integer_spelling_to_byte(spelling, radix)?;

                match real.sign {
                    Some(lex::Sign::Negative) => {
                        if value == 0 {
                            Some(0)
                        } else {
                            None
                        }
                    }
                    _ => Some(value),
                }
            }
            _ => None,
        },
        _ => None,
    }
}

fn integer_spelling_to_byte(spelling: &str, radix: u32) -> Option<u8> {
    if spelling.is_empty() {
        return None;
    }

    let mut value: u32 = 0;
    for ch in spelling.chars() {
        let digit = ch.to_digit(radix)?;
        value = value.checked_mul(radix)?;
        value = value.checked_add(digit)?;
        if value > 255 {
            return None;
        }
    }

    Some(value as u8)
}

/// Parse a single `<datum>` from the given source string.
///
/// Grammar reference: see `syn.tex`, section *External representations*,
/// production:
///
/// ```text
/// <datum> ::= <simple datum> | <compound datum>
///           | <label> = <datum> | <label> #
/// ```
pub fn parse_datum<W: DatumWriter>(
    source: &str,
    writer: &mut W,
) -> Result<(W::Output, Span), ParseError> {
    parse_datum_with_max_depth(source, writer, DEFAULT_MAX_DEPTH)
}

/// Parse a single `<datum>` from the given source string with an
/// explicit maximum nesting depth.
pub fn parse_datum_with_max_depth<W: DatumWriter>(
    source: &str,
    writer: &mut W,
    max_depth: u32,
) -> Result<(W::Output, Span), ParseError> {
    let mut stream = TokenStream::from_source(source);
    let datum = stream.parse_datum_with_max_depth(writer, max_depth)?;

    if !stream.is_empty() {
        // If there are remaining tokens, it's an error for a single datum parse
        let next = stream.peek()?.ok_or(ParseError::Incomplete)?;
        return Err(ParseError::lexical(
            next.span,
            "<datum>",
            "unexpected token after datum",
        ));
    }

    Ok(datum)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scheme::{
        Unsupported,
        lex::Token,
        primitivenumbers::SimpleNumber,
        samples::scheme::{Datum, SampleWriter},
    };
    use bumpalo::Bump;

    struct TestCase {
        name: &'static str,
        input: &'static str,
        mode: TestMode,
    }

    enum TestMode {
        Datum(Expected<DatumMatcher>),
        TokenStream(Expected<Vec<TokenMatcher>>),
    }

    enum Expected<T> {
        Success(T),
        Error(ErrorMatcher),
    }

    #[derive(Debug)]
    enum DatumMatcher {
        Bool(bool),
        Int(i64),
        Float(f64),
        Char(char),
        Str(&'static str),
        Sym(&'static str),
        EmptyList,
        Pair(Box<DatumMatcher>, Box<DatumMatcher>),
        Vector(Vec<DatumMatcher>),
        ByteVector(Vec<u8>),
        Labeled(u64, Box<DatumMatcher>),
        LabelRef(u64),
    }

    #[derive(Debug)]
    enum TokenMatcher {
        Ident(&'static str),
    }

    #[derive(Debug)]
    enum ErrorMatcher {
        Incomplete,
        Syntax(&'static str),
        UnsupportedDepth,
    }

    impl TestCase {
        fn run(&self) {
            match &self.mode {
                TestMode::Datum(expected) => self.run_datum(expected),
                TestMode::TokenStream(expected) => self.run_token_stream(expected),
            }
        }

        fn run_datum(&self, expected: &Expected<DatumMatcher>) {
            let arena = Bump::new();
            let mut writer = SampleWriter::new(&arena);
            let result = parse_datum(self.input, &mut writer);
            match expected {
                Expected::Success(matcher) => {
                    let (syntax, _) = result
                        .unwrap_or_else(|e| panic!("{}: expected success, got {:?}", self.name, e));
                    matcher.check(&syntax.value, self.name);
                }
                Expected::Error(matcher) => {
                    let err =
                        result.expect_err(&format!("{}: expected error, got success", self.name));
                    matcher.check(&err, self.name);
                }
            }
        }

        fn run_token_stream(&self, expected: &Expected<Vec<TokenMatcher>>) {
            let mut ts = TokenStream::from_source(self.input);

            match expected {
                Expected::Success(matchers) => {
                    let mut tokens = Vec::new();
                    while let Some(tok) = ts.next_token().unwrap() {
                        tokens.push(tok);
                    }

                    assert_eq!(
                        tokens.len(),
                        matchers.len(),
                        "{}: token count mismatch",
                        self.name
                    );
                    for (i, (tok, matcher)) in tokens.iter().zip(matchers.iter()).enumerate() {
                        matcher.check(&tok.value, self.name, i);
                    }
                }
                Expected::Error(_) => {
                    // TokenStream::from_source handles lex errors, but next_token doesn't return errors currently.
                }
            }
        }
    }

    impl DatumMatcher {
        fn check(&self, datum: &Datum, test_name: &str) {
            match (self, datum) {
                (DatumMatcher::Bool(e), Datum::Boolean(a)) => {
                    assert_eq!(e, a, "{test_name}: boolean mismatch")
                }
                (DatumMatcher::Int(e), Datum::Number(SimpleNumber::Integer(a))) => {
                    assert_eq!(e, a, "{test_name}: integer mismatch")
                }
                (DatumMatcher::Float(e), Datum::Number(SimpleNumber::Float(a))) => {
                    assert!((e - a).abs() < f64::EPSILON, "{test_name}: float mismatch")
                }
                (DatumMatcher::Char(e), Datum::Character(a)) => {
                    assert_eq!(e, a, "{test_name}: character mismatch")
                }
                (DatumMatcher::Str(e), Datum::String(a)) => {
                    assert_eq!(e, a, "{test_name}: string mismatch")
                }
                (DatumMatcher::Sym(e), Datum::Symbol(a)) => {
                    assert_eq!(e, a, "{test_name}: symbol mismatch")
                }
                (DatumMatcher::EmptyList, Datum::EmptyList) => {}
                (DatumMatcher::Pair(e_car, e_cdr), Datum::Pair(a_car, a_cdr)) => {
                    e_car.check(&a_car.value, test_name);
                    e_cdr.check(&a_cdr.value, test_name);
                }
                (DatumMatcher::Vector(e_vec), Datum::Vector(a_vec)) => {
                    assert_eq!(
                        e_vec.len(),
                        a_vec.len(),
                        "{test_name}: vector length mismatch"
                    );
                    for (e, a) in e_vec.iter().zip(a_vec.iter()) {
                        e.check(&a.value, test_name);
                    }
                }
                (DatumMatcher::ByteVector(e), Datum::ByteVector(a)) => {
                    assert_eq!(e, a, "{test_name}: bytevector mismatch")
                }
                (DatumMatcher::Labeled(e_n, e_d), Datum::Labeled(a_n, a_d)) => {
                    assert_eq!(e_n, a_n, "{test_name}: label id mismatch");
                    e_d.check(&a_d.value, test_name);
                }
                (DatumMatcher::LabelRef(e), Datum::LabelRef(a)) => {
                    assert_eq!(e, a, "{test_name}: label ref mismatch")
                }
                _ => panic!("{test_name}: datum type mismatch. Expected {self:?}, got {datum:?}"),
            }
        }
    }

    impl TokenMatcher {
        fn check(&self, token: &Token, test_name: &str, index: usize) {
            match (self, token) {
                (TokenMatcher::Ident(e), Token::Identifier(a)) => {
                    assert_eq!(e, a, "{test_name}: token {index} mismatch")
                }
                _ => panic!(
                    "{test_name}: token {index} type mismatch. Expected {self:?}, got {token:?}"
                ),
            }
        }
    }

    impl ErrorMatcher {
        fn check(&self, err: &ParseError, test_name: &str) {
            match (self, err) {
                (ErrorMatcher::Incomplete, ParseError::Incomplete) => {}
                (ErrorMatcher::Syntax(expected_nt), ParseError::Syntax { nonterminal, .. }) => {
                    assert_eq!(
                        expected_nt, nonterminal,
                        "{test_name}: nonterminal mismatch"
                    );
                }
                (ErrorMatcher::UnsupportedDepth, ParseError::Unsupported { feature, .. }) => {
                    assert_eq!(
                        feature,
                        &Unsupported::DepthLimit,
                        "{test_name}: expected depth-limit unsupported error",
                    );
                }
                _ => panic!("{test_name}: error mismatch. Expected {self:?}, got {err:?}"),
            }
        }
    }

    #[test]
    fn depth_limit_enforced_by_default() {
        // Build a deeply nested list: (((... 0 ...))) with depth > 64
        let depth = 70usize;
        let mut input = String::new();
        for _ in 0..depth {
            input.push('(');
        }
        input.push('0');
        for _ in 0..depth {
            input.push(')');
        }

        let arena = Bump::new();
        let mut writer = SampleWriter::new(&arena);
        let result = parse_datum(&input, &mut writer);
        let err = result.expect_err("expected depth-limit error");
        ErrorMatcher::UnsupportedDepth.check(&err, "depth_limit_enforced_by_default");
    }

    #[test]
    fn depth_limit_can_be_raised() {
        // Same nested list but with an increased max depth that should succeed.
        let depth = 70usize;
        let mut input = String::new();
        for _ in 0..depth {
            input.push('(');
        }
        input.push('0');
        for _ in 0..depth {
            input.push(')');
        }

        let arena = Bump::new();
        let mut writer = SampleWriter::new(&arena);
        let (syntax, _) = parse_datum_with_max_depth(&input, &mut writer, 128)
            .expect("expected success with increased max depth");
        if let Datum::Pair(_, _) = syntax.value {
            // Shallow sanity check: we at least parsed a non-trivial list.
        } else {
            panic!("depth_limit_can_be_raised: expected a list datum");
        }
    }

    fn list_matcher(elements: Vec<DatumMatcher>) -> DatumMatcher {
        let mut current = DatumMatcher::EmptyList;
        for elem in elements.into_iter().rev() {
            current = DatumMatcher::Pair(Box::new(elem), Box::new(current));
        }
        current
    }

    #[test]
    fn run_all_tests() {
        let cases = vec![
            // --- Datum Tests ---
            TestCase {
                name: "boolean_true_short",
                input: "#t",
                mode: TestMode::Datum(Expected::Success(DatumMatcher::Bool(true))),
            },
            TestCase {
                name: "boolean_false_short",
                input: "#f",
                mode: TestMode::Datum(Expected::Success(DatumMatcher::Bool(false))),
            },
            TestCase {
                name: "boolean_true_long",
                input: "#true",
                mode: TestMode::Datum(Expected::Success(DatumMatcher::Bool(true))),
            },
            TestCase {
                name: "boolean_false_long",
                input: "#false",
                mode: TestMode::Datum(Expected::Success(DatumMatcher::Bool(false))),
            },
            TestCase {
                name: "boolean_case_insensitive_1",
                input: "#T",
                mode: TestMode::Datum(Expected::Success(DatumMatcher::Bool(true))),
            },
            TestCase {
                name: "boolean_case_insensitive_2",
                input: "#FaLsE",
                mode: TestMode::Datum(Expected::Success(DatumMatcher::Bool(false))),
            },
            TestCase {
                name: "number_simple_42",
                input: "42",
                mode: TestMode::Datum(Expected::Success(DatumMatcher::Int(42))),
            },
            TestCase {
                name: "number_negative",
                input: "-123",
                mode: TestMode::Datum(Expected::Success(DatumMatcher::Int(-123))),
            },
            TestCase {
                name: "number_float",
                input: "3.15",
                mode: TestMode::Datum(Expected::Success(DatumMatcher::Float(3.15))),
            },
            TestCase {
                name: "character_simple",
                input: "#\\a",
                mode: TestMode::Datum(Expected::Success(DatumMatcher::Char('a'))),
            },
            TestCase {
                name: "symbol_simple",
                input: "foo",
                mode: TestMode::Datum(Expected::Success(DatumMatcher::Sym("foo"))),
            },
            TestCase {
                name: "list_empty",
                input: "()",
                mode: TestMode::Datum(Expected::Success(DatumMatcher::EmptyList)),
            },
            TestCase {
                name: "list_proper",
                input: "(1 2 3)",
                mode: TestMode::Datum(Expected::Success(list_matcher(vec![
                    DatumMatcher::Int(1),
                    DatumMatcher::Int(2),
                    DatumMatcher::Int(3),
                ]))),
            },
            TestCase {
                name: "list_dotted",
                input: "(1 . 2)",
                mode: TestMode::Datum(Expected::Success(DatumMatcher::Pair(
                    Box::new(DatumMatcher::Int(1)),
                    Box::new(DatumMatcher::Int(2)),
                ))),
            },
            TestCase {
                name: "vector_simple",
                input: "#(1 2)",
                mode: TestMode::Datum(Expected::Success(DatumMatcher::Vector(vec![
                    DatumMatcher::Int(1),
                    DatumMatcher::Int(2),
                ]))),
            },
            TestCase {
                name: "bytevector_simple",
                input: "#u8(1 2 255)",
                mode: TestMode::Datum(Expected::Success(DatumMatcher::ByteVector(vec![1, 2, 255]))),
            },
            TestCase {
                name: "bytevector_mixed_radix",
                input: "#u8(#xFF #o10 #b11 #d0 #e7 #x0A)",
                mode: TestMode::Datum(Expected::Success(DatumMatcher::ByteVector(vec![
                    255, 8, 3, 0, 7, 10,
                ]))),
            },
            TestCase {
                name: "bytevector_negative_zero",
                input: "#u8(-0 0)",
                mode: TestMode::Datum(Expected::Success(DatumMatcher::ByteVector(vec![0, 0]))),
            },
            TestCase {
                name: "bytevector_inexact",
                input: "#u8(#i10)",
                mode: TestMode::Datum(Expected::Error(ErrorMatcher::Syntax("<bytevector>"))),
            },
            TestCase {
                name: "bytevector_out_of_range",
                input: "#u8(256)",
                mode: TestMode::Datum(Expected::Error(ErrorMatcher::Syntax("<bytevector>"))),
            },
            TestCase {
                name: "label_def",
                input: "#1=(1 2)",
                mode: TestMode::Datum(Expected::Success(DatumMatcher::Labeled(
                    1,
                    Box::new(list_matcher(vec![
                        DatumMatcher::Int(1),
                        DatumMatcher::Int(2),
                    ])),
                ))),
            },
            TestCase {
                name: "label_ref",
                input: "#1#",
                mode: TestMode::Datum(Expected::Success(DatumMatcher::LabelRef(1))),
            },
            TestCase {
                name: "label_cycle",
                input: "#1=(1 . #1#)",
                mode: TestMode::Datum(Expected::Success(DatumMatcher::Labeled(
                    1,
                    Box::new(DatumMatcher::Pair(
                        Box::new(DatumMatcher::Int(1)),
                        Box::new(DatumMatcher::LabelRef(1)),
                    )),
                ))),
            },
            TestCase {
                name: "quote_simple",
                input: "'foo",
                mode: TestMode::Datum(Expected::Success(list_matcher(vec![
                    DatumMatcher::Sym("quote"),
                    DatumMatcher::Sym("foo"),
                ]))),
            },
            TestCase {
                name: "quasiquote_list",
                input: "`(1 ,2)",
                mode: TestMode::Datum(Expected::Success(list_matcher(vec![
                    DatumMatcher::Sym("quasiquote"),
                    list_matcher(vec![
                        DatumMatcher::Int(1),
                        list_matcher(vec![DatumMatcher::Sym("unquote"), DatumMatcher::Int(2)]),
                    ]),
                ]))),
            },
            TestCase {
                name: "string_simple",
                input: "\"hello\"",
                mode: TestMode::Datum(Expected::Success(DatumMatcher::Str("hello"))),
            },
            TestCase {
                name: "string_whitespace",
                input: "  \"hi\"  ",
                mode: TestMode::Datum(Expected::Success(DatumMatcher::Str("hi"))),
            },
            TestCase {
                name: "string_escapes",
                input: r#""a\n\t\r\b\a\\\"""#,
                mode: TestMode::Datum(Expected::Success(DatumMatcher::Str(
                    "a\n\t\r\u{8}\u{7}\\\"",
                ))),
            },
            TestCase {
                name: "string_hex_escape",
                input: r#""\x41;""#,
                mode: TestMode::Datum(Expected::Success(DatumMatcher::Str("A"))),
            },
            TestCase {
                name: "string_line_splice",
                input: "\"foo\\\n   bar\"",
                mode: TestMode::Datum(Expected::Success(DatumMatcher::Str("foobar"))),
            },
            TestCase {
                name: "string_incomplete",
                input: "\"unterminated",
                mode: TestMode::Datum(Expected::Error(ErrorMatcher::Incomplete)),
            },
            TestCase {
                name: "number_simple_123",
                input: "123",
                mode: TestMode::Datum(Expected::Success(DatumMatcher::Int(123))),
            },
            TestCase {
                name: "symbol_simple_abc",
                input: "abc",
                mode: TestMode::Datum(Expected::Success(DatumMatcher::Sym("abc"))),
            },
            TestCase {
                name: "syntax_unexpected_rparen",
                input: ")",
                mode: TestMode::Datum(Expected::Error(ErrorMatcher::Syntax("<datum>"))),
            },
            TestCase {
                name: "incomplete_list",
                input: "(1 2",
                mode: TestMode::Datum(Expected::Error(ErrorMatcher::Incomplete)),
            },
            // --- TokenStream Tests (Datum Comments) ---
            TestCase {
                name: "ts_skip_simple",
                input: "#; foo bar",
                mode: TestMode::TokenStream(Expected::Success(vec![TokenMatcher::Ident("bar")])),
            },
            TestCase {
                name: "ts_skip_list",
                input: "#; (a b c) bar",
                mode: TestMode::TokenStream(Expected::Success(vec![TokenMatcher::Ident("bar")])),
            },
            TestCase {
                name: "ts_skip_nested",
                input: "#; (a #; b c) bar",
                mode: TestMode::TokenStream(Expected::Success(vec![TokenMatcher::Ident("bar")])),
            },
            TestCase {
                name: "ts_skip_quoted",
                input: "#; 'foo bar",
                mode: TestMode::TokenStream(Expected::Success(vec![TokenMatcher::Ident("bar")])),
            },
            TestCase {
                name: "ts_skip_vector",
                input: "#; #(1 2 3) bar",
                mode: TestMode::TokenStream(Expected::Success(vec![TokenMatcher::Ident("bar")])),
            },
            TestCase {
                name: "ts_skip_multiple",
                input: "#; a #; b c",
                mode: TestMode::TokenStream(Expected::Success(vec![TokenMatcher::Ident("c")])),
            },
            TestCase {
                name: "ts_skip_dotted",
                input: "#; (a . b) c",
                mode: TestMode::TokenStream(Expected::Success(vec![TokenMatcher::Ident("c")])),
            },
        ];

        for case in cases {
            case.run();
        }
    }
}
