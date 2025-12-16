use crate::common::{Span, Syntax};
use crate::scheme::datumtraits::{
    NumberLiteral, NumberValue, PrimitiveOps, RealRepr, SchemeNumberOps, SimpleNumber,
};
use crate::scheme::lex::{self, FiniteRealKind, NumberExactness, NumberRadix, SpannedToken, Token};
use crate::scheme::{ParseError, Unsupported};

/// Datum syntax as defined in the "External representations" section
/// of `spec/syn.md`.
#[derive(Clone, Debug, PartialEq)]
pub enum Datum {
    Boolean(bool),
    Number(SimpleNumber),
    Character(char),
    String(String),
    Symbol(String),
    ByteVector(Vec<u8>),
    /// The empty list `()`.
    EmptyList,
    /// Proper and improper lists are represented via pairs.
    Pair(Box<Syntax<Datum>>, Box<Syntax<Datum>>),
    Vector(Vec<Syntax<Datum>>),
    /// A labeled datum: #n=datum
    Labeled(u64, Box<Syntax<Datum>>),
    /// A reference to a previously defined label: #n#
    LabelRef(u64),
}

// ============================================================================
// Token Stream with Datum Comment Handling
// ============================================================================

/// A token stream that handles `#;` datum comments at the parser level.
pub struct TokenStream<'i> {
    lexer: std::iter::Peekable<lex::Lexer<'i>>,
}

const DEFAULT_MAX_DEPTH: u32 = 64;

impl<'i> TokenStream<'i> {
    /// Create a new token stream from lexed tokens.
    pub fn new(lexer: lex::Lexer<'i>) -> Self {
        Self {
            lexer: lexer.peekable(),
        }
    }

    /// Lex source and create a token stream.
    pub fn from_source(source: &'i str) -> Self {
        Self::new(lex::lex(source))
    }
    /// Peek at the next token without consuming it, skipping intertoken
    /// space such as datum comments, with an explicit maximum depth
    /// used when skipping comments.
    fn peek_with_max_depth(&mut self, depth: u32) -> Result<Option<&SpannedToken<'i>>, ParseError> {
        self.consume_intertoken_space_with_max_depth(depth)?;
        match self.lexer.peek() {
            Some(Ok(token)) => Ok(Some(token)),
            Some(Err(e)) => Err(e.clone()),
            None => Ok(None),
        }
    }

    /// Public peek that uses the default maximum depth when skipping
    /// comments.
    pub fn peek(&mut self) -> Result<Option<&SpannedToken<'i>>, ParseError> {
        self.peek_with_max_depth(DEFAULT_MAX_DEPTH)
    }

    /// Peek at the next token's value without consuming it, skipping
    /// intertoken space, with an explicit maximum depth.
    fn peek_token_value_with_max_depth(
        &mut self,
        depth: u32,
    ) -> Result<Option<&Token<'i>>, ParseError> {
        Ok(self.peek_with_max_depth(depth)?.map(|st| &st.value))
    }

    /// Public peek of the token value using the default depth.
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
        match self.lexer.next() {
            Some(Ok(token)) => Ok(Some(token)),
            Some(Err(e)) => Err(e),
            None => Ok(None),
        }
    }

    /// Public `next_token` that uses the default maximum depth when
    /// skipping comments.
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
            let span = match self.lexer.peek() {
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
                    self.lexer.next(); // consume #;
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
    #[allow(dead_code)]
    fn skip_one_datum_with_max_depth(&mut self, depth: u32) -> Result<(), ParseError> {
        // First, skip any leading datum comments within this datum.
        self.consume_intertoken_space_with_max_depth(depth)?;
        let (span, token_type) = {
            let token = match self.lexer.peek() {
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
                self.lexer.next();
            }

            // List or dotted list
            Token::LParen => {
                self.lexer.next(); // consume (
                self.skip_list_contents_with_max_depth(depth - 1)?;
            }

            // Vector
            Token::VectorStart => {
                self.lexer.next(); // consume #(
                self.skip_list_contents_with_max_depth(depth - 1)?;
            }

            // Bytevector
            Token::ByteVectorStart => {
                self.lexer.next(); // consume #u8(
                self.skip_list_contents_with_max_depth(depth - 1)?;
            }

            // Abbreviations: quote, quasiquote, unquote, unquote-splicing
            Token::Quote | Token::Backquote | Token::Comma | Token::CommaAt => {
                self.lexer.next(); // consume the prefix
                self.skip_one_datum_with_max_depth(depth - 1)?; // skip the following datum
            }

            // Labels
            Token::LabelDef(_) => {
                self.lexer.next(); // consume #n=
                self.skip_one_datum_with_max_depth(depth - 1)?; // skip the following datum
            }
            Token::LabelRef(_) => {
                self.lexer.next(); // consume #n#
            }

            // Nested datum comment - already handled by consume_intertoken_space, but
            // handle explicitly just in case.
            Token::DatumComment => {
                self.lexer.next();
                self.skip_one_datum_with_max_depth(depth - 1)?;
            }

            // Unexpected tokens - leave for parser to handle
            Token::RParen | Token::Dot => {
                // Don't consume - this will be an error in the parser
            }
        }
        Ok(())
    }

    #[allow(dead_code)]
    fn skip_one_datum(&mut self) -> Result<(), ParseError> {
        self.skip_one_datum_with_max_depth(DEFAULT_MAX_DEPTH)
    }

    /// Skip contents of a list/vector until the closing `)`.
    #[allow(dead_code)]
    fn skip_list_contents_with_max_depth(&mut self, depth: u32) -> Result<(), ParseError> {
        loop {
            self.consume_intertoken_space_with_max_depth(depth)?;

            let token_type = match self.lexer.peek() {
                Some(Ok(token)) => token.value.clone(),
                Some(Err(e)) => return Err(e.clone()),
                None => return Ok(()),
            };

            match token_type {
                Token::RParen => {
                    self.lexer.next(); // consume )
                    return Ok(());
                }
                Token::Dot => {
                    // Dotted list: skip the dot and the final datum
                    self.lexer.next(); // consume .
                    self.skip_one_datum_with_max_depth(depth - 1)?;
                    // Now expect )
                    self.consume_intertoken_space_with_max_depth(depth)?;
                    if let Some(Ok(token)) = self.lexer.peek()
                        && matches!(token.value, Token::RParen)
                    {
                        self.lexer.next();
                    }
                    return Ok(());
                }
                _ => {
                    self.skip_one_datum_with_max_depth(depth - 1)?;
                }
            }
        }
    }

    #[allow(dead_code)]
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
    pub fn parse_datum(&mut self) -> Result<Syntax<Datum>, ParseError> {
        self.parse_datum_with_max_depth(DEFAULT_MAX_DEPTH)
    }

    fn parse_datum_with_max_depth(&mut self, depth: u32) -> Result<Syntax<Datum>, ParseError> {
        let token = self
            .next_token_with_max_depth(depth)?
            .ok_or(ParseError::Incomplete)?;
        let span = token.span;

        if depth == 0 {
            return Err(ParseError::unsupported(span, Unsupported::DepthLimit));
        }

        match token.value {
            Token::Boolean(b) => Ok(Syntax::new(span, Datum::Boolean(b))),
            Token::Number(n) => {
                let num = PrimitiveOps::from_literal(&n.into(), span)?;
                Ok(Syntax::new(span, Datum::Number(num)))
            }
            Token::Character(c) => Ok(Syntax::new(span, Datum::Character(c))),
            Token::String(s) => Ok(Syntax::new(span, Datum::String(s.into_owned()))),
            Token::Identifier(s) => Ok(Syntax::new(span, Datum::Symbol(s.into_owned()))),

            Token::LParen => self.parse_list_with_max_depth(span, depth),
            Token::VectorStart => self.parse_vector_with_max_depth(span, depth),
            Token::ByteVectorStart => self.parse_bytevector_with_max_depth(span, depth),
            Token::Quote => self.parse_abbreviation_with_max_depth("quote", span, depth),
            Token::Backquote => self.parse_abbreviation_with_max_depth("quasiquote", span, depth),
            Token::Comma => self.parse_abbreviation_with_max_depth("unquote", span, depth),
            Token::CommaAt => {
                self.parse_abbreviation_with_max_depth("unquote-splicing", span, depth)
            }

            Token::LabelDef(n) => {
                let datum = self.parse_datum_with_max_depth(depth - 1)?;
                let span = span.merge(datum.span);
                Ok(Syntax::new(span, Datum::Labeled(n, Box::new(datum))))
            }
            Token::LabelRef(n) => Ok(Syntax::new(span, Datum::LabelRef(n))),

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
    fn parse_list_with_max_depth(
        &mut self,
        start_span: Span,
        depth: u32,
    ) -> Result<Syntax<Datum>, ParseError> {
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
                    if tail.is_none() {
                        tail = Some(Syntax::new(end_span, Datum::EmptyList));
                    }
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
                    let tail_datum = self.parse_datum_with_max_depth(depth - 1)?;
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
                    elements.push(self.parse_datum_with_max_depth(depth - 1)?);
                }
            }
        }

        // Construct the list from right to left
        let mut current = tail.unwrap();

        for elem in elements.into_iter().rev() {
            let span = elem.span.merge(current.span);
            current = Syntax::new(span, Datum::Pair(Box::new(elem), Box::new(current)));
        }

        Ok(Syntax::new(start_span.merge(end_span), current.value))
    }

    /// Parse a `<vector>` once the `#(` prefix has been consumed.
    ///
    /// Grammar reference (`syn.tex` / External representations):
    ///
    /// ```text
    /// <vector> ::= #( <datum>* )
    /// ```
    fn parse_vector_with_max_depth(
        &mut self,
        start_span: Span,
        depth: u32,
    ) -> Result<Syntax<Datum>, ParseError> {
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
                    elements.push(self.parse_datum_with_max_depth(depth - 1)?);
                }
            }
        }

        Ok(Syntax::new(
            start_span.merge(end_span),
            Datum::Vector(elements),
        ))
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
    fn parse_abbreviation_with_max_depth(
        &mut self,
        name: &str,
        start_span: Span,
        depth: u32,
    ) -> Result<Syntax<Datum>, ParseError> {
        if depth == 0 {
            return Err(ParseError::unsupported(start_span, Unsupported::DepthLimit));
        }

        let datum = self.parse_datum_with_max_depth(depth - 1)?;
        let end_span = datum.span;

        // Construct (name datum)
        // tail = Pair(datum, EmptyList)
        // We use the datum's span for the tail parts as they don't have their own source tokens
        let empty = Syntax::new(end_span, Datum::EmptyList);
        let tail = Syntax::new(end_span, Datum::Pair(Box::new(datum), Box::new(empty)));

        // head = Pair(name, tail)
        let sym = Syntax::new(start_span, Datum::Symbol(name.to_string()));
        let head = Syntax::new(
            start_span.merge(end_span),
            Datum::Pair(Box::new(sym), Box::new(tail)),
        );

        Ok(head)
    }

    /// Parse a `<bytevector>` datum once the `#u8(` prefix has been consumed.
    ///
    /// Grammar reference (`syn.tex` / External representations):
    ///
    /// ```text
    /// <bytevector> ::= #u8( <byte>* )
    /// <byte> ::= any exact integer between 0 and 255
    /// ```
    fn parse_bytevector_with_max_depth(
        &mut self,
        start_span: Span,
        depth: u32,
    ) -> Result<Syntax<Datum>, ParseError> {
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
                    let datum = self.parse_datum_with_max_depth(depth - 1)?;
                    if let Some(value) = match &datum.value {
                        Datum::Number(SimpleNumber::Literal(lit)) => number_literal_to_byte(lit),
                        Datum::Number(SimpleNumber::Integer(i)) => {
                            if *i >= 0 && *i <= 255 {
                                Some(*i as u8)
                            } else {
                                None
                            }
                        }
                        _ => None,
                    } {
                        elements.push(value);
                    } else {
                        return Err(ParseError::syntax(
                            datum.span,
                            "<bytevector>",
                            "expected exact integer 0-255",
                        ));
                    }
                }
            }
        }

        Ok(Syntax::new(
            start_span.merge(end_span),
            Datum::ByteVector(elements),
        ))
    }
}

/// Attempt to interpret `literal` as a `<byte>` value (exact integer 0-255).
fn number_literal_to_byte(literal: &NumberLiteral) -> Option<u8> {
    match literal.kind.exactness {
        NumberExactness::Inexact => return None,
        NumberExactness::Exact | NumberExactness::Unspecified => {}
    }

    let radix = match literal.kind.radix {
        NumberRadix::Binary => 2,
        NumberRadix::Octal => 8,
        NumberRadix::Decimal => 10,
        NumberRadix::Hexadecimal => 16,
    };

    match &literal.kind.value {
        NumberValue::Real(RealRepr::Finite {
            kind: FiniteRealKind::Integer,
            spelling,
        }) => integer_spelling_to_byte(spelling, radix),
        _ => None,
    }
}

fn integer_spelling_to_byte(spelling: &str, radix: u32) -> Option<u8> {
    let digits = if let Some(rest) = spelling.strip_prefix('+') {
        rest
    } else if spelling.starts_with('-') {
        return None;
    } else {
        spelling
    };

    if digits.is_empty() {
        return None;
    }

    let mut value: u32 = 0;
    for ch in digits.chars() {
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
pub fn parse_datum(source: &str) -> Result<Syntax<Datum>, ParseError> {
    parse_datum_with_max_depth(source, DEFAULT_MAX_DEPTH)
}

/// Parse a single `<datum>` from the given source string with an
/// explicit maximum nesting depth.
pub fn parse_datum_with_max_depth(
    source: &str,
    max_depth: u32,
) -> Result<Syntax<Datum>, ParseError> {
    let mut stream = TokenStream::from_source(source);
    let datum = stream.parse_datum_with_max_depth(max_depth)?;

    if !stream.is_empty() {
        // If there are remaining tokens, it's an error for a single datum parse
        let next = stream.peek()?.ok_or(ParseError::Incomplete)?;
        return Err(ParseError::lexical(
            next.span,
            "<datum>",
            "extra tokens after datum",
        ));
    }

    Ok(datum)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scheme::{Unsupported, lex::Token};

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
        Num(&'static str),
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
            let result = parse_datum(self.input);
            match expected {
                Expected::Success(matcher) => {
                    let syntax = result
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
                    assert_eq!(e, a, "{}: boolean mismatch", test_name)
                }
                (DatumMatcher::Num(e), Datum::Number(SimpleNumber::Literal(a))) => {
                    assert_eq!(e, &a.text, "{}: number text mismatch", test_name)
                }
                (DatumMatcher::Int(e), Datum::Number(SimpleNumber::Integer(a))) => {
                    assert_eq!(e, a, "{}: integer mismatch", test_name)
                }
                (DatumMatcher::Float(e), Datum::Number(SimpleNumber::Float(a))) => {
                    assert!((e - a).abs() < f64::EPSILON, "{}: float mismatch", test_name)
                }
                (DatumMatcher::Char(e), Datum::Character(a)) => {
                    assert_eq!(e, a, "{}: character mismatch", test_name)
                }
                (DatumMatcher::Str(e), Datum::String(a)) => {
                    assert_eq!(e, a, "{}: string mismatch", test_name)
                }
                (DatumMatcher::Sym(e), Datum::Symbol(a)) => {
                    assert_eq!(e, a, "{}: symbol mismatch", test_name)
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
                        "{}: vector length mismatch",
                        test_name
                    );
                    for (e, a) in e_vec.iter().zip(a_vec.iter()) {
                        e.check(&a.value, test_name);
                    }
                }
                (DatumMatcher::ByteVector(e), Datum::ByteVector(a)) => {
                    assert_eq!(e, a, "{}: bytevector mismatch", test_name)
                }
                (DatumMatcher::Labeled(e_n, e_d), Datum::Labeled(a_n, a_d)) => {
                    assert_eq!(e_n, a_n, "{}: label id mismatch", test_name);
                    e_d.check(&a_d.value, test_name);
                }
                (DatumMatcher::LabelRef(e), Datum::LabelRef(a)) => {
                    assert_eq!(e, a, "{}: label ref mismatch", test_name)
                }
                _ => panic!(
                    "{}: datum type mismatch. Expected {:?}, got {:?}",
                    test_name, self, datum
                ),
            }
        }
    }

    impl TokenMatcher {
        fn check(&self, token: &Token, test_name: &str, index: usize) {
            match (self, token) {
                (TokenMatcher::Ident(e), Token::Identifier(a)) => {
                    assert_eq!(e, a, "{}: token {} mismatch", test_name, index)
                }
                _ => panic!(
                    "{}: token {} type mismatch. Expected {:?}, got {:?}",
                    test_name, index, self, token
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
                        "{}: nonterminal mismatch",
                        test_name
                    );
                }
                (ErrorMatcher::UnsupportedDepth, ParseError::Unsupported { feature, .. }) => {
                    assert_eq!(
                        feature,
                        &Unsupported::DepthLimit,
                        "{}: expected depth-limit unsupported error",
                        test_name,
                    );
                }
                _ => panic!(
                    "{}: error mismatch. Expected {:?}, got {:?}",
                    test_name, self, err
                ),
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

        let result = parse_datum(&input);
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

        let syntax = parse_datum_with_max_depth(&input, 128)
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
                input: "3.14",
                mode: TestMode::Datum(Expected::Success(DatumMatcher::Float(3.14))),
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
