// Scheme Configuration and Parser Driver
//
// This module provides a builder pattern for configuring Scheme parsing,
// and a driver struct `SchemeParser` that orchestrates the parsing process.
//
// The caller provides a concrete `DatumWriter` implementation to construct the AST.

use crate::scheme::{Result, constants, lex, reader::TokenStream, traits::DatumWriter};

// ============================================================================
// Configuration Builder
// ============================================================================

/// Configuration builder for Scheme parsing.
///
/// # Examples
///
/// Simple usage with defaults:
/// ```
/// use parpl::scheme::Builder;
///
/// let parser = Builder::default().build();
/// ```
///
/// With custom configuration:
/// ```
/// use parpl::scheme::Builder;
///
/// let parser = Builder::default()
///     .max_depth(128)
///     .reject_comments(true)
///     .reject_fold_case(true)
///     .build();
/// ```
#[derive(Debug, Clone)]
pub struct Builder {
    /// Maximum nesting depth for parsing (default: 64)
    max_depth: u32,

    /// Reject `#!fold-case` and `#!no-fold-case` directives
    reject_fold_case: bool,

    /// Reject comments (`;`, `#|...|#`, `#;`)
    reject_comments: bool,
}

impl Default for Builder {
    /// Create a new builder with default configuration.
    ///
    /// Defaults:
    /// - `max_depth`: 64
    /// - `reject_fold_case`: false
    /// - `reject_comments`: false
    fn default() -> Self {
        Self {
            max_depth: constants::DEFAULT_MAX_DEPTH,
            reject_fold_case: false,
            reject_comments: false,
        }
    }
}

impl Builder {
    /// Set maximum nesting depth for parsing.
    ///
    /// This protects against stack overflow from deeply nested structures.
    ///
    /// # Examples
    /// ```
    /// use parpl::scheme::Builder;
    ///
    /// let parser = Builder::default()
    ///     .max_depth(128)
    ///     .build();
    /// ```
    #[must_use]
    pub fn max_depth(mut self, depth: u32) -> Self {
        self.max_depth = depth;
        self
    }

    /// Reject `#!fold-case` and `#!no-fold-case` directives.
    ///
    /// When enabled, these directives will cause a parse error.
    /// Useful for configurations that don't support case folding.
    ///
    /// # Examples
    /// ```
    /// use parpl::scheme::Builder;
    ///
    /// let parser = Builder::default()
    ///     .reject_fold_case(true)
    ///     .build();
    /// ```
    #[must_use]
    pub fn reject_fold_case(mut self, reject: bool) -> Self {
        self.reject_fold_case = reject;
        self
    }

    /// Reject comments (`;`, `#|...|#`, `#;`).
    ///
    /// When enabled, any comment syntax will cause a parse error.
    /// Useful for data-only formats where comments aren't expected.
    ///
    /// # Examples
    /// ```
    /// use parpl::scheme::Builder;
    ///
    /// let parser = Builder::default()
    ///     .reject_comments(true)
    ///     .build();
    /// ```
    #[must_use]
    pub fn reject_comments(mut self, reject: bool) -> Self {
        self.reject_comments = reject;
        self
    }

    /// Build a Scheme parser with this configuration.
    ///
    /// The parser can be reused for parsing multiple datums.
    ///
    /// # Examples
    /// ```
    /// use parpl::scheme::Builder;
    ///
    /// let parser = Builder::default().build();
    /// ```
    #[must_use]
    pub fn build(self) -> SchemeParser {
        SchemeParser {
            max_depth: self.max_depth,
            lex_config: lex::LexConfig {
                reject_fold_case: self.reject_fold_case,
                reject_comments: self.reject_comments,
            },
        }
    }
}

// ============================================================================
// Scheme Parser Driver
// ============================================================================

/// Scheme Parser Driver.
///
/// This struct holds the configuration for parsing and provides methods
/// to parse Scheme external representations using a provided `DatumWriter`
/// that constructs a user-defined AST.
pub struct SchemeParser {
    max_depth: u32,
    lex_config: lex::LexConfig,
}

impl Default for SchemeParser {
    fn default() -> Self {
        Builder::default().build()
    }
}

impl SchemeParser {
    /// Parse a single datum from source using the provided writer.
    ///
    /// This method:
    /// 1. Lexes the input string into tokens
    /// 2. Parses tokens into a datum using the `writer` to build the AST
    /// 3. Verifies no trailing tokens remain
    ///
    /// # Examples
    ///
    /// ```ignore
    /// let parser = SchemeParser::default();
    /// let mut writer = MyWriter::new();
    /// let (datum, span) = parser.parse("(+ 1 2)", &mut writer)?;
    /// ```
    ///
    /// # Errors
    ///
    /// - [`Error::Syntax`](crate::Error::Syntax) - Invalid syntax
    /// - [`Error::Incomplete`](crate::Error::Incomplete) - Input ends before datum is complete
    /// - [`Error::IncompleteToken`](crate::Error::IncompleteToken) - Input ends mid-token
    /// - [`Error::LimitExceeded`](crate::Error::LimitExceeded) - Nesting depth exceeded
    /// - [`Error::Unsupported`](crate::Error::Unsupported) - Feature not supported by writer
    pub fn parse<W: DatumWriter>(
        &self,
        source: &str,
        writer: &mut W,
    ) -> Result<(W::Output, crate::Span)> {
        let lexer = lex::lex_with_config(source, self.lex_config);
        let mut stream = TokenStream::new(lexer);
        let datum = stream.parse_with_max_depth(writer, self.max_depth)?;

        if !stream.is_empty() {
            // If there are remaining tokens, it's an error for a single datum parse
            let next = stream.peek()?.ok_or(crate::Error::Incomplete)?;
            return Err(crate::Error::syntax(
                next.span,
                "<datum>",
                "unexpected token after datum",
            ));
        }

        Ok(datum)
    }

    /// Create a token stream for parsing multiple datums.
    ///
    /// Use this when you need to parse multiple datums from a single source,
    /// or when you need more control over the parsing process.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// let parser = SchemeParser::default();
    /// let mut stream = parser.token_stream("(a) (b) (c)");
    /// let mut writer = MyWriter::new();
    ///
    /// while !stream.is_empty() {
    ///     let (datum, span) = stream.parse(&mut writer)?;
    ///     // process datum...
    /// }
    /// ```
    #[must_use]
    pub fn token_stream<'i>(&self, source: &'i str) -> TokenStream<'i> {
        let lexer = lex::lex_with_config(source, self.lex_config);
        TokenStream::new(lexer)
    }
}
