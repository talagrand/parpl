// CEL Configuration and Parser Driver
//
// This module provides a builder pattern for configuring CEL parsing,
// and a driver struct `Cel` that orchestrates the parsing process.
//
// Unlike the previous `Context` implementation, this API is agnostic to the
// memory management strategy (e.g. arena allocation). The caller provides
// a concrete `CelWriter` implementation to construct the AST.

use crate::cel::{
    Result, ast_builder, constants,
    parser::{self, ParseConfig},
    traits::CelWriter,
};

// ============================================================================
// Configuration Builder
// ============================================================================

/// Configuration builder for CEL parsing
///
/// # Examples
///
/// Simple usage with defaults:
/// ```
/// use parpl::cel::Builder;
///
/// let parser = Builder::default().build();
/// ```
///
/// With custom configuration:
/// ```
/// use parpl::cel::Builder;
///
/// let parser = Builder::default()
///     .max_parse_depth(128)
///     .max_ast_depth(24)
///     .max_call_limit(50_000_000)
///     .strict_mode(true)
///     .build();
/// ```
#[derive(Debug, Clone)]
pub struct Builder {
    /// Maximum parse depth for heuristic pre-validation (default: 128)
    ///
    /// This protects against Pest parser stack overflow (~171 depth on 1MB stack).
    /// Uses a simple heuristic that counts opening delimiters.
    max_parse_depth: usize,

    /// Maximum AST nesting depth (default: 24)
    ///
    /// This protects against AST builder stack overflow (~38 depth on 1MB stack).
    /// Must be LOWER than max_parse_depth to prevent crashes during AST construction.
    max_ast_depth: usize,

    /// Maximum call limit for pest parser (default: 10 million)
    ///
    /// This provides protection against Denial of Service (DoS) attacks that
    /// exploit parser complexity (e.g. deep recursion or backtracking).
    max_call_limit: usize,

    /// Enable strict mode (default: false)
    strict_mode: bool,
}

impl Default for Builder {
    /// Create a new builder with default configuration
    ///
    /// Defaults:
    /// - `max_parse_depth`: 128 (heuristic pre-validation, protects Pest parser)
    /// - `max_ast_depth`: 24 (precise AST recursion limit, 2x CEL spec minimum)
    /// - `max_call_limit`: 10,000,000
    /// - `strict_mode`: false
    fn default() -> Self {
        Self {
            max_parse_depth: constants::DEFAULT_MAX_PARSE_DEPTH,
            max_ast_depth: constants::DEFAULT_MAX_AST_DEPTH,
            max_call_limit: 10_000_000,
            strict_mode: false,
        }
    }
}

impl Builder {
    /// Set maximum parse depth for heuristic pre-validation
    ///
    /// This protects against Pest parser stack overflow (~171 depth on 1MB stack).
    /// Should be higher than `max_ast_depth`.
    ///
    /// # Examples
    /// ```
    /// use parpl::cel::Builder;
    ///
    /// let parser = Builder::default()
    ///     .max_parse_depth(128)
    ///     .build();
    /// ```
    #[must_use]
    pub fn max_parse_depth(mut self, depth: usize) -> Self {
        self.max_parse_depth = depth;
        self
    }

    /// Set maximum AST nesting depth
    ///
    /// This protects against AST builder stack overflow (~38 depth on 1MB stack).
    /// The CEL specification requires supporting at least 12 levels of nesting.
    /// We default to 24 (2x spec minimum).
    ///
    /// # Examples
    /// ```
    /// use parpl::cel::Builder;
    ///
    /// let parser = Builder::default()
    ///     .max_ast_depth(30)
    ///     .build();
    /// ```
    #[must_use]
    pub fn max_ast_depth(mut self, depth: usize) -> Self {
        self.max_ast_depth = depth;
        self
    }

    /// Set maximum nesting depth (sets both parse and AST depth to same value)
    ///
    /// **Deprecated**: Use `max_parse_depth()` and `max_ast_depth()` separately.
    /// This convenience method sets both to the same value.
    ///
    /// # Examples
    /// ```
    /// use parpl::cel::Builder;
    ///
    /// let parser = Builder::default()
    ///     .max_nesting_depth(100)
    ///     .build();
    /// ```
    #[must_use]
    pub fn max_nesting_depth(mut self, depth: usize) -> Self {
        self.max_parse_depth = depth;
        self.max_ast_depth = depth;
        self
    }

    /// Set maximum call limit for the pest parser
    ///
    /// This prevents timeout/DoS attacks from deeply recursive grammars.
    /// Default is 10 million total rule invocations.
    ///
    /// # Examples
    /// ```
    /// use parpl::cel::Builder;
    ///
    /// let parser = Builder::default()
    ///     .max_call_limit(50_000_000)
    ///     .build();
    /// ```
    #[must_use]
    pub fn max_call_limit(mut self, limit: usize) -> Self {
        self.max_call_limit = limit;
        self
    }

    /// Enable strict mode
    ///
    /// In strict mode, we may reject programs that the CEL specification
    /// would accept. This is useful for enforcing coding standards.
    ///
    /// # Examples
    /// ```
    /// use parpl::cel::Builder;
    ///
    /// let parser = Builder::default()
    ///     .strict_mode(true)
    ///     .build();
    /// ```
    #[must_use]
    pub fn strict_mode(mut self, enabled: bool) -> Self {
        self.strict_mode = enabled;
        self
    }

    /// Build a CEL parser driver with this configuration
    ///
    /// The driver can be reused for parsing multiple expressions.
    ///
    /// # Examples
    /// ```
    /// use parpl::cel::Builder;
    ///
    /// let parser = Builder::default().build();
    /// ```
    #[must_use]
    pub fn build(self) -> CelParser {
        CelParser {
            config: ParseConfig {
                max_parse_depth: self.max_parse_depth,
                max_ast_depth: self.max_ast_depth,
                max_call_limit: self.max_call_limit,
            },
            strict_mode: self.strict_mode,
        }
    }
}

// ============================================================================
// CEL Parser Driver
// ============================================================================

/// CEL Parser Driver
///
/// This struct holds the configuration for parsing and provides methods
/// to parse CEL expressions using a provided `CelWriter`.
///
/// It is designed to be:
/// - **Agnostic**: Does not enforce a specific memory management strategy.
/// - **Safe**: Enforces limits on recursion depth and complexity to prevent stack overflows and DoS.
/// - **Reusable**: Can be reused to parse multiple expressions with the same configuration.
pub struct CelParser {
    config: ParseConfig,
    strict_mode: bool,
}

impl Default for CelParser {
    fn default() -> Self {
        Builder::default().build()
    }
}

impl CelParser {
    /// Parse a CEL expression using the provided writer
    ///
    /// This method:
    /// 1. Configures the parser with the stored limits
    /// 2. Parses the input string into a concrete syntax tree (CST)
    /// 3. Traverses the CST and calls methods on the `writer` to build the AST
    ///
    /// # Examples
    ///
    /// ```ignore
    /// let parser = CelParser::default();
    /// let mut writer = MyWriter::new();
    /// let ast = parser.parse("1 + 2", &mut writer)?;
    /// ```
    pub fn parse<W: CelWriter>(&self, input: &str, writer: &mut W) -> Result<W::Expr> {
        // 1. Parse with Pest
        let pairs = parser::parse_with_config(input, self.config)?;

        // 2. Build AST using the writer
        ast_builder::build_ast_from_pairs(pairs, self.config.max_ast_depth, writer)
    }

    /// Get the underlying parse configuration
    pub fn config(&self) -> &ParseConfig {
        &self.config
    }

    /// Check if strict mode is enabled
    pub fn is_strict_mode(&self) -> bool {
        self.strict_mode
    }
}
