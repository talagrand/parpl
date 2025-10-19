// CEL Context and Builder
//
// This module provides a builder pattern for configuring CEL parsing and evaluation,
// along with a context that manages the parsing state.
//
// The builder allows fluent configuration, and the context owns the parsed AST
// and will eventually own the arena allocator for values.

use crate::ast::Expr;
use crate::error::Result;

/// Configuration builder for CEL parsing and evaluation
///
/// # Examples
///
/// Simple usage with defaults:
/// ```
/// use cello::CelloBuilder;
///
/// let mut ctx = CelloBuilder::new().build();
/// ctx.parse("1 + 2")?;
/// let ast = ctx.ast()?;
/// # Ok::<(), cello::Error>(())
/// ```
///
/// With custom configuration:
/// ```
/// use cello::CelloBuilder;
///
/// let mut ctx = CelloBuilder::new()
///     .max_nesting_depth(100)
///     .max_call_limit(50_000_000)
///     .strict_mode(true)
///     .build();
/// # Ok::<(), cello::Error>(())
/// ```
#[derive(Debug, Clone)]
pub struct CelloBuilder {
    /// Maximum nesting depth for expressions (default: 50, CEL spec requires 12)
    max_nesting_depth: usize,
    /// Maximum call limit for pest parser (default: 10 million)
    max_call_limit: usize,
    /// Enable strict mode - reject more programs than spec requires (default: false)
    strict_mode: bool,
}

impl CelloBuilder {
    /// Create a new builder with default configuration
    ///
    /// Defaults:
    /// - `max_nesting_depth`: 50 (CEL spec requires 12)
    /// - `max_call_limit`: 10,000,000
    /// - `strict_mode`: false
    pub fn new() -> Self {
        Self {
            max_nesting_depth: 50,
            max_call_limit: 10_000_000,
            strict_mode: false,
        }
    }

    /// Set maximum nesting depth for expressions
    ///
    /// The CEL specification requires supporting at least 12 levels of nesting.
    /// We default to 50 for generosity.
    ///
    /// # Examples
    /// ```
    /// use cello::CelloBuilder;
    ///
    /// let ctx = CelloBuilder::new()
    ///     .max_nesting_depth(100)
    ///     .build();
    /// ```
    pub fn max_nesting_depth(mut self, depth: usize) -> Self {
        self.max_nesting_depth = depth;
        self
    }

    /// Set maximum call limit for the pest parser
    ///
    /// This prevents timeout/DoS attacks from deeply recursive grammars.
    /// Default is 10 million total rule invocations.
    ///
    /// # Examples
    /// ```
    /// use cello::CelloBuilder;
    ///
    /// let ctx = CelloBuilder::new()
    ///     .max_call_limit(50_000_000)
    ///     .build();
    /// ```
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
    /// use cello::CelloBuilder;
    ///
    /// let ctx = CelloBuilder::new()
    ///     .strict_mode(true)
    ///     .build();
    /// ```
    pub fn strict_mode(mut self, enabled: bool) -> Self {
        self.strict_mode = enabled;
        self
    }

    /// Build a CEL context with this configuration
    ///
    /// The context can be reused for parsing multiple expressions.
    ///
    /// # Examples
    /// ```
    /// use cello::CelloBuilder;
    ///
    /// let mut ctx = CelloBuilder::new().build();
    /// ctx.parse("1 + 2")?;
    /// let ast = ctx.ast()?;
    /// # Ok::<(), cello::Error>(())
    /// ```
    pub fn build(self) -> CelloContext {
        CelloContext {
            config: self,
            input: None,
            ast: None,
        }
    }

    /// Parse and process CEL within a scoped context
    ///
    /// This is a convenience method for one-shot parsing and processing.
    /// The closure receives a context that has already parsed the input.
    ///
    /// # Examples
    /// ```
    /// use cello::CelloBuilder;
    ///
    /// let result = CelloBuilder::new()
    ///     .max_nesting_depth(100)
    ///     .parse_scoped("1 + 2", |ctx| {
    ///         let ast = ctx.ast()?;
    ///         // Process ast...
    ///         Ok(42)
    ///     })?;
    ///
    /// assert_eq!(result, 42);
    /// # Ok::<(), cello::Error>(())
    /// ```
    pub fn parse_scoped<F, T>(self, input: &str, f: F) -> Result<T>
    where
        F: FnOnce(&CelloContext) -> Result<T>,
    {
        let mut ctx = self.build();
        ctx.parse(input)?;
        f(&ctx)
    }

    /// Get the maximum nesting depth
    pub fn get_max_nesting_depth(&self) -> usize {
        self.max_nesting_depth
    }

    /// Get the maximum call limit
    pub fn get_max_call_limit(&self) -> usize {
        self.max_call_limit
    }

    /// Check if strict mode is enabled
    pub fn is_strict_mode(&self) -> bool {
        self.strict_mode
    }
}

impl Default for CelloBuilder {
    fn default() -> Self {
        Self::new()
    }
}

/// CEL processing context
///
/// The context manages the state of a parsed CEL expression and will eventually
/// own the arena allocator for values. It can be reused for parsing multiple
/// expressions.
///
/// # Examples
///
/// ```
/// use cello::CelloBuilder;
///
/// let mut ctx = CelloBuilder::new().build();
///
/// // Parse first expression
/// ctx.parse("1 + 2")?;
/// let ast1 = ctx.ast()?;
///
/// // Parse second expression (replaces previous state)
/// ctx.parse("3 * 4")?;
/// let ast2 = ctx.ast()?;
/// # Ok::<(), cello::Error>(())
/// ```
pub struct CelloContext {
    config: CelloBuilder,
    input: Option<String>,
    ast: Option<Expr>,
}

impl CelloContext {
    /// Parse a CEL expression
    ///
    /// This replaces any previously parsed expression. The AST is stored
    /// in the context and can be accessed via `ast()`.
    ///
    /// # Examples
    /// ```
    /// use cello::CelloBuilder;
    ///
    /// let mut ctx = CelloBuilder::new().build();
    /// ctx.parse("1 + 2")?;
    /// # Ok::<(), cello::Error>(())
    /// ```
    pub fn parse(&mut self, input: &str) -> Result<()> {
        self.input = Some(input.to_string());
        self.ast = None;

        // Use the builder's configuration for parsing
        let config = crate::parser::ParseConfig {
            max_nesting_depth: self.config.max_nesting_depth,
            max_call_limit: self.config.max_call_limit,
        };

        let ast = crate::build_ast_with_config(input, config)?;
        self.ast = Some(ast);

        Ok(())
    }

    /// Get the parsed AST
    ///
    /// Returns an error if no expression has been parsed yet.
    ///
    /// # Examples
    /// ```
    /// use cello::CelloBuilder;
    ///
    /// let mut ctx = CelloBuilder::new().build();
    /// ctx.parse("1 + 2")?;
    /// let ast = ctx.ast()?;
    /// # Ok::<(), cello::Error>(())
    /// ```
    pub fn ast(&self) -> Result<&Expr> {
        self.ast.as_ref().ok_or_else(|| {
            crate::error::Error::new(
                crate::error::Phase::AstConstruction,
                crate::error::ErrorKind::Custom("No AST available".to_string()),
                "No expression has been parsed yet".to_string(),
            )
        })
    }

    /// Get the input string that was parsed
    ///
    /// Returns `None` if no expression has been parsed yet.
    pub fn input(&self) -> Option<&str> {
        self.input.as_deref()
    }

    /// Get the configuration used by this context
    pub fn config(&self) -> &CelloBuilder {
        &self.config
    }

    /// Reset the context, clearing all state
    ///
    /// After calling this, the context is ready to parse a new expression.
    pub fn reset(&mut self) {
        self.input = None;
        self.ast = None;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_builder_defaults() {
        let builder = CelloBuilder::new();
        assert_eq!(builder.get_max_nesting_depth(), 50);
        assert_eq!(builder.get_max_call_limit(), 10_000_000);
        assert!(!builder.is_strict_mode());
    }

    #[test]
    fn test_builder_configuration() {
        let builder = CelloBuilder::new()
            .max_nesting_depth(100)
            .max_call_limit(50_000_000)
            .strict_mode(true);

        assert_eq!(builder.get_max_nesting_depth(), 100);
        assert_eq!(builder.get_max_call_limit(), 50_000_000);
        assert!(builder.is_strict_mode());
    }

    #[test]
    fn test_context_parse() {
        let mut ctx = CelloBuilder::new().build();
        assert!(ctx.input().is_none());
        assert!(ctx.ast().is_err());

        ctx.parse("1 + 2").unwrap();
        assert_eq!(ctx.input(), Some("1 + 2"));
        assert!(ctx.ast().is_ok());
    }

    #[test]
    fn test_context_reuse() {
        let mut ctx = CelloBuilder::new().build();

        // Parse first expression
        ctx.parse("1 + 2").unwrap();
        let input1 = ctx.input().unwrap().to_string();
        assert_eq!(input1, "1 + 2");

        // Parse second expression
        ctx.parse("3 * 4").unwrap();
        let input2 = ctx.input().unwrap().to_string();
        assert_eq!(input2, "3 * 4");

        // Second parse replaced the first
        assert_ne!(input1, input2);
    }

    #[test]
    fn test_context_reset() {
        let mut ctx = CelloBuilder::new().build();
        ctx.parse("1 + 2").unwrap();
        assert!(ctx.input().is_some());
        assert!(ctx.ast().is_ok());

        ctx.reset();
        assert!(ctx.input().is_none());
        assert!(ctx.ast().is_err());
    }

    #[test]
    fn test_scoped_api() {
        let result = CelloBuilder::new()
            .max_nesting_depth(100)
            .parse_scoped("1 + 2", |ctx| {
                let _ast = ctx.ast()?;
                assert!(ctx.input().is_some());
                Ok(42)
            })
            .unwrap();

        assert_eq!(result, 42);
    }

    #[test]
    fn test_builder_default_trait() {
        let builder = CelloBuilder::default();
        assert_eq!(builder.get_max_nesting_depth(), 50);
    }

    #[test]
    fn test_context_config_access() {
        let ctx = CelloBuilder::new().max_nesting_depth(200).build();

        assert_eq!(ctx.config().get_max_nesting_depth(), 200);
    }

    #[test]
    fn test_ast_error_before_parse() {
        let ctx = CelloBuilder::new().build();
        let result = ctx.ast();
        assert!(result.is_err());

        if let Err(e) = result {
            assert_eq!(e.phase, crate::error::Phase::AstConstruction);
            assert!(e.message.contains("No expression has been parsed"));
        }
    }

    #[test]
    fn test_config_max_nesting_depth_honored() {
        // Create a context with low nesting depth
        let mut ctx = CelloBuilder::new().max_nesting_depth(3).build();

        // This should succeed (depth 3)
        assert!(ctx.parse("(((1)))").is_ok());

        // This should fail (depth 4)
        let result = ctx.parse("((((1))))");
        assert!(result.is_err());

        if let Err(e) = result {
            assert_eq!(e.phase, crate::error::Phase::Parsing);
            assert!(matches!(
                e.kind,
                crate::error::ErrorKind::NestingDepthExceeded { .. }
            ));
        }
    }

    #[test]
    fn test_config_different_limits() {
        // Test with moderately permissive limits
        let mut ctx = CelloBuilder::new().max_nesting_depth(20).build();

        // Create deeply nested expression (depth 15 - should succeed)
        let deep = "(".repeat(15) + "1" + &")".repeat(15);
        assert!(ctx.parse(&deep).is_ok());

        // Test with very restrictive limits
        let mut ctx = CelloBuilder::new().max_nesting_depth(2).build();
        assert!(ctx.parse("((1))").is_ok());
        assert!(ctx.parse("(((1)))").is_err());
    }
}
