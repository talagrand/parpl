// CEL Context and Builder
//
// This module provides a builder pattern for configuring CEL parsing and evaluation,
// along with a context that manages the parsing state and arena allocation.
//
// The builder allows fluent configuration, and the context owns the parsed AST
// in a bumpalo::Bump arena for efficient memory management.

use crate::{
    cel::{
        ast::Expr,
        constants,
        error::{Error, ErrorKind, Phase, Result},
        parser::ParseConfig,
        samples::reader,
    },
    common::{Interner, StringPool, StringPoolId},
};
use bumpalo::Bump;

// ============================================================================
// Configuration Builder
// ============================================================================

/// Configuration builder for CEL parsing and evaluation
///
/// # Examples
///
/// Simple usage with defaults:
/// ```
/// use parpl::cel::Builder;
///
/// let mut ctx = Builder::default().build();
/// ctx.parse("1 + 2")?;
/// let ast = ctx.ast()?;
/// # Ok::<(), parpl::cel::Error>(())
/// ```
///
/// With custom configuration:
/// ```
/// use parpl::cel::Builder;
///
/// let mut ctx = Builder::default()
///     .max_parse_depth(128)
///     .max_ast_depth(24)
///     .max_call_limit(50_000_000)
///     .strict_mode(true)
///     .build();
/// # Ok::<(), parpl::cel::Error>(())
/// ```
#[derive(Debug, Clone)]
pub struct Builder {
    /// Maximum parse depth for heuristic pre-validation (default: 128)
    /// Protects against Pest parser stack overflow (~171 on 1MB stack)
    max_parse_depth: usize,
    /// Maximum AST nesting depth (default: 24)
    /// Protects against AST builder stack overflow (~38 on 1MB stack)
    max_ast_depth: usize,
    /// Maximum call limit for pest parser (default: 10 million)
    max_call_limit: usize,
    /// Enable strict mode - reject more programs than spec requires (default: false)
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
    /// let ctx = Builder::default()
    ///     .max_parse_depth(128)
    ///     .build();
    /// ```
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
    /// let ctx = Builder::default()
    ///     .max_ast_depth(30)
    ///     .build();
    /// ```
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
    /// let ctx = Builder::default()
    ///     .max_nesting_depth(100)
    ///     .build();
    /// ```
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
    /// let ctx = Builder::default()
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
    /// use parpl::cel::Builder;
    ///
    /// let ctx = Builder::default()
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
    /// use parpl::cel::Builder;
    ///
    /// let mut ctx = Builder::default().build();
    /// ctx.parse("1 + 2")?;
    /// let ast = ctx.ast()?;
    /// # Ok::<(), parpl::cel::Error>(())
    /// ```
    pub fn build(self) -> Context {
        let arena = Bump::new();
        let interner = StringPool::default();

        Context {
            arena,
            interner,
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
    /// use parpl::cel::Builder;
    ///
    /// let result = Builder::default()
    ///     .max_nesting_depth(100)
    ///     .parse_scoped("1 + 2", |ctx| {
    ///         let ast = ctx.ast()?;
    ///         // Process ast...
    ///         Ok(42)
    ///     })?;
    ///
    /// assert_eq!(result, 42);
    /// # Ok::<(), parpl::cel::Error>(())
    /// ```
    pub fn parse_scoped<F, T>(self, input: &str, f: F) -> Result<T>
    where
        F: FnOnce(&Context) -> Result<T>,
    {
        let mut ctx = self.build();
        ctx.parse(input)?;
        f(&ctx)
    }

    /// Get the maximum parse depth (heuristic pre-validation)
    pub fn get_max_parse_depth(&self) -> usize {
        self.max_parse_depth
    }

    /// Get the maximum AST nesting depth (precise limit)
    pub fn get_max_ast_depth(&self) -> usize {
        self.max_ast_depth
    }

    /// Get the maximum nesting depth (returns parse depth for backward compatibility)
    ///
    /// **Deprecated**: Use `get_max_parse_depth()` or `get_max_ast_depth()` explicitly.
    pub fn get_max_nesting_depth(&self) -> usize {
        self.max_parse_depth
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

/// CEL processing context
///
/// The context manages the state of a parsed CEL expression and will eventually
/// own the arena allocator for values. It can be reused for parsing multiple
/// expressions.
///
/// # Examples
///
/// ```
/// use parpl::cel::Builder;
///
/// let mut ctx = Builder::default().build();
///
/// // Parse first expression
/// ctx.parse("1 + 2")?;
/// let ast1 = ctx.ast()?;
///
/// // Parse second expression (replaces previous state)
/// ctx.parse("3 * 4")?;
/// let ast2 = ctx.ast()?;
/// # Ok::<(), parpl::cel::Error>(())
/// ```
pub struct Context {
    arena: Bump,
    interner: StringPool,
    config: Builder,
    input: Option<String>,
    ast: Option<&'static Expr<'static>>, // Transmuted lifetime - actually tied to arena
}

impl Context {
    /// Parse a CEL expression
    ///
    /// This replaces any previously parsed expression. The AST is stored
    /// in the context and can be accessed via `ast()`.
    ///
    /// # Examples
    /// ```
    /// use parpl::cel::Builder;
    ///
    /// let mut ctx = Builder::default().build();
    /// ctx.parse("1 + 2")?;
    /// # Ok::<(), parpl::cel::Error>(())
    /// ```
    pub fn parse(&mut self, input: &str) -> Result<()> {
        // Reset arena for new parse
        self.arena.reset();

        // Reset interner
        self.interner = StringPool::default();

        self.input = Some(input.to_string());
        self.ast = None;

        // Use the builder's configuration for parsing
        let config = ParseConfig {
            max_parse_depth: self.config.max_parse_depth,
            max_ast_depth: self.config.max_ast_depth,
            max_call_limit: self.config.max_call_limit,
        };

        // Build AST using the arena and interner
        // SAFETY: We transmute the arena reference to 'static, but it's actually
        // tied to &self. This is safe because:
        // 1. The arena lives as long as Context
        // 2. We reset the arena on each parse
        // 3. References are transmuted back to correct lifetime in ast()
        let arena_ref: &'static Bump = unsafe { std::mem::transmute(&self.arena) };
        let interner = &mut self.interner;

        let ast = reader::build_ast_with_arena(input, config, arena_ref, interner)?;

        // Store with 'static lifetime (transmuted)
        self.ast = Some(ast);

        Ok(())
    }

    /// Get the parsed AST
    ///
    /// Returns an error if no expression has been parsed yet.
    ///
    /// # Examples
    /// ```
    /// use parpl::cel::Builder;
    ///
    /// let mut ctx = Builder::default().build();
    /// ctx.parse("42")?;
    /// let ast = ctx.ast()?;
    /// # Ok::<(), parpl::cel::Error>(())
    /// ```
    pub fn ast(&self) -> Result<&Expr<'_>> {
        // SAFETY: Transmute from 'static back to lifetime tied to &self
        // This is safe because the arena is owned by self
        self.ast
            .map(|ast_static| unsafe {
                std::mem::transmute::<&'static Expr<'static>, &Expr>(ast_static)
            })
            .ok_or_else(|| {
                Error::new(
                    Phase::AstConstruction,
                    ErrorKind::Custom("No AST available".to_string()),
                    "No expression has been parsed yet".to_string(),
                )
            })
    }

    /// Resolve an interned string ID back to its string value.
    pub fn resolve<'a>(&'a self, id: &'a StringPoolId) -> Option<&'a str> {
        self.interner.resolve(id)
    }

    /// Get the input string that was parsed
    ///
    /// Returns `None` if no expression has been parsed yet.
    pub fn input(&self) -> Option<&str> {
        self.input.as_deref()
    }

    /// Get the configuration used by this context
    pub fn config(&self) -> &Builder {
        &self.config
    }

    /// Reset the context, clearing all state
    ///
    /// After calling this, the context is ready to parse a new expression.
    /// The arena and string interner are cleared.
    pub fn reset(&mut self) {
        self.arena.reset();
        // Reset interner
        self.interner = StringPool::default();
        self.input = None;
        self.ast = None;
    }
}

impl Interner for Context {
    type Id = StringPoolId;

    #[inline]
    fn intern(&mut self, text: &str) -> Self::Id {
        self.interner.intern(text)
    }

    #[inline]
    fn resolve<'a>(&'a self, id: &'a Self::Id) -> Option<&'a str> {
        self.interner.resolve(id)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! test_cases {
        ($($name:ident: $test:expr),* $(,)?) => {
            $(
                #[test]
                fn $name() {
                    $test
                }
            )*
        };
    }

    // ============================================================
    // Section: Builder Configuration Tests
    // ============================================================

    test_cases! {
        test_builder_defaults: {
            let builder = Builder::default();
            assert_eq!(builder.get_max_nesting_depth(), 128);
            assert_eq!(builder.get_max_call_limit(), 10_000_000);
            assert!(!builder.is_strict_mode());
        },

        test_builder_configuration: {
            let builder = Builder::default()
                .max_nesting_depth(100)
                .max_call_limit(50_000_000)
                .strict_mode(true);

            assert_eq!(builder.get_max_nesting_depth(), 100);
            assert_eq!(builder.get_max_call_limit(), 50_000_000);
            assert!(builder.is_strict_mode());
        },

        test_builder_default_trait: {
            let builder = Builder::default();
            assert_eq!(builder.get_max_nesting_depth(), 128);
        },
    }

    // ============================================================
    // Section: Context Parse and Reset Tests
    // ============================================================

    test_cases! {
        test_context_parse: {
            let mut ctx = Builder::default().build();
            assert!(ctx.input().is_none());
            assert!(ctx.ast().is_err());

            ctx.parse("1 + 2").unwrap();
            assert_eq!(ctx.input(), Some("1 + 2"));
            assert!(ctx.ast().is_ok());
        },

        test_context_reuse: {
            let mut ctx = Builder::default().build();

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
        },

        test_context_reset: {
            let mut ctx = Builder::default().build();
            ctx.parse("1 + 2").unwrap();
            assert!(ctx.input().is_some());
            assert!(ctx.ast().is_ok());

            ctx.reset();
            assert!(ctx.input().is_none());
            assert!(ctx.ast().is_err());
        },

        test_context_config_access: {
            let ctx = Builder::default().max_nesting_depth(200).build();
            assert_eq!(ctx.config().get_max_nesting_depth(), 200);
        },
    }

    // ============================================================
    // Section: Scoped API Tests
    // ============================================================

    test_cases! {
        test_scoped_api: {
            let result = Builder::default()
                .max_nesting_depth(100)
                .parse_scoped("1 + 2", |ctx| {
                    let _ast = ctx.ast()?;
                    assert!(ctx.input().is_some());
                    Ok(42)
                })
                .unwrap();

            assert_eq!(result, 42);
        },
    }

    // ============================================================
    // Section: Error Handling Tests
    // ============================================================

    test_cases! {
        test_ast_error_before_parse: {
            let ctx = Builder::default().build();
            let result = ctx.ast();
            assert!(result.is_err());

            if let Err(e) = result {
                assert_eq!(e.phase, Phase::AstConstruction);
                assert!(e.message.contains("No expression has been parsed"));
            }
        },
    }

    // ============================================================
    // Section: Configuration Enforcement Tests
    // ============================================================

    test_cases! {
        test_config_max_parse_depth_honored: {
            // Create a context with low parse depth but generous AST depth
            // so that the heuristic pre-validation is the limiting factor.
            let mut ctx = Builder::default()
                .max_parse_depth(3)
                .max_ast_depth(128)
                .build();

            // This should succeed (3 opening delimiters is at the limit)
            let first = ctx.parse("(((1)))");
            assert!(first.is_ok());

            // This should fail (4 opening delimiters exceeds the parse depth limit)
            let result = ctx.parse("((((1))))");
            assert!(result.is_err());

            if let Err(e) = result {
                assert_eq!(e.phase, Phase::Parsing);
                assert!(matches!(
                    e.kind,
                    ErrorKind::NestingDepthExceeded { .. }
                ));
            }
        },
    }

    #[test]
    fn test_config_different_limits() {
        // Test with moderately permissive limits
        // Each logical nesting level consumes ~10 depth units.
        let mut ctx = Builder::default().max_nesting_depth(200).build();

        // Create deeply nested expression (depth 5)
        let deep = "(".repeat(5) + "1" + &")".repeat(5);
        if let Err(e) = ctx.parse(&deep) {
            panic!("Parse failed for depth 5 with limit 200: {:?}", e);
        }

        // Test with very restrictive limits
        // Even depth 2 requires ~20 units
        let mut ctx = Builder::default().max_nesting_depth(30).build();
        assert!(ctx.parse("((1))").is_ok());
        assert!(ctx.parse("(((1)))").is_err());
    }
}
