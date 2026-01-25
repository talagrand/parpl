// Test utilities for arena-based CEL parsing
//
// This module provides helper functions to make testing cleaner and more concise.
// Since our API is arena-based and requires scoped access, these utilities handle
// the boilerplate of creating arenas, interners, and writers.

use crate::{
    Error, Interner, StringPool, StringPoolId,
    cel::{
        CelParser, Result,
        context::Builder,
        parser::ParseConfig,
        reference::arena::{ArenaCelWriter, Expr, ExprKind},
        traits::{BinaryOp, Literal},
    },
};
use bumpalo::Bump;

/// A simple string-based error for test utilities.
#[derive(Debug)]
struct TestError(String);

impl std::fmt::Display for TestError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl std::error::Error for TestError {}

// ============================================================================
// Test Context
// ============================================================================
//
// TestContext bundles an arena, string interner, and parser configuration
// for convenient test setup. It uses unsafe lifetime extension to store
// the AST reference alongside the arena - this is acceptable in tests where
// the context owns all resources and outlives all references.

pub struct TestContext {
    pub arena: Bump,
    pub interner: StringPool,
    pub parser: CelParser,
    pub ast: Option<&'static Expr<'static>>,
}

impl TestContext {
    pub fn new(config: ParseConfig) -> Self {
        let parser = Builder::default()
            .max_parse_depth(config.max_parse_depth)
            .max_ast_depth(config.max_ast_depth)
            .max_call_limit(config.max_call_limit)
            .build();

        Self {
            arena: Bump::new(),
            interner: StringPool::default(),
            parser,
            ast: None,
        }
    }

    pub fn parse(&mut self, input: &str) -> Result<()> {
        self.arena.reset();
        self.ast = None;

        // BUGBUG: Unsafe lifetime extension - code smell, consider redesigning.
        // We extend the arena lifetime to 'static so we can store the AST
        // reference in the same struct. This is "safe enough" for tests because:
        // 1. TestContext owns the arena and the AST reference
        // 2. The arena outlives any access to self.ast
        // 3. We reset the arena (invalidating old AST) before each parse
        let arena_ref: &'static Bump = unsafe { std::mem::transmute(&self.arena) };
        let mut writer = ArenaCelWriter::new(arena_ref, &mut self.interner);

        let ast = self.parser.parse(input, &mut writer)?;
        self.ast = Some(ast);
        Ok(())
    }

    pub fn ast(&self) -> Result<&'static Expr<'static>> {
        self.ast.ok_or_else(|| crate::Error::WriterError {
            span: crate::Span::new(0, 0),
            source: Box::new(TestError("No AST".into())),
        })
    }

    pub fn resolve<'a>(&'a self, id: &'a StringPoolId) -> Option<&'a str> {
        self.interner.resolve(id)
    }
}

impl Interner for TestContext {
    type Id = StringPoolId;

    fn intern(&mut self, s: &str) -> Self::Id {
        self.interner.intern(s)
    }

    fn resolve<'a>(&'a self, id: &'a Self::Id) -> Option<&'a str> {
        self.interner.resolve(id)
    }
}

/// Parse an expression and run assertions on the AST within a scoped callback
///
/// This is the main test helper. The callback receives a reference to the AST.
///
/// # Examples
/// ```
/// # use parpl::cel::test_util::*;
/// # use parpl::cel::ExprKind;
/// parse("1 + 2", |_, ast| {
///     assert!(matches!(ast.kind, ExprKind::Binary(..)));
/// });
/// ```
#[track_caller]
pub fn parse<F>(input: &str, f: F)
where
    F: for<'a> FnOnce(&TestContext, &Expr<'a>),
{
    let mut ctx = TestContext::new(ParseConfig::default());
    ctx.parse(input)
        .unwrap_or_else(|e| panic!("Parse failed for '{input}': {e}"));
    f(&ctx, ctx.ast().unwrap());
}

/// Parse with custom configuration
///
/// # Examples
/// ```
/// # use parpl::cel::test_util::*;
/// # use parpl::cel::{ExprKind, ParseConfig};
/// let config = ParseConfig {
///     max_parse_depth: 128,
///     max_ast_depth: 24,
///     max_call_limit: 100,
/// };
/// parse_with_config("1 + 2", config, |_, ast| {
///     assert!(matches!(ast.kind, ExprKind::Binary(..)));
/// });
/// ```
#[track_caller]
pub fn parse_with_config<F>(input: &str, config: ParseConfig, f: F)
where
    F: for<'a> FnOnce(&TestContext, &Expr<'a>),
{
    let mut ctx = TestContext::new(config);
    ctx.parse(input)
        .unwrap_or_else(|e| panic!("Parse failed for '{input}': {e}"));
    f(&ctx, ctx.ast().unwrap());
}

/// Assert that parsing succeeds
///
/// # Examples
/// ```
/// # use parpl::cel::test_util::*;
/// assert_parses("1 + 2");
/// assert_parses("true ? 1 : 2");
/// ```
#[track_caller]
pub fn assert_parses(input: &str) {
    parse(input, |_, _| {});
}

/// Assert that parsing fails
///
/// # Examples
/// ```
/// # use parpl::cel::test_util::*;
/// assert_parse_fails("1 +");
/// assert_parse_fails("@#$");
/// ```
#[track_caller]
pub fn assert_parse_fails(input: &str) {
    let mut ctx = TestContext::new(ParseConfig::default());
    assert!(
        ctx.parse(input).is_err(),
        "Expected '{input}' to fail parsing, but it succeeded"
    )
}

/// Assert that parsing fails with a specific error kind
///
/// Takes a matcher function that returns `true` if the error kind matches.
///
/// # Examples
/// ```ignore
/// # use parpl::cel::test_util::*;
/// # use parpl::Error;
/// assert_parse_fails_with("1 +", |e| matches!(e, Error::Syntax { .. }));
/// ```
#[track_caller]
pub fn assert_parse_fails_with<F>(input: &str, matcher: F)
where
    F: FnOnce(&Error) -> bool,
{
    let mut ctx = TestContext::new(ParseConfig::default());
    match ctx.parse(input) {
        Ok(()) => panic!("Expected '{input}' to fail, but it succeeded"),
        Err(e) => {
            assert!(
                matcher(&e),
                "Error did not match for '{input}', got {e:?}: {e}"
            );
        }
    }
}

/// Assert that the AST has a specific kind
///
/// # Examples
/// ```
/// # use parpl::cel::test_util::*;
/// # use parpl::cel::ExprKind;
/// assert_ast_kind("1 + 2", |kind| matches!(kind, ExprKind::Binary(..)));
/// ```
#[track_caller]
pub fn assert_ast_kind<F>(input: &str, predicate: F)
where
    F: for<'a> FnOnce(&ExprKind<'a>) -> bool,
{
    parse(input, |_ctx, ast| {
        assert!(
            predicate(&ast.kind),
            "AST kind predicate failed for '{input}':\n{ast:?}"
        );
    });
}

/// Assert that the AST is a literal with specific value
///
/// # Examples
/// ```
/// # use parpl::cel::test_util::*;
/// # use parpl::cel::Literal;
/// assert_literal("42", |lit| matches!(lit, Literal::Int(42)));
/// assert_literal("true", |lit| matches!(lit, Literal::Bool(true)));
/// ```
#[track_caller]
pub fn assert_literal<F>(input: &str, predicate: F)
where
    F: FnOnce(&Literal<StringPoolId, &[u8]>) -> bool,
{
    parse(input, |_ctx, ast| match &ast.kind {
        ExprKind::Literal(lit) => {
            assert!(
                predicate(lit),
                "Literal predicate failed for '{input}':\n{lit:?}"
            );
        }
        _ => panic!("Expected literal for '{input}', got:\n{ast:?}"),
    });
}

/// Assert that the AST is an identifier with specific name
///
/// # Examples
/// ```
/// # use parpl::cel::test_util::*;
/// assert_ident("foo", "foo");
/// assert_ident("my_var", "my_var");
/// ```
#[track_caller]
pub fn assert_ident(input: &str, expected_name: &str) {
    parse(input, |ctx, ast| match &ast.kind {
        ExprKind::Ident(name) => {
            let actual = ctx.resolve(name).unwrap_or("<unresolved>");
            assert!(
                (actual == expected_name),
                "Expected identifier '{expected_name}' for '{input}', got '{actual}'"
            )
        }
        _ => panic!("Expected identifier for '{input}', got:\n{ast:?}"),
    });
}

/// Assert that the AST is a binary operation
///
/// # Examples
/// ```
/// # use parpl::cel::test_util::*;
/// # use parpl::cel::BinaryOp;
/// assert_binary("1 + 2", BinaryOp::Add);
/// assert_binary("x && y", BinaryOp::And);
/// ```
#[track_caller]
pub fn assert_binary(input: &str, expected_op: BinaryOp) {
    parse(input, |_ctx, ast| match &ast.kind {
        ExprKind::Binary(op, _, _) => {
            assert!(
                !(*op != expected_op),
                "Expected binary op {expected_op:?} for '{input}', got {op:?}"
            );
        }
        _ => panic!("Expected binary operation for '{input}', got:\n{ast:?}"),
    });
}

/// Assert that the AST is a ternary operation
///
/// # Examples
/// ```
/// # use parpl::cel::test_util::*;
/// assert_ternary("true ? 1 : 2");
/// ```
#[track_caller]
pub fn assert_ternary(input: &str) {
    parse(input, |_ctx, ast| match &ast.kind {
        ExprKind::Ternary(_, _, _) => {}
        _ => panic!("Expected ternary operation for '{input}', got:\n{ast:?}"),
    });
}

/// Assert that the AST is a list
///
/// # Examples
/// ```
/// # use parpl::cel::test_util::*;
/// assert_list("[1, 2, 3]", 3);
/// ```
#[track_caller]
pub fn assert_list(input: &str, expected_len: usize) {
    parse(input, |_ctx, ast| match &ast.kind {
        ExprKind::List(elements) => {
            assert!(
                (elements.len() == expected_len),
                "Expected list of length {expected_len} for '{input}', got {}",
                elements.len()
            );
        }
        _ => panic!("Expected list for '{input}', got:\n{ast:?}"),
    });
}

/// Assert that the AST is a map
///
/// # Examples
/// ```
/// # use parpl::cel::test_util::*;
/// assert_map("{a: 1, b: 2}", 2);
/// ```
#[track_caller]
pub fn assert_map(input: &str, expected_len: usize) {
    parse(input, |_ctx, ast| match &ast.kind {
        ExprKind::Map(entries) => {
            assert!(
                (entries.len() == expected_len),
                "Expected map with {expected_len} entries for '{input}', got {}",
                entries.len()
            );
        }
        _ => panic!("Expected map for '{input}', got:\n{ast:?}"),
    });
}

/// Parse and format AST for debugging
///
/// # Examples
/// ```
/// # use parpl::cel::test_util::*;
/// let output = parse_and_pretty("1 + 2");
/// println!("{}", output);
/// ```
pub fn parse_and_pretty(input: &str) -> String {
    let mut ctx = TestContext::new(ParseConfig::default());
    match ctx.parse(input) {
        Ok(_) => format!("{:?}", ctx.ast().unwrap()),
        Err(e) => format!("Parse error: {e}"),
    }
}

/// Macro for table-driven tests
///
/// # Examples
/// ```
/// # use parpl::cel::test_util::*;
/// test_cases! {
///     literal_42: "42" => assert_parses,
///     literal_true: "true" => assert_parses,
///     invalid: "1 +" => assert_parse_fails,
/// }
/// ```
#[macro_export]
macro_rules! test_cases {
    ($($name:ident: $input:expr => $assertion:ident),* $(,)?) => {
        $(
            #[test]
            fn $name() {
                $assertion($input);
            }
        )*
    };
}
