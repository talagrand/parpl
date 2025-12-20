// Test utilities for arena-based CEL parsing
//
// This module provides helper functions to make testing cleaner and more concise.
// Since our API is arena-based and requires scoped access, these utilities handle
// the boilerplate of creating contexts.

use crate::cel::{
    ast::{BinaryOp, Expr, ExprKind, Literal},
    context::Builder,
    error::ErrorKind,
    parser::ParseConfig,
    pretty::pretty_print,
};

/// Parse an expression and run assertions on the AST within a scoped callback
///
/// This is the main test helper. The callback receives a reference to the AST.
///
/// # Examples
/// ```
/// # use parpl::cel::test_util::*;
/// # use parpl::cel::ExprKind;
/// parse("1 + 2", |ast| {
///     assert!(matches!(ast.kind, ExprKind::Binary(..)));
/// });
/// ```
#[track_caller]
pub fn parse<F>(input: &str, f: F)
where
    F: for<'a> FnOnce(&Expr<'a>),
{
    Builder::default()
        .parse_scoped(input, |ctx| {
            f(ctx.ast()?);
            Ok(())
        })
        .unwrap_or_else(|e| panic!("Parse failed for '{}': {}", input, e));
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
/// parse_with_config("1 + 2", config, |ast| {
///     assert!(matches!(ast.kind, ExprKind::Binary(..)));
/// });
/// ```
#[track_caller]
pub fn parse_with_config<F>(input: &str, config: ParseConfig, f: F)
where
    F: for<'a> FnOnce(&Expr<'a>),
{
    Builder::default()
        .max_parse_depth(config.max_parse_depth)
        .max_ast_depth(config.max_ast_depth)
        .max_call_limit(config.max_call_limit)
        .parse_scoped(input, |ctx| {
            f(ctx.ast()?);
            Ok(())
        })
        .unwrap_or_else(|e| panic!("Parse failed for '{}': {}", input, e));
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
    parse(input, |_| {});
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
    let result = Builder::default().parse_scoped(input, |ctx| ctx.ast().map(|_| ()));
    if result.is_ok() {
        panic!("Expected '{}' to fail parsing, but it succeeded", input);
    }
}

/// Assert that parsing fails with a specific error kind
///
/// # Examples
/// ```
/// # use parpl::cel::test_util::*;
/// # use parpl::cel::ErrorKind;
/// assert_parse_fails_with("1 +", ErrorKind::UnexpectedEOF);
/// ```
#[track_caller]
pub fn assert_parse_fails_with(input: &str, expected_kind: ErrorKind) {
    let result = Builder::default().parse_scoped(input, |ctx| ctx.ast().map(|_| ()));
    match result {
        Ok(()) => panic!(
            "Expected '{}' to fail with {:?}, but it succeeded",
            input, expected_kind
        ),
        Err(e) => {
            if e.kind != expected_kind {
                panic!(
                    "Expected error kind {:?} for '{}', but got {:?}: {}",
                    expected_kind, input, e.kind, e
                );
            }
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
    parse(input, |ast| {
        if !predicate(&ast.kind) {
            panic!(
                "AST kind predicate failed for '{}':\n{}",
                input,
                pretty_print(ast)
            );
        }
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
    F: FnOnce(&Literal) -> bool,
{
    parse(input, |ast| match &ast.kind {
        ExprKind::Literal(lit) => {
            if !predicate(lit) {
                panic!("Literal predicate failed for '{}':\n{:?}", input, lit);
            }
        }
        _ => panic!(
            "Expected literal for '{}', got:\n{}",
            input,
            pretty_print(ast)
        ),
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
    parse(input, |ast| match &ast.kind {
        ExprKind::Ident(name) => {
            if *name != expected_name {
                panic!(
                    "Expected identifier '{}' for '{}', got '{}'",
                    expected_name, input, name
                );
            }
        }
        _ => panic!(
            "Expected identifier for '{}', got:\n{}",
            input,
            pretty_print(ast)
        ),
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
    parse(input, |ast| match &ast.kind {
        ExprKind::Binary(op, _, _) => {
            if *op != expected_op {
                panic!(
                    "Expected binary op {:?} for '{}', got {:?}",
                    expected_op, input, op
                );
            }
        }
        _ => panic!(
            "Expected binary operation for '{}', got:\n{}",
            input,
            pretty_print(ast)
        ),
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
    parse(input, |ast| match &ast.kind {
        ExprKind::Ternary(_, _, _) => {}
        _ => panic!(
            "Expected ternary operation for '{}', got:\n{}",
            input,
            pretty_print(ast)
        ),
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
    parse(input, |ast| match &ast.kind {
        ExprKind::List(elements) => {
            if elements.len() != expected_len {
                panic!(
                    "Expected list of length {} for '{}', got {}",
                    expected_len,
                    input,
                    elements.len()
                );
            }
        }
        _ => panic!("Expected list for '{}', got:\n{}", input, pretty_print(ast)),
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
    parse(input, |ast| match &ast.kind {
        ExprKind::Map(entries) => {
            if entries.len() != expected_len {
                panic!(
                    "Expected map with {} entries for '{}', got {}",
                    expected_len,
                    input,
                    entries.len()
                );
            }
        }
        _ => panic!("Expected map for '{}', got:\n{}", input, pretty_print(ast)),
    });
}

/// Parse and pretty-print for debugging
///
/// # Examples
/// ```
/// # use parpl::cel::test_util::*;
/// let output = parse_and_pretty("1 + 2");
/// println!("{}", output);
/// ```
pub fn parse_and_pretty(input: &str) -> String {
    Builder::default()
        .parse_scoped(input, |ctx| Ok(pretty_print(ctx.ast()?)))
        .unwrap_or_else(|e| format!("Parse error: {}", e))
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
