// AST builder - converts pest parse tree to AST
//
// This module transforms pest's `Pairs` into our typed AST.
// All allocations are done in a bumpalo arena, and strings are interned
// for deduplication.
//
// Deferred processing:
// - Escape sequences: handled during value construction (not here)
// - Numeric parsing: strings stored as-is, parsed during value construction
// - Identifier resolution: handled during evaluation

use crate::ast::*;
use crate::error::Result;
use crate::interner::StringInterner;
use crate::parser::{ParseConfig, Rule};
use bumpalo::Bump;
use pest::iterators::Pair;
use std::cell::RefCell;

/// Build an AST using a provided arena and interner
///
/// This is the core AST building function used by `CelloContext`.
/// All AST nodes and strings are allocated in the provided arena.
///
/// # Safety
///
/// The returned `Expr` has lifetime `'arena` tied to the arena parameter.
/// The caller must ensure the arena outlives all references to the AST.
pub fn build_ast_with_arena<'arena>(
    input: &str,
    config: ParseConfig,
    arena: &'arena Bump,
    interner: &RefCell<StringInterner<'arena>>,
) -> Result<&'arena Expr<'arena>> {
    // First parse with pest
    let pairs = crate::parser::parse_with_config(input, config)?;

    // Convert to AST
    // The parse tree has structure: SOI ~ expr ~ EOI
    // We want just the expr
    let pair = pairs
        .into_iter()
        .next()
        .expect("parse should return at least one pair (cel rule)");

    // The cel rule contains: SOI ~ expr ~ EOI
    // Extract the expr
    let mut inner = pair.into_inner();
    let expr_pair = inner.next().expect("cel rule should contain expr");

    Ok(build_expr(expr_pair, arena, interner))
}

/// Build an expression from a pest Pair
/// Main recursive function to build an Expr from a pest Pair
fn build_expr<'arena>(
    pair: pest::iterators::Pair<'_, Rule>,
    arena: &'arena Bump,
    interner: &RefCell<StringInterner<'arena>>,
) -> &'arena Expr<'arena> {
    let span = span_from_pair(&pair);

    match pair.as_rule() {
        Rule::expr => {
            // expr = { conditional_or ~ ("?" ~ conditional_or ~ ":" ~ expr)? }
            let mut inner = pair.into_inner();
            let condition = build_expr(inner.next().unwrap(), arena, interner);

            // Check for ternary operator
            if let Some(if_true) = inner.next() {
                let if_false = inner.next().unwrap();
                arena.alloc(Expr::new(
                    ExprKind::Ternary(
                        condition,
                        build_expr(if_true, arena, interner),
                        build_expr(if_false, arena, interner),
                    ),
                    span,
                ))
            } else {
                condition
            }
        }

        Rule::conditional_or => {
            // conditional_or = { conditional_and ~ ("||" ~ conditional_and)* }
            build_binary_chain(pair, arena, interner, BinaryOp::LogicalOr)
        }

        Rule::conditional_and => {
            // conditional_and = { relation ~ ("&&" ~ relation)* }
            build_binary_chain(pair, arena, interner, BinaryOp::LogicalAnd)
        }

        Rule::relation => {
            // relation = { addition ~ (relop ~ addition)* }
            let mut inner = pair.into_inner();
            let mut left = build_expr(inner.next().unwrap(), arena, interner);

            while let Some(op_pair) = inner.next() {
                let op = match op_pair.as_str() {
                    "<" => BinaryOp::Less,
                    "<=" => BinaryOp::LessEq,
                    ">" => BinaryOp::Greater,
                    ">=" => BinaryOp::GreaterEq,
                    "==" => BinaryOp::Equals,
                    "!=" => BinaryOp::NotEquals,
                    "in" => BinaryOp::In,
                    _ => unreachable!("unexpected relop: {}", op_pair.as_str()),
                };
                let right = build_expr(inner.next().unwrap(), arena, interner);
                left = alloc_binary(arena, op, left, right, span);
            }

            left
        }

        Rule::addition => {
            // addition = { multiplication ~ (("+" | "-") ~ multiplication)* }
            let mut inner = pair.into_inner();
            let mut left = build_expr(inner.next().unwrap(), arena, interner);

            while let Some(next) = inner.next() {
                let op = match next.as_str() {
                    "+" => BinaryOp::Add,
                    "-" => BinaryOp::Subtract,
                    _ => {
                        // It's the right operand
                        left = alloc_binary(
                            arena,
                            if inner.len() == 0 {
                                BinaryOp::Add
                            } else {
                                BinaryOp::Subtract
                            },
                            left,
                            build_expr(next, arena, interner),
                            span,
                        );
                        continue;
                    }
                };
                let right = build_expr(inner.next().unwrap(), arena, interner);
                left = alloc_binary(arena, op, left, right, span);
            }

            left
        }

        Rule::multiplication => {
            // multiplication = { unary ~ (("*" | "/" | "%") ~ unary)* }
            let mut inner = pair.into_inner();
            let mut left = build_expr(inner.next().unwrap(), arena, interner);

            while let Some(next) = inner.next() {
                let op = match next.as_str() {
                    "*" => BinaryOp::Multiply,
                    "/" => BinaryOp::Divide,
                    "%" => BinaryOp::Modulo,
                    _ => {
                        // It's the right operand (shouldn't happen with current grammar)
                        left = alloc_binary(
                            arena,
                            BinaryOp::Multiply,
                            left,
                            build_expr(next, arena, interner),
                            span,
                        );
                        continue;
                    }
                };
                let right = build_expr(inner.next().unwrap(), arena, interner);
                left = alloc_binary(arena, op, left, right, span);
            }

            left
        }

        Rule::unary => {
            // unary = { member | "!"+ ~ member | "-"+ ~ member }
            let mut inner = pair.into_inner();
            let first = inner.next().unwrap();

            match first.as_str() {
                s if s.chars().all(|c| c == '!') => {
                    let count = s.len();
                    let operand = build_expr(inner.next().unwrap(), arena, interner);
                    // Apply NOT count times (!! cancels out)
                    apply_unary_repeated(arena, UnaryOp::Not, count, operand, span)
                }
                s if s.chars().all(|c| c == '-') => {
                    let count = s.len();
                    let operand = build_expr(inner.next().unwrap(), arena, interner);
                    // Apply Negate count times (-- cancels out)
                    apply_unary_repeated(arena, UnaryOp::Negate, count, operand, span)
                }
                _ => build_expr(first, arena, interner), // It's a member expression
            }
        }

        Rule::member => {
            // member = { primary ~ ("." ~ selector ~ ("(" ~ expr_list? ~ ")")? | "[" ~ expr ~ "]")* }
            let mut inner = pair.into_inner();
            let mut expr = build_expr(inner.next().unwrap(), arena, interner);

            while let Some(next) = inner.next() {
                match next.as_str() {
                    "." => {
                        // Field access or method call
                        let selector = inner.next().unwrap();
                        let field_name = interner.borrow_mut().intern(selector.as_str());

                        // Check if there's a function call
                        if let Some(peek) = inner.peek() {
                            if peek.as_str() == "(" {
                                inner.next(); // consume "("
                                let args = if let Some(args_pair) = inner.peek() {
                                    if args_pair.as_rule() == Rule::expr_list {
                                        build_expr_list(inner.next().unwrap(), arena, interner)
                                    } else {
                                        &[]
                                    }
                                } else {
                                    &[]
                                };
                                // Consume ")" - it's implicit in the grammar
                                let new_span = expr.span.combine(&span);
                                expr = arena.alloc(Expr::new(
                                    ExprKind::Member(expr, field_name, Some(args)),
                                    new_span,
                                ));
                            } else {
                                let new_span = expr.span.combine(&span);
                                expr = arena.alloc(Expr::new(
                                    ExprKind::Member(expr, field_name, None),
                                    new_span,
                                ));
                            }
                        } else {
                            let new_span = expr.span.combine(&span);
                            expr = arena.alloc(Expr::new(
                                ExprKind::Member(expr, field_name, None),
                                new_span,
                            ));
                        }
                    }
                    "[" => {
                        // Index access
                        let index = build_expr(inner.next().unwrap(), arena, interner);
                        // "]" is implicit
                        let new_span = expr.span.combine(&span);
                        expr = arena.alloc(Expr::new(ExprKind::Index(expr, index), new_span));
                    }
                    _ => {
                        // This is part of the next operation
                        continue;
                    }
                }
            }

            expr
        }

        Rule::primary => {
            // primary = { literal | "."? ~ ident ~ ("(" ~ expr_list? ~ ")")? | ... }
            let mut inner = pair.into_inner();
            let first = inner.next().unwrap();

            match first.as_rule() {
                Rule::literal => arena.alloc(Expr::new(
                    ExprKind::Literal(build_literal(first, span, interner)),
                    span,
                )),
                Rule::ident => {
                    let name = interner.borrow_mut().intern(first.as_str());
                    // Check for function call
                    if inner.peek().map(|p| p.as_str()) == Some("(") {
                        inner.next(); // consume "("
                        let args = if let Some(args_pair) = inner.peek() {
                            if args_pair.as_rule() == Rule::expr_list {
                                build_expr_list(inner.next().unwrap(), arena, interner)
                            } else {
                                &[]
                            }
                        } else {
                            &[]
                        };
                        arena.alloc(Expr::new(ExprKind::Call(None, name, args), span))
                    } else {
                        arena.alloc(Expr::new(ExprKind::Ident(name), span))
                    }
                }
                Rule::expr => build_expr(first, arena, interner), // Parenthesized expression
                Rule::expr_list => {
                    // List literal: [expr, ...]
                    let items = build_expr_list(first, arena, interner);
                    arena.alloc(Expr::new(ExprKind::List(items), span))
                }
                Rule::map_inits => {
                    // Map literal: {key: value, ...}
                    let entries = build_map_inits(first, arena, interner);
                    arena.alloc(Expr::new(ExprKind::Map(entries), span))
                }
                _ => {
                    // Handle other primary forms
                    match first.as_str() {
                        "[" => {
                            // Empty list or list with items
                            if let Some(list_pair) = inner.peek() {
                                if list_pair.as_rule() == Rule::expr_list {
                                    let items =
                                        build_expr_list(inner.next().unwrap(), arena, interner);
                                    arena.alloc(Expr::new(ExprKind::List(items), span))
                                } else {
                                    arena.alloc(Expr::new(ExprKind::List(&[]), span))
                                }
                            } else {
                                arena.alloc(Expr::new(ExprKind::List(&[]), span))
                            }
                        }
                        "{" => {
                            // Empty map or map with entries
                            if let Some(map_pair) = inner.peek() {
                                if map_pair.as_rule() == Rule::map_inits {
                                    let entries =
                                        build_map_inits(inner.next().unwrap(), arena, interner);
                                    arena.alloc(Expr::new(ExprKind::Map(entries), span))
                                } else {
                                    arena.alloc(Expr::new(ExprKind::Map(&[]), span))
                                }
                            } else {
                                arena.alloc(Expr::new(ExprKind::Map(&[]), span))
                            }
                        }
                        _ => unreachable!("unexpected primary: {}", first.as_str()),
                    }
                }
            }
        }

        Rule::literal => arena.alloc(Expr::new(
            ExprKind::Literal(build_literal(pair, span, interner)),
            span,
        )),
        Rule::ident => arena.alloc(Expr::new(
            ExprKind::Ident(interner.borrow_mut().intern(pair.as_str())),
            span,
        )),

        _ => unreachable!("unexpected rule in build_expr: {:?}", pair.as_rule()),
    }
}

/// Build a literal expression
fn build_literal<'arena>(
    pair: Pair<Rule>,
    _span: Span,
    interner: &RefCell<StringInterner<'arena>>,
) -> Literal<'arena> {
    let inner = pair.into_inner().next().unwrap();

    match inner.as_rule() {
        Rule::int_lit => Literal::Int(interner.borrow_mut().intern(inner.as_str())),
        Rule::uint_lit => {
            // Remove the 'u' suffix
            let s = inner.as_str();
            Literal::UInt(interner.borrow_mut().intern(&s[..s.len() - 1]))
        }
        Rule::float_lit => Literal::Float(interner.borrow_mut().intern(inner.as_str())),
        Rule::string_lit => {
            let s = inner.as_str();
            let (content, is_raw, quote_style) = parse_string_literal(s, interner);
            Literal::String(content, is_raw, quote_style)
        }
        Rule::bytes_lit => {
            // Skip the 'b' or 'B' prefix
            let s = &inner.as_str()[1..];
            let (content, is_raw, quote_style) = parse_string_literal(s, interner);
            Literal::Bytes(content, is_raw, quote_style)
        }
        Rule::bool_lit => Literal::Bool(inner.as_str() == "true"),
        Rule::null_lit => Literal::Null,
        _ => unreachable!("unexpected literal rule: {:?}", inner.as_rule()),
    }
}

/// Parse a string literal, extracting content, raw flag, and quote style
///
/// **CEL-RESTRICTED**: Escape sequences are NOT processed here.
/// They will be processed during value construction.
fn parse_string_literal<'arena>(
    s: &str,
    interner: &RefCell<StringInterner<'arena>>,
) -> (&'arena str, bool, QuoteStyle) {
    let is_raw = s.starts_with('r') || s.starts_with('R');
    let s = if is_raw { &s[1..] } else { s };

    let (content, quote_style) = if s.starts_with("\"\"\"") {
        (&s[3..s.len() - 3], QuoteStyle::TripleDoubleQuote)
    } else if s.starts_with("'''") {
        (&s[3..s.len() - 3], QuoteStyle::TripleSingleQuote)
    } else if s.starts_with('"') {
        (&s[1..s.len() - 1], QuoteStyle::DoubleQuote)
    } else if s.starts_with('\'') {
        (&s[1..s.len() - 1], QuoteStyle::SingleQuote)
    } else {
        unreachable!("invalid string literal: {}", s)
    };

    (interner.borrow_mut().intern(content), is_raw, quote_style)
}

/// Build an expression list - collect into std Vec, then clone into arena slice
///
/// We must clone because build_expr returns &Expr (reference) but we need to store
/// Expr values in the slice. Since Expr is not Copy, we clone.
fn build_expr_list<'arena>(
    pair: Pair<Rule>,
    arena: &'arena Bump,
    interner: &RefCell<StringInterner<'arena>>,
) -> &'arena [Expr<'arena>] {
    let exprs: Vec<&Expr<'arena>> = pair
        .into_inner()
        .map(|p| build_expr(p, arena, interner))
        .collect();

    arena.alloc_slice_fill_with(exprs.len(), |i| exprs[i].clone())
}

/// Build map initializers - collect into std Vec, then clone into arena slice
///
/// We must clone because build_expr returns &Expr (reference) but we need to store
/// Expr values in the slice. Since Expr is not Copy, we clone.
fn build_map_inits<'arena>(
    pair: Pair<Rule>,
    arena: &'arena Bump,
    interner: &RefCell<StringInterner<'arena>>,
) -> &'arena [(Expr<'arena>, Expr<'arena>)] {
    let mut inner = pair.into_inner();
    let mut entries: Vec<(&Expr<'arena>, &Expr<'arena>)> = Vec::new();

    while let Some(key) = inner.next() {
        let value = inner.next().unwrap();
        entries.push((
            build_expr(key, arena, interner),
            build_expr(value, arena, interner),
        ));
    }

    arena.alloc_slice_fill_with(entries.len(), |i| {
        (entries[i].0.clone(), entries[i].1.clone())
    })
}

/// Extract span from a pest Pair
fn span_from_pair(pair: &Pair<Rule>) -> Span {
    let span = pair.as_span();
    Span::new(span.start(), span.end())
}

// Helper functions for arena-allocated AST construction

/// Allocate a binary expression in the arena
fn alloc_binary<'arena>(
    arena: &'arena Bump,
    op: BinaryOp,
    left: &'arena Expr<'arena>,
    right: &'arena Expr<'arena>,
    span: Span,
) -> &'arena Expr<'arena> {
    arena.alloc(Expr::new(ExprKind::Binary(op, left, right), span))
}

/// Allocate a unary expression in the arena
fn alloc_unary<'arena>(
    arena: &'arena Bump,
    op: UnaryOp,
    operand: &'arena Expr<'arena>,
    span: Span,
) -> &'arena Expr<'arena> {
    arena.alloc(Expr::new(ExprKind::Unary(op, operand), span))
}

/// Apply a unary operator multiple times
fn apply_unary_repeated<'arena>(
    arena: &'arena Bump,
    op: UnaryOp,
    count: usize,
    mut expr: &'arena Expr<'arena>,
    base_span: Span,
) -> &'arena Expr<'arena> {
    for _ in 0..count {
        expr = alloc_unary(arena, op, expr, base_span);
    }
    expr
}

/// Build a binary chain (left-associative)
fn build_binary_chain<'arena>(
    pair: pest::iterators::Pair<'_, Rule>,
    arena: &'arena Bump,
    interner: &RefCell<StringInterner<'arena>>,
    op: BinaryOp,
) -> &'arena Expr<'arena> {
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();
    let mut left = build_expr(inner.next().unwrap(), arena, interner);

    while inner.peek().is_some() {
        let right = build_expr(inner.next().unwrap(), arena, interner);
        left = alloc_binary(arena, op, left, right, span);
    }

    left
}

#[cfg(test)]
mod tests {
    use super::*;

    // Test helper that leaks arena (acceptable in tests)
    fn build_ast(input: &str) -> Result<Expr<'static>> {
        let arena = Box::leak(Box::new(Bump::new()));
        let interner = RefCell::new(StringInterner::new(arena));
        build_ast_with_arena(input, ParseConfig::default(), arena, &interner).cloned()
    }

    macro_rules! test_cases {
        ($($name:ident: $input:expr => |$ast:ident| $check:block),* $(,)?) => {
            $(
                #[test]
                fn $name() {
                    let $ast = build_ast($input).unwrap();
                    $check
                }
            )*
        };
    }

    // ============================================================
    // Section: AST Construction Tests
    // ============================================================

    test_cases! {
        test_build_ast_literal_int: "42" => |ast| {
            match ast.kind {
                ExprKind::Literal(Literal::Int(s)) => assert_eq!(s, "42"),
                _ => panic!("expected int literal"),
            }
        },

        test_build_ast_literal_string: r#""hello""# => |ast| {
            match ast.kind {
                ExprKind::Literal(Literal::String(content, is_raw, quote)) => {
                    assert_eq!(content, "hello");
                    assert!(!is_raw);
                    assert_eq!(quote, QuoteStyle::DoubleQuote);
                }
                _ => panic!("expected string literal"),
            }
        },

        test_build_ast_binary_add: "1 + 2" => |ast| {
            match ast.kind {
                ExprKind::Binary(op, left, right) => {
                    assert_eq!(op, BinaryOp::Add);
                    match left.kind {
                        ExprKind::Literal(Literal::Int(s)) => assert_eq!(s, "1"),
                        _ => panic!("expected int literal for left"),
                    }
                    match right.kind {
                        ExprKind::Literal(Literal::Int(s)) => assert_eq!(s, "2"),
                        _ => panic!("expected int literal for right"),
                    }
                }
                _ => panic!("expected binary expression"),
            }
        },

        test_build_ast_ternary: "true ? 1 : 2" => |ast| {
            match ast.kind {
                ExprKind::Ternary(cond, if_true, if_false) => {
                    match cond.kind {
                        ExprKind::Literal(Literal::Bool(true)) => {}
                        _ => panic!("expected true literal"),
                    }
                    match if_true.kind {
                        ExprKind::Literal(Literal::Int(s)) => assert_eq!(s, "1"),
                        _ => panic!("expected int literal"),
                    }
                    match if_false.kind {
                        ExprKind::Literal(Literal::Int(s)) => assert_eq!(s, "2"),
                        _ => panic!("expected int literal"),
                    }
                }
                _ => panic!("expected ternary expression"),
            }
        },

        test_build_ast_identifier: "foo" => |ast| {
            match ast.kind {
                ExprKind::Ident(name) => assert_eq!(name, "foo"),
                _ => panic!("expected identifier"),
            }
        },

        test_build_ast_list: "[1, 2, 3]" => |ast| {
            match ast.kind {
                ExprKind::List(items) => {
                    assert_eq!(items.len(), 3);
                }
                _ => panic!("expected list"),
            }
        },
    }
}
