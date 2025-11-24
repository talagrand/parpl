// AST builder - converts pest parse tree to AST
//
// This module transforms pest's `Pairs` into our typed AST.
// All allocations are done in a bumpalo arena, and strings are interned
// for deduplication.
//
// Processing during AST construction:
// - Escape sequences: processed immediately via literal::process_literal
// - Numeric parsing: validated and parsed immediately
// - Identifier resolution: handled during evaluation

use crate::ast::*;
use crate::context::StringInterner;
use crate::error::{Error, Result};
use crate::parser::{ParseConfig, Rule};
use bumpalo::Bump;
use pest::iterators::Pair;
use std::cell::RefCell;

/// Check recursion depth remaining and return error if exhausted
///
/// This is called at the entry of each recursive function.
/// Since depth_left is passed by value, it automatically "resets" on return.
#[inline(always)]
fn check_depth(depth_left: usize) -> Result<usize> {
    if depth_left == 0 {
        Err(Error::nesting_depth(0, 0)) // Will be improved to show actual limit
    } else {
        Ok(depth_left - 1)
    }
}

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

    // Convert to AST with depth tracking
    // The parse tree has structure: SOI ~ expr ~ EOI
    // We want just the expr
    let pair = pairs
        .into_iter()
        .next()
        .expect("Parser validated: successful parse returns at least one pair");

    // The cel rule contains: SOI ~ expr ~ EOI
    // Extract the expr
    let mut inner = pair.into_inner();
    let expr_pair = inner
        .next()
        .expect("Parser validated: cel = { SOI ~ expr ~ EOI }");

    // Start with max depth remaining
    build_expr(config.max_ast_depth, expr_pair, arena, interner)
}

// ============================================================================
// EXPRESSION PRECEDENCE CHAIN (CEL Spec lines 68-94)
// ============================================================================
//
// Precedence from lowest to highest (each function calls the next level):
//
//   1. build_expr_ternary     - Ternary: a ? b : c
//   2. build_conditional_or   - Logical OR: ||
//   3. build_conditional_and  - Logical AND: &&
//   4. build_relation         - Comparisons: <, <=, >, >=, ==, !=, in
//   5. build_addition         - Addition/Subtraction: +, -
//   6. build_multiplication   - Multiply/Divide/Modulo: *, /, %
//   7. build_unary            - Unary operators: !, -
//   8. build_member           - Member access/indexing: .field, [index]
//   9. build_primary          - Literals, identifiers, parentheses
//
// KEY OPTIMIZATION: Each function calls the NEXT precedence level directly,
// not through build_expr(). This eliminates the dispatch overhead.
//
// Previously, every level called build_expr() which dispatched through a
// giant match statement, causing ~10 stack frames per nesting level.
// Now we get ~1 stack frame per nesting level, allowing 10x deeper nesting.
//
// ONLY build_primary() calls build_expr() for parenthesized expressions,
// which need to start at the top of the precedence chain.
//
// TO ADD NEW PRECEDENCE LEVEL:
//   1. Create new build_foo() function
//   2. Make it call the next level down
//   3. Update the level above to call your new function
//   4. Add Rule::foo case to build_expr() dispatch
//   5. Update this comment
//
// ============================================================================

/// Build an expression from a pest Pair (dispatch entry point)
///
/// This function dispatches to the appropriate precedence level based on
/// the rule type. It should only be called from:
///   1. build_ast_with_arena() - top-level entry point
///   2. build_primary() - for parenthesized expressions
///
/// All other cases call precedence-level functions directly.
fn build_expr<'arena>(
    depth_left: usize,
    pair: pest::iterators::Pair<'_, Rule>,
    arena: &'arena Bump,
    interner: &RefCell<StringInterner<'arena>>,
) -> Result<&'arena Expr<'arena>> {
    // Check depth and decrement for recursive calls
    let depth_left = check_depth(depth_left)?;

    match pair.as_rule() {
        Rule::expr => build_expr_ternary(depth_left, pair, arena, interner),
        Rule::conditional_or => build_conditional_or(depth_left, pair, arena, interner),
        Rule::conditional_and => build_conditional_and(depth_left, pair, arena, interner),
        Rule::relation => build_relation(depth_left, pair, arena, interner),
        Rule::addition => build_addition(depth_left, pair, arena, interner),
        Rule::multiplication => build_multiplication(depth_left, pair, arena, interner),
        Rule::unary => build_unary(depth_left, pair, arena, interner),
        Rule::member => build_member(depth_left, pair, arena, interner),
        Rule::primary => build_primary(depth_left, pair, arena, interner),
        Rule::literal => {
            let span = span_from_pair(&pair);
            Ok(arena.alloc(Expr::new(
                ExprKind::Literal(build_literal(pair, span, arena, interner)?),
                span,
            )))
        }
        Rule::ident => {
            let span = span_from_pair(&pair);
            let name = interner.borrow_mut().intern(pair.as_str());
            Ok(arena.alloc(Expr::new(ExprKind::Ident(name), span)))
        }
        _ => unreachable!("Unexpected rule in build_expr: {:?}", pair.as_rule()),
    }
}

/// Build ternary conditional expression (top of precedence chain)
/// CEL Spec: expr = { conditional_or ~ ("?" ~ conditional_or ~ ":" ~ expr)? }
fn build_expr_ternary<'arena>(
    depth_left: usize,
    pair: pest::iterators::Pair<'_, Rule>,
    arena: &'arena Bump,
    interner: &RefCell<StringInterner<'arena>>,
) -> Result<&'arena Expr<'arena>> {
    let depth_left = check_depth(depth_left)?;
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();

    // Build condition - call next precedence level DIRECTLY
    let condition = build_conditional_or(
        depth_left,
        inner
            .next()
            .expect("Parser validated: expr = { conditional_or ~ ... }"),
        arena,
        interner,
    )?;

    // Check for ternary operator
    if let Some(if_true_pair) = inner.next() {
        let if_false_pair = inner
            .next()
            .expect("Parser validated: expr = { ... ~ (\"?\" ~ conditional_or ~ \":\" ~ expr)? }");
        Ok(arena.alloc(Expr::new(
            ExprKind::Ternary(
                condition,
                build_conditional_or(depth_left, if_true_pair, arena, interner)?,
                build_expr_ternary(depth_left, if_false_pair, arena, interner)?, // Right-associative
            ),
            span,
        )))
    } else {
        Ok(condition)
    }
}

/// Build logical OR expression
/// CEL Spec: conditional_or = { conditional_and ~ ("||" ~ conditional_and)* }
fn build_conditional_or<'arena>(
    depth_left: usize,
    pair: pest::iterators::Pair<'_, Rule>,
    arena: &'arena Bump,
    interner: &RefCell<StringInterner<'arena>>,
) -> Result<&'arena Expr<'arena>> {
    let depth_left = check_depth(depth_left)?;
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();

    let mut left = build_conditional_and(
        depth_left,
        inner
            .next()
            .expect("Parser validated: conditional_or = { conditional_and ~ ... }"),
        arena,
        interner,
    )?;

    for right_pair in inner {
        let right = build_conditional_and(depth_left, right_pair, arena, interner)?;
        left = alloc_binary(arena, BinaryOp::LogicalOr, left, right, span);
    }

    Ok(left)
}

/// Build logical AND expression
/// CEL Spec: conditional_and = { relation ~ ("&&" ~ relation)* }
fn build_conditional_and<'arena>(
    depth_left: usize,
    pair: pest::iterators::Pair<'_, Rule>,
    arena: &'arena Bump,
    interner: &RefCell<StringInterner<'arena>>,
) -> Result<&'arena Expr<'arena>> {
    let depth_left = check_depth(depth_left)?;
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();

    let mut left = build_relation(
        depth_left,
        inner
            .next()
            .expect("Parser validated: conditional_and = { relation ~ ... }"),
        arena,
        interner,
    )?;

    for right_pair in inner {
        let right = build_relation(depth_left, right_pair, arena, interner)?;
        left = alloc_binary(arena, BinaryOp::LogicalAnd, left, right, span);
    }

    Ok(left)
}

/// Build relational expression
/// CEL Spec: relation = { addition ~ (relop ~ addition)* }
fn build_relation<'arena>(
    depth_left: usize,
    pair: pest::iterators::Pair<'_, Rule>,
    arena: &'arena Bump,
    interner: &RefCell<StringInterner<'arena>>,
) -> Result<&'arena Expr<'arena>> {
    let depth_left = check_depth(depth_left)?;
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();

    let mut left = build_addition(
        depth_left,
        inner
            .next()
            .expect("Parser validated: relation = { addition ~ ... }"),
        arena,
        interner,
    )?;

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
        let right = build_addition(
            depth_left,
            inner
                .next()
                .expect("Parser validated: relation = { ... ~ (relop ~ addition)* }"),
            arena,
            interner,
        )?;
        left = alloc_binary(arena, op, left, right, span);
    }

    Ok(left)
}

/// Build addition/subtraction expression
/// CEL Spec: addition = { multiplication ~ (("+" | "-") ~ multiplication)* }
fn build_addition<'arena>(
    depth_left: usize,
    pair: pest::iterators::Pair<'_, Rule>,
    arena: &'arena Bump,
    interner: &RefCell<StringInterner<'arena>>,
) -> Result<&'arena Expr<'arena>> {
    let depth_left = check_depth(depth_left)?;
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();

    let mut left = build_multiplication(
        depth_left,
        inner
            .next()
            .expect("Parser validated: addition = { multiplication ~ ... }"),
        arena,
        interner,
    )?;

    while let Some(next) = inner.next() {
        let op = match next.as_str() {
            "+" => BinaryOp::Add,
            "-" => BinaryOp::Subtract,
            _ => {
                // It's the right operand
                left = alloc_binary(
                    arena,
                    BinaryOp::Add,
                    left,
                    build_multiplication(depth_left, next, arena, interner)?,
                    span,
                );
                continue;
            }
        };
        let right = build_multiplication(
            depth_left,
            inner.next().expect(
                "Parser validated: addition = { ... ~ ((\" +\" | \"-\") ~ multiplication)* }",
            ),
            arena,
            interner,
        )?;
        left = alloc_binary(arena, op, left, right, span);
    }

    Ok(left)
}

/// Build multiplication/division/modulo expression
/// CEL Spec: multiplication = { unary ~ (("*" | "/" | "%") ~ unary)* }
fn build_multiplication<'arena>(
    depth_left: usize,
    pair: pest::iterators::Pair<'_, Rule>,
    arena: &'arena Bump,
    interner: &RefCell<StringInterner<'arena>>,
) -> Result<&'arena Expr<'arena>> {
    let depth_left = check_depth(depth_left)?;
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();

    let mut left = build_unary(
        depth_left,
        inner
            .next()
            .expect("Parser validated: multiplication = { unary ~ ... }"),
        arena,
        interner,
    )?;

    while let Some(next) = inner.next() {
        let op = match next.as_str() {
            "*" => BinaryOp::Multiply,
            "/" => BinaryOp::Divide,
            "%" => BinaryOp::Modulo,
            _ => {
                // It's the right operand
                left = alloc_binary(
                    arena,
                    BinaryOp::Multiply,
                    left,
                    build_unary(depth_left, next, arena, interner)?,
                    span,
                );
                continue;
            }
        };
        let right = build_unary(
            depth_left,
            inner.next().expect(
                "Parser validated: multiplication = { ... ~ ((\"*\" | \"/\" | \"%\") ~ unary)* }",
            ),
            arena,
            interner,
        )?;
        left = alloc_binary(arena, op, left, right, span);
    }

    Ok(left)
}

/// Build unary expression
/// CEL Spec: unary = { member | "!"+ ~ member | "-"+ ~ member }
fn build_unary<'arena>(
    depth_left: usize,
    pair: pest::iterators::Pair<'_, Rule>,
    arena: &'arena Bump,
    interner: &RefCell<StringInterner<'arena>>,
) -> Result<&'arena Expr<'arena>> {
    let depth_left = check_depth(depth_left)?;
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();
    let first = inner
        .next()
        .expect("Parser validated: unary = { member | \"!\"+  ~ member | \"-\"+ ~ member }");

    match first.as_str() {
        s if s.chars().all(|c| c == '!') => {
            let count = s.len();
            let operand = build_member(
                depth_left,
                inner
                    .next()
                    .expect("Parser validated: unary = { ... | \"!\"+ ~ member | ... }"),
                arena,
                interner,
            )?;
            // Apply NOT count times (!! cancels out)
            Ok(apply_unary_repeated(
                arena,
                UnaryOp::Not,
                count,
                operand,
                span,
            ))
        }
        s if s.chars().all(|c| c == '-') => {
            let count = s.len();
            let operand = build_member(
                depth_left,
                inner
                    .next()
                    .expect("Parser validated: unary = { ... | \"-\"+ ~ member }"),
                arena,
                interner,
            )?;
            // Apply Negate count times (-- cancels out)
            Ok(apply_unary_repeated(
                arena,
                UnaryOp::Negate,
                count,
                operand,
                span,
            ))
        }
        _ => build_member(depth_left, first, arena, interner), // It's a member expression
    }
}

/// Build member access/indexing expression
/// CEL Spec: member = { primary ~ ("." ~ selector ~ ("(" ~ expr_list? ~ ")")? | "[" ~ expr ~ "]")* }
fn build_member<'arena>(
    depth_left: usize,
    pair: pest::iterators::Pair<'_, Rule>,
    arena: &'arena Bump,
    interner: &RefCell<StringInterner<'arena>>,
) -> Result<&'arena Expr<'arena>> {
    let depth_left = check_depth(depth_left)?;
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();

    let mut expr = build_primary(
        depth_left,
        inner
            .next()
            .expect("Parser validated: member = { primary ~ ... }"),
        arena,
        interner,
    )?;

    while let Some(next) = inner.next() {
        match next.as_str() {
            "." => {
                // Field access or method call
                let selector = inner
                    .next()
                    .expect("Parser validated: member = { ... ~ (\".\" ~ selector ~ ...)* }");
                let field_name = interner.borrow_mut().intern(selector.as_str());

                // Check if there's a function call
                if let Some(peek) = inner.peek() {
                    if peek.as_str() == "(" {
                        inner.next(); // consume "("
                        let args = if let Some(args_pair) = inner.peek() {
                            if args_pair.as_rule() == Rule::expr_list {
                                build_expr_list(
                                    depth_left,
                                    inner.next().expect(
                                        "Parser validated: member = { ... ~ (\"(\" ~ expr_list? ~ \")\")? }",
                                    ),
                                    arena,
                                    interner,
                                )?
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
                // Index access - call build_expr to start at top of precedence chain
                let index = build_expr(
                    depth_left,
                    inner
                        .next()
                        .expect("Parser validated: member = { ... ~ (\"[\" ~ expr ~ \"]\")* }"),
                    arena,
                    interner,
                )?;
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

    Ok(expr)
}

/// Build primary expression (bottom of precedence chain)
/// CEL Spec: primary = { literal | "."? ~ ident ~ ("(" ~ expr_list? ~ ")")? | ... }
fn build_primary<'arena>(
    depth_left: usize,
    pair: pest::iterators::Pair<'_, Rule>,
    arena: &'arena Bump,
    interner: &RefCell<StringInterner<'arena>>,
) -> Result<&'arena Expr<'arena>> {
    let depth_left = check_depth(depth_left)?;
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();
    let first = inner
        .next()
        .expect("Parser validated: primary = { literal | ... | \"(\" ~ expr ~ \")\" | \"[\" ~ expr_list? ~ \",\"? ~ \"]\" | \"{\" ~ map_inits? ~ \",\"? ~ \"}\" | ... }");

    match first.as_rule() {
        Rule::literal => Ok(arena.alloc(Expr::new(
            ExprKind::Literal(build_literal(first, span, arena, interner)?),
            span,
        ))),
        Rule::ident => {
            let name = interner.borrow_mut().intern(first.as_str());
            // Check for function call
            if inner.peek().map(|p| p.as_str()) == Some("(") {
                inner.next(); // consume "("
                let args = if let Some(args_pair) = inner.peek() {
                    if args_pair.as_rule() == Rule::expr_list {
                        build_expr_list(
                            depth_left,
                            inner.next().expect(
                                "Parser validated: primary = { ... ~ \"(\" ~ expr_list? ~ \")\" }",
                            ),
                            arena,
                            interner,
                        )?
                    } else {
                        &[]
                    }
                } else {
                    &[]
                };
                Ok(arena.alloc(Expr::new(ExprKind::Call(None, name, args), span)))
            } else {
                Ok(arena.alloc(Expr::new(ExprKind::Ident(name), span)))
            }
        }
        // Parenthesized expression - ONLY place that calls build_expr()
        // This starts at the top of the precedence chain again
        Rule::expr => build_expr(depth_left, first, arena, interner),
        Rule::expr_list => {
            // List literal: [expr, ...]
            let items = build_expr_list(depth_left, first, arena, interner)?;
            Ok(arena.alloc(Expr::new(ExprKind::List(items), span)))
        }
        Rule::map_inits => {
            // Map literal: {key: value, ...}
            let entries = build_map_inits(depth_left, first, arena, interner)?;
            Ok(arena.alloc(Expr::new(ExprKind::Map(entries), span)))
        }
        _ => {
            // Handle other primary forms
            match first.as_str() {
                "[" => {
                    // Empty list or list with items
                    if let Some(list_pair) = inner.peek() {
                        if list_pair.as_rule() == Rule::expr_list {
                            let items = build_expr_list(
                                depth_left,
                                inner.next().expect(
                                    "Parser validated: primary = { ... ~ \"[\" ~ expr_list? ~ \",\"? ~ \"]\" }",
                                ),
                                arena,
                                interner,
                            )?;
                            Ok(arena.alloc(Expr::new(ExprKind::List(items), span)))
                        } else {
                            Ok(arena.alloc(Expr::new(ExprKind::List(&[]), span)))
                        }
                    } else {
                        Ok(arena.alloc(Expr::new(ExprKind::List(&[]), span)))
                    }
                }
                "{" => {
                    // Empty map or map with entries
                    if let Some(map_pair) = inner.peek() {
                        if map_pair.as_rule() == Rule::map_inits {
                            let entries = build_map_inits(
                                depth_left,
                                inner.next().expect(
                                    "Parser validated: primary = { ... ~ \"{\" ~ map_inits? ~ \",\"? ~ \"}\" }",
                                ),
                                arena,
                                interner,
                            )?;
                            Ok(arena.alloc(Expr::new(ExprKind::Map(entries), span)))
                        } else {
                            Ok(arena.alloc(Expr::new(ExprKind::Map(&[]), span)))
                        }
                    } else {
                        Ok(arena.alloc(Expr::new(ExprKind::Map(&[]), span)))
                    }
                }
                _ => unreachable!("unexpected primary: {}", first.as_str()),
            }
        }
    }
}

/// Build a literal expression
fn build_literal<'arena>(
    pair: Pair<Rule>,
    span: Span,
    arena: &'arena Bump,
    interner: &RefCell<StringInterner<'arena>>,
) -> Result<Literal<'arena>> {
    let inner = pair
        .into_inner()
        .next()
        .expect("Parser validated: literal = { float_lit | uint_lit | int_lit | bytes_lit | string_lit | bool_lit | null_lit }");

    // First, create a RawLiteral from the parser output
    let raw_literal = match inner.as_rule() {
        Rule::int_lit => RawLiteral::Int(interner.borrow_mut().intern(inner.as_str())),
        Rule::uint_lit => {
            // Remove the 'u' suffix using strip_suffix
            let s = inner.as_str();
            let s_without_suffix = s
                .strip_suffix('u')
                .or_else(|| s.strip_suffix('U'))
                .expect("Parser validated: uint_lit ends with 'u' or 'U'");
            RawLiteral::UInt(interner.borrow_mut().intern(s_without_suffix))
        }
        Rule::float_lit => RawLiteral::Float(interner.borrow_mut().intern(inner.as_str())),
        Rule::string_lit => {
            let s = inner.as_str();
            let (content, is_raw, quote_style) = parse_string_literal(s, interner);
            RawLiteral::String(content, is_raw, quote_style)
        }
        Rule::bytes_lit => {
            // Skip the 'b' or 'B' prefix using strip_prefix
            let s = inner
                .as_str()
                .strip_prefix('b')
                .or_else(|| inner.as_str().strip_prefix('B'))
                .expect("Parser validated: bytes_lit starts with 'b' or 'B'");
            let (content, is_raw, quote_style) = parse_string_literal(s, interner);
            RawLiteral::Bytes(content, is_raw, quote_style)
        }
        Rule::bool_lit => RawLiteral::Bool(inner.as_str() == "true"),
        Rule::null_lit => RawLiteral::Null,
        _ => unreachable!("unexpected literal rule: {:?}", inner.as_rule()),
    };

    // Process the RawLiteral into a Literal, adding span information to any errors
    crate::literal::process_literal(&raw_literal, &mut interner.borrow_mut(), arena)
        .map_err(|e| e.with_span(span))
}

/// Parse a string literal, extracting content, raw flag, and quote style
///
/// **CEL-RESTRICTED**: Escape sequences are NOT processed here.
/// They will be processed during value construction.
fn parse_string_literal<'arena>(
    s: &str,
    interner: &RefCell<StringInterner<'arena>>,
) -> (&'arena str, bool, QuoteStyle) {
    // Check for raw string prefix using pattern matching
    let (s, is_raw) = if let Some(rest) = s.strip_prefix('r').or_else(|| s.strip_prefix('R')) {
        (rest, true)
    } else {
        (s, false)
    };

    // Match quote style and extract content using strip_prefix/strip_suffix
    let (content, quote_style) = if let Some(rest) = s.strip_prefix("\"\"\"") {
        let content = rest
            .strip_suffix("\"\"\"")
            .expect("Parser validated: triple-quoted string ends with \"\"\"");
        (content, QuoteStyle::TripleDoubleQuote)
    } else if let Some(rest) = s.strip_prefix("'''") {
        let content = rest
            .strip_suffix("'''")
            .expect("Parser validated: triple-quoted string ends with '''");
        (content, QuoteStyle::TripleSingleQuote)
    } else if let Some(rest) = s.strip_prefix('"') {
        let content = rest
            .strip_suffix('"')
            .expect("Parser validated: double-quoted string ends with \"");
        (content, QuoteStyle::DoubleQuote)
    } else if let Some(rest) = s.strip_prefix('\'') {
        let content = rest
            .strip_suffix('\'')
            .expect("Parser validated: single-quoted string ends with '");
        (content, QuoteStyle::SingleQuote)
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
    depth_left: usize,
    pair: Pair<Rule>,
    arena: &'arena Bump,
    interner: &RefCell<StringInterner<'arena>>,
) -> Result<&'arena [Expr<'arena>]> {
    let exprs: Result<Vec<&Expr<'arena>>> = pair
        .into_inner()
        .map(|p| build_expr(depth_left, p, arena, interner))
        .collect();
    let exprs = exprs?;

    // Use iterator instead of indexing
    Ok(arena.alloc_slice_fill_iter(exprs.iter().map(|e| (*e).clone())))
}

/// Build map initializers - collect into std Vec, then clone into arena slice
///
/// We must clone because build_expr returns &Expr (reference) but we need to store
/// Expr values in the slice. Since Expr is not Copy, we clone.
fn build_map_inits<'arena>(
    depth_left: usize,
    pair: Pair<Rule>,
    arena: &'arena Bump,
    interner: &RefCell<StringInterner<'arena>>,
) -> Result<&'arena [(Expr<'arena>, Expr<'arena>)]> {
    let mut inner = pair.into_inner();
    let mut entries: Vec<(&Expr<'arena>, &Expr<'arena>)> = Vec::new();

    while let Some(key) = inner.next() {
        let value = inner
            .next()
            .expect("Parser validated: map_inits = { expr ~ \":\" ~ expr ~ ... }");
        entries.push((
            build_expr(depth_left, key, arena, interner)?,
            build_expr(depth_left, value, arena, interner)?,
        ));
    }

    // Use iterator instead of indexing
    Ok(arena.alloc_slice_fill_iter(entries.iter().map(|(k, v)| ((*k).clone(), (*v).clone()))))
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

#[cfg(test)]
mod tests {
    use super::*;

    // Test helper that leaks arena (acceptable in tests)
    fn build_ast(input: &str) -> Result<Expr<'static>> {
        let arena = Box::leak(Box::new(Bump::new()));
        let interner = RefCell::new(StringInterner::new());
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
                ExprKind::Literal(Literal::Int(val)) => assert_eq!(val, 42),
                _ => panic!("expected int literal"),
            }
        },

        test_build_ast_literal_string: r#""hello""# => |ast| {
            match ast.kind {
                ExprKind::Literal(Literal::String(content)) => {
                    assert_eq!(content, "hello");
                }
                _ => panic!("expected string literal"),
            }
        },

        test_build_ast_binary_add: "1 + 2" => |ast| {
            match ast.kind {
                ExprKind::Binary(op, left, right) => {
                    assert_eq!(op, BinaryOp::Add);
                    match left.kind {
                        ExprKind::Literal(Literal::Int(val)) => assert_eq!(val, 1),
                        _ => panic!("expected int literal for left"),
                    }
                    match right.kind {
                        ExprKind::Literal(Literal::Int(val)) => assert_eq!(val, 2),
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
                        ExprKind::Literal(Literal::Int(val)) => assert_eq!(val, 1),
                        _ => panic!("expected int literal"),
                    }
                    match if_false.kind {
                        ExprKind::Literal(Literal::Int(val)) => assert_eq!(val, 2),
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
