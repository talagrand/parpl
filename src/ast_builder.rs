// AST builder - converts pest parse tree to AST
//
// This module transforms pest's `Pairs` into our typed AST.
// Deferred processing:
// - Escape sequences: handled during value construction (not here)
// - Numeric parsing: strings stored as-is, parsed during value construction
// - Identifier resolution: handled during evaluation

use crate::ast::*;
use crate::error::Result;
use crate::parser::{ParseConfig, Rule};
use pest::iterators::Pair;

/// Build an AST from a CEL source string with default configuration
///
/// This is a convenience function that uses default parsing limits.
///
/// # Examples
/// ```
/// use cello::build_ast;
///
/// let ast = build_ast("1 + 2").unwrap();
/// ```
pub fn build_ast(input: &str) -> Result<Expr> {
    build_ast_with_config(input, ParseConfig::default())
}

/// Build an AST from a CEL source string with custom configuration
///
/// This allows you to customize the complexity limits for parsing.
///
/// # Examples
/// ```
/// use cello::{build_ast_with_config, ParseConfig};
///
/// let config = ParseConfig {
///     max_nesting_depth: 100,
///     max_call_limit: 1_000_000,
/// };
/// let ast = build_ast_with_config("1 + 2", config).unwrap();
/// ```
pub fn build_ast_with_config(input: &str, config: ParseConfig) -> Result<Expr> {
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

    Ok(build_expr(expr_pair))
}

/// Build an expression from a pest Pair
fn build_expr(pair: Pair<Rule>) -> Expr {
    let span = span_from_pair(&pair);

    match pair.as_rule() {
        Rule::expr => {
            // expr = { conditional_or ~ ("?" ~ conditional_or ~ ":" ~ expr)? }
            let mut inner = pair.into_inner();
            let condition = build_expr(inner.next().unwrap());

            // Check for ternary operator
            if let Some(if_true) = inner.next() {
                let if_false = inner.next().unwrap();
                Expr::ternary(condition, build_expr(if_true), build_expr(if_false))
            } else {
                condition
            }
        }

        Rule::conditional_or => {
            // conditional_or = { conditional_and ~ ("||" ~ conditional_and)* }
            build_binary_chain(pair, BinaryOp::LogicalOr)
        }

        Rule::conditional_and => {
            // conditional_and = { relation ~ ("&&" ~ relation)* }
            build_binary_chain(pair, BinaryOp::LogicalAnd)
        }

        Rule::relation => {
            // relation = { addition ~ (relop ~ addition)* }
            let mut inner = pair.into_inner();
            let mut left = build_expr(inner.next().unwrap());

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
                let right = build_expr(inner.next().unwrap());
                left = Expr::binary(op, left, right);
            }

            left
        }

        Rule::addition => {
            // addition = { multiplication ~ (("+" | "-") ~ multiplication)* }
            let mut inner = pair.into_inner();
            let mut left = build_expr(inner.next().unwrap());

            while let Some(next) = inner.next() {
                let op = match next.as_str() {
                    "+" => BinaryOp::Add,
                    "-" => BinaryOp::Subtract,
                    _ => {
                        // It's the right operand
                        left = Expr::binary(
                            if inner.len() == 0 {
                                BinaryOp::Add
                            } else {
                                BinaryOp::Subtract
                            },
                            left,
                            build_expr(next),
                        );
                        continue;
                    }
                };
                let right = build_expr(inner.next().unwrap());
                left = Expr::binary(op, left, right);
            }

            left
        }

        Rule::multiplication => {
            // multiplication = { unary ~ (("*" | "/" | "%") ~ unary)* }
            let mut inner = pair.into_inner();
            let mut left = build_expr(inner.next().unwrap());

            while let Some(next) = inner.next() {
                let op = match next.as_str() {
                    "*" => BinaryOp::Multiply,
                    "/" => BinaryOp::Divide,
                    "%" => BinaryOp::Modulo,
                    _ => {
                        // It's the right operand (shouldn't happen with current grammar)
                        left = Expr::binary(BinaryOp::Multiply, left, build_expr(next));
                        continue;
                    }
                };
                let right = build_expr(inner.next().unwrap());
                left = Expr::binary(op, left, right);
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
                    let operand = build_expr(inner.next().unwrap());
                    // Apply NOT count times (!! cancels out)
                    apply_unary_repeated(UnaryOp::Not, count, operand, span)
                }
                s if s.chars().all(|c| c == '-') => {
                    let count = s.len();
                    let operand = build_expr(inner.next().unwrap());
                    // Apply Negate count times (-- cancels out)
                    apply_unary_repeated(UnaryOp::Negate, count, operand, span)
                }
                _ => build_expr(first), // It's a member expression
            }
        }

        Rule::member => {
            // member = { primary ~ ("." ~ selector ~ ("(" ~ expr_list? ~ ")")? | "[" ~ expr ~ "]")* }
            let mut inner = pair.into_inner();
            let mut expr = build_expr(inner.next().unwrap());

            while let Some(next) = inner.next() {
                match next.as_str() {
                    "." => {
                        // Field access or method call
                        let selector = inner.next().unwrap();
                        let field_name = selector.as_str().to_string();

                        // Check if there's a function call
                        if let Some(peek) = inner.peek() {
                            if peek.as_str() == "(" {
                                inner.next(); // consume "("
                                let args = if let Some(args_pair) = inner.peek() {
                                    if args_pair.as_rule() == Rule::expr_list {
                                        build_expr_list(inner.next().unwrap())
                                    } else {
                                        vec![]
                                    }
                                } else {
                                    vec![]
                                };
                                // Consume ")" - it's implicit in the grammar
                                let new_span = expr.span.combine(&span);
                                expr = Expr::new(
                                    ExprKind::Member(Box::new(expr), field_name, Some(args)),
                                    new_span,
                                );
                            } else {
                                let new_span = expr.span.combine(&span);
                                expr = Expr::new(
                                    ExprKind::Member(Box::new(expr), field_name, None),
                                    new_span,
                                );
                            }
                        } else {
                            let new_span = expr.span.combine(&span);
                            expr = Expr::new(
                                ExprKind::Member(Box::new(expr), field_name, None),
                                new_span,
                            );
                        }
                    }
                    "[" => {
                        // Index access
                        let index = build_expr(inner.next().unwrap());
                        // "]" is implicit
                        let new_span = expr.span.combine(&span);
                        expr =
                            Expr::new(ExprKind::Index(Box::new(expr), Box::new(index)), new_span);
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
                Rule::literal => build_literal(first, span),
                Rule::ident => {
                    let name = first.as_str().to_string();
                    // Check for function call
                    if inner.peek().map(|p| p.as_str()) == Some("(") {
                        inner.next(); // consume "("
                        let args = if let Some(args_pair) = inner.peek() {
                            if args_pair.as_rule() == Rule::expr_list {
                                build_expr_list(inner.next().unwrap())
                            } else {
                                vec![]
                            }
                        } else {
                            vec![]
                        };
                        Expr::new(ExprKind::Call(None, name, args), span)
                    } else {
                        Expr::ident(name, span)
                    }
                }
                Rule::expr => build_expr(first), // Parenthesized expression
                Rule::expr_list => {
                    // List literal: [expr, ...]
                    let items = build_expr_list(first);
                    Expr::new(ExprKind::List(items), span)
                }
                Rule::map_inits => {
                    // Map literal: {key: value, ...}
                    let entries = build_map_inits(first);
                    Expr::new(ExprKind::Map(entries), span)
                }
                _ => {
                    // Handle other primary forms
                    match first.as_str() {
                        "[" => {
                            // Empty list or list with items
                            if let Some(list_pair) = inner.peek() {
                                if list_pair.as_rule() == Rule::expr_list {
                                    let items = build_expr_list(inner.next().unwrap());
                                    Expr::new(ExprKind::List(items), span)
                                } else {
                                    Expr::new(ExprKind::List(vec![]), span)
                                }
                            } else {
                                Expr::new(ExprKind::List(vec![]), span)
                            }
                        }
                        "{" => {
                            // Empty map or map with entries
                            if let Some(map_pair) = inner.peek() {
                                if map_pair.as_rule() == Rule::map_inits {
                                    let entries = build_map_inits(inner.next().unwrap());
                                    Expr::new(ExprKind::Map(entries), span)
                                } else {
                                    Expr::new(ExprKind::Map(vec![]), span)
                                }
                            } else {
                                Expr::new(ExprKind::Map(vec![]), span)
                            }
                        }
                        _ => unreachable!("unexpected primary: {}", first.as_str()),
                    }
                }
            }
        }

        Rule::literal => build_literal(pair, span),
        Rule::ident => Expr::ident(pair.as_str().to_string(), span),

        _ => unreachable!("unexpected rule in build_expr: {:?}", pair.as_rule()),
    }
}

/// Build a binary operation chain (for left-associative operators)
fn build_binary_chain(pair: Pair<Rule>, op: BinaryOp) -> Expr {
    let mut inner = pair.into_inner();
    let mut left = build_expr(inner.next().unwrap());

    for right_pair in inner {
        let right = build_expr(right_pair);
        left = Expr::binary(op, left, right);
    }

    left
}

/// Apply a unary operator multiple times
fn apply_unary_repeated(op: UnaryOp, count: usize, mut expr: Expr, span: Span) -> Expr {
    for _ in 0..count {
        expr = Expr::unary(op, expr, span.clone());
    }
    expr
}

/// Build a literal expression
fn build_literal(pair: Pair<Rule>, span: Span) -> Expr {
    let inner = pair.into_inner().next().unwrap();

    let literal = match inner.as_rule() {
        Rule::int_lit => Literal::Int(inner.as_str().to_string()),
        Rule::uint_lit => {
            // Remove the 'u' suffix
            let s = inner.as_str();
            Literal::UInt(s[..s.len() - 1].to_string())
        }
        Rule::float_lit => Literal::Float(inner.as_str().to_string()),
        Rule::string_lit => {
            let s = inner.as_str();
            let (content, is_raw, quote_style) = parse_string_literal(s);
            Literal::String(content, is_raw, quote_style)
        }
        Rule::bytes_lit => {
            // Skip the 'b' or 'B' prefix
            let s = &inner.as_str()[1..];
            let (content, is_raw, quote_style) = parse_string_literal(s);
            Literal::Bytes(content, is_raw, quote_style)
        }
        Rule::bool_lit => Literal::Bool(inner.as_str() == "true"),
        Rule::null_lit => Literal::Null,
        _ => unreachable!("unexpected literal rule: {:?}", inner.as_rule()),
    };

    Expr::literal(literal, span)
}

/// Parse a string literal, extracting content, raw flag, and quote style
///
/// **CEL-RESTRICTED**: Escape sequences are NOT processed here.
/// They will be processed during value construction.
fn parse_string_literal(s: &str) -> (String, bool, QuoteStyle) {
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

    (content.to_string(), is_raw, quote_style)
}

/// Build an expression list
fn build_expr_list(pair: Pair<Rule>) -> Vec<Expr> {
    pair.into_inner().map(build_expr).collect()
}

/// Build map initializers
fn build_map_inits(pair: Pair<Rule>) -> Vec<(Expr, Expr)> {
    let mut inner = pair.into_inner();
    let mut entries = Vec::new();

    while let Some(key) = inner.next() {
        let value = inner.next().unwrap();
        entries.push((build_expr(key), build_expr(value)));
    }

    entries
}

/// Extract span from a pest Pair
fn span_from_pair(pair: &Pair<Rule>) -> Span {
    let span = pair.as_span();
    Span::new(span.start(), span.end())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_build_ast_literal_int() {
        let ast = build_ast("42").unwrap();
        match ast.kind {
            ExprKind::Literal(Literal::Int(s)) => assert_eq!(s, "42"),
            _ => panic!("expected int literal"),
        }
    }

    #[test]
    fn test_build_ast_literal_string() {
        let ast = build_ast(r#""hello""#).unwrap();
        match ast.kind {
            ExprKind::Literal(Literal::String(content, is_raw, quote)) => {
                assert_eq!(content, "hello");
                assert!(!is_raw);
                assert_eq!(quote, QuoteStyle::DoubleQuote);
            }
            _ => panic!("expected string literal"),
        }
    }

    #[test]
    fn test_build_ast_binary_add() {
        let ast = build_ast("1 + 2").unwrap();
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
    }

    #[test]
    fn test_build_ast_ternary() {
        let ast = build_ast("true ? 1 : 2").unwrap();
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
    }

    #[test]
    fn test_build_ast_identifier() {
        let ast = build_ast("foo").unwrap();
        match ast.kind {
            ExprKind::Ident(name) => assert_eq!(name, "foo"),
            _ => panic!("expected identifier"),
        }
    }

    #[test]
    fn test_build_ast_list() {
        let ast = build_ast("[1, 2, 3]").unwrap();
        match ast.kind {
            ExprKind::List(items) => {
                assert_eq!(items.len(), 3);
            }
            _ => panic!("expected list"),
        }
    }
}
