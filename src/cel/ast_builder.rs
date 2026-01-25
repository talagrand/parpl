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

use crate::{
    Interner, Span,
    cel::{
        ast::{BinaryOp, Literal, QuoteStyle, RawLiteral, UnaryOp},
        error::{Error, Result},
        literal::process_literal,
        parser::Rule,
        traits::CelWriter,
    },
};
use pest::iterators::Pair;

fn map_writer_error<E: std::error::Error + Send + Sync + 'static>(e: E, span: Span) -> Error {
    Error::WriterError {
        span,
        source: Box::new(e),
    }
}

/// Check recursion depth remaining and return error if exhausted
///
/// This is called at the entry of each recursive function.
/// Since depth_left is passed by value, it automatically "resets" on return.
#[inline(always)]
fn check_depth(depth_left: usize) -> Result<usize> {
    if depth_left == 0 {
        // Use zero-span since we don't have position context here
        Err(Error::nesting_depth(crate::Span::new(0, 0), None))
    } else {
        Ok(depth_left - 1)
    }
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

/// Build an AST from parsed pairs
///
/// This extracts the expression from the top-level rule and builds the AST.
pub fn build_ast_from_pairs<W: CelWriter>(
    pairs: pest::iterators::Pairs<'_, Rule>,
    max_ast_depth: usize,
    writer: &mut W,
) -> Result<W::Expr> {
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

    build_expr(max_ast_depth, expr_pair, writer)
}

/// Build an expression from a pest Pair (dispatch entry point)
///
/// This function dispatches to the appropriate precedence level based on
/// the rule type. It should only be called from:
///   1. build_ast_with_arena() - top-level entry point
///   2. build_primary() - for parenthesized expressions
///
/// All other cases call precedence-level functions directly.
pub fn build_expr<W: CelWriter>(
    depth_left: usize,
    pair: pest::iterators::Pair<'_, Rule>,
    writer: &mut W,
) -> Result<W::Expr> {
    // Check depth and decrement for recursive calls
    let depth_left = check_depth(depth_left)?;

    match pair.as_rule() {
        Rule::expr => build_expr_ternary(depth_left, pair, writer),
        Rule::conditional_or => build_conditional_or(depth_left, pair, writer),
        Rule::conditional_and => build_conditional_and(depth_left, pair, writer),
        Rule::relation => build_relation(depth_left, pair, writer),
        Rule::addition => build_addition(depth_left, pair, writer),
        Rule::multiplication => build_multiplication(depth_left, pair, writer),
        Rule::unary => build_unary(depth_left, pair, writer),
        Rule::member => build_member(depth_left, pair, writer),
        Rule::primary => build_primary(depth_left, pair, writer),
        Rule::literal => {
            let span = span_from_pair(&pair);
            let lit = process_literal_pair(pair, writer)?;
            writer
                .literal(lit, span)
                .map_err(|e| map_writer_error(e, span))
        }
        Rule::ident => {
            let span = span_from_pair(&pair);
            let name = writer.interner().intern(pair.as_str());
            writer
                .ident(name, span)
                .map_err(|e| map_writer_error(e, span))
        }
        _ => unreachable!("Unexpected rule in build_expr: {:?}", pair.as_rule()),
    }
}

/// Build ternary conditional expression (top of precedence chain)
/// CEL Spec: expr = { conditional_or ~ ("?" ~ conditional_or ~ ":" ~ expr)? }
fn build_expr_ternary<W: CelWriter>(
    depth_left: usize,
    pair: pest::iterators::Pair<'_, Rule>,
    writer: &mut W,
) -> Result<W::Expr> {
    let depth_left = check_depth(depth_left)?;
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();

    // Build condition - call next precedence level DIRECTLY
    let condition = build_conditional_or(
        depth_left,
        inner
            .next()
            .expect("Parser validated: expr = { conditional_or ~ ... }"),
        writer,
    )?;

    // Check for ternary operator
    if let Some(if_true_pair) = inner.next() {
        let if_false_pair = inner
            .next()
            .expect("Parser validated: expr = { ... ~ (\"?\" ~ conditional_or ~ \":\" ~ expr)? }");

        let true_expr = build_conditional_or(depth_left, if_true_pair, writer)?;
        let false_expr = build_expr_ternary(depth_left, if_false_pair, writer)?;

        writer
            .ternary(condition, true_expr, false_expr, span)
            .map_err(|e| map_writer_error(e, span))
    } else {
        Ok(condition)
    }
}

/// Build logical OR expression
/// CEL Spec: conditional_or = { conditional_and ~ ("||" ~ conditional_and)* }
fn build_conditional_or<W: CelWriter>(
    depth_left: usize,
    pair: pest::iterators::Pair<'_, Rule>,
    writer: &mut W,
) -> Result<W::Expr> {
    let depth_left = check_depth(depth_left)?;
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();

    let mut left = build_conditional_and(
        depth_left,
        inner
            .next()
            .expect("Parser validated: conditional_or = { conditional_and ~ ... }"),
        writer,
    )?;

    for right_pair in inner {
        let right = build_conditional_and(depth_left, right_pair, writer)?;
        left = writer
            .binary(BinaryOp::LogicalOr, left, right, span)
            .map_err(|e| map_writer_error(e, span))?;
    }

    Ok(left)
}

/// Build logical AND expression
/// CEL Spec: conditional_and = { relation ~ ("&&" ~ relation)* }
fn build_conditional_and<W: CelWriter>(
    depth_left: usize,
    pair: pest::iterators::Pair<'_, Rule>,
    writer: &mut W,
) -> Result<W::Expr> {
    let depth_left = check_depth(depth_left)?;
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();

    let mut left = build_relation(
        depth_left,
        inner
            .next()
            .expect("Parser validated: conditional_and = { relation ~ ... }"),
        writer,
    )?;

    for right_pair in inner {
        let right = build_relation(depth_left, right_pair, writer)?;
        left = writer
            .binary(BinaryOp::LogicalAnd, left, right, span)
            .map_err(|e| map_writer_error(e, span))?;
    }

    Ok(left)
}

/// Build relational expression
/// CEL Spec: relation = { addition ~ (relop ~ addition)* }
fn build_relation<W: CelWriter>(
    depth_left: usize,
    pair: pest::iterators::Pair<'_, Rule>,
    writer: &mut W,
) -> Result<W::Expr> {
    let depth_left = check_depth(depth_left)?;
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();

    let mut left = build_addition(
        depth_left,
        inner
            .next()
            .expect("Parser validated: relation = { addition ~ ... }"),
        writer,
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
            writer,
        )?;
        left = writer
            .binary(op, left, right, span)
            .map_err(|e| map_writer_error(e, span))?;
    }

    Ok(left)
}

/// Build addition/subtraction expression
/// CEL Spec: addition = { multiplication ~ (("+" | "-") ~ multiplication)* }
fn build_addition<W: CelWriter>(
    depth_left: usize,
    pair: pest::iterators::Pair<'_, Rule>,
    writer: &mut W,
) -> Result<W::Expr> {
    let depth_left = check_depth(depth_left)?;
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();

    let mut left = build_multiplication(
        depth_left,
        inner
            .next()
            .expect("Parser validated: addition = { multiplication ~ ... }"),
        writer,
    )?;

    while let Some(next) = inner.next() {
        let op = match next.as_str() {
            "+" => BinaryOp::Add,
            "-" => BinaryOp::Subtract,
            _ => {
                // It's the right operand
                let right = build_multiplication(depth_left, next, writer)?;
                left = writer
                    .binary(BinaryOp::Add, left, right, span)
                    .map_err(|e| map_writer_error(e, span))?;
                continue;
            }
        };
        let right = build_multiplication(
            depth_left,
            inner.next().expect(
                "Parser validated: addition = { ... ~ ((\" +\" | \"-\") ~ multiplication)* }",
            ),
            writer,
        )?;
        left = writer
            .binary(op, left, right, span)
            .map_err(|e| map_writer_error(e, span))?;
    }

    Ok(left)
}

/// Build multiplication/division/modulo expression
/// CEL Spec: multiplication = { unary ~ (("*" | "/" | "%") ~ unary)* }
fn build_multiplication<W: CelWriter>(
    depth_left: usize,
    pair: pest::iterators::Pair<'_, Rule>,
    writer: &mut W,
) -> Result<W::Expr> {
    let depth_left = check_depth(depth_left)?;
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();

    let mut left = build_unary(
        depth_left,
        inner
            .next()
            .expect("Parser validated: multiplication = { unary ~ ... }"),
        writer,
    )?;

    while let Some(next) = inner.next() {
        let op = match next.as_str() {
            "*" => BinaryOp::Multiply,
            "/" => BinaryOp::Divide,
            "%" => BinaryOp::Modulo,
            _ => {
                // It's the right operand
                let right = build_unary(depth_left, next, writer)?;
                left = writer
                    .binary(BinaryOp::Multiply, left, right, span)
                    .map_err(|e| map_writer_error(e, span))?;
                continue;
            }
        };
        let right = build_unary(
            depth_left,
            inner.next().expect(
                "Parser validated: multiplication = { ... ~ ((\"*\" | \"/\" | \"%\") ~ unary)* }",
            ),
            writer,
        )?;
        left = writer
            .binary(op, left, right, span)
            .map_err(|e| map_writer_error(e, span))?;
    }

    Ok(left)
}

/// Build unary expression
/// CEL Spec: unary = { member | "!"+ ~ member | "-"+ ~ member }
fn build_unary<W: CelWriter>(
    depth_left: usize,
    pair: pest::iterators::Pair<'_, Rule>,
    writer: &mut W,
) -> Result<W::Expr> {
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
                writer,
            )?;
            // Apply NOT count times (!! cancels out)
            apply_unary_repeated(writer, UnaryOp::Not, count, operand, span)
        }
        s if s.chars().all(|c| c == '-') => {
            let count = s.len();
            let operand = build_member(
                depth_left,
                inner
                    .next()
                    .expect("Parser validated: unary = { ... | \"-\"+ ~ member }"),
                writer,
            )?;
            // Apply Negate count times (-- cancels out)
            apply_unary_repeated(writer, UnaryOp::Negate, count, operand, span)
        }
        _ => build_member(depth_left, first, writer), // It's a member expression
    }
}

/// Build member access/indexing expression
/// CEL Spec: member = { primary ~ ("." ~ selector ~ ("(" ~ expr_list? ~ ")")? | "[" ~ expr ~ "]")* }
fn build_member<W: CelWriter>(
    depth_left: usize,
    pair: pest::iterators::Pair<'_, Rule>,
    writer: &mut W,
) -> Result<W::Expr> {
    let depth_left = check_depth(depth_left)?;
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();

    let mut expr = build_primary(
        depth_left,
        inner
            .next()
            .expect("Parser validated: member = { primary ~ ... }"),
        writer,
    )?;

    while let Some(next) = inner.next() {
        match next.as_str() {
            "." => {
                // Field access or method call
                let selector = inner
                    .next()
                    .expect("Parser validated: member = { ... ~ (\".\" ~ selector ~ ...)* }");
                let field_name = writer.interner().intern(selector.as_str());

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
                                    writer,
                                )?
                            } else {
                                Vec::new()
                            }
                        } else {
                            Vec::new()
                        };
                        // Consume ")" - it's implicit in the grammar

                        expr = writer
                            .member(expr, field_name, Some(&args), span)
                            .map_err(|e| map_writer_error(e, span))?;
                    } else {
                        expr = writer
                            .member(expr, field_name, None, span)
                            .map_err(|e| map_writer_error(e, span))?;
                    }
                } else {
                    expr = writer
                        .member(expr, field_name, None, span)
                        .map_err(|e| map_writer_error(e, span))?;
                }
            }
            "[" => {
                // Index access - call build_expr to start at top of precedence chain
                let index = build_expr(
                    depth_left,
                    inner
                        .next()
                        .expect("Parser validated: member = { ... ~ (\"[\" ~ expr ~ \"]\")* }"),
                    writer,
                )?;
                // "]" is implicit
                expr = writer
                    .index(expr, index, span)
                    .map_err(|e| map_writer_error(e, span))?;
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
fn build_primary<W: CelWriter>(
    depth_left: usize,
    pair: pest::iterators::Pair<'_, Rule>,
    writer: &mut W,
) -> Result<W::Expr> {
    let depth_left = check_depth(depth_left)?;
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();
    let first = inner
        .next()
        .expect("Parser validated: primary = { literal | ... | \"(\" ~ expr ~ \")\" | \"[\" ~ expr_list? ~ \",\"? ~ \"]\" | \"{\" ~ map_inits? ~ \",\"? ~ \"}\" | ... }");

    match first.as_rule() {
        Rule::literal => {
            let lit = process_literal_pair(first, writer)?;
            writer
                .literal(lit, span)
                .map_err(|e| map_writer_error(e, span))
        }
        Rule::ident => {
            let name = writer.interner().intern(first.as_str());
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
                            writer,
                        )?
                    } else {
                        Vec::new()
                    }
                } else {
                    Vec::new()
                };
                writer
                    .call(None, name, &args, span)
                    .map_err(|e| map_writer_error(e, span))
            } else {
                writer
                    .ident(name, span)
                    .map_err(|e| map_writer_error(e, span))
            }
        }
        // Parenthesized expression - ONLY place that calls build_expr()
        // This starts at the top of the precedence chain again
        Rule::expr => build_expr(depth_left, first, writer),
        Rule::expr_list => {
            // List literal: [expr, ...]
            let items = build_expr_list(depth_left, first, writer)?;
            writer
                .list(&items, span)
                .map_err(|e| map_writer_error(e, span))
        }
        Rule::map_inits => {
            // Map literal: {key: value, ...}
            let entries = build_map_inits(depth_left, first, writer)?;
            writer
                .map(&entries, span)
                .map_err(|e| map_writer_error(e, span))
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
                                writer,
                            )?;
                            writer
                                .list(&items, span)
                                .map_err(|e| map_writer_error(e, span))
                        } else {
                            writer
                                .list(&[], span)
                                .map_err(|e| map_writer_error(e, span))
                        }
                    } else {
                        writer
                            .list(&[], span)
                            .map_err(|e| map_writer_error(e, span))
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
                                writer,
                            )?;
                            writer
                                .map(&entries, span)
                                .map_err(|e| map_writer_error(e, span))
                        } else {
                            writer.map(&[], span).map_err(|e| map_writer_error(e, span))
                        }
                    } else {
                        writer.map(&[], span).map_err(|e| map_writer_error(e, span))
                    }
                }
                "." => {
                    // Leading dot identifier: .ident
                    let ident_pair = inner
                        .next()
                        .expect("Parser validated: primary = { \".\" ~ ident }");
                    let name = writer.interner().intern(ident_pair.as_str());
                    writer
                        .ident(name, span)
                        .map_err(|e| map_writer_error(e, span))
                }
                _ => unreachable!("unexpected primary: {}", first.as_str()),
            }
        }
    }
}

fn process_literal_pair<W: CelWriter>(
    pair: pest::iterators::Pair<'_, Rule>,
    writer: &mut W,
) -> Result<Literal<W::StringId, W::Bytes>> {
    // Check if pair is already one of the inner rules (if called with inner pair)
    // But build_primary calls it with `literal` rule pair.
    // build_expr calls it with `literal` rule pair.

    // If pair is `literal`, get inner.
    let inner = if pair.as_rule() == Rule::literal {
        pair.into_inner()
            .next()
            .expect("Parser validated: literal has one child")
    } else {
        pair
    };

    // Extract span before match borrows inner
    let span = span_from_pair(&inner);

    let raw_literal = match inner.as_rule() {
        Rule::int_lit => RawLiteral::Int(inner.as_str()),
        Rule::uint_lit => {
            let s = inner.as_str();
            let s_without_suffix = s
                .strip_suffix('u')
                .or_else(|| s.strip_suffix('U'))
                .expect("Parser validated: uint_lit ends with 'u' or 'U'");
            RawLiteral::UInt(s_without_suffix)
        }
        Rule::float_lit => RawLiteral::Float(inner.as_str()),
        Rule::string_lit => {
            let s = inner.as_str();
            let (content, is_raw, quote_style) = parse_string_literal(s);
            RawLiteral::String(content, is_raw, quote_style)
        }
        Rule::bytes_lit => {
            let s = inner.as_str();
            let s_without_prefix = s
                .strip_prefix('b')
                .or_else(|| s.strip_prefix('B'))
                .expect("Parser validated: bytes_lit starts with 'b' or 'B'");
            let (content, is_raw, quote_style) = parse_string_literal(s_without_prefix);
            RawLiteral::Bytes(content, is_raw, quote_style)
        }
        Rule::bool_lit => RawLiteral::Bool(inner.as_str() == "true"),
        Rule::null_lit => RawLiteral::Null,
        _ => unreachable!("unexpected literal rule: {:?}", inner.as_rule()),
    };

    process_literal(&raw_literal, span, writer)
}

/// Parse a string literal, extracting content, raw flag, and quote style
///
/// **CEL-RESTRICTED**: Escape sequences are NOT processed here.
/// They will be processed during value construction.
fn parse_string_literal(s: &str) -> (&str, bool, QuoteStyle) {
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

    (content, is_raw, quote_style)
}

/// Build an expression list
fn build_expr_list<W: CelWriter>(
    depth_left: usize,
    pair: pest::iterators::Pair<'_, Rule>,
    writer: &mut W,
) -> Result<Vec<W::Expr>> {
    pair.into_inner()
        .map(|p| build_expr(depth_left, p, writer))
        .collect()
}

/// Build map initializers
fn build_map_inits<W: CelWriter>(
    depth_left: usize,
    pair: pest::iterators::Pair<'_, Rule>,
    writer: &mut W,
) -> Result<Vec<(W::Expr, W::Expr)>> {
    let mut inner = pair.into_inner();
    let mut entries = Vec::new();

    while let Some(key) = inner.next() {
        let value = inner
            .next()
            .expect("Parser validated: map_inits = { expr ~ \":\" ~ expr ~ ... }");
        entries.push((
            build_expr(depth_left, key, writer)?,
            build_expr(depth_left, value, writer)?,
        ));
    }

    Ok(entries)
}

/// Extract span from a pest Pair
fn span_from_pair(pair: &Pair<Rule>) -> Span {
    let span = pair.as_span();
    Span::new(span.start(), span.end())
}

/// Apply a unary operator multiple times
fn apply_unary_repeated<W: CelWriter>(
    writer: &mut W,
    op: UnaryOp,
    count: usize,
    mut expr: W::Expr,
    base_span: Span,
) -> Result<W::Expr> {
    for _ in 0..count {
        expr = writer
            .unary(op, expr, base_span)
            .map_err(|e| map_writer_error(e, base_span))?;
    }
    Ok(expr)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cel::ast::ExprKind;
    use crate::cel::parser::ParseConfig;
    use crate::cel::test_util::TestContext;

    // Test helper that uses TestContext
    fn build_ast(input: &str) -> Result<TestContext> {
        let mut ctx = TestContext::new(ParseConfig::default());
        ctx.parse(input)?;
        Ok(ctx)
    }

    macro_rules! test_cases {
        ($($name:ident: $input:expr => |$ctx:ident| $check:block),* $(,)?) => {
            $(
                #[test]
                fn $name() {
                    let $ctx = build_ast($input).unwrap();
                    $check
                }
            )*
        };
    }

    // ============================================================
    // Section: AST Construction Tests
    // ============================================================

    test_cases! {
        test_build_ast_literal_int: "42" => |ctx| {
            let ast = ctx.ast().unwrap();
            match ast.kind {
                ExprKind::Literal(Literal::Int(val)) => assert_eq!(val, 42),
                _ => panic!("expected int literal"),
            }
        },

        test_build_ast_literal_string: r#""hello""# => |ctx| {
            let ast = ctx.ast().unwrap();
            match ast.kind {
                ExprKind::Literal(Literal::String(content)) => {
                    assert_eq!(ctx.resolve(&content).unwrap(), "hello");
                }
                _ => panic!("expected string literal"),
            }
        },

        test_build_ast_binary_add: "1 + 2" => |ctx| {
            let ast = ctx.ast().unwrap();
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

        test_build_ast_ternary: "true ? 1 : 2" => |ctx| {
            let ast = ctx.ast().unwrap();
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

        test_build_ast_identifier: "foo" => |ctx| {
            let ast = ctx.ast().unwrap();
            match ast.kind {
                ExprKind::Ident(name) => assert_eq!(ctx.resolve(&name).unwrap(), "foo"),
                _ => panic!("expected identifier"),
            }
        },

        test_build_ast_list: "[1, 2, 3]" => |ctx| {
            let ast = ctx.ast().unwrap();
            match ast.kind {
                ExprKind::List(items) => {
                    assert_eq!(items.len(), 3);
                }
                _ => panic!("expected list"),
            }
        },
    }
}
