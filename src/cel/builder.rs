// Builder - converts pest parse tree to user's representation
//
// This module transforms pest's `Pairs` into the user's representation
// by calling `CelWriter` trait methods. Users control what gets built.
//
// Processing during construction:
// - Escape sequences: processed immediately via literal::process_literal
// - Numeric parsing: validated and parsed immediately
// - Identifier resolution: handled during evaluation

use crate::{
    Error, Interner, Span,
    cel::{
        Result,
        literal::{RawLiteral, process_literal},
        parser::Rule,
        traits::{BinaryOp, CelWriter, Literal, QuoteStyle, UnaryOp},
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
fn check_depth(depth_left: u32) -> Result<u32> {
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
    max_ast_depth: u32,
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
    depth_left: u32,
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
    depth_left: u32,
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
    depth_left: u32,
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
    depth_left: u32,
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
    depth_left: u32,
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
        // op_pair is a relop rule
        let op_str = op_pair.as_str();
        let op = match op_str {
            "<" => BinaryOp::Less,
            "<=" => BinaryOp::LessEq,
            ">" => BinaryOp::Greater,
            ">=" => BinaryOp::GreaterEq,
            "==" => BinaryOp::Equals,
            "!=" => BinaryOp::NotEquals,
            "in" => BinaryOp::In,
            _ => unreachable!("unexpected relop: {}", op_str),
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
/// CEL Spec: addition = { multiplication ~ (add_op ~ multiplication)* }
fn build_addition<W: CelWriter>(
    depth_left: u32,
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

    // Process (add_op ~ multiplication) pairs
    while let Some(op_pair) = inner.next() {
        debug_assert_eq!(op_pair.as_rule(), Rule::add_op, "Expected add_op");
        let op = match op_pair.as_str() {
            "+" => BinaryOp::Add,
            "-" => BinaryOp::Subtract,
            _ => unreachable!("Parser validated: add_op = {{ \"+\" | \"-\" }}"),
        };
        let right = build_multiplication(
            depth_left,
            inner
                .next()
                .expect("Parser validated: addition = { ... ~ (add_op ~ multiplication)* }"),
            writer,
        )?;
        left = writer
            .binary(op, left, right, span)
            .map_err(|e| map_writer_error(e, span))?;
    }

    Ok(left)
}

/// Build multiplication/division/modulo expression
/// CEL Spec: multiplication = { unary ~ (mul_op ~ unary)* }
fn build_multiplication<W: CelWriter>(
    depth_left: u32,
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

    // Process (mul_op ~ unary) pairs
    while let Some(op_pair) = inner.next() {
        debug_assert_eq!(op_pair.as_rule(), Rule::mul_op, "Expected mul_op");
        let op = match op_pair.as_str() {
            "*" => BinaryOp::Multiply,
            "/" => BinaryOp::Divide,
            "%" => BinaryOp::Modulo,
            _ => unreachable!("Parser validated: mul_op = {{ \"*\" | \"/\" | \"%\" }}"),
        };
        let right = build_unary(
            depth_left,
            inner
                .next()
                .expect("Parser validated: multiplication = { ... ~ (mul_op ~ unary)* }"),
            writer,
        )?;
        left = writer
            .binary(op, left, right, span)
            .map_err(|e| map_writer_error(e, span))?;
    }

    Ok(left)
}

/// Build unary expression
/// CEL Spec: unary = { not_unary | neg_unary | member }
fn build_unary<W: CelWriter>(
    depth_left: u32,
    pair: pest::iterators::Pair<'_, Rule>,
    writer: &mut W,
) -> Result<W::Expr> {
    let depth_left = check_depth(depth_left)?;
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();
    let first = inner
        .next()
        .expect("Parser validated: unary = { not_unary | neg_unary | member }");

    match first.as_rule() {
        Rule::not_unary => {
            // not_unary = ${ "!"+ ~ member }
            // Use pair text to count leading ! characters
            let text = first.as_str();
            let count = text.chars().take_while(|&c| c == '!').count();
            let member = first
                .into_inner()
                .next()
                .expect("Parser validated: not_unary = { \"!\"+ ~ member }");
            let operand = build_member(depth_left, member, writer)?;
            // Apply NOT count times (!! cancels out)
            apply_unary_repeated(writer, UnaryOp::Not, count, operand, span)
        }
        Rule::neg_unary => {
            // neg_unary = ${ "-"+ ~ member }
            // Use pair text to count leading - characters
            let text = first.as_str();
            let count = text.chars().take_while(|&c| c == '-').count();
            let member = first
                .into_inner()
                .next()
                .expect("Parser validated: neg_unary = { \"-\"+ ~ member }");
            let operand = build_member(depth_left, member, writer)?;
            // Apply Negate count times (-- cancels out)
            apply_unary_repeated(writer, UnaryOp::Negate, count, operand, span)
        }
        Rule::member => build_member(depth_left, first, writer),
        _ => unreachable!(
            "Parser validated: unary contains not_unary, neg_unary, or member, got {:?}",
            first.as_rule()
        ),
    }
}

/// Build member access/indexing expression
/// CEL Spec: member = { primary ~ ("." ~ selector ~ ("(" ~ expr_list? ~ ")")? | "[" ~ expr ~ "]")* }
fn build_member<W: CelWriter>(
    depth_left: u32,
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
            .expect("Parser validated: member = { primary ~ member_suffix* }"),
        writer,
    )?;

    // Process member_suffix rules (field_access or index_access)
    for suffix in inner {
        debug_assert_eq!(
            suffix.as_rule(),
            Rule::member_suffix,
            "Expected member_suffix"
        );
        let suffix_inner = suffix
            .into_inner()
            .next()
            .expect("Parser validated: member_suffix = { field_access | index_access }");

        match suffix_inner.as_rule() {
            Rule::field_access => {
                // field_access = { "." ~ selector ~ call_suffix? }
                let mut fa_inner = suffix_inner.into_inner();
                let selector = fa_inner
                    .next()
                    .expect("Parser validated: field_access = { \".\" ~ selector ~ ... }");
                let field_name = writer.interner().intern(selector.as_str());

                // Check for call_suffix (method call with arguments)
                if let Some(call_suffix) = fa_inner.next() {
                    debug_assert_eq!(
                        call_suffix.as_rule(),
                        Rule::call_suffix,
                        "Expected call_suffix"
                    );
                    let args = build_call_suffix_args(depth_left, call_suffix, writer)?;
                    expr = writer
                        .member(expr, field_name, Some(&args), span)
                        .map_err(|e| map_writer_error(e, span))?;
                } else {
                    // Field access without call
                    expr = writer
                        .member(expr, field_name, None, span)
                        .map_err(|e| map_writer_error(e, span))?;
                }
            }
            Rule::index_access => {
                // index_access = { "[" ~ expr ~ "]" }
                let index_expr = suffix_inner
                    .into_inner()
                    .next()
                    .expect("Parser validated: index_access = { \"[\" ~ expr ~ \"]\" }");
                let index = build_expr(depth_left, index_expr, writer)?;
                expr = writer
                    .index(expr, index, span)
                    .map_err(|e| map_writer_error(e, span))?;
            }
            _ => unreachable!(
                "Parser validated: member_suffix contains field_access or index_access, got {:?}",
                suffix_inner.as_rule()
            ),
        }
    }

    Ok(expr)
}

/// Extract arguments from a call_suffix rule
fn build_call_suffix_args<W: CelWriter>(
    depth_left: u32,
    call_suffix: pest::iterators::Pair<'_, Rule>,
    writer: &mut W,
) -> Result<Vec<W::Expr>> {
    // call_suffix = { "(" ~ expr_list? ~ ")" }
    let mut cs_inner = call_suffix.into_inner();
    if let Some(expr_list) = cs_inner.next() {
        debug_assert_eq!(expr_list.as_rule(), Rule::expr_list, "Expected expr_list");
        build_expr_list(depth_left, expr_list, writer)
    } else {
        Ok(Vec::new())
    }
}

/// Build primary expression (bottom of precedence chain)
/// CEL Spec: primary = { literal | message_literal | ident_or_call | paren_expr | list_literal | map_literal }
fn build_primary<W: CelWriter>(
    depth_left: u32,
    pair: pest::iterators::Pair<'_, Rule>,
    writer: &mut W,
) -> Result<W::Expr> {
    let depth_left = check_depth(depth_left)?;
    let span = span_from_pair(&pair);
    let mut inner = pair.into_inner();

    let first = inner
        .next()
        .expect("Parser validated: primary has at least one child rule");

    match first.as_rule() {
        Rule::literal => {
            let lit = process_literal_pair(first, writer)?;
            writer
                .literal(lit, span)
                .map_err(|e| map_writer_error(e, span))
        }
        Rule::message_literal => {
            // message_literal = { "."? ~ selector ~ ("." ~ selector)* ~ "{" ~ field_inits? ~ ","? ~ "}" }
            build_message_literal_rule(depth_left, first, span, writer)
        }
        Rule::ident_or_call => {
            // ident_or_call = { "."? ~ ident ~ call_suffix? }
            build_ident_or_call(depth_left, first, span, writer)
        }
        Rule::paren_expr => {
            // paren_expr = { "(" ~ expr ~ ")" }
            let expr_pair = first
                .into_inner()
                .next()
                .expect("Parser validated: paren_expr = { \"(\" ~ expr ~ \")\" }");
            build_expr(depth_left, expr_pair, writer)
        }
        Rule::list_literal => {
            // list_literal = { "[" ~ expr_list? ~ ","? ~ "]" }
            let mut ll_inner = first.into_inner();
            if let Some(expr_list) = ll_inner.next() {
                debug_assert_eq!(expr_list.as_rule(), Rule::expr_list, "Expected expr_list");
                let items = build_expr_list(depth_left, expr_list, writer)?;
                writer
                    .list(&items, span)
                    .map_err(|e| map_writer_error(e, span))
            } else {
                // Empty list
                writer
                    .list(&[], span)
                    .map_err(|e| map_writer_error(e, span))
            }
        }
        Rule::map_literal => {
            // map_literal = { "{" ~ map_inits? ~ ","? ~ "}" }
            let mut ml_inner = first.into_inner();
            if let Some(map_inits) = ml_inner.next() {
                debug_assert_eq!(map_inits.as_rule(), Rule::map_inits, "Expected map_inits");
                let entries = build_map_inits(depth_left, map_inits, writer)?;
                writer
                    .map(&entries, span)
                    .map_err(|e| map_writer_error(e, span))
            } else {
                // Empty map
                writer.map(&[], span).map_err(|e| map_writer_error(e, span))
            }
        }
        _ => unreachable!(
            "Parser validated: primary contains one of the expected rules, got {:?}",
            first.as_rule()
        ),
    }
}

/// Build ident_or_call: identifier or function call with optional leading dot
fn build_ident_or_call<W: CelWriter>(
    depth_left: u32,
    pair: pest::iterators::Pair<'_, Rule>,
    span: Span,
    writer: &mut W,
) -> Result<W::Expr> {
    // ident_or_call = { "."? ~ ident ~ call_suffix? }
    // CEL Spec: Leading dot (.) forces absolute/root scope resolution, bypassing
    // container prefixes and comprehension iteration variables. We preserve it
    // in the identifier name per cel-go's approach (e.g., ".y" not "y").
    let has_leading_dot = pair.as_str().starts_with('.');
    let mut inner = pair.into_inner();
    let ident = inner
        .next()
        .expect("Parser validated: ident_or_call = { \".\"? ~ ident ~ ... }");
    let name = if has_leading_dot {
        let dotted_name = format!(".{}", ident.as_str());
        writer.interner().intern(&dotted_name)
    } else {
        writer.interner().intern(ident.as_str())
    };

    if let Some(call_suffix) = inner.next() {
        // Function call
        debug_assert_eq!(
            call_suffix.as_rule(),
            Rule::call_suffix,
            "Expected call_suffix"
        );
        let args = build_call_suffix_args(depth_left, call_suffix, writer)?;
        writer
            .call(None, name, &args, span)
            .map_err(|e| map_writer_error(e, span))
    } else {
        // Plain identifier
        writer
            .ident(name, span)
            .map_err(|e| map_writer_error(e, span))
    }
}

/// Build message_literal from Rule::message_literal pair
fn build_message_literal_rule<W: CelWriter>(
    depth_left: u32,
    pair: pest::iterators::Pair<'_, Rule>,
    span: Span,
    writer: &mut W,
) -> Result<W::Expr> {
    // message_literal = { "."? ~ selector ~ ("." ~ selector)* ~ "{" ~ field_inits? ~ ","? ~ "}" }
    // CEL Spec: Leading dot (.) forces absolute/root scope resolution, bypassing
    // container prefixes. We preserve it in the first type part per cel-go's approach.
    let has_leading_dot = pair.as_str().starts_with('.');
    let mut inner = pair.into_inner();

    // Collect type name parts (selectors)
    let mut type_parts = Vec::new();
    let mut is_first = true;
    for part in inner.by_ref() {
        if part.as_rule() == Rule::selector {
            let name = if is_first && has_leading_dot {
                let dotted_name = format!(".{}", part.as_str());
                writer.interner().intern(&dotted_name)
            } else {
                writer.interner().intern(part.as_str())
            };
            type_parts.push(name);
            is_first = false;
        } else if part.as_rule() == Rule::field_inits {
            // Process field initializers
            let mut values = Vec::new();
            let mut field_inner = part.into_inner();
            // field_inits = { selector ~ ":" ~ expr ~ ("," ~ selector ~ ":" ~ expr)* }
            while let Some(field_name_pair) = field_inner.next() {
                let field_name = writer.interner().intern(field_name_pair.as_str());
                let field_value_pair = field_inner
                    .next()
                    .expect("Parser validated: field_inits = { selector ~ \":\" ~ expr ~ ... }");
                let field_value = build_expr(depth_left, field_value_pair, writer)?;
                values.push((field_name, field_value));
            }
            return writer
                .structure(None, &type_parts, &values, span)
                .map_err(|e| map_writer_error(e, span));
        }
    }

    // No field_inits found - empty message literal
    writer
        .structure(None, &type_parts, &[], span)
        .map_err(|e| map_writer_error(e, span))
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
    depth_left: u32,
    pair: pest::iterators::Pair<'_, Rule>,
    writer: &mut W,
) -> Result<Vec<W::Expr>> {
    pair.into_inner()
        .map(|p| build_expr(depth_left, p, writer))
        .collect()
}

/// Build map initializers
fn build_map_inits<W: CelWriter>(
    depth_left: u32,
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
    use crate::cel::{
        CelParser,
        context::Builder,
        parser::ParseConfig,
        reference::arena::{ArenaCelWriter, Expr, ExprKind},
    };
    use crate::{Interner, StringPool, StringPoolId};
    use bumpalo::Bump;

    /// Simple error type for test failures.
    #[derive(Debug)]
    struct TestError(String);

    impl std::fmt::Display for TestError {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "{}", self.0)
        }
    }

    impl std::error::Error for TestError {}

    /// Test context that bundles arena, interner, and parser for convenient test setup.
    struct TestContext {
        arena: Bump,
        interner: StringPool,
        parser: CelParser,
        ast: Option<&'static Expr<'static>>,
    }

    impl TestContext {
        fn new(config: ParseConfig) -> Self {
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

        fn parse(&mut self, input: &str) -> Result<()> {
            self.arena.reset();
            self.ast = None;

            // Unsafe lifetime extension for test convenience.
            // Safe because TestContext owns the arena and outlives the AST reference.
            let arena_ref: &'static Bump = unsafe { std::mem::transmute(&self.arena) };
            let mut writer = ArenaCelWriter::new(arena_ref, &mut self.interner);

            let ast = self.parser.parse(input, &mut writer)?;
            self.ast = Some(ast);
            Ok(())
        }

        fn ast(&self) -> Result<&'static Expr<'static>> {
            self.ast.ok_or_else(|| crate::Error::WriterError {
                span: crate::Span::new(0, 0),
                source: Box::new(TestError("No AST".into())),
            })
        }

        fn resolve<'a>(&'a self, id: &'a StringPoolId) -> Option<&'a str> {
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
    // Note: Most test coverage is derived from the CEL integration test
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

        test_build_ast_empty_list: "[]" => |ctx| {
            let ast = ctx.ast().unwrap();
            match ast.kind {
                ExprKind::List(items) => {
                    assert_eq!(items.len(), 0);
                }
                _ => panic!("expected empty list"),
            }
        },

        test_build_ast_empty_map: "{}" => |ctx| {
            let ast = ctx.ast().unwrap();
            match ast.kind {
                ExprKind::Map(entries) => {
                    assert_eq!(entries.len(), 0);
                }
                _ => panic!("expected empty map"),
            }
        },

        test_build_ast_reserved_word_struct: "for{}" => |ctx| {
            // Reserved words can be used as selectors in message literals
            // since they're not valid idents, the message literal rule is used
            let ast = ctx.ast().unwrap();
            match ast.kind {
                ExprKind::Struct(_, type_parts, values) => {
                    assert_eq!(type_parts.len(), 1);
                    assert_eq!(ctx.resolve(&type_parts[0]).unwrap(), "for");
                    assert_eq!(values.len(), 0);
                }
                _ => panic!("expected struct with reserved word type, got {:?}", ast.kind),
            }
        },

        test_build_ast_qualified_struct: "for.Type{}" => |ctx| {
            // Qualified message literal with reserved word prefix
            let ast = ctx.ast().unwrap();
            match ast.kind {
                ExprKind::Struct(_, type_parts, values) => {
                    assert_eq!(type_parts.len(), 2);
                    assert_eq!(ctx.resolve(&type_parts[0]).unwrap(), "for");
                    assert_eq!(ctx.resolve(&type_parts[1]).unwrap(), "Type");
                    assert_eq!(values.len(), 0);
                }
                _ => panic!("expected qualified struct, got {:?}", ast.kind),
            }
        },

        test_build_ast_ident_struct: "Foo{}" => |ctx| {
            // Message literal with normal identifier (not reserved word)
            // This tests that PEG ordering works correctly
            let ast = ctx.ast().unwrap();
            match ast.kind {
                ExprKind::Struct(_, type_parts, values) => {
                    assert_eq!(type_parts.len(), 1);
                    assert_eq!(ctx.resolve(&type_parts[0]).unwrap(), "Foo");
                    assert_eq!(values.len(), 0);
                }
                _ => panic!("expected struct Foo{{}}, got {:?}", ast.kind),
            }
        },

        test_build_ast_leading_dot_struct: ".Foo{}" => |ctx| {
            // Message literal with leading dot (preserved for absolute scope resolution)
            let ast = ctx.ast().unwrap();
            match ast.kind {
                ExprKind::Struct(_, type_parts, values) => {
                    assert_eq!(type_parts.len(), 1);
                    assert_eq!(ctx.resolve(&type_parts[0]).unwrap(), ".Foo");
                    assert_eq!(values.len(), 0);
                }
                _ => panic!("expected struct .Foo{{}}, got {:?}", ast.kind),
            }
        },
    }
}
