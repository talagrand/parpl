//! Seed corpus definitions for fuzz targets.
//!
//! These seeds are the source of truth for fuzzing starting points.
//! The `generate-seeds` binary writes these to `corpus/` directories
//! where libFuzzer picks them up.

/// CEL expression seeds covering grammar constructs and edge cases.
#[rustfmt::skip]
pub const CEL_SEEDS: &[(&str, &str)] = &[
    // Empty collections (edge cases that previously caused panics)
    ("empty_list", "[]"),
    ("empty_map", "{}"),

    // Literals
    ("bool_true", "true"),
    ("bool_false", "false"),
    ("null_literal", "null"),
    ("int_literal", "42"),
    ("float_literal", "3.14"),
    ("string_literal", r#""hello""#),

    // Operators
    ("binary_op", "a + b"),
    ("unary_op", "!x"),
    ("ternary", "x ? y : z"),
    ("logical_ops", "a && b || c"),
    ("comparison", "a == b != c"),
    ("in_operator", "a in b"),

    // Expressions
    ("function_call", "foo(1, 2)"),
    ("member_access", "x.y.z"),
    ("index_access", "a[0]"),
    ("parenthesized", "(a + b) * c"),
    ("list_with_items", "[1, 2, 3]"),
    ("map_with_items", r#"{"a": 1}"#),

    // Message literals
    ("ident_struct", "Foo{}"),
    ("leading_dot_struct", ".Foo{}"),
    ("struct_with_fields", "Foo{a: 1, b: 2}"),
    ("reserved_struct", "for{}"),
    ("qualified_struct", "for.Type{}"),
];

/// Scheme datum seeds covering grammar constructs and edge cases.
#[rustfmt::skip]
pub const SCHEME_SEEDS: &[(&str, &str)] = &[
    // Empty forms
    ("empty_list", "()"),
    ("empty_vector", "#()"),

    // Literals
    ("bool_true", "#t"),
    ("bool_false", "#f"),
    ("integer", "42"),
    ("negative", "-17"),
    ("float", "3.14"),
    ("rational", "1/2"),
    ("complex", "1+2i"),
    ("char", r#"#\a"#),
    ("char_newline", r#"#\newline"#),

    // Strings
    ("simple_string", r#""hello""#),
    ("string_escape", r#""a\nb""#),
    ("empty_string", r#""""#),

    // Symbols
    ("symbol", "foo"),
    ("quoted_symbol", "'foo"),
    ("dotted_pair", "(a . b)"),

    // Lists
    ("simple_list", "(1 2 3)"),
    ("nested_list", "((a b) (c d))"),
    ("improper_list", "(a b . c)"),

    // Special forms
    ("quasiquote", "`(a ,b ,@c)"),
    ("define", "(define x 42)"),
    ("lambda", "(lambda (x) x)"),
    ("if_expr", "(if #t 1 2)"),

    // Vectors
    ("vector", "#(1 2 3)"),
    ("bytevector", "#u8(1 2 3)"),

    // Comments
    ("line_comment", "; comment\n42"),
    ("block_comment", "#| comment |# 42"),
    ("datum_comment", "#;ignored 42"),

    // Edge cases
    ("whitespace_only", "   \n\t  "),
    ("multiple_datums", "1 2 3"),
];
