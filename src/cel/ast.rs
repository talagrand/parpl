// AST (Abstract Syntax Tree) for CEL expressions
//
// This module defines the AST types that represent parsed CEL expressions.
// The AST is constructed from pest's parse tree and includes:
// - All expression types from the CEL grammar
// - Span information for error reporting
// - Deferred processing (escape sequences handled during value construction)
// - Arena allocation for efficient memory management

pub use crate::common::Span;
use crate::common::StringPoolId;
use std::fmt;

/// A complete CEL expression (the root of the AST)
///
/// **Arena-allocated**: All `Expr` nodes are allocated in a `bumpalo::Bump` arena.
/// The lifetime `'arena` ties the expression to the arena that owns it.
#[derive(Debug, Clone, PartialEq)]
pub struct Expr<'arena> {
    pub kind: ExprKind<'arena>,
    pub span: Span,
}

/// The kind of expression (CEL spec lines 68-94)
///
/// **Arena-allocated**: Uses `&'arena Expr<'arena>` instead of `Box<Expr>`.
#[derive(Debug, Clone, PartialEq)]
pub enum ExprKind<'arena> {
    /// Ternary conditional: `condition ? true_expr : false_expr`
    /// CEL Spec (line 68): Expr = ConditionalOr ["?" ConditionalOr ":" Expr]
    Ternary(
        &'arena Expr<'arena>,
        &'arena Expr<'arena>,
        &'arena Expr<'arena>,
    ),

    /// Binary operation: left op right
    /// Covers: ||, &&, <, <=, >=, >, ==, !=, in, +, -, *, /, %
    Binary(BinaryOp, &'arena Expr<'arena>, &'arena Expr<'arena>),

    /// Unary operation: op expr
    /// Covers: !, - (with repetition like !! or --)
    Unary(UnaryOp, &'arena Expr<'arena>),

    /// Member access: expr.field or expr.method(args)
    /// CEL Spec (line 79): Member "." SELECTOR \["(" \[ExprList\] ")"\]
    Member(
        &'arena Expr<'arena>,
        StringPoolId,
        Option<&'arena [Expr<'arena>]>,
    ),

    /// Index access: expr\[index\]
    /// CEL Spec (line 79): Member "\[" Expr "\]"
    Index(&'arena Expr<'arena>, &'arena Expr<'arena>),

    /// Function call: func(args) or .func(args)
    /// CEL Spec (line 83): \["."\] IDENT "(" \[ExprList\] ")"
    Call(
        Option<&'arena Expr<'arena>>,
        StringPoolId,
        &'arena [Expr<'arena>],
    ),

    /// Identifier reference
    /// CEL Spec (line 83): IDENT
    Ident(StringPoolId),

    /// List literal: \[expr, ...\]
    /// CEL Spec (line 86): "\[" \[ExprList\] "\]"
    List(&'arena [Expr<'arena>]),

    /// Map literal: {key: value, ...}
    /// CEL Spec (line 87): "{" \[MapInits\] "}"
    Map(&'arena [(Expr<'arena>, Expr<'arena>)]),

    /// Message/struct literal: Type{field: value, ...} or .Type{...}
    /// CEL Spec (line 88): \["."\] SELECTOR {"." SELECTOR} "{" \[FieldInits\] "}"
    Struct(
        Option<&'arena Expr<'arena>>,
        &'arena [StringPoolId],
        &'arena [(StringPoolId, Expr<'arena>)],
    ),

    /// Literal value (processed and validated)
    Literal(Literal<StringPoolId, &'arena [u8]>),
}

/// Raw literal from the parser (unparsed strings)
///
/// This represents the literal as it appears in the source code, before any
/// processing or validation. The ast_builder converts these to `Literal` nodes.
#[derive(Debug, Clone, PartialEq)]
pub enum RawLiteral<S> {
    /// Integer literal: "123", "0xFF", "-456"
    /// CEL Spec (line 145): INT_LIT ::= -? DIGIT+ | -? 0x HEXDIGIT+
    Int(S),

    /// Unsigned integer literal: "123", "0xFF" (without 'u' suffix)
    /// CEL Spec (line 146): UINT_LIT ::= INT_LIT [uU]
    UInt(S),

    /// Floating-point literal: "3.14", "1e10", ".5"
    /// CEL Spec (line 147): FLOAT_LIT
    Float(S),

    /// String literal: raw content between quotes
    /// CEL Spec (lines 149-153): STRING_LIT
    /// Stores: (content, is_raw, quote_style)
    /// - content: the text between quotes (without the quotes themselves)
    /// - is_raw: true if prefixed with r/R (no escape processing needed)
    /// - quote_style: which quote delimiters were used
    String(S, bool, QuoteStyle),

    /// Bytes literal: raw content between quotes
    /// CEL Spec (line 154): BYTES_LIT = [bB] STRING_LIT
    /// Stores: (content, is_raw, quote_style)
    Bytes(S, bool, QuoteStyle),

    /// Boolean literal: true, false
    /// CEL Spec (line 160): BOOL_LIT
    /// Already processed by parser
    Bool(bool),

    /// Null literal: null
    /// CEL Spec (line 161): NULL_LIT
    /// Already processed by parser
    Null,
}

/// Binary operators (in precedence order from spec)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOp {
    // Logical (lowest precedence)
    /// Logical OR: ||
    LogicalOr,
    /// Logical AND: &&
    LogicalAnd,

    // Relational
    /// Less than: <
    Less,
    /// Less than or equal: <=
    LessEq,
    /// Greater than: >
    Greater,
    /// Greater than or equal: >=
    GreaterEq,
    /// Equal: ==
    Equals,
    /// Not equal: !=
    NotEquals,
    /// In: in
    In,

    // Arithmetic
    /// Addition: +
    Add,
    /// Subtraction: -
    Subtract,
    /// Multiplication: *
    Multiply,
    /// Division: /
    Divide,
    /// Modulo: %
    Modulo,
}

impl fmt::Display for BinaryOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            BinaryOp::LogicalOr => "||",
            BinaryOp::LogicalAnd => "&&",
            BinaryOp::Less => "<",
            BinaryOp::LessEq => "<=",
            BinaryOp::Greater => ">",
            BinaryOp::GreaterEq => ">=",
            BinaryOp::Equals => "==",
            BinaryOp::NotEquals => "!=",
            BinaryOp::In => "in",
            BinaryOp::Add => "+",
            BinaryOp::Subtract => "-",
            BinaryOp::Multiply => "*",
            BinaryOp::Divide => "/",
            BinaryOp::Modulo => "%",
        };
        write!(f, "{}", s)
    }
}

/// Unary operators
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    /// Logical NOT: !
    /// Can be repeated: !! expr = expr
    Not,
    /// Arithmetic negation: -
    /// Can be repeated: -- expr = expr
    Negate,
}

impl fmt::Display for UnaryOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            UnaryOp::Not => "!",
            UnaryOp::Negate => "-",
        };
        write!(f, "{}", s)
    }
}

/// Processed literal values (validated and ready for evaluation)
///
/// All numeric values are parsed, all escape sequences are processed.
/// **Arena-allocated**: String data stored as `&'arena str` instead of `String`.
#[derive(Debug, Clone, PartialEq)]
pub enum Literal<S, B> {
    /// Integer literal: parsed i64 value
    /// CEL Spec (line 143): INT_LIT = -? DIGIT+ | -? 0x HEXDIGIT+
    /// Range: i64::MIN to i64::MAX
    Int(i64),

    /// Unsigned integer literal: parsed u64 value
    /// CEL Spec (line 144): UINT_LIT = INT_LIT [uU]
    /// Range: 0 to u64::MAX
    UInt(u64),

    /// Floating-point literal: parsed f64 value
    /// CEL Spec (line 145): FLOAT_LIT
    /// IEEE 754 double-precision
    Float(f64),

    /// String literal: processed with escape sequences resolved
    /// CEL Spec (lines 149-153): STRING_LIT
    /// All escape sequences (\n, \t, \xHH, \uHHHH, \UHHHHHHHH, octal) are processed
    String(S),

    /// Bytes literal: processed with escape sequences resolved
    /// CEL Spec (line 154): BYTES_LIT = [bB] STRING_LIT
    /// Octal and \xHH escapes represent byte values, Unicode escapes produce UTF-8
    /// **IMPORTANT**: Bytes are arbitrary octet sequences, may not be valid UTF-8!
    Bytes(B),

    /// Boolean literal: true, false
    /// CEL Spec (line 160): BOOL_LIT
    Bool(bool),

    /// Null literal: null
    /// CEL Spec (line 161): NULL_LIT
    Null,
}

/// Quote style for string/bytes literals
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QuoteStyle {
    /// Single quotes: 'text'
    SingleQuote,
    /// Double quotes: "text"
    DoubleQuote,
    /// Triple single quotes: '''text'''
    TripleSingleQuote,
    /// Triple double quotes: """text"""
    TripleDoubleQuote,
}

impl<'arena> Expr<'arena> {
    pub fn new(kind: ExprKind<'arena>, span: Span) -> Self {
        Self { kind, span }
    }
}
