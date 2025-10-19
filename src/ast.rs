// AST (Abstract Syntax Tree) for CEL expressions
//
// This module defines the AST types that represent parsed CEL expressions.
// The AST is constructed from pest's parse tree and includes:
// - All expression types from the CEL grammar
// - Span information for error reporting
// - Deferred processing (escape sequences handled during value construction)

use std::fmt;

/// A complete CEL expression (the root of the AST)
#[derive(Debug, Clone, PartialEq)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

/// Source location information for error reporting
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }

    pub fn combine(&self, other: &Span) -> Span {
        Span {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }
}

/// The kind of expression (CEL spec lines 68-94)
#[derive(Debug, Clone, PartialEq)]
pub enum ExprKind {
    /// Ternary conditional: `condition ? true_expr : false_expr`
    /// CEL Spec (line 68): Expr = ConditionalOr ["?" ConditionalOr ":" Expr]
    Ternary(Box<Expr>, Box<Expr>, Box<Expr>),

    /// Binary operation: left op right
    /// Covers: ||, &&, <, <=, >=, >, ==, !=, in, +, -, *, /, %
    Binary(BinaryOp, Box<Expr>, Box<Expr>),

    /// Unary operation: op expr
    /// Covers: !, - (with repetition like !! or --)
    Unary(UnaryOp, Box<Expr>),

    /// Member access: expr.field or expr.method(args)
    /// CEL Spec (line 79): Member "." SELECTOR ["(" [ExprList] ")"]
    Member(Box<Expr>, String, Option<Vec<Expr>>),

    /// Index access: expr[index]
    /// CEL Spec (line 79): Member "[" Expr "]"
    Index(Box<Expr>, Box<Expr>),

    /// Function call: func(args) or .func(args)
    /// CEL Spec (line 83): ["."] IDENT "(" [ExprList] ")"
    Call(Option<Box<Expr>>, String, Vec<Expr>),

    /// Identifier reference
    /// CEL Spec (line 83): IDENT
    Ident(String),

    /// List literal: [expr, ...]
    /// CEL Spec (line 86): "[" [ExprList] "]"
    List(Vec<Expr>),

    /// Map literal: {key: value, ...}
    /// CEL Spec (line 87): "{" [MapInits] "}"
    Map(Vec<(Expr, Expr)>),

    /// Message/struct literal: Type{field: value, ...} or .Type{...}
    /// CEL Spec (line 88): ["."] SELECTOR {"." SELECTOR} "{" [FieldInits] "}"
    Struct(Option<Box<Expr>>, Vec<String>, Vec<(String, Expr)>),

    /// Literal value
    Literal(Literal),
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

/// Literal values (CEL spec lines 141-161)
#[derive(Debug, Clone, PartialEq)]
pub enum Literal {
    /// Integer literal: 123, -456, 0xFF
    /// CEL Spec (line 143): INT_LIT = -? DIGIT+ | -? 0x HEXDIGIT+
    /// Raw string from parser - parsing happens during value construction
    Int(String),

    /// Unsigned integer literal: 123u, 0xFFu
    /// CEL Spec (line 144): UINT_LIT = INT_LIT [uU]
    /// Raw string from parser (without 'u' suffix) - parsing happens during value construction
    UInt(String),

    /// Floating-point literal: 1.5, 1e10, -3.14e-2
    /// CEL Spec (line 145): FLOAT_LIT
    /// Raw string from parser - parsing happens during value construction
    Float(String),

    /// String literal: "hello", 'world', """multiline""", r"raw\n"
    /// CEL Spec (lines 149-153): STRING_LIT
    /// **CEL-RESTRICTED**: Escape sequences processed during value construction
    /// Stores: (raw_content, is_raw, quote_style)
    /// - raw_content: the content between quotes (without quotes)
    /// - is_raw: true if prefixed with r/R (no escape processing)
    /// - quote_style: SingleQuote, DoubleQuote, TripleSingleQuote, TripleDoubleQuote
    String(String, bool, QuoteStyle),

    /// Bytes literal: b"hello", b'bytes', b"""multi"""
    /// CEL Spec (line 154): BYTES_LIT = [bB] STRING_LIT
    /// **CEL-RESTRICTED**: Escape sequences processed during value construction
    /// Stores: (raw_content, is_raw, quote_style)
    Bytes(String, bool, QuoteStyle),

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

impl Expr {
    pub fn new(kind: ExprKind, span: Span) -> Self {
        Self { kind, span }
    }

    /// Create a literal expression
    pub fn literal(lit: Literal, span: Span) -> Self {
        Self::new(ExprKind::Literal(lit), span)
    }

    /// Create an identifier expression
    pub fn ident(name: String, span: Span) -> Self {
        Self::new(ExprKind::Ident(name), span)
    }

    /// Create a binary operation
    pub fn binary(op: BinaryOp, left: Expr, right: Expr) -> Self {
        let span = left.span.combine(&right.span);
        Self::new(ExprKind::Binary(op, Box::new(left), Box::new(right)), span)
    }

    /// Create a unary operation
    pub fn unary(op: UnaryOp, expr: Expr, span: Span) -> Self {
        Self::new(ExprKind::Unary(op, Box::new(expr)), span)
    }

    /// Create a ternary conditional
    pub fn ternary(cond: Expr, if_true: Expr, if_false: Expr) -> Self {
        let span = cond.span.combine(&if_false.span);
        Self::new(
            ExprKind::Ternary(Box::new(cond), Box::new(if_true), Box::new(if_false)),
            span,
        )
    }
}
