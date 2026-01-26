//! Traits and shared types for CEL AST construction.
//!
//! This module defines:
//!
//! - [`CelWriter`]: The core trait for AST construction
//! - [`BinaryOp`], [`UnaryOp`]: Operator enums used by the trait
//! - [`Literal`]: Generic literal type used by the trait
//! - [`QuoteStyle`]: Quote delimiter classification for strings/bytes

use crate::{Interner, Span};
use std::fmt::{self, Debug};

// ============================================================================
// Operator Types
// ============================================================================

/// Binary operators for CEL expressions.
///
/// CEL supports the standard set of binary operators for logical operations,
/// comparisons, and arithmetic. Operators are listed in precedence order
/// (lowest to highest).
///
/// # Precedence (lowest to highest)
///
/// 1. `||` (logical or)
/// 2. `&&` (logical and)
/// 3. `<`, `<=`, `>`, `>=`, `==`, `!=`, `in` (relational)
/// 4. `+`, `-` (additive)
/// 5. `*`, `/`, `%` (multiplicative)
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
        write!(f, "{s}")
    }
}

/// Unary operators for CEL expressions.
///
/// CEL supports logical negation (`!`) and arithmetic negation (`-`).
/// Both operators can be repeated (e.g., `!!x` = `x`, `--x` = `x`).
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
        write!(f, "{s}")
    }
}

// ============================================================================
// Literal Types
// ============================================================================

/// Processed literal values (validated and ready for evaluation).
///
/// All numeric values are parsed, all escape sequences are processed.
/// The type parameters allow different string/bytes representations:
///
/// - `S`: String identifier type (e.g., `StringPoolId` for interned, `String` for owned)
/// - `B`: Bytes type (e.g., `&'arena [u8]` for arena, `Vec<u8>` for owned)
#[derive(Debug, Clone, PartialEq)]
pub enum Literal<S, B> {
    /// Integer literal: parsed i64 value
    /// CEL Spec (line 143): INT_LIT = -? DIGIT+ | -? 0x HEXDIGIT+
    /// Range: i64::MIN to i64::MAX
    Int(i64),

    /// Unsigned integer literal: parsed u64 value
    /// CEL Spec (line 144): UINT_LIT = INT_LIT \[uU\]
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
    /// CEL Spec (line 154): BYTES_LIT = \[bB\] STRING_LIT
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

/// Quote style for CEL string and bytes literals.
///
/// CEL supports four quote styles, allowing strings with embedded quotes
/// or multi-line content:
///
/// | Style | Syntax | Multi-line | Escape `'` | Escape `"` |
/// |-------|--------|------------|------------|------------|
/// | Single | `'text'` | No | Required | Optional |
/// | Double | `"text"` | No | Optional | Required |
/// | Triple Single | `'''text'''` | Yes | Optional | Optional |
/// | Triple Double | `"""text"""` | Yes | Optional | Optional |
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QuoteStyle {
    /// Single quotes: `'text'`
    SingleQuote,
    /// Double quotes: `"text"`
    DoubleQuote,
    /// Triple single quotes: `'''text'''` (multi-line)
    TripleSingleQuote,
    /// Triple double quotes: `"""text"""` (multi-line)
    TripleDoubleQuote,
}

// ============================================================================
// CelWriter Trait
// ============================================================================

/// Trait for constructing CEL AST nodes.
///
/// `CelWriter` abstracts over AST construction, allowing the parser to work
/// with any expression representation. This enables:
///
/// - **Arena allocation**: Zero-copy ASTs with bumpalo
/// - **Box allocation**: Traditional heap-allocated ASTs
/// - **Custom types**: Your own expression types for evaluation
///
/// # Associated Types
///
/// - `StringId`: Handle type for interned strings (identifiers, field names)
/// - `Bytes`: Type for byte literals (typically `&'arena [u8]` or `Vec<u8>`)
/// - `Expr`: The expression node type you're building
/// - `Error`: Error type for writer failures (use `Infallible` if infallible)
/// - `Interner`: The string interner type (implements [`Interner`])
///
/// # Example
///
/// See [`reference::arena::ArenaCelWriter`](crate::cel::reference::arena::ArenaCelWriter)
/// for a full implementation.
///
/// ```ignore
/// impl CelWriter for MyCelWriter {
///     type StringId = StringPoolId;
///     type Bytes = Vec<u8>;
///     type Expr = MyExpr;
///     type Error = Infallible;
///     type Interner = StringPool;
///
///     fn literal(&mut self, lit: Literal<...>, span: Span) -> Result<Self::Expr, Self::Error> {
///         Ok(MyExpr::Literal(lit))
///     }
///
///     // ... implement other methods
/// }
/// ```
pub trait CelWriter {
    /// The type of string identifiers used by this writer (e.g. StringPoolId)
    type StringId: Clone + PartialEq + Debug;

    /// The type of byte slices used by this writer (e.g. &'a [u8])
    type Bytes: Clone + PartialEq + Debug;

    /// The type of expression nodes produced by this writer
    type Expr: Clone + PartialEq + Debug;

    /// The error type returned by this writer
    type Error: std::error::Error + Send + Sync + 'static;

    /// The interner used by this writer
    type Interner: Interner<Id = Self::StringId>;

    /// Access the interner mutably
    fn interner(&mut self) -> &mut Self::Interner;

    /// Access the interner immutably
    fn interner_ref(&self) -> &Self::Interner;

    /// Allocate bytes
    fn bytes(&mut self, bytes: &[u8]) -> Self::Bytes;

    /// Create a literal expression
    fn literal(
        &mut self,
        lit: Literal<Self::StringId, Self::Bytes>,
        span: Span,
    ) -> Result<Self::Expr, Self::Error>;

    /// Create an identifier expression
    fn ident(&mut self, name: Self::StringId, span: Span) -> Result<Self::Expr, Self::Error>;

    /// Create a unary operation expression
    fn unary(
        &mut self,
        op: UnaryOp,
        operand: Self::Expr,
        span: Span,
    ) -> Result<Self::Expr, Self::Error>;

    /// Create a binary operation expression
    fn binary(
        &mut self,
        op: BinaryOp,
        left: Self::Expr,
        right: Self::Expr,
        span: Span,
    ) -> Result<Self::Expr, Self::Error>;

    /// Create a ternary conditional expression
    fn ternary(
        &mut self,
        cond: Self::Expr,
        true_expr: Self::Expr,
        false_expr: Self::Expr,
        span: Span,
    ) -> Result<Self::Expr, Self::Error>;

    /// Create a member access expression
    fn member(
        &mut self,
        target: Self::Expr,
        field: Self::StringId,
        args: Option<&[Self::Expr]>,
        span: Span,
    ) -> Result<Self::Expr, Self::Error>;

    /// Create an index access expression
    fn index(
        &mut self,
        target: Self::Expr,
        index: Self::Expr,
        span: Span,
    ) -> Result<Self::Expr, Self::Error>;

    /// Create a function call expression
    fn call(
        &mut self,
        target: Option<Self::Expr>,
        function: Self::StringId,
        args: &[Self::Expr],
        span: Span,
    ) -> Result<Self::Expr, Self::Error>;

    /// Create a list literal expression
    fn list(&mut self, items: &[Self::Expr], span: Span) -> Result<Self::Expr, Self::Error>;

    /// Create a map literal expression
    fn map(
        &mut self,
        entries: &[(Self::Expr, Self::Expr)],
        span: Span,
    ) -> Result<Self::Expr, Self::Error>;

    /// Create a struct/message literal expression
    fn structure(
        &mut self,
        type_name: Option<Self::Expr>,
        fields: &[Self::StringId],
        values: &[(Self::StringId, Self::Expr)],
        span: Span,
    ) -> Result<Self::Expr, Self::Error>;
}
