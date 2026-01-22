use crate::{
    Interner, Span,
    cel::ast::{BinaryOp, Literal, UnaryOp},
};
use std::fmt::Debug;

/// Trait for constructing CEL AST nodes.
///
/// This trait abstracts over the memory management strategy (e.g. arena allocation).
/// It allows the parser to be decoupled from specific allocator implementations.
pub trait CelWriter {
    /// The type of string identifiers used by this writer (e.g. StringPoolId)
    type StringId: Clone + PartialEq + Debug;

    /// The type of byte slices used by this writer (e.g. &'a [u8])
    type Bytes: Clone + PartialEq + Debug;

    /// The type of expression nodes produced by this writer
    type Expr: Clone + PartialEq + Debug;

    /// The error type returned by this writer
    type Error: Debug;

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
