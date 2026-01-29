//! Arena-allocated CEL AST implementation.
//!
//! This module provides a working `CelWriter` implementation using bumpalo
//! arena allocation. It demonstrates how to build an efficient, zero-copy AST.
//!
//! # Types
//!
//! - [`Expr`]: A CEL expression node with span information
//! - [`ExprKind`]: The specific kind of expression
//! - [`ArenaCelWriter`]: The `CelWriter` implementation
//!
//! # Example
//!
//! ```
//! # #[cfg(feature = "reference")]
//! # fn example() -> Result<(), parpl::Error> {
//! use bumpalo::Bump;
//! use parpl::StringPool;
//! use parpl::cel::{Builder, CelWriter};
//! use parpl::cel::reference::arena::ArenaCelWriter;
//!
//! let arena = Bump::new();
//! let mut interner = StringPool::new();
//! let mut writer = ArenaCelWriter::new(&arena, &mut interner);
//!
//! let parser = Builder::default().build();
//! let expr = parser.parse("1 + 2 * 3", &mut writer)?;
//! # Ok(())
//! # }
//! ```

use crate::{
    Span, StringPool, StringPoolId,
    cel::{BinaryOp, CelWriter, Literal, UnaryOp},
};
use bumpalo::Bump;

// ============================================================================
// AST Types
// ============================================================================

/// A complete CEL expression (the root of the AST).
///
/// **Arena-allocated**: All `Expr` nodes are allocated in a `bumpalo::Bump` arena.
/// The lifetime `'arena` ties the expression to the arena that owns it.
#[derive(Debug, Clone, PartialEq)]
pub struct Expr<'arena> {
    /// The kind of expression
    pub kind: ExprKind<'arena>,
    /// Source location
    pub span: Span,
}

impl<'arena> Expr<'arena> {
    /// Create a new expression with the given kind and span.
    pub fn new(kind: ExprKind<'arena>, span: Span) -> Self {
        Self { kind, span }
    }
}

/// The kind of expression (CEL spec lines 68-94).
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

// ============================================================================
// CelWriter Implementation
// ============================================================================

/// Arena-based `CelWriter` implementation.
///
/// Allocates all AST nodes in a bumpalo arena for efficient memory management.
/// Strings are interned in a `StringPool`.
pub struct ArenaCelWriter<'a, 'arena> {
    arena: &'arena Bump,
    interner: &'a mut StringPool,
}

impl<'a, 'arena> ArenaCelWriter<'a, 'arena> {
    /// Creates a new arena-based CEL writer.
    pub fn new(arena: &'arena Bump, interner: &'a mut StringPool) -> Self {
        Self { arena, interner }
    }
}

impl<'a, 'arena> CelWriter for ArenaCelWriter<'a, 'arena> {
    type StringId = StringPoolId;
    type Interner = StringPool;
    type Bytes = &'arena [u8];
    type Expr = &'arena Expr<'arena>;
    type Error = std::convert::Infallible;

    fn interner(&mut self) -> &mut Self::Interner {
        self.interner
    }

    fn interner_ref(&self) -> &Self::Interner {
        self.interner
    }

    fn bytes(&mut self, bytes: &[u8]) -> Self::Bytes {
        self.arena.alloc_slice_copy(bytes)
    }

    fn literal(
        &mut self,
        lit: Literal<Self::StringId, Self::Bytes>,
        span: Span,
    ) -> std::result::Result<Self::Expr, Self::Error> {
        Ok(self.arena.alloc(Expr::new(ExprKind::Literal(lit), span)))
    }

    fn ident(
        &mut self,
        name: Self::StringId,
        span: Span,
    ) -> std::result::Result<Self::Expr, Self::Error> {
        Ok(self.arena.alloc(Expr::new(ExprKind::Ident(name), span)))
    }

    fn unary(
        &mut self,
        op: UnaryOp,
        operand: Self::Expr,
        span: Span,
    ) -> std::result::Result<Self::Expr, Self::Error> {
        Ok(self
            .arena
            .alloc(Expr::new(ExprKind::Unary(op, operand), span)))
    }

    fn binary(
        &mut self,
        op: BinaryOp,
        left: Self::Expr,
        right: Self::Expr,
        span: Span,
    ) -> std::result::Result<Self::Expr, Self::Error> {
        Ok(self
            .arena
            .alloc(Expr::new(ExprKind::Binary(op, left, right), span)))
    }

    fn ternary(
        &mut self,
        cond: Self::Expr,
        true_expr: Self::Expr,
        false_expr: Self::Expr,
        span: Span,
    ) -> std::result::Result<Self::Expr, Self::Error> {
        Ok(self.arena.alloc(Expr::new(
            ExprKind::Ternary(cond, true_expr, false_expr),
            span,
        )))
    }

    fn member(
        &mut self,
        target: Self::Expr,
        field: Self::StringId,
        args: Option<&[Self::Expr]>,
        span: Span,
    ) -> std::result::Result<Self::Expr, Self::Error> {
        let args = args.map(|a| {
            self.arena
                .alloc_slice_fill_iter(a.iter().map(|&e| e.clone()))
                as &'arena [Expr<'arena>]
        });
        Ok(self
            .arena
            .alloc(Expr::new(ExprKind::Member(target, field, args), span)))
    }

    fn index(
        &mut self,
        target: Self::Expr,
        index: Self::Expr,
        span: Span,
    ) -> std::result::Result<Self::Expr, Self::Error> {
        Ok(self
            .arena
            .alloc(Expr::new(ExprKind::Index(target, index), span)))
    }

    fn call(
        &mut self,
        target: Option<Self::Expr>,
        function: Self::StringId,
        args: &[Self::Expr],
        span: Span,
    ) -> std::result::Result<Self::Expr, Self::Error> {
        let args = self
            .arena
            .alloc_slice_fill_iter(args.iter().map(|&e| e.clone()));
        Ok(self
            .arena
            .alloc(Expr::new(ExprKind::Call(target, function, args), span)))
    }

    fn list(
        &mut self,
        items: &[Self::Expr],
        span: Span,
    ) -> std::result::Result<Self::Expr, Self::Error> {
        let items = self
            .arena
            .alloc_slice_fill_iter(items.iter().map(|&e| e.clone()));
        Ok(self.arena.alloc(Expr::new(ExprKind::List(items), span)))
    }

    fn map(
        &mut self,
        entries: &[(Self::Expr, Self::Expr)],
        span: Span,
    ) -> std::result::Result<Self::Expr, Self::Error> {
        let entries = self
            .arena
            .alloc_slice_fill_iter(entries.iter().map(|(k, v)| ((*k).clone(), (*v).clone())));
        Ok(self.arena.alloc(Expr::new(ExprKind::Map(entries), span)))
    }

    fn structure(
        &mut self,
        type_name: Option<Self::Expr>,
        fields: &[Self::StringId],
        values: &[(Self::StringId, Self::Expr)],
        span: Span,
    ) -> std::result::Result<Self::Expr, Self::Error> {
        let fields = self.arena.alloc_slice_copy(fields);
        let values = self
            .arena
            .alloc_slice_fill_iter(values.iter().map(|(k, v)| (*k, (*v).clone())));
        Ok(self
            .arena
            .alloc(Expr::new(ExprKind::Struct(type_name, fields, values), span)))
    }
}
