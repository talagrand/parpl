use crate::{
    Span, StringPool, StringPoolId,
    cel::{
        ast::{BinaryOp, Expr, ExprKind, Literal, UnaryOp},
        ast_builder::build_ast_from_pairs,
        error::Result,
        parser::{ParseConfig, parse_with_config},
        traits::CelWriter,
    },
};
use bumpalo::Bump;

pub struct ArenaCelWriter<'a, 'arena> {
    arena: &'arena Bump,
    interner: &'a mut StringPool,
}

impl<'a, 'arena> ArenaCelWriter<'a, 'arena> {
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

/// Build an AST using a provided arena and interner
///
/// This is the core AST building function used by `Context`.
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
    interner: &mut StringPool,
) -> Result<&'arena Expr<'arena>> {
    // First parse with pest
    let pairs = parse_with_config(input, config)?;

    // Start with max depth remaining
    let mut writer = ArenaCelWriter { arena, interner };
    build_ast_from_pairs(pairs, config.max_ast_depth, &mut writer)
}
