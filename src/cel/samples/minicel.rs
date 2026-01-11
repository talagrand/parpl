use crate::{
    cel::{
        ast::{BinaryOp, Literal, Span, UnaryOp},
        ast_builder::build_expr,
        error::Result,
        parser::{ParseConfig, parse_with_config},
        traits::CelWriter,
    },
    common::NoOpInterner,
};

#[derive(Debug, Clone, PartialEq)]
pub struct MiniExpr {
    pub kind: MiniExprKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum MiniExprKind {
    Ternary(Box<MiniExpr>, Box<MiniExpr>, Box<MiniExpr>),
    Binary(BinaryOp, Box<MiniExpr>, Box<MiniExpr>),
    Unary(UnaryOp, Box<MiniExpr>),
    Member(Box<MiniExpr>, String, Option<Vec<MiniExpr>>),
    Index(Box<MiniExpr>, Box<MiniExpr>),
    Call(Option<Box<MiniExpr>>, String, Vec<MiniExpr>),
    Ident(String),
    List(Vec<MiniExpr>),
    Map(Vec<(MiniExpr, MiniExpr)>),
    Struct(Option<Box<MiniExpr>>, Vec<String>, Vec<(String, MiniExpr)>),
    Literal(Literal<String, Vec<u8>>),
}

#[derive(Debug)]
pub enum MiniError {
    UnsupportedFloat,
    UnsupportedNull,
}

pub struct MiniCelWriter {
    interner: NoOpInterner,
}

impl CelWriter for MiniCelWriter {
    type StringId = String;
    type Interner = NoOpInterner;
    type Bytes = Vec<u8>;
    type Expr = Box<MiniExpr>;
    type Error = MiniError;

    fn interner(&mut self) -> &mut Self::Interner {
        &mut self.interner
    }

    fn interner_ref(&self) -> &Self::Interner {
        &self.interner
    }

    fn bytes(&mut self, bytes: &[u8]) -> Self::Bytes {
        bytes.to_vec()
    }

    fn literal(
        &mut self,
        lit: Literal<Self::StringId, Self::Bytes>,
        span: Span,
    ) -> std::result::Result<Self::Expr, Self::Error> {
        // Reject floats and nulls as requested
        match lit {
            Literal::Float(_) => Err(MiniError::UnsupportedFloat),
            Literal::Null => Err(MiniError::UnsupportedNull),
            _ => Ok(Box::new(MiniExpr {
                kind: MiniExprKind::Literal(lit),
                span,
            })),
        }
    }

    fn ident(
        &mut self,
        name: Self::StringId,
        span: Span,
    ) -> std::result::Result<Self::Expr, Self::Error> {
        Ok(Box::new(MiniExpr {
            kind: MiniExprKind::Ident(name),
            span,
        }))
    }

    fn unary(
        &mut self,
        op: UnaryOp,
        operand: Self::Expr,
        span: Span,
    ) -> std::result::Result<Self::Expr, Self::Error> {
        Ok(Box::new(MiniExpr {
            kind: MiniExprKind::Unary(op, operand),
            span,
        }))
    }

    fn binary(
        &mut self,
        op: BinaryOp,
        left: Self::Expr,
        right: Self::Expr,
        span: Span,
    ) -> std::result::Result<Self::Expr, Self::Error> {
        Ok(Box::new(MiniExpr {
            kind: MiniExprKind::Binary(op, left, right),
            span,
        }))
    }

    fn ternary(
        &mut self,
        cond: Self::Expr,
        true_expr: Self::Expr,
        false_expr: Self::Expr,
        span: Span,
    ) -> std::result::Result<Self::Expr, Self::Error> {
        Ok(Box::new(MiniExpr {
            kind: MiniExprKind::Ternary(cond, true_expr, false_expr),
            span,
        }))
    }

    fn member(
        &mut self,
        target: Self::Expr,
        field: Self::StringId,
        args: Option<&[Self::Expr]>,
        span: Span,
    ) -> std::result::Result<Self::Expr, Self::Error> {
        let args = args.map(|a| a.iter().map(|e| *e.clone()).collect());
        Ok(Box::new(MiniExpr {
            kind: MiniExprKind::Member(target, field, args),
            span,
        }))
    }

    fn index(
        &mut self,
        target: Self::Expr,
        index: Self::Expr,
        span: Span,
    ) -> std::result::Result<Self::Expr, Self::Error> {
        Ok(Box::new(MiniExpr {
            kind: MiniExprKind::Index(target, index),
            span,
        }))
    }

    fn call(
        &mut self,
        target: Option<Self::Expr>,
        function: Self::StringId,
        args: &[Self::Expr],
        span: Span,
    ) -> std::result::Result<Self::Expr, Self::Error> {
        let args = args.iter().map(|e| *e.clone()).collect();
        Ok(Box::new(MiniExpr {
            kind: MiniExprKind::Call(target, function, args),
            span,
        }))
    }

    fn list(
        &mut self,
        items: &[Self::Expr],
        span: Span,
    ) -> std::result::Result<Self::Expr, Self::Error> {
        let items = items.iter().map(|e| *e.clone()).collect();
        Ok(Box::new(MiniExpr {
            kind: MiniExprKind::List(items),
            span,
        }))
    }

    fn map(
        &mut self,
        entries: &[(Self::Expr, Self::Expr)],
        span: Span,
    ) -> std::result::Result<Self::Expr, Self::Error> {
        let entries = entries
            .iter()
            .map(|(k, v)| (*k.clone(), *v.clone()))
            .collect();
        Ok(Box::new(MiniExpr {
            kind: MiniExprKind::Map(entries),
            span,
        }))
    }

    fn structure(
        &mut self,
        target: Option<Self::Expr>,
        path: &[Self::StringId],
        fields: &[(Self::StringId, Self::Expr)],
        span: Span,
    ) -> std::result::Result<Self::Expr, Self::Error> {
        let path = path.to_vec();
        let fields = fields
            .iter()
            .map(|(k, v)| (k.clone(), *v.clone()))
            .collect();
        Ok(Box::new(MiniExpr {
            kind: MiniExprKind::Struct(target, path, fields),
            span,
        }))
    }
}

pub fn build_ast_mini(input: &str) -> Result<Box<MiniExpr>> {
    let mut writer = MiniCelWriter {
        interner: NoOpInterner,
    };
    let config = ParseConfig::default();
    let mut pairs = parse_with_config(input, config)?;
    let root_pair = pairs.next().unwrap(); // Parser guarantees at least one pair (EOI included)

    // The root rule is usually `cel` which contains `expr` and `EOI`.
    // We need to find the `expr` pair.
    let expr_pair = if root_pair.as_rule() == crate::cel::parser::Rule::cel {
        root_pair.into_inner().next().unwrap()
    } else {
        root_pair
    };

    build_expr(config.max_ast_depth, expr_pair, &mut writer)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mini_simple() {
        let ast = build_ast_mini("1 + 2").unwrap();
        match ast.kind {
            MiniExprKind::Binary(BinaryOp::Add, left, right) => {
                match left.kind {
                    MiniExprKind::Literal(Literal::Int(1)) => {}
                    _ => panic!("expected 1"),
                }
                match right.kind {
                    MiniExprKind::Literal(Literal::Int(2)) => {}
                    _ => panic!("expected 2"),
                }
            }
            _ => panic!("expected binary add"),
        }
    }

    #[test]
    fn test_mini_string() {
        let ast = build_ast_mini("'hello'").unwrap();
        match ast.kind {
            MiniExprKind::Literal(Literal::String(s)) => assert_eq!(s, "hello"),
            _ => panic!("expected string"),
        }
    }

    #[test]
    fn test_mini_reject_float() {
        let err = build_ast_mini("1.0").unwrap_err();
        assert!(format!("{:?}", err).contains("UnsupportedFloat"));
    }

    #[test]
    fn test_mini_reject_null() {
        let err = build_ast_mini("null").unwrap_err();
        assert!(format!("{:?}", err).contains("UnsupportedNull"));
    }
}
