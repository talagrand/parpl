// Cello: A fully conformant CEL (Common Expression Language) parser

pub mod ast;
mod ast_builder;
pub mod context;
pub mod error;
pub mod parser;
pub mod pretty;

pub use ast_builder::{build_ast, build_ast_with_config};
pub use context::{CelloBuilder, CelloContext};
pub use error::{Error, ErrorKind, Phase, Result};
pub use parser::{parse, parse_with_config, ParseConfig};
pub use pretty::{pretty_print, pretty_print_with_config, PrettyConfig};

// Convenience functions

/// Parse a CEL expression with default settings
///
/// This is a convenience function that wraps the builder API.
/// For custom configuration, use `CelloBuilder`.
///
/// # Examples
/// ```
/// use cello::parse_expr;
///
/// let ast = parse_expr("1 + 2")?;
/// # Ok::<(), cello::Error>(())
/// ```
pub fn parse_expr(input: &str) -> Result<ast::Expr> {
    CelloBuilder::new().parse_scoped(input, |ctx| Ok(ctx.ast()?.clone()))
}
