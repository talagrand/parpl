// Cello: A fully conformant CEL (Common Expression Language) parser

mod ast;
mod ast_builder;
mod constants;
mod context;
mod error;
mod literal;
mod parser;
mod pretty;
#[cfg(any(test, feature = "reference"))]
pub mod reference;
pub mod traits;

// Test utilities - only available in test builds
#[cfg(test)]
pub mod test_util;

// Re-export key types for convenient access (single canonical path)
pub use ast::{BinaryOp, Expr, ExprKind, Literal, QuoteStyle, UnaryOp};
pub use context::{Builder, CelParser};
pub use error::{Error, ErrorKind, Result};
pub use parser::{ParseConfig, parse, parse_with_config};
pub use pretty::{PrettyConfig, pretty_print, pretty_print_with_config};
