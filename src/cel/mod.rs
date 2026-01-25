// Cello: A fully conformant CEL (Common Expression Language) parser

mod ast;
mod ast_builder;
mod constants;
mod context;
mod literal;
mod parser;
#[cfg(any(test, feature = "reference"))]
pub mod reference;
pub mod traits;

// Test utilities - only available in test builds
#[cfg(test)]
pub mod test_util;

/// Result type alias for parser operations.
pub type Result<T> = std::result::Result<T, crate::Error>;

// Re-export key types for convenient access (single canonical path)
pub use ast::{BinaryOp, Expr, ExprKind, Literal, QuoteStyle, UnaryOp};
pub use context::{Builder, CelParser};
pub use parser::{ParseConfig, parse, parse_with_config};
