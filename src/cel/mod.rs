// Cello: A fully conformant CEL (Common Expression Language) parser

pub(crate) mod builder;
mod constants;
mod context;
mod literal;
mod parser;
#[cfg(any(test, feature = "reference"))]
pub mod reference;
pub mod traits;

/// Result type alias for parser operations.
pub type Result<T> = std::result::Result<T, crate::Error>;

// Re-export key types for convenient access (single canonical path)
pub use context::{Builder, CelParser};
pub use traits::{BinaryOp, CelWriter, Literal, QuoteStyle, UnaryOp};
