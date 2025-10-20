// Cello: A fully conformant CEL (Common Expression Language) parser

pub mod ast;
mod ast_builder;
pub mod constants;
pub mod context;
pub mod error;
mod literal;
pub mod parser;
pub mod pretty;

// Test utilities - only available in test builds
#[cfg(test)]
pub mod test_util;

pub use context::{CelloBuilder, CelloContext};
pub use error::{Error, ErrorKind, Phase, Result};
pub use parser::{parse, parse_with_config, ParseConfig};
pub use pretty::{pretty_print, pretty_print_with_config, PrettyConfig};

// Re-exports for public API
