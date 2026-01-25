#![doc = include_str!("../README.md")]
// Allow indexing in test code - tests should panic on unexpected values
#![cfg_attr(test, allow(clippy::indexing_slicing))]

mod common;
mod error;

// Re-export common types at crate root
pub use common::{Interner, NoOpInterner, Span, StringId, StringPool, StringPoolId, Syntax};
pub use error::{Error, LimitExceeded};

#[cfg(feature = "cel")]
pub mod cel;

#[cfg(feature = "scheme")]
pub mod scheme;
