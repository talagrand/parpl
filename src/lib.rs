#![doc = include_str!("../README.md")]
// Allow indexing in test code - tests should panic on unexpected values
#![cfg_attr(test, allow(clippy::indexing_slicing))]

mod common;

// Re-export common types at crate root
pub use common::{
    Interner, LimitExceeded, NoOpInterner, Span, StringId, StringPool, StringPoolId, Syntax,
};

#[cfg(feature = "cel")]
pub mod cel;

#[cfg(feature = "scheme")]
pub mod scheme;
