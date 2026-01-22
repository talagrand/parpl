//! Reference implementations of `CelWriter` for different use cases.
//!
//! - [`arena`]: Full CEL support using bumpalo arena allocation
//! - [`mini`]: Subset of CEL (no floats/null) using Box allocation

pub mod arena;
pub mod mini;
