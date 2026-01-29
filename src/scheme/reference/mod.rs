//! Starter implementations of [`DatumWriter`](super::DatumWriter) and
//! [`SchemeNumberOps`](super::SchemeNumberOps).
//!
//! These implementations are designed to be studied and forked.
//! They are provided for illustrative purposes for how everything comes
//! together, and for prototyping.
//! Use them as-is for quick integration, or copy the code into your
//! project and adapt it to your needs.
//!
//! # Available Implementations
//!
//! - [`arena`]: Full R7RS datum support using bumpalo arena allocation with i64/f64 numbers
//! - [`mini`]: Subset of Scheme (integers only, no vectors/chars/labels) using Vec allocation
//!
//! # Also available
//!
//! - [`numbers`]: Number tower implementations which can be used by any AST implementation (`SimpleNumberOps` for i64/f64)

/// Full R7RS datum support using bumpalo arena allocation with i64/f64 numbers.
pub mod arena;
/// Subset of Scheme (integers only, no vectors/chars/labels) using Vec allocation.
pub mod mini;
/// Number tower implementations (`SimpleNumberOps` for i64/f64).
pub mod numbers;
