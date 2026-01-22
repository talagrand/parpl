//! Reference implementations of `DatumWriter` and `SchemeNumberOps` for different use cases.
//!
//! - [`arena`]: Full R7RS datum support using bumpalo arena allocation
//! - [`mini`]: Subset of Scheme (integers only, no vectors/chars/labels) using Vec allocation
//! - [`numbers`]: Number tower implementations (`SimpleNumberOps` for i64/f64)

pub mod arena;
pub mod mini;
pub mod numbers;
