//! Starter implementations of [`CelWriter`](super::traits::CelWriter).
//!
//! These implementations are designed to be studied and forked.
//! They are provided for illustrative purposes for how everything comes
//! together, and for prototyping.
//! Use them as-is for quick integration, or copy the code into your
//! project and adapt it to your needs.
//!
//! - **Learning**: Study working code to understand the trait API
//! - **Prototyping**: Quick experiments before building your own AST
//! - **Production**: Fork and customize for your evaluator or compiler
//!
//! # Available Implementations
//!
//! - [`arena`]: Full CEL AST using bumpalo arena allocation
//! - [`mini`]: Minimal CEL subset (no floats/null) using Box allocation

pub mod arena;
pub mod mini;
