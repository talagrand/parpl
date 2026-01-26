//! CEL (Common Expression Language) parser.
//!
//! This module provides a complete, specification-conformant parser for
//! [CEL](https://cel.dev), a non-Turing complete expression language designed
//! for security policies, access control, and data validation.
//! It is designed as a foundation for building CEL interpreters and tooling.
//!
//! # Integration
//!
//! Parpl is designed to integrate into your project. You provide your own AST
//! representation by implementing [`CelWriter`], and the
//! parser calls your methods to construct nodes as it parses.
//!
//! ```ignore
//! impl CelWriter for MyEvaluator {
//!     type Expr = MyExpr;
//!     // ...
//!     fn binary(&mut self, op: BinaryOp, left: Self::Expr, right: Self::Expr, span: Span)
//!         -> Result<Self::Expr, Self::Error>
//!     {
//!         Ok(MyExpr::Binary { op, left, right })
//!     }
//! }
//!
//! let parser = CelParser::default();
//! let ast = parser.parse("x + y", &mut my_evaluator)?;
//! ```
//!
//! # Starter Implementation
//!
//! The [`mod@reference`] module (requires the `reference` feature) provides
//! working implementations designed to be studied and forked. Use them as-is
//! for quick integration, or adapt the code to your project's needs.
//!
//! ```
//! # #[cfg(feature = "reference")]
//! # fn example() -> Result<(), parpl::Error> {
//! use parpl::StringPool;
//! use parpl::cel::{Builder, reference::arena::ArenaCelWriter};
//! use bumpalo::Bump;
//!
//! let arena = Bump::new();
//! let mut interner = StringPool::new();
//! let mut writer = ArenaCelWriter::new(&arena, &mut interner);
//! let parser = Builder::default().build();
//!
//! let expr = parser.parse("1 + 2 * 3", &mut writer)?;
//! # Ok(())
//! # }
//! ```
//!
//! # Safety Limits
//!
//! The parser enforces configurable depth limits to prevent stack overflow:
//!
//! - **`max_parse_depth`**: Heuristic pre-validation (protects the pest parser)
//! - **`max_ast_depth`**: Precise recursion limit during AST construction
//! - **`max_call_limit`**: Maximum pest rule invocations (DoS protection)
//!
//! Configure limits via [`Builder`]:
//!
//! ```
//! use parpl::cel::Builder;
//!
//! let parser = Builder::default()
//!     .max_parse_depth(128)
//!     .max_ast_depth(24)
//!     .max_call_limit(10_000_000)
//!     .build();
//! ```

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
