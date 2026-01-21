#![doc = include_str!("../README.md")]

// Allow indexing in test code - tests should panic on unexpected values
#![cfg_attr(test, allow(clippy::indexing_slicing))]

pub mod common;

#[cfg(feature = "cel")]
pub mod cel;

#[cfg(feature = "scheme")]
pub mod scheme;
