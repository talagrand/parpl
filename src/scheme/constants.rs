// Scheme Implementation Constants
//
// This module defines constants based on the R7RS Scheme specification.

/// Default maximum nesting depth for datum parsing.
///
/// This is used to prevent stack overflow when parsing deeply nested
/// structures like lists, vectors, and quoted forms.
///
/// Set to 64 for:
/// - Safe operation on typical stacks
/// - Comfortable margin for most Scheme programs
/// - Conservative default that can be increased if needed
///
/// This limit is enforced in:
/// - Reader (`reader.rs`): depth parameter passed to parse functions
/// - Each nested structure decrements remaining depth
pub const DEFAULT_MAX_DEPTH: u32 = 64;
