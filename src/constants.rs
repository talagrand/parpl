// CEL Implementation Constants
//
// This module defines constants based on the CEL specification requirements
// from langdef.md lines 95-115.

/// CEL spec-mandated minimum recursion depth (langdef.md line 107)
///
/// The CEL specification requires implementations to support at least:
/// - 12 repetitions of recursive rules, including:
///   - 12 nested function calls
///   - 12 selection (`.`) operators in a row
///   - 12 indexing (`[_]`) operators in a row
///   - 12 nested list, map, or message literals
pub const CEL_SPEC_MIN_RECURSION_DEPTH: usize = 12;

/// Default maximum recursion/nesting depth (2x spec minimum for safety margin)
///
/// We set our default to 2x the spec-mandated minimum to provide a comfortable
/// safety margin while still being conservative with stack usage.
///
/// This limit is enforced in:
/// - Parser validation (`parser.rs`: `validate_nesting_depth`)
/// - AST builder recursion (implicit via parser enforcement)
///
/// Note: After refactoring, our stack usage supports much deeper nesting
/// (depth ~38 on 1MB stack, ~158 on 8MB stack), but we keep the default
/// conservative to align with spec requirements.
pub const DEFAULT_MAX_RECURSION_DEPTH: usize = CEL_SPEC_MIN_RECURSION_DEPTH * 2;

/// CEL spec-mandated minimum repetitions for repeating rules (langdef.md line 97)
///
/// The CEL specification requires implementations to support 24-32 repetitions of:
/// - Terms separated by `||` or `&&`
/// - Function call arguments
/// - List/map literal elements
/// - Binary operators of the same precedence
pub const CEL_SPEC_MIN_REPETITIONS: usize = 24;
