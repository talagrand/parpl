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
#[expect(dead_code)]
const CEL_SPEC_MIN_RECURSION_DEPTH: u32 = 12;

/// Default maximum nesting depth for pre-parse validation (heuristic)
///
/// This is used by the heuristic pre-validation check that tracks the maximum depth
/// of opening delimiters `(`, `[`, `{` (closing delimiters decrement the counter).
///
/// Set to ~10x the CEL spec minimum (12) to protect against Pest parser overflow:
/// - Pest parser can handle ~171 depth on 1MB stack before stack overflow
/// - This limit (128) provides protection with some headroom
/// - False positives on extreme inputs are acceptable
///
/// **IMPORTANT**: This is just the first line of defense. The AST builder has its own
/// stricter limit (DEFAULT_MAX_AST_DEPTH = 24) enforced via depth parameter.
///
/// This limit is enforced in:
/// - Parser validation (`parser.rs`: `validate_nesting_depth`) - tracks max opening depth
pub const DEFAULT_MAX_PARSE_DEPTH: u32 = 128;

/// Default maximum AST nesting depth (precise)
///
/// This is the **actual** recursion depth limit for the AST builder, which uses
/// stack recursion to construct the AST from the parse tree.
///
/// Set to 2x CEL spec minimum (12) = 24 for:
/// - Safe operation on 1MB stack (measured safe depth: ~38)
/// - Comfortable margin above spec requirement (12)
/// - Conservative default that can be increased if needed
///
/// Empirically measured safe depths:
/// - ~38 on 1MB stack (Windows default)
/// - ~158 on 8MB stack
///
/// This limit is enforced in:
/// - AST builder (`ast_builder.rs`): depth parameter passed to all build functions
/// - Each recursive call increments depth, checked against this limit
/// - By-value parameter means no manual decrement needed (automatic on return)
pub const DEFAULT_MAX_AST_DEPTH: u32 = 24;

/// CEL spec-mandated minimum repetitions for repeating rules (langdef.md line 97)
///
/// The CEL specification requires implementations to support 24-32 repetitions of:
/// - Terms separated by `||` or `&&`
/// - Function call arguments
/// - List/map literal elements
/// - Binary operators of the same precedence
#[expect(dead_code)]
const CEL_SPEC_MIN_REPETITIONS: u32 = 24;
