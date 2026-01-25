// CEL Parser
//
// This module handles parsing CEL expressions using the pest PEG parser.
// It includes complexity protection against stack overflow and timeout attacks.

use crate::cel::{
    constants,
    error::{Error, Result},
};
use pest::Parser;
use pest_derive::Parser;
use std::num::NonZeroUsize;

#[derive(Parser)]
#[grammar = "cel/grammar.pest"]
pub struct CelParser;

pub use pest::iterators::Pairs;

/// Configuration for parsing CEL expressions
#[derive(Debug, Clone, Copy)]
pub struct ParseConfig {
    /// Maximum nesting depth for pre-parse heuristic validation (default: 128)
    ///
    /// This protects against Pest parser stack overflow (~171 depth on 1MB stack).
    /// Uses a simple heuristic that counts opening delimiters.
    pub max_parse_depth: usize,

    /// Maximum AST nesting depth for AST builder (default: 24)
    ///
    /// This protects against AST builder stack overflow (~38 depth on 1MB stack).
    /// Must be LOWER than max_parse_depth to prevent crashes during AST construction.
    pub max_ast_depth: usize,

    /// Maximum number of rule invocations (pest call limit for DoS protection)
    pub max_call_limit: usize,
}

impl Default for ParseConfig {
    fn default() -> Self {
        Self {
            max_parse_depth: constants::DEFAULT_MAX_PARSE_DEPTH,
            max_ast_depth: constants::DEFAULT_MAX_AST_DEPTH,
            max_call_limit: 10_000_000,
        }
    }
}

/// Parse a CEL expression from a string with default configuration
///
/// Uses default limits:
/// - `max_nesting_depth`: 128 (see `constants::DEFAULT_MAX_PARSE_DEPTH`)
/// - `max_call_limit`: 10,000,000
///
/// For custom limits, use [`parse_with_config`].
///
/// # Example
/// ```
/// use parpl::cel::parse;
///
/// let pairs = parse("1 + 2")?;
/// # Ok::<(), parpl::cel::Error>(())
/// ```
pub fn parse(input: &str) -> Result<Pairs<'_, Rule>> {
    parse_with_config(input, ParseConfig::default())
}

/// Parse a CEL expression with custom configuration
///
/// Allows configuring:
/// - `max_parse_depth`: Maximum depth for heuristic pre-validation (default: 128)
/// - `max_ast_depth`: Maximum AST recursion depth (default: 24)
/// - `max_call_limit`: Maximum Pest rule invocations (default: 10M)
///
/// # Example
/// ```
/// use parpl::cel::{parse_with_config, ParseConfig};
///
/// let config = ParseConfig {
///     max_parse_depth: 128,
///     max_ast_depth: 24,
///     max_call_limit: 50_000_000,
/// };
/// let result = parse_with_config("1 + 2", config);
/// assert!(result.is_ok());
/// ```
pub fn parse_with_config(input: &str, config: ParseConfig) -> Result<Pairs<'_, Rule>> {
    // Set Pest's call limit to prevent DoS attacks
    // This limits TOTAL rule invocations across the entire parse, not recursion depth
    pest::set_call_limit(Some(
        NonZeroUsize::new(config.max_call_limit)
            .unwrap_or_else(|| NonZeroUsize::new(10_000_000).expect("10_000_000 is non-zero")),
    ));

    // Pre-validate nesting depth to prevent Pest parser stack overflow
    // Pre-validate nesting depth using heuristic (protects against Pest parser overflow).
    // Pest itself uses recursion and will overflow at ~171 depth on Windows 1MB stack.
    // Our heuristic check counts all delimiters, so the limit is set higher than actual depth.
    validate_nesting_depth(input, config.max_parse_depth)?;

    CelParser::parse(Rule::cel, input).map_err(|e| Error::from_pest_error(e, input.len()))
}

/// Validate that input doesn't exceed maximum delimiter count (heuristic depth check)
///
/// **Why this exists:** Pest parser uses recursion internally and will stack overflow
/// at ~171 actual nesting depth on Windows 1MB stack. This pre-check prevents malicious
/// inputs from crashing the parser by providing a friendly error message.
///
/// **Approach:** This is a simple heuristic that tracks the maximum depth of opening
/// delimiters. Each `(`, `[`, `{` increments the counter, and each `)`, `]`, `}` decrements
/// it. We track the maximum depth reached during the scan.
///
/// **What it counts:**
/// - Opening delimiters `(`, `[`, `{` increment the counter
/// - Closing delimiters `)`, `]`, `}` decrement the counter (with saturation)
/// - We track the maximum counter value reached
/// - For `((1))`, counter reaches max of 2
///
/// **Limitations:**
/// - Counts delimiters in strings (false positives possible, but rare)
/// - This is acceptable: we prefer rejecting extreme inputs over risking crashes
///
/// Default limit: 128 (see `constants::DEFAULT_MAX_PARSE_DEPTH`)
fn validate_nesting_depth(input: &str, max_depth: usize) -> Result<()> {
    let mut depth = 0;
    let mut max_reached = 0;
    let mut pos = 0;

    for ch in input.chars() {
        match ch {
            '(' | '[' | '{' => {
                depth += 1;
                max_reached = max_reached.max(depth);
                if max_reached > max_depth {
                    // Span from the offending delimiter to end of input
                    let span = crate::Span::new(pos, input.len());
                    return Err(Error::nesting_depth(span, max_reached, max_depth));
                }
            }
            ')' | ']' | '}' => {
                depth = depth.saturating_sub(1);
            }
            _ => {}
        }
        pos += ch.len_utf8();
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(test)]
    mod test_util {
        use super::super::*;

        pub fn assert_parses(input: &str) {
            let result = parse(input);
            assert!(result.is_ok(), "Failed to parse '{input}': {result:?}");
        }

        pub fn assert_parse_fails(input: &str) {
            let result = parse(input);
            assert!(result.is_err(), "Expected '{input}' to fail parsing");
        }

        pub fn assert_error_contains(input: &str, expected: &str) {
            match parse(input) {
                Err(e) => {
                    let msg = format!("{e}");
                    assert!(
                        msg.contains(expected),
                        "Error message '{msg}' should contain '{expected}'"
                    );
                }
                Ok(_) => panic!("Expected '{input}' to fail, but it parsed successfully"),
            }
        }
    }

    macro_rules! test_cases {
        ($($name:ident: $input:expr => $assert_fn:ident),* $(,)?) => {
            $(
                #[test]
                fn $name() {
                    test_util::$assert_fn($input);
                }
            )*
        };
    }

    // ============================================================
    // Section: Literal Parsing (CEL Spec lines 147-148)
    // ============================================================

    test_cases! {
        // Integer literals
        test_int_42: "42" => assert_parses,
        test_int_negative: "-17" => assert_parses,
        test_int_zero: "0" => assert_parses,
        test_int_negative_42: "-42" => assert_parses,

        // Hex integer literals
        test_hex_1a: "0x1A" => assert_parses,
        test_hex_ff: "0xFF" => assert_parses,
        test_hex_negative: "-0x10" => assert_parses,
        test_hex_upper_x: "0X2B" => assert_parses,

        // Unsigned integers
        test_uint_42: "42u" => assert_parses,

        // Float literals
        test_float_pi: "3.14" => assert_parses,

        // String literals
        test_string_double: r#""hello""# => assert_parses,
        test_string_single: "'world'" => assert_parses,
        test_string_raw_double: r#"r"raw""# => assert_parses,
        test_string_raw_single: "R'raw'" => assert_parses,

        // Boolean literals
        test_bool_true: "true" => assert_parses,
        test_bool_false: "false" => assert_parses,

        // Null literal
        test_null: "null" => assert_parses,
    }

    #[test]
    fn test_triple_quoted_strings() {
        // These need special handling due to newlines
        assert!(
            parse(
                r#""""multi
line
string""""#
            )
            .is_ok()
        );
        assert!(
            parse(
                r"'''another
multi-line'''"
            )
            .is_ok()
        );
        assert!(
            parse(
                r#"r"""raw multi
line""""#
            )
            .is_ok()
        );
    }

    // ============================================================
    // Section: Arithmetic Operations (CEL Spec lines 81-82)
    // ============================================================

    test_cases! {
        test_addition: "1 + 2" => assert_parses,
        test_multiplication: "3 * 4" => assert_parses,
        test_complex_arithmetic: "1 + 2 * 3" => assert_parses,
    }

    // ============================================================
    // Section: Logical Operations (CEL Spec lines 77-78)
    // ============================================================

    test_cases! {
        test_logical_and: "true && false" => assert_parses,
        test_logical_or: "true || false" => assert_parses,
    }

    // ============================================================
    // Section: Ternary Operator (CEL Spec line 76)
    // ============================================================

    test_cases! {
        test_ternary: "true ? 1 : 2" => assert_parses,
    }

    // ============================================================
    // Section: Parenthesized Expressions (CEL Spec line 92)
    // ============================================================

    test_cases! {
        test_parentheses: "(1 + 2)" => assert_parses,
    }

    // ============================================================
    // Section: List Literals (CEL Spec line 93)
    // ============================================================

    test_cases! {
        test_empty_list: "[]" => assert_parses,
        test_list_with_elements: "[1, 2, 3]" => assert_parses,
    }

    // ============================================================
    // Section: Reserved Words (CEL Spec lines 170-172)
    // ============================================================

    test_cases! {
        test_reserved_word_for: "for" => assert_parse_fails,
    }

    // ============================================================
    // Section: Complexity Limits
    // CEL spec (langdef.md lines 95-108) requires:
    // - 24-32 repetitions of repeating rules, we support unlimited width
    // - 12 repetitions of recursive rules, we support ~64 actual depth (128 delimiter count)
    // ============================================================

    #[test]
    fn test_complexity_limits_respected() {
        // 64 terms with || (within our doubled limit of spec's 32)
        let many_ors = (0..64).map(|_| "true").collect::<Vec<_>>().join(" || ");
        assert!(parse(&many_ors).is_ok(), "Should handle 64 OR terms");

        // 48 additions (within our doubled limit of spec's 24)
        let many_adds = (0..48)
            .map(|i| i.to_string())
            .collect::<Vec<_>>()
            .join(" + ");
        assert!(parse(&many_adds).is_ok(), "Should handle 48 additions");
    }

    #[test]
    fn test_pathological_inputs_handled() {
        // These should either parse successfully or fail gracefully (not stack overflow)

        // Very long identifier (should parse fine - no recursion)
        let long_id = "a".repeat(1000);
        let _ = parse(&long_id);

        // Moderately nested parentheses (128 levels - at our depth limit)
        let deep_parens = format!("{}1{}", "(".repeat(128), ")".repeat(128));
        assert!(
            parse(&deep_parens).is_ok(),
            "Should handle 128 nested parentheses"
        );
    }

    // ============================================================
    // Section: Nesting Depth Validation
    // CEL spec requires 12 recursive repetitions, we default to 128 delimiter count
    // (which allows ~64 actual nesting depth since we count both open and close)
    // ============================================================

    #[test]
    fn test_nesting_depth_limit_parentheses() {
        // 128 open parens should work (at limit)
        let at_limit = format!("{}1{}", "(".repeat(128), ")".repeat(128));
        assert!(parse(&at_limit).is_ok(), "Should accept 128 nested parens");

        // 129 open parens should fail
        let over_limit = format!("{}1{}", "(".repeat(129), ")".repeat(129));
        test_util::assert_error_contains(&over_limit, "Nesting depth");
        test_util::assert_error_contains(&over_limit, "exceeds maximum");
    }

    #[test]
    fn test_nesting_depth_limit_brackets() {
        // Test nested brackets (list indexing)
        let at_limit = format!("{}x{}", "[".repeat(128), "]".repeat(128));
        assert!(
            parse(&at_limit).is_ok(),
            "Should accept 128 nested brackets"
        );

        let over_limit = format!("{}x{}", "[".repeat(129), "]".repeat(129));
        assert!(
            parse(&over_limit).is_err(),
            "Should reject 129 nested brackets"
        );
    }

    #[test]
    fn test_nesting_depth_limit_braces() {
        // Test nested braces (map literals)
        // Use lists inside maps to avoid ternary operator parsing issues
        let at_limit = format!("{{1:{}}}", "[".repeat(127) + "x" + &"]".repeat(127));
        assert!(
            parse(&at_limit).is_ok(),
            "Should accept 128 total depth (1 brace + 127 brackets)"
        );

        let over_limit = format!("{{1:{}}}", "[".repeat(128) + "x" + &"]".repeat(128));
        assert!(
            parse(&over_limit).is_err(),
            "Should reject 129+ total depth (1 brace + 128 brackets)"
        );
    }

    #[test]
    fn test_nesting_depth_mixed_delimiters() {
        // Mixed delimiters should count toward total delimiter count
        let mixed = "(".repeat(64) + &"[".repeat(64) + "1" + &"]".repeat(64) + &")".repeat(64);
        assert!(
            parse(&mixed).is_ok(),
            "Should accept 128 total max depth (64 parens + 64 brackets)"
        );

        let mixed_over = "(".repeat(65) + &"[".repeat(64) + "1" + &"]".repeat(64) + &")".repeat(65);
        assert!(
            parse(&mixed_over).is_err(),
            "Should reject 129 total max depth (65 parens + 64 brackets)"
        );
    }
}
