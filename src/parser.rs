// CEL Parser
//
// This module handles parsing CEL expressions using the pest PEG parser.
// It includes complexity protection against stack overflow and timeout attacks.

use crate::error::{Error, Result};
use pest::Parser;
use pest_derive::Parser;
use std::num::NonZeroUsize;

#[derive(Parser)]
#[grammar = "grammar.pest"]
pub struct CelParser;

pub use pest::iterators::Pairs;

/// Configuration for parsing CEL expressions
#[derive(Debug, Clone, Copy)]
pub struct ParseConfig {
    /// Maximum nesting depth (parentheses, brackets, braces)
    pub max_nesting_depth: usize,
    /// Maximum number of rule invocations (pest call limit)
    pub max_call_limit: usize,
}

impl Default for ParseConfig {
    fn default() -> Self {
        Self {
            max_nesting_depth: crate::constants::DEFAULT_MAX_RECURSION_DEPTH,
            max_call_limit: 10_000_000,
        }
    }
}

/// Parse a CEL expression from a string with default configuration
///
/// This parser enforces complexity limits to prevent stack overflow and excessive
/// execution time on malicious inputs. The limits are set to double the minimum
/// requirements specified in the CEL specification (langdef.md lines 95-108).
///
/// **CEL Spec Requirements (doubled for generosity):**
/// - Repeating rules: 48-64 repetitions (spec requires 24-32)
/// - Recursive rules: 24 repetitions (spec requires 12)
///
/// **Complexity Protection:**
/// - Pest tracks the **total number of rule invocations** (not stack depth)
/// - Limit set to 10 million total rule calls across the entire parse
/// - Prevents timeout/DoS attacks
/// - **Stack depth** is enforced by pre-parse validation (count nesting)
///
/// # Examples
/// ```
/// use cello::parse;
///
/// let result = parse("1 + 2");
/// assert!(result.is_ok());
/// ```
pub fn parse(input: &str) -> Result<Pairs<'_, Rule>> {
    parse_with_config(input, ParseConfig::default())
}

/// Parse a CEL expression from a string with custom configuration
///
/// This allows you to customize the complexity limits for parsing.
/// Use this when you need different limits than the defaults.
///
/// # Examples
/// ```
/// use cello::parser::{parse_with_config, ParseConfig};
///
/// let config = ParseConfig {
///     max_nesting_depth: 100,
///     max_call_limit: 1_000_000,
/// };
/// let result = parse_with_config("1 + 2", config);
/// assert!(result.is_ok());
/// ```
pub fn parse_with_config(input: &str, config: ParseConfig) -> Result<Pairs<'_, Rule>> {
    // Set call limit to prevent timeouts (langdef.md lines 95-108)
    // Pest tracks TOTAL rule invocations (not stack depth) across the entire parse.
    // CEL spec requires supporting at least:
    // - 24-32 repetitions of repeating rules (we support 48-64)
    // - 12 repetitions of recursive rules (we support 24)
    pest::set_call_limit(Some(
        NonZeroUsize::new(config.max_call_limit).unwrap_or_else(|| {
            NonZeroUsize::new(10_000_000).expect("10_000_000 is non-zero and a valid call limit")
        }),
    ));

    // Pre-validate nesting depth to prevent stack overflow
    // Note: pest's set_call_limit only tracks total rule invocations, not stack depth
    // See: https://github.com/pest-parser/pest/issues/674
    validate_nesting_depth(input, config.max_nesting_depth)?;

    CelParser::parse(Rule::cel, input).map_err(Error::from)
}

/// Validate that input doesn't exceed maximum nesting depth
///
/// Default limit: 24 (2x CEL spec minimum of 12, per langdef.md line 107).
/// This prevents stack overflow from deeply nested parentheses, brackets, or
/// ternary expressions.
///
/// Pest's `set_call_limit` only tracks total rule invocations, not recursion depth.
/// Manual depth validation is required to prevent stack overflow.
/// See: https://github.com/pest-parser/pest/issues/674
///
/// Counts:
/// - Parentheses: `(((expr)))`
/// - Brackets: `[[[expr]]]`
/// - Braces: `{{{expr}}}`
///
/// Returns an error if depth exceeds `max_depth`.
fn validate_nesting_depth(input: &str, max_depth: usize) -> Result<()> {
    let mut depth = 0;

    for ch in input.chars() {
        match ch {
            '(' | '[' | '{' => {
                depth += 1;
                if depth > max_depth {
                    return Err(Error::nesting_depth(depth, max_depth));
                }
            }
            ')' | ']' | '}' => {
                depth = depth.saturating_sub(1);
            }
            _ => {}
        }
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
            assert!(result.is_ok(), "Failed to parse '{}': {:?}", input, result);
        }

        pub fn assert_parse_fails(input: &str) {
            let result = parse(input);
            assert!(result.is_err(), "Expected '{}' to fail parsing", input);
        }

        pub fn assert_error_contains(input: &str, expected: &str) {
            match parse(input) {
                Err(e) => {
                    let msg = format!("{}", e);
                    assert!(
                        msg.contains(expected),
                        "Error message '{}' should contain '{}'",
                        msg,
                        expected
                    );
                }
                Ok(_) => panic!("Expected '{}' to fail, but it parsed successfully", input),
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
        assert!(parse(
            r#""""multi
line
string""""#
        )
        .is_ok());
        assert!(parse(
            r"'''another
multi-line'''"
        )
        .is_ok());
        assert!(parse(
            r#"r"""raw multi
line""""#
        )
        .is_ok());
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
    // - 24-32 repetitions of repeating rules, we support 48-64
    // - 12 repetitions of recursive rules, we support 24
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

        // Moderately nested parentheses (24 levels - at our depth limit)
        let deep_parens = format!("{}1{}", "(".repeat(24), ")".repeat(24));
        assert!(
            parse(&deep_parens).is_ok(),
            "Should handle 24 nested parentheses"
        );
    }

    // ============================================================
    // Section: Nesting Depth Validation
    // CEL spec requires 12 recursive repetitions, we default to 24 (2x)
    // ============================================================

    #[test]
    fn test_nesting_depth_limit_parentheses() {
        // 24 nested parens should work (at limit)
        let at_limit = format!("{}1{}", "(".repeat(24), ")".repeat(24));
        assert!(parse(&at_limit).is_ok(), "Should accept 24 nested parens");

        // 25 nested parens should fail
        let over_limit = format!("{}1{}", "(".repeat(25), ")".repeat(25));
        test_util::assert_error_contains(&over_limit, "Nesting depth");
        test_util::assert_error_contains(&over_limit, "exceeds maximum");
    }

    #[test]
    fn test_nesting_depth_limit_brackets() {
        // Test nested brackets (list indexing)
        let at_limit = format!("{}x{}", "[".repeat(24), "]".repeat(24));
        assert!(parse(&at_limit).is_ok(), "Should accept 24 nested brackets");

        let over_limit = format!("{}x{}", "[".repeat(25), "]".repeat(25));
        assert!(
            parse(&over_limit).is_err(),
            "Should reject 25 nested brackets"
        );
    }

    #[test]
    fn test_nesting_depth_limit_braces() {
        // Test nested braces (map literals)
        // Use lists inside maps to avoid ternary operator parsing issues
        let at_limit = format!("{{1:{}}}", "[".repeat(23) + "x" + &"]".repeat(23));
        assert!(
            parse(&at_limit).is_ok(),
            "Should accept 24 total nesting depth (1 brace + 23 brackets)"
        );

        let over_limit = format!("{{1:{}}}", "[".repeat(24) + "x" + &"]".repeat(24));
        assert!(
            parse(&over_limit).is_err(),
            "Should reject 25 total nesting depth (1 brace + 24 brackets)"
        );
    }

    #[test]
    fn test_nesting_depth_mixed_delimiters() {
        // Mixed delimiters should count toward total depth
        let mixed = "(".repeat(12) + &"[".repeat(12) + "1" + &"]".repeat(12) + &")".repeat(12);
        assert!(
            parse(&mixed).is_ok(),
            "Should accept 24 total nesting depth"
        );

        let mixed_over = "(".repeat(26) + &"[".repeat(25) + "1" + &"]".repeat(25) + &")".repeat(26);
        assert!(
            parse(&mixed_over).is_err(),
            "Should reject 51 total nesting depth"
        );
    }
}
