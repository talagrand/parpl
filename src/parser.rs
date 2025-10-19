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
            max_nesting_depth: 50,
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
        NonZeroUsize::new(config.max_call_limit).unwrap_or(NonZeroUsize::new(10_000_000).unwrap()),
    ));

    // Pre-validate nesting depth to prevent stack overflow
    // Note: pest's set_call_limit only tracks total rule invocations, not stack depth
    // See: https://github.com/pest-parser/pest/issues/674
    validate_nesting_depth(input, config.max_nesting_depth)?;

    CelParser::parse(Rule::cel, input).map_err(Error::from)
}

/// Validate that input doesn't exceed maximum nesting depth
///
/// **CEL-RESTRICTED**: We limit nesting depth to 50 (spec requires 12 minimum).
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

    /// Test basic literal parsing
    /// CEL Spec (line 147-148): Literals
    #[test]
    fn test_int_literals() {
        assert!(parse("42").is_ok());
        assert!(parse("-17").is_ok());
        assert!(parse("0").is_ok());
    }

    #[test]
    fn test_hex_int_literals() {
        assert!(parse("0x1A").is_ok());
        assert!(parse("0xFF").is_ok());
        assert!(parse("-0x10").is_ok());
        assert!(parse("0X2B").is_ok());
    }

    #[test]
    fn test_negative_integer() {
        let result = parse("-42");
        assert!(
            result.is_ok(),
            "Failed to parse negative integer: {:?}",
            result
        );
    }

    #[test]
    fn test_uint_literal() {
        let result = parse("42u");
        assert!(result.is_ok(), "Failed to parse uint literal: {:?}", result);
    }

    #[test]
    fn test_float_literal() {
        let result = parse("3.14");
        assert!(
            result.is_ok(),
            "Failed to parse float literal: {:?}",
            result
        );
    }

    #[test]
    fn test_string_literals() {
        assert!(parse(r#""hello""#).is_ok());
        assert!(parse("'world'").is_ok());
        assert!(parse(r#"r"raw""#).is_ok());
        assert!(parse("R'raw'").is_ok());
    }

    #[test]
    fn test_triple_quoted_strings() {
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

    #[test]
    fn test_bool_literal_true() {
        let result = parse("true");
        assert!(result.is_ok(), "Failed to parse bool literal: {:?}", result);
    }

    #[test]
    fn test_bool_literal_false() {
        let result = parse("false");
        assert!(result.is_ok(), "Failed to parse bool literal: {:?}", result);
    }

    #[test]
    fn test_null_literal() {
        let result = parse("null");
        assert!(result.is_ok(), "Failed to parse null literal: {:?}", result);
    }

    /// Test arithmetic operations
    /// CEL Spec (lines 81-82): Addition and Multiplication
    #[test]
    fn test_addition() {
        let result = parse("1 + 2");
        assert!(result.is_ok(), "Failed to parse addition: {:?}", result);
    }

    #[test]
    fn test_multiplication() {
        let result = parse("3 * 4");
        assert!(
            result.is_ok(),
            "Failed to parse multiplication: {:?}",
            result
        );
    }

    #[test]
    fn test_complex_arithmetic() {
        let result = parse("1 + 2 * 3");
        assert!(
            result.is_ok(),
            "Failed to parse complex arithmetic: {:?}",
            result
        );
    }

    /// Test logical operations
    /// CEL Spec (lines 77-78): ConditionalOr and ConditionalAnd
    #[test]
    fn test_logical_and() {
        let result = parse("true && false");
        assert!(result.is_ok(), "Failed to parse logical AND: {:?}", result);
    }

    #[test]
    fn test_logical_or() {
        let result = parse("true || false");
        assert!(result.is_ok(), "Failed to parse logical OR: {:?}", result);
    }

    /// Test ternary operator
    /// CEL Spec (line 76): Expr with conditional
    #[test]
    fn test_ternary() {
        let result = parse("true ? 1 : 2");
        assert!(result.is_ok(), "Failed to parse ternary: {:?}", result);
    }

    /// Test parenthesized expressions
    /// CEL Spec (line 92): Primary with parentheses
    #[test]
    fn test_parentheses() {
        let result = parse("(1 + 2)");
        assert!(
            result.is_ok(),
            "Failed to parse parenthesized expr: {:?}",
            result
        );
    }

    /// Test list literals
    /// CEL Spec (line 93): List literal
    #[test]
    fn test_empty_list() {
        let result = parse("[]");
        assert!(result.is_ok(), "Failed to parse empty list: {:?}", result);
    }

    #[test]
    fn test_list_with_elements() {
        let result = parse("[1, 2, 3]");
        assert!(result.is_ok(), "Failed to parse list: {:?}", result);
    }

    /// Test that reserved words are rejected as identifiers
    /// CEL Spec (lines 170-172): Reserved words
    #[test]
    fn test_reserved_word_rejection() {
        // "for" is a reserved word and should not parse as an identifier
        let result = parse("for");
        assert!(
            result.is_err(),
            "Reserved word 'for' should not parse as identifier"
        );
    }

    /// Tests that we can handle expressions within the doubled CEL spec limits
    /// CEL spec (langdef.md lines 95-108) requires:
    /// - 24-32 repetitions of repeating rules, we support 48-64
    /// - 12 repetitions of recursive rules, we support 24
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

        // Moderately nested parentheses (50 levels - at our depth limit)
        // Note: Pest's call limit prevents timeout, not stack overflow from deep recursion
        // Deep recursion is inherent to recursive descent parsers
        let deep_parens = format!("{}1{}", "(".repeat(50), ")".repeat(50));
        assert!(
            parse(&deep_parens).is_ok(),
            "Should handle 50 nested parentheses"
        );
    }

    /// Test nesting depth validation
    /// CEL spec requires 12 recursive repetitions, we support 50
    #[test]
    fn test_nesting_depth_limit_parentheses() {
        // 50 nested parens should work (at limit)
        let at_limit = format!("{}1{}", "(".repeat(50), ")".repeat(50));
        assert!(parse(&at_limit).is_ok(), "Should accept 50 nested parens");

        // 51 nested parens should fail
        let over_limit = format!("{}1{}", "(".repeat(51), ")".repeat(51));
        let result = parse(&over_limit);
        assert!(result.is_err(), "Should reject 51 nested parens");

        if let Err(e) = result {
            let msg = format!("{}", e);
            assert!(
                msg.contains("Nesting depth") && msg.contains("exceeds maximum"),
                "Error should mention nesting depth: {}",
                msg
            );
        }
    }

    #[test]
    fn test_nesting_depth_limit_brackets() {
        // Test nested brackets (list indexing)
        let at_limit = format!("{}x{}", "[".repeat(50), "]".repeat(50));
        assert!(parse(&at_limit).is_ok(), "Should accept 50 nested brackets");

        let over_limit = format!("{}x{}", "[".repeat(51), "]".repeat(51));
        assert!(
            parse(&over_limit).is_err(),
            "Should reject 51 nested brackets"
        );
    }

    #[test]
    fn test_nesting_depth_limit_braces() {
        // Test nested braces (map literals)
        // Use lists inside maps to avoid ternary operator parsing issues
        let at_limit = format!("{{1:{}}}", "[".repeat(49) + "x" + &"]".repeat(49));
        assert!(
            parse(&at_limit).is_ok(),
            "Should accept 50 total nesting depth (1 brace + 49 brackets)"
        );

        let over_limit = format!("{{1:{}}}", "[".repeat(50) + "x" + &"]".repeat(50));
        assert!(
            parse(&over_limit).is_err(),
            "Should reject 51 total nesting depth (1 brace + 50 brackets)"
        );
    }

    #[test]
    fn test_nesting_depth_mixed_delimiters() {
        // Mixed delimiters should count toward total depth
        let mixed = "(".repeat(25) + &"[".repeat(25) + "1" + &"]".repeat(25) + &")".repeat(25);
        assert!(
            parse(&mixed).is_ok(),
            "Should accept 50 total nesting depth"
        );

        let mixed_over = "(".repeat(26) + &"[".repeat(25) + "1" + &"]".repeat(25) + &")".repeat(26);
        assert!(
            parse(&mixed_over).is_err(),
            "Should reject 51 total nesting depth"
        );
    }
}
