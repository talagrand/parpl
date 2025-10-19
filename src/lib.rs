// Cello: A fully conformant CEL (Common Expression Language) parser

use pest::Parser;
use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "grammar.pest"]
pub struct CelParser;

/// Parse a CEL expression from a string
///
/// CEL Spec: Entry point for parsing complete CEL expressions
///
/// # Examples
/// ```
/// use cello::parse;
/// 
/// let result = parse("1 + 2");
/// assert!(result.is_ok());
/// ```
pub fn parse(input: &str) -> Result<pest::iterators::Pairs<'_, Rule>, pest::error::Error<Rule>> {
    CelParser::parse(Rule::cel, input)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Test basic literal parsing
    /// CEL Spec (line 147-148): Literals
    #[test]
    fn test_integer_literal() {
        let result = parse("42");
        assert!(result.is_ok(), "Failed to parse integer literal: {:?}", result);
    }

    #[test]
    fn test_negative_integer() {
        let result = parse("-42");
        assert!(result.is_ok(), "Failed to parse negative integer: {:?}", result);
    }

    #[test]
    fn test_uint_literal() {
        let result = parse("42u");
        assert!(result.is_ok(), "Failed to parse uint literal: {:?}", result);
    }

    #[test]
    fn test_float_literal() {
        let result = parse("3.14");
        assert!(result.is_ok(), "Failed to parse float literal: {:?}", result);
    }

    #[test]
    fn test_string_literal() {
        let result = parse("\"hello\"");
        assert!(result.is_ok(), "Failed to parse string literal: {:?}", result);
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
        assert!(result.is_ok(), "Failed to parse multiplication: {:?}", result);
    }

    #[test]
    fn test_complex_arithmetic() {
        let result = parse("1 + 2 * 3");
        assert!(result.is_ok(), "Failed to parse complex arithmetic: {:?}", result);
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
        assert!(result.is_ok(), "Failed to parse parenthesized expr: {:?}", result);
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
        assert!(result.is_err(), "Reserved word 'for' should not parse as identifier");
    }
}
