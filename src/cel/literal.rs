// Literal value processing for CEL
//
// This module handles the conversion of raw literal strings from the parser
// into processed literal values. This includes:
// - Parsing integer literals (decimal and hexadecimal)
// - Parsing floating-point literals
// - Processing escape sequences in strings and bytes
// - Validating Unicode code points
//
// **CEL Spec Reference**: langdef.md lines 143-161 (literal grammar)
// **CEL Spec Reference**: langdef.md lines 156-159 (escape sequences)
// **CEL Spec Reference**: langdef.md lines 270-360 (string/bytes semantics)

use crate::{
    Interner,
    cel::traits::CelWriter,
    cel::{
        ast::{Literal, RawLiteral},
        error::{Error, Result},
    },
};

//==============================================================================
// Common Escape Processing
//==============================================================================

/// Simple escape lookup table for common escape sequences.
/// CEL Spec (langdef.md line 156, lines 305-317)
const SIMPLE_ESCAPES: &[(char, char)] = &[
    // Punctuation escapes
    ('\\', '\\'),
    ('?', '?'),
    ('"', '"'),
    ('\'', '\''),
    ('`', '`'),
    // Whitespace escapes
    ('a', '\x07'), // bell
    ('b', '\x08'), // backspace
    ('f', '\x0C'), // form feed
    ('n', '\n'),   // line feed
    ('r', '\r'),   // carriage return
    ('t', '\t'),   // horizontal tab
    ('v', '\x0B'), // vertical tab
];

/// Lookup a simple escape sequence.
#[inline]
fn simple_escape(ch: char) -> Option<char> {
    SIMPLE_ESCAPES
        .iter()
        .find(|(from, _)| *from == ch)
        .map(|(_, to)| *to)
}

/// Validate that a Unicode code point is not a UTF-16 surrogate.
/// CEL Spec (langdef.md lines 347-348)
#[inline]
fn validate_unicode_codepoint(code_point: u32) -> Result<char> {
    if (0xD800..=0xDFFF).contains(&code_point) {
        return Err(Error::invalid_escape(format!(
            "UTF-16 surrogate code point not allowed: U+{code_point:04X}"
        )));
    }
    char::from_u32(code_point).ok_or_else(|| {
        Error::invalid_escape(format!("invalid Unicode code point: U+{code_point:08X}"))
    })
}

/// Process a hex escape sequence (\xHH or \XHH).
/// Returns the code point value (0-255 for valid hex escapes).
/// CEL Spec (langdef.md line 158, lines 325-326)
fn process_hex_escape(chars: &mut std::str::Chars) -> Result<u32> {
    let hex = collect_hex_digits(chars, 2)?;
    u32::from_str_radix(&hex, 16)
        .map_err(|_| Error::invalid_escape(format!("invalid hex escape: \\x{hex}")))
}

/// Process a short Unicode escape sequence (\uHHHH).
/// Returns a validated Unicode character.
/// CEL Spec (langdef.md line 157, lines 318-319)
fn process_unicode_short_escape(chars: &mut std::str::Chars) -> Result<char> {
    let hex = collect_hex_digits(chars, 4)?;
    let code_point = u32::from_str_radix(&hex, 16)
        .map_err(|_| Error::invalid_escape(format!("invalid unicode escape: \\u{hex}")))?;
    validate_unicode_codepoint(code_point)
}

/// Process a long Unicode escape sequence (\UHHHHHHHH).
/// Returns a validated Unicode character.
/// CEL Spec (langdef.md line 157, lines 320-321)
fn process_unicode_long_escape(chars: &mut std::str::Chars) -> Result<char> {
    let hex = collect_hex_digits(chars, 8)?;
    let code_point = u32::from_str_radix(&hex, 16)
        .map_err(|_| Error::invalid_escape(format!("invalid unicode escape: \\U{hex}")))?;
    validate_unicode_codepoint(code_point)
}

/// Process an octal escape sequence (\OOO).
/// Returns the byte value (0-255).
/// CEL Spec (langdef.md line 159, lines 327-328)
fn process_octal_escape(chars: &mut std::str::Chars, first_digit: char) -> Result<u8> {
    let mut octal = String::with_capacity(3);
    octal.push(first_digit);

    octal.push(
        chars
            .next()
            .ok_or_else(|| Error::invalid_escape("incomplete octal escape sequence".to_string()))?,
    );

    octal.push(
        chars
            .next()
            .ok_or_else(|| Error::invalid_escape("incomplete octal escape sequence".to_string()))?,
    );

    let value = u32::from_str_radix(&octal, 8)
        .map_err(|_| Error::invalid_escape(format!("invalid octal escape: \\{octal}")))?;

    if value > 255 {
        return Err(Error::invalid_escape(format!(
            "octal escape out of range: \\{octal}"
        )));
    }

    Ok(value as u8)
}

/// Helper: Collect exactly `count` hexadecimal digits from the iterator.
fn collect_hex_digits(chars: &mut std::str::Chars, count: usize) -> Result<String> {
    let mut result = String::with_capacity(count);
    for _ in 0..count {
        let ch = chars.next().ok_or_else(|| {
            Error::invalid_escape(format!(
                "incomplete hex escape sequence, expected {count} digits"
            ))
        })?;
        if !ch.is_ascii_hexdigit() {
            return Err(Error::invalid_escape(format!("invalid hex digit: {ch}")));
        }
        result.push(ch);
    }
    Ok(result)
}

//==============================================================================
// Number Parsing
//==============================================================================

/// Process a raw integer literal string into an i64 value.
///
/// CEL Spec (langdef.md line 144): INT_LIT ::= -? DIGIT+ | -? 0x HEXDIGIT+
///
/// Supports:
/// - Decimal: "123", "-456"
/// - Hexadecimal: "0xFF", "-0x10"
///
/// This is **fully conformant** with the CEL spec - only decimal and hex are defined.
/// Overflow checking ensures values fit in i64 range (spec requires overflow errors).
pub fn parse_int(s: &str) -> Result<i64> {
    // Handle negative sign
    let (negative, s) = if let Some(rest) = s.strip_prefix('-') {
        (true, rest)
    } else {
        (false, s)
    };

    // Parse based on prefix
    let abs_value = if let Some(hex) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) {
        // Hexadecimal
        i64::from_str_radix(hex, 16)
            .map_err(|_| Error::syntax(format!("Invalid integer literal: {s}"), 0))?
    } else {
        // Decimal
        s.parse::<i64>()
            .map_err(|_| Error::syntax(format!("Invalid integer literal: {s}"), 0))?
    };

    // Apply sign
    if negative {
        abs_value
            .checked_neg()
            .ok_or_else(|| Error::syntax(format!("Integer overflow: -{s}"), 0))
    } else {
        Ok(abs_value)
    }
}

/// Process a raw unsigned integer literal string into a u64 value.
///
/// CEL Spec (langdef.md line 145): UINT_LIT ::= INT_LIT [uU]
///
/// Note: The 'u' or 'U' suffix should already be stripped by the parser.
///
/// Supports:
/// - Decimal: "123", "456"
/// - Hexadecimal: "0xFF", "0x10"
///
/// This is **fully conformant** with the CEL spec - only decimal and hex are defined.
/// Overflow checking ensures values fit in u64 range (spec requires overflow errors).
pub fn parse_uint(s: &str) -> Result<u64> {
    // Parse based on prefix
    if let Some(hex) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) {
        // Hexadecimal
        u64::from_str_radix(hex, 16)
            .map_err(|_| Error::syntax(format!("Invalid unsigned integer literal: {s}"), 0))
    } else {
        // Decimal
        s.parse::<u64>()
            .map_err(|_| Error::syntax(format!("Invalid unsigned integer literal: {s}"), 0))
    }
}

/// Process a raw floating-point literal string into an f64 value.
///
/// CEL Spec (langdef.md line 146): FLOAT_LIT ::= -? DIGIT* . DIGIT+ EXPONENT? | -? DIGIT+ EXPONENT
///
/// Examples: "3.14", "-2.5e10", "1e-5", ".5"
///
/// This is **fully conformant** with the CEL spec.
/// Rust's f64::parse implements IEEE 754 double-precision parsing, matching CEL requirements.
/// CEL spec (line 248): "CEL supports...64-bit IEEE double-precision floating-point"
/// CEL spec (line 1101): "The double type follows the IEEE 754 standard"
pub fn parse_float(s: &str) -> Result<f64> {
    s.parse::<f64>()
        .map_err(|_| Error::syntax(format!("Invalid floating-point literal: {s}"), 0))
}

//==============================================================================
// String and Bytes Escape Processing
//==============================================================================

/// Process escape sequences in a string literal.
///
/// CEL Spec (langdef.md lines 156-159): ESCAPE grammar
/// CEL Spec (langdef.md lines 300-328): Escape sequence semantics
///
/// Handles:
/// - Simple escapes: \n, \t, \r, etc.
/// - Hex escapes: \xHH (2 hex digits) → Unicode code point
/// - Unicode escapes: \uHHHH (4 hex digits) → BMP code point
/// - Unicode escapes: \UHHHHHHHH (8 hex digits) → any code point
/// - Octal escapes: \OOO (3 octal digits, 000-377) → Unicode code point
///
/// Returns the processed string allocated in the arena.
///
/// This is **fully conformant** with the CEL spec.
/// CEL Spec (line 347): Invalid Unicode code points are rejected
/// CEL Spec (line 348): UTF-16 surrogate code points are rejected (even in valid pairs)
pub fn process_string_escapes<W: CelWriter>(s: &str, writer: &mut W) -> Result<W::StringId> {
    // Fast path: no escapes
    if !s.contains('\\') {
        return Ok(writer.interner().intern(s));
    }

    let mut result = String::with_capacity(s.len());
    let mut chars = s.chars();

    while let Some(ch) = chars.next() {
        if ch != '\\' {
            result.push(ch);
            continue;
        }

        // Process escape sequence
        let next = chars.next().ok_or_else(|| {
            Error::invalid_escape("incomplete escape sequence at end of string".to_string())
        })?;

        // Try simple escapes first
        if let Some(escaped) = simple_escape(next) {
            result.push(escaped);
            continue;
        }

        // Complex escapes
        match next {
            'x' | 'X' => {
                let code_point = process_hex_escape(&mut chars)?;
                let ch = validate_unicode_codepoint(code_point)?;
                result.push(ch);
            }
            'u' => {
                let ch = process_unicode_short_escape(&mut chars)?;
                result.push(ch);
            }
            'U' => {
                let ch = process_unicode_long_escape(&mut chars)?;
                result.push(ch);
            }
            '0'..='3' => {
                let byte_value = process_octal_escape(&mut chars, next)?;
                let ch = validate_unicode_codepoint(byte_value as u32)?;
                result.push(ch);
            }
            _ => {
                return Err(Error::invalid_escape(format!(
                    "invalid escape sequence: \\{next}"
                )));
            }
        }
    }

    Ok(writer.interner().intern(&result))
}

/// Process escape sequences in a bytes literal.
///
/// Similar to string escapes but octal and \xHH sequences represent byte values,
/// not Unicode code points.
///
/// CEL Spec (langdef.md lines 271): "Bytes are arbitrary sequences of octets"
/// CEL Spec (langdef.md lines 296-298): Octal escapes as octet values
/// CEL Spec (langdef.md lines 318, 320): \x and octal escapes represent octet values for bytes
///
/// Returns the processed bytes allocated in the arena.
/// **IMPORTANT**: Result may contain invalid UTF-8, which is correct per spec!
pub fn process_bytes_escapes<W: CelWriter>(s: &str, writer: &mut W) -> Result<W::Bytes> {
    // Fast path: no escapes - just convert UTF-8 string to bytes
    if !s.contains('\\') {
        return Ok(writer.bytes(s.as_bytes()));
    }

    let mut result = Vec::with_capacity(s.len());
    let mut chars = s.chars();

    while let Some(ch) = chars.next() {
        if ch != '\\' {
            // Regular UTF-8 character - add its bytes
            let mut buf = [0u8; 4];
            let bytes = ch.encode_utf8(&mut buf).as_bytes();
            result.extend_from_slice(bytes);
            continue;
        }

        // Process escape sequence
        let next = chars.next().ok_or_else(|| {
            Error::invalid_escape("incomplete escape sequence at end of bytes literal".to_string())
        })?;

        // Try simple escapes first (as ASCII bytes)
        if let Some(escaped) = simple_escape(next) {
            result.push(escaped as u8);
            continue;
        }

        // Complex escapes
        match next {
            // Hex escape: \xHH - represents a BYTE value (not a Unicode code point!)
            // CEL Spec line 318: "For bytes, it represents an octet value."
            'x' | 'X' => {
                let byte_value = process_hex_escape(&mut chars)? as u8;
                result.push(byte_value);
            }
            // Unicode escapes: converted to UTF-8 bytes
            'u' => {
                let ch = process_unicode_short_escape(&mut chars)?;
                let mut buf = [0u8; 4];
                let bytes = ch.encode_utf8(&mut buf).as_bytes();
                result.extend_from_slice(bytes);
            }
            'U' => {
                let ch = process_unicode_long_escape(&mut chars)?;
                let mut buf = [0u8; 4];
                let bytes = ch.encode_utf8(&mut buf).as_bytes();
                result.extend_from_slice(bytes);
            }
            // Octal escape: \OOO - represents a BYTE value
            // CEL Spec line 320: "For bytes, it represents an octet value."
            '0'..='3' => {
                let byte_value = process_octal_escape(&mut chars, next)?;
                result.push(byte_value);
            }
            _ => {
                return Err(Error::invalid_escape(format!(
                    "invalid escape sequence: \\{next}"
                )));
            }
        }
    }

    // Allocate bytes in the arena
    // No UTF-8 validation - bytes can contain arbitrary octet sequences!
    Ok(writer.bytes(&result))
}

//==============================================================================
// Main Entry Point
//==============================================================================

/// Process a raw literal into a fully processed literal.
///
/// This is called during AST construction to convert parser output into
/// validated, processed literal values.
///
/// For strings and bytes:
/// - If `is_raw` is true, no escape processing is performed
/// - If `is_raw` is false, escape sequences are processed
/// - String interning happens AFTER processing (not before)
///
/// For numbers:
/// - Parse and validate the numeric format directly from borrowed input
/// - Check for overflow
///
/// Returns a `Literal` with all values parsed and validated.
pub fn process_literal<W: CelWriter>(
    raw: &RawLiteral<'_>,
    writer: &mut W,
) -> Result<Literal<W::StringId, W::Bytes>> {
    match raw {
        RawLiteral::Int(s) => {
            let value = parse_int(s)?;
            Ok(Literal::Int(value))
        }
        RawLiteral::UInt(s) => {
            let value = parse_uint(s)?;
            Ok(Literal::UInt(value))
        }
        RawLiteral::Float(s) => {
            let value = parse_float(s)?;
            Ok(Literal::Float(value))
        }
        RawLiteral::String(content, is_raw, _quote_style) => {
            if *is_raw {
                // Raw strings: no escape processing, intern directly
                Ok(Literal::String(writer.interner().intern(content)))
            } else {
                // Process escape sequences, then intern the result
                let processed = process_string_escapes(content, writer)?;
                Ok(Literal::String(processed))
            }
        }
        RawLiteral::Bytes(content, is_raw, _quote_style) => {
            if *is_raw {
                // Raw bytes: no escape processing, just convert string to bytes
                Ok(Literal::Bytes(writer.bytes(content.as_bytes())))
            } else {
                // Process escape sequences
                let processed = process_bytes_escapes(content, writer)?;
                Ok(Literal::Bytes(processed))
            }
        }
        RawLiteral::Bool(b) => Ok(Literal::Bool(*b)),
        RawLiteral::Null => Ok(Literal::Null),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cel::ast::QuoteStyle;
    use crate::{Interner, Span, StringPool, StringPoolId};
    use bumpalo::Bump;

    struct TestContext {
        arena: Bump,
        interner: StringPool,
    }

    impl Default for TestContext {
        fn default() -> Self {
            Self {
                arena: Bump::new(),
                interner: StringPool::default(),
            }
        }
    }

    struct TestWriter<'a> {
        arena: &'a Bump,
        interner: &'a mut StringPool,
    }

    impl<'a> CelWriter for TestWriter<'a> {
        type StringId = StringPoolId;
        type Interner = StringPool;
        type Bytes = &'a [u8];
        type Expr = ();
        type Error = ();

        fn interner(&mut self) -> &mut Self::Interner {
            self.interner
        }
        fn interner_ref(&self) -> &Self::Interner {
            self.interner
        }
        fn bytes(&mut self, bytes: &[u8]) -> Self::Bytes {
            self.arena.alloc_slice_copy(bytes)
        }
        fn literal(
            &mut self,
            _lit: Literal<Self::StringId, Self::Bytes>,
            _span: Span,
        ) -> std::result::Result<Self::Expr, Self::Error> {
            Ok(())
        }
        fn ident(
            &mut self,
            _name: Self::StringId,
            _span: Span,
        ) -> std::result::Result<Self::Expr, Self::Error> {
            Ok(())
        }
        fn unary(
            &mut self,
            _op: crate::cel::ast::UnaryOp,
            _operand: Self::Expr,
            _span: Span,
        ) -> std::result::Result<Self::Expr, Self::Error> {
            Ok(())
        }
        fn binary(
            &mut self,
            _op: crate::cel::ast::BinaryOp,
            _left: Self::Expr,
            _right: Self::Expr,
            _span: Span,
        ) -> std::result::Result<Self::Expr, Self::Error> {
            Ok(())
        }
        fn ternary(
            &mut self,
            _cond: Self::Expr,
            _true_expr: Self::Expr,
            _false_expr: Self::Expr,
            _span: Span,
        ) -> std::result::Result<Self::Expr, Self::Error> {
            Ok(())
        }
        fn member(
            &mut self,
            _target: Self::Expr,
            _field: Self::StringId,
            _args: Option<&[Self::Expr]>,
            _span: Span,
        ) -> std::result::Result<Self::Expr, Self::Error> {
            Ok(())
        }
        fn index(
            &mut self,
            _target: Self::Expr,
            _index: Self::Expr,
            _span: Span,
        ) -> std::result::Result<Self::Expr, Self::Error> {
            Ok(())
        }
        fn call(
            &mut self,
            _target: Option<Self::Expr>,
            _function: Self::StringId,
            _args: &[Self::Expr],
            _span: Span,
        ) -> std::result::Result<Self::Expr, Self::Error> {
            Ok(())
        }
        fn list(
            &mut self,
            _items: &[Self::Expr],
            _span: Span,
        ) -> std::result::Result<Self::Expr, Self::Error> {
            Ok(())
        }
        fn map(
            &mut self,
            _entries: &[(Self::Expr, Self::Expr)],
            _span: Span,
        ) -> std::result::Result<Self::Expr, Self::Error> {
            Ok(())
        }
        fn structure(
            &mut self,
            _type_name: Option<Self::Expr>,
            _fields: &[Self::StringId],
            _values: &[(Self::StringId, Self::Expr)],
            _span: Span,
        ) -> std::result::Result<Self::Expr, Self::Error> {
            Ok(())
        }
    }

    impl TestContext {
        fn writer(&mut self) -> TestWriter<'_> {
            TestWriter {
                arena: &self.arena,
                interner: &mut self.interner,
            }
        }
    }

    #[test]
    fn test_parse_int_decimal() {
        assert_eq!(parse_int("0").unwrap(), 0);
        assert_eq!(parse_int("123").unwrap(), 123);
        assert_eq!(parse_int("-456").unwrap(), -456);
    }

    #[test]
    fn test_parse_int_hex() {
        assert_eq!(parse_int("0xFF").unwrap(), 255);
        assert_eq!(parse_int("0x10").unwrap(), 16);
        assert_eq!(parse_int("-0xA").unwrap(), -10);
    }

    #[test]
    fn test_parse_uint() {
        assert_eq!(parse_uint("0").unwrap(), 0);
        assert_eq!(parse_uint("123").unwrap(), 123);
        assert_eq!(parse_uint("0xFF").unwrap(), 255);
    }

    #[test]
    fn test_parse_float() {
        assert_eq!(parse_float("1.234").unwrap(), 1.234);
        assert_eq!(parse_float("-2.5").unwrap(), -2.5);
        assert_eq!(parse_float("1e10").unwrap(), 1e10);
        assert_eq!(parse_float(".5").unwrap(), 0.5);
    }

    #[test]
    fn test_string_escapes_simple() {
        let mut ctx = TestContext::default();

        let id = process_string_escapes("hello\\nworld", &mut ctx.writer()).unwrap();
        assert_eq!(ctx.interner.resolve(&id).unwrap(), "hello\nworld");

        let id = process_string_escapes("tab\\there", &mut ctx.writer()).unwrap();
        assert_eq!(ctx.interner.resolve(&id).unwrap(), "tab\there");

        let id = process_string_escapes("quote\\\"test", &mut ctx.writer()).unwrap();
        assert_eq!(ctx.interner.resolve(&id).unwrap(), "quote\"test");
    }

    #[test]
    fn test_string_escapes_hex() {
        let mut ctx = TestContext::default();

        let id = process_string_escapes("\\x41", &mut ctx.writer()).unwrap();
        assert_eq!(ctx.interner.resolve(&id).unwrap(), "A");

        let id = process_string_escapes("\\xFF", &mut ctx.writer()).unwrap();
        assert_eq!(ctx.interner.resolve(&id).unwrap(), "\u{FF}");
    }

    #[test]
    fn test_string_escapes_unicode() {
        let mut ctx = TestContext::default();

        let id = process_string_escapes("\\u0041", &mut ctx.writer()).unwrap();
        assert_eq!(ctx.interner.resolve(&id).unwrap(), "A");

        let id = process_string_escapes("\\U00000041", &mut ctx.writer()).unwrap();
        assert_eq!(ctx.interner.resolve(&id).unwrap(), "A");

        let id = process_string_escapes("\\u2764", &mut ctx.writer()).unwrap();
        assert_eq!(ctx.interner.resolve(&id).unwrap(), "❤");
    }

    #[test]
    fn test_string_escapes_octal() {
        let mut ctx = TestContext::default();

        let id = process_string_escapes("\\101", &mut ctx.writer()).unwrap();
        assert_eq!(ctx.interner.resolve(&id).unwrap(), "A");

        let id = process_string_escapes("\\377", &mut ctx.writer()).unwrap();
        assert_eq!(ctx.interner.resolve(&id).unwrap(), "\u{FF}");
    }

    #[test]
    fn test_string_escapes_invalid_surrogate() {
        let mut ctx = TestContext::default();

        // UTF-16 surrogates should be rejected
        assert!(process_string_escapes("\\uD800", &mut ctx.writer()).is_err());
        assert!(process_string_escapes("\\uDFFF", &mut ctx.writer()).is_err());
    }

    #[test]
    fn test_string_escapes_invalid_sequence() {
        let mut ctx = TestContext::default();

        // Invalid escape sequences
        assert!(process_string_escapes("\\s", &mut ctx.writer()).is_err());
        assert!(process_string_escapes("\\", &mut ctx.writer()).is_err());
    }

    #[test]
    fn test_no_escapes_fast_path() {
        let mut ctx = TestContext::default();

        let id = process_string_escapes("hello world", &mut ctx.writer()).unwrap();
        assert_eq!(ctx.interner.resolve(&id).unwrap(), "hello world");
    }

    #[test]
    fn test_process_literal_integers() {
        let mut ctx = TestContext::default();

        // Decimal integers
        let raw = RawLiteral::Int("123");
        assert_eq!(
            process_literal(&raw, &mut ctx.writer()).unwrap(),
            Literal::Int(123)
        );

        let raw = RawLiteral::Int("-456");
        assert_eq!(
            process_literal(&raw, &mut ctx.writer()).unwrap(),
            Literal::Int(-456)
        );

        // Hex integers
        let raw = RawLiteral::Int("0xFF");
        assert_eq!(
            process_literal(&raw, &mut ctx.writer()).unwrap(),
            Literal::Int(255)
        );

        // Unsigned integers
        let raw = RawLiteral::UInt("789");
        assert_eq!(
            process_literal(&raw, &mut ctx.writer()).unwrap(),
            Literal::UInt(789)
        );
    }

    #[test]
    fn test_process_literal_floats() {
        let mut ctx = TestContext::default();

        let raw = RawLiteral::Float("3.14");
        if let Literal::Float(val) = process_literal(&raw, &mut ctx.writer()).unwrap() {
            #[expect(clippy::approx_constant)] // Test value, not using constant
            {
                assert!((val - 3.14).abs() < 0.0001);
            }
        } else {
            panic!("Expected Float literal");
        }
    }

    #[test]
    fn test_process_literal_strings() {
        let mut ctx = TestContext::default();

        // Raw string - no processing
        let raw = RawLiteral::String("hello\\nworld", true, QuoteStyle::DoubleQuote);
        let lit = process_literal(&raw, &mut ctx.writer()).unwrap();
        match lit {
            Literal::String(id) => {
                assert_eq!(ctx.interner.resolve(&id).unwrap(), "hello\\nworld");
            }
            _ => panic!("Expected String literal"),
        }

        // Non-raw string - process escapes
        let raw = RawLiteral::String("hello\\nworld", false, QuoteStyle::DoubleQuote);
        let lit = process_literal(&raw, &mut ctx.writer()).unwrap();
        match lit {
            Literal::String(id) => {
                assert_eq!(ctx.interner.resolve(&id).unwrap(), "hello\nworld");
            }
            _ => panic!("Expected String literal"),
        }
    }

    #[test]
    fn test_process_literal_bools_and_null() {
        let mut ctx = TestContext::default();

        let raw = RawLiteral::Bool(true);
        assert_eq!(
            process_literal(&raw, &mut ctx.writer()).unwrap(),
            Literal::Bool(true)
        );

        let raw = RawLiteral::Bool(false);
        assert_eq!(
            process_literal(&raw, &mut ctx.writer()).unwrap(),
            Literal::Bool(false)
        );

        let raw = RawLiteral::Null;
        assert_eq!(
            process_literal(&raw, &mut ctx.writer()).unwrap(),
            Literal::Null
        );
    }

    /// Test that bytes can contain invalid UTF-8 sequences
    /// CEL Spec (line 271): "Bytes are arbitrary sequences of octets"
    /// CEL Spec (line 338-339): b"\377" is byte 255, not UTF-8 of ÿ
    #[test]
    fn test_bytes_invalid_utf8() {
        let mut ctx = TestContext::default();

        // \xFF is byte 255 - NOT valid UTF-8 on its own
        let raw = RawLiteral::Bytes("\\xFF", false, QuoteStyle::DoubleQuote);
        let result = process_literal(&raw, &mut ctx.writer()).unwrap();

        if let Literal::Bytes(bytes) = result {
            assert_eq!(bytes.len(), 1);
            assert_eq!(bytes[0], 0xFF);
            // Verify this is NOT valid UTF-8
            assert!(std::str::from_utf8(bytes).is_err());
        } else {
            panic!("Expected Bytes literal");
        }

        // \377 (octal) is also byte 255
        let raw = RawLiteral::Bytes("\\377", false, QuoteStyle::DoubleQuote);
        let result = process_literal(&raw, &mut ctx.writer()).unwrap();

        if let Literal::Bytes(bytes) = result {
            assert_eq!(bytes.len(), 1);
            assert_eq!(bytes[0], 255);
        } else {
            panic!("Expected Bytes literal");
        }

        // Sequence of invalid UTF-8 bytes
        let raw = RawLiteral::Bytes("\\xFF\\xFE\\xFD", false, QuoteStyle::DoubleQuote);
        let result = process_literal(&raw, &mut ctx.writer()).unwrap();

        if let Literal::Bytes(bytes) = result {
            assert_eq!(bytes, &[0xFF, 0xFE, 0xFD]);
            // Verify this is NOT valid UTF-8
            assert!(std::str::from_utf8(bytes).is_err());
        } else {
            panic!("Expected Bytes literal");
        }
    }

    /// Test that bytes containing valid UTF-8 still work
    #[test]
    fn test_bytes_valid_utf8() {
        let mut ctx = TestContext::default();

        // ASCII is valid UTF-8
        let raw = RawLiteral::Bytes("abc", false, QuoteStyle::DoubleQuote);
        let result = process_literal(&raw, &mut ctx.writer()).unwrap();

        if let Literal::Bytes(bytes) = result {
            assert_eq!(bytes, b"abc");
            assert_eq!(std::str::from_utf8(bytes).unwrap(), "abc");
        } else {
            panic!("Expected Bytes literal");
        }

        // CEL Spec example (line 335): b"ÿ" is bytes [195, 191] (UTF-8 of ÿ)
        let raw = RawLiteral::Bytes("ÿ", false, QuoteStyle::DoubleQuote);
        let result = process_literal(&raw, &mut ctx.writer()).unwrap();

        if let Literal::Bytes(bytes) = result {
            assert_eq!(bytes, &[195, 191]); // UTF-8 encoding of ÿ (U+00FF)
            assert_eq!(std::str::from_utf8(bytes).unwrap(), "ÿ");
        } else {
            panic!("Expected Bytes literal");
        }
    }
}
