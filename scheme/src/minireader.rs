use crate::ParseError;
use crate::ast::Span;
use crate::lex::{
    FiniteReal, FiniteRealKind, Lexer, NumberLiteral, NumberRadix, NumberValue, RealRepr,
    SpannedToken, Token,
};
use std::iter::Peekable;

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    /// Numbers (integers only)
    Number(i64),
    /// Symbols (identifiers)
    Symbol(String),
    /// String literals
    String(String),
    /// Boolean values
    Bool(bool),
    /// Lists (including proper and improper lists, empty list represents nil)
    List(Vec<Value>),
}

pub struct MiniReader<'a> {
    lexer: Peekable<Lexer<'a>>,
}

impl<'a> MiniReader<'a> {
    pub fn new(source: &'a str) -> Self {
        Self {
            lexer: crate::lex::lex(source).peekable(),
        }
    }

    fn peek(&mut self) -> Result<Option<&SpannedToken<'a>>, ParseError> {
        match self.lexer.peek() {
            Some(Ok(token)) => Ok(Some(token)),
            Some(Err(e)) => Err(e.clone()),
            None => Ok(None),
        }
    }

    fn next(&mut self) -> Result<Option<SpannedToken<'a>>, ParseError> {
        match self.lexer.next() {
            Some(Ok(token)) => Ok(Some(token)),
            Some(Err(e)) => Err(e),
            None => Ok(None),
        }
    }

    pub fn parse_value(&mut self) -> Result<Value, ParseError> {
        loop {
            let token = self.next()?.ok_or(ParseError::Incomplete)?;

            match token.value {
                Token::DatumComment => {
                    // Recursively parse the next datum and discard it
                    let _ = self.parse_value()?;
                    continue;
                }
                Token::Boolean(b) => return Ok(Value::Bool(b)),
                Token::Identifier(s) => return Ok(Value::Symbol(s.to_string())),
                Token::String(s) => return Ok(Value::String(s.into_owned())),
                Token::Number(n) => return self.parse_number(n, token.span),
                Token::LParen => return self.parse_list(),
                Token::Quote => {
                    // Expand 'x to (quote x)
                    let datum = self.parse_value()?;
                    return Ok(Value::List(vec![Value::Symbol("quote".to_string()), datum]));
                }
                Token::VectorStart => return Err(ParseError::unsupported(token.span, "vectors")),
                Token::ByteVectorStart => {
                    return Err(ParseError::unsupported(token.span, "bytevectors"));
                }
                Token::RParen => {
                    return Err(ParseError::syntax(token.span, "datum", "unexpected ')'"));
                }
                Token::Dot => {
                    return Err(ParseError::syntax(token.span, "datum", "unexpected '.'"));
                }
                Token::Comma | Token::CommaAt | Token::Backquote => {
                    return Err(ParseError::unsupported(token.span, "quasiquote/unquote"));
                }
                Token::LabelDef(_) | Token::LabelRef(_) => {
                    return Err(ParseError::unsupported(token.span, "labels"));
                }
                Token::Character(_) => {
                    return Err(ParseError::unsupported(token.span, "characters"));
                }
            }
        }
    }

    fn parse_list(&mut self) -> Result<Value, ParseError> {
        let mut elements = Vec::new();
        loop {
            let peeked = self.peek()?;
            match peeked {
                Some(t) => match t.value {
                    Token::RParen => {
                        self.next()?;
                        return Ok(Value::List(elements));
                    }
                    Token::Dot => {
                        return Err(ParseError::unsupported(t.span, "improper lists"));
                    }
                    Token::DatumComment => {
                        // We must handle datum comments here to support lists ending with a comment,
                        // e.g. `(1 2 #; 3)`. If we delegated to `parse_value`, it would consume
                        // the comment and then fail to find a value before the closing `)`.
                        self.next()?; // consume #;
                        let _ = self.parse_value()?; // parse and discard
                    }
                    _ => {
                        elements.push(self.parse_value()?);
                    }
                },
                None => return Err(ParseError::Incomplete),
            }
        }
    }

    fn parse_number(&self, n: NumberLiteral, span: Span) -> Result<Value, ParseError> {
        match n.kind.value {
            NumberValue::Real(RealRepr::Finite(FiniteReal {
                kind: FiniteRealKind::Integer,
                spelling,
            })) => {
                let radix = match n.kind.radix {
                    NumberRadix::Binary => 2,
                    NumberRadix::Octal => 8,
                    NumberRadix::Decimal => 10,
                    NumberRadix::Hexadecimal => 16,
                };

                let (sign, digits) = if let Some(stripped) = spelling.strip_prefix('+') {
                    (1, stripped)
                } else if let Some(stripped) = spelling.strip_prefix('-') {
                    (-1, stripped)
                } else {
                    (1, spelling)
                };

                let val = u64::from_str_radix(digits, radix).map_err(|_| {
                    ParseError::unsupported(span, "integer overflow or invalid format")
                })?;

                let result = if sign == 1 {
                    i64::try_from(val)
                        .map_err(|_| ParseError::unsupported(span, "integer overflow"))?
                } else {
                    if val > i64::MIN.unsigned_abs() {
                        return Err(ParseError::unsupported(span, "integer overflow"));
                    }
                    (val as i64).wrapping_neg()
                };

                Ok(Value::Number(result))
            }
            _ => Err(ParseError::unsupported(span, "non-integer number")),
        }
    }
}

pub fn read(source: &str) -> Result<Value, ParseError> {
    let mut reader = MiniReader::new(source);
    reader.parse_value()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ParseError;

    #[test]
    fn test_basic_parsing() {
        assert_eq!(read("123").unwrap(), Value::Number(123));
        assert_eq!(read("-42").unwrap(), Value::Number(-42));
        assert_eq!(read("abc").unwrap(), Value::Symbol("abc".to_string()));
        assert_eq!(
            read("\"hello\"").unwrap(),
            Value::String("hello".to_string())
        );
        assert_eq!(read("#t").unwrap(), Value::Bool(true));
        assert_eq!(read("#f").unwrap(), Value::Bool(false));
    }

    #[test]
    fn test_list_parsing() {
        let val = read("(1 2 3)").unwrap();
        if let Value::List(v) = val {
            assert_eq!(v.len(), 3);
            assert_eq!(v[0], Value::Number(1));
            assert_eq!(v[1], Value::Number(2));
            assert_eq!(v[2], Value::Number(3));
        } else {
            panic!("Expected list");
        }
    }

    #[test]
    fn test_datum_comment() {
        assert_eq!(read("#; 1 2").unwrap(), Value::Number(2));
        assert_eq!(
            read("(1 #; 2 3)").unwrap(),
            Value::List(vec![Value::Number(1), Value::Number(3)])
        );
    }

    #[test]
    fn test_unsupported() {
        match read("#(1 2)") {
            Err(ParseError::Unsupported { message, .. }) => assert_eq!(message, "vectors"),
            _ => panic!("Expected unsupported vector error"),
        }
        match read("1.5") {
            Err(ParseError::Unsupported { message, .. }) => {
                assert_eq!(message, "non-integer number")
            }
            _ => panic!("Expected unsupported float error"),
        }
    }

    #[test]
    fn test_syntax_error() {
        match read(")") {
            Err(ParseError::Syntax { message, .. }) => assert_eq!(message, "unexpected ')'"),
            _ => panic!("Expected syntax error"),
        }
    }

    #[test]
    fn test_number_edge_cases() {
        assert_eq!(
            read("9223372036854775807").unwrap(),
            Value::Number(i64::MAX)
        );
        assert_eq!(
            read("-9223372036854775808").unwrap(),
            Value::Number(i64::MIN)
        );
        match read("9223372036854775808") {
            Err(ParseError::Unsupported { message, .. }) => assert_eq!(message, "integer overflow"),
            _ => panic!("Expected overflow error for i64::MAX + 1"),
        }
        match read("-9223372036854775809") {
            Err(ParseError::Unsupported { message, .. }) => assert_eq!(message, "integer overflow"),
            _ => panic!("Expected overflow error for i64::MIN - 1"),
        }
    }
}
