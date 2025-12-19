use crate::{
    common::Span,
    scheme::{
        ParseError, Unsupported,
        datumtraits::SchemeNumberOps,
        lex::{self, FiniteRealKind, NumberExactness, Sign},
    },
};

/// A simple number representation that can hold integers, floats, or
/// fall back to the raw literal for complex cases.
#[derive(Debug, Clone, PartialEq)]
pub enum SimpleNumber {
    Integer(i64),
    Float(f64),
}

/// Default implementation using `SimpleNumber`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PrimitiveOps;

impl SchemeNumberOps for PrimitiveOps {
    type Number = SimpleNumber;

    fn from_literal(lit: &lex::NumberLiteral<'_>, span: Span) -> Result<Self::Number, ParseError> {
        let kind = &lit.kind;

        let radix = kind.radix;

        let parse_mag_u64 =
            |digits: &str| -> Option<u64> { u64::from_str_radix(digits, radix).ok() };

        let mag_to_i64 = |mag: u64, sign: Sign| -> Option<i64> {
            match sign {
                Sign::Positive => i64::try_from(mag).ok(),
                Sign::Negative => {
                    // Two's-complement is asymmetric: `i64::MIN` is -2^63, whose magnitude (2^63)
                    // is one larger than `i64::MAX` and therefore doesn't fit in a positive `i64`.
                    // If we parsed that magnitude with a negative sign, it is still a valid i64.
                    let min_mag = (i64::MAX as u64) + 1;
                    if mag == min_mag {
                        Some(i64::MIN)
                    } else {
                        let v = i64::try_from(mag).ok()?;
                        v.checked_neg()
                    }
                }
            }
        };

        if let lex::NumberValue::Real(real) = &kind.value {
            let sign = real.effective_sign();
            match &real.magnitude {
                lex::RealMagnitude::Finite(finite) => match (kind.exactness, finite.kind) {
                    (
                        NumberExactness::Exact | NumberExactness::Unspecified,
                        FiniteRealKind::Integer,
                    ) => {
                        if let Some(mag) = parse_mag_u64(&finite.spelling) {
                            if let Some(i) = mag_to_i64(mag, sign) {
                                return Ok(SimpleNumber::Integer(i));
                            }
                        }
                    }
                    (NumberExactness::Inexact, FiniteRealKind::Integer) => {
                        if let Some(mag) = parse_mag_u64(&finite.spelling) {
                            let mut f = mag as f64;
                            if sign == Sign::Negative {
                                f = -f;
                            }
                            return Ok(SimpleNumber::Float(f));
                        }
                    }
                    (_, FiniteRealKind::Decimal) => {
                        if kind.exactness == NumberExactness::Exact {
                            return Err(ParseError::unsupported(
                                span,
                                Unsupported::InvalidIntegerFormat,
                            ));
                        }

                        // Stdlib float parsing only supports base 10 decimal spellings.
                        if radix == 10 {
                            if let Ok(mut f) = finite.spelling.parse::<f64>() {
                                if sign == Sign::Negative {
                                    f = -f;
                                }
                                return Ok(SimpleNumber::Float(f));
                            }
                        }
                    }
                    _ => {}
                },
                lex::RealMagnitude::Infinity => {
                    let mut f = f64::INFINITY;
                    if sign == Sign::Negative {
                        f = -f;
                    }
                    return Ok(SimpleNumber::Float(f));
                }
                lex::RealMagnitude::NaN => {
                    let mut f = f64::NAN;
                    if sign == Sign::Negative {
                        f = -f;
                    }
                    return Ok(SimpleNumber::Float(f));
                }
            }
        }

        // Fallback
        Err(ParseError::unsupported(span, Unsupported::NonIntegerNumber))
    }

    fn eqv(a: &Self::Number, b: &Self::Number) -> bool {
        match (a, b) {
            (SimpleNumber::Integer(a), SimpleNumber::Integer(b)) => a == b,
            (SimpleNumber::Float(a), SimpleNumber::Float(b)) => {
                // Scheme eqv? on floats is usually IEEE equality,
                // but exact behavior on NaNs is unspecified/implementation-dependent.
                // For now, standard PartialEq is a reasonable start.
                a == b
            }
            _ => false,
        }
    }
}
