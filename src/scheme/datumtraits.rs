use crate::common::{Span, StringId};
use crate::scheme::{
    ParseError,
    lex::{self, FiniteRealKind, NumberExactness, NumberRadix, Sign},
};
use std::fmt::Debug;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DatumKind {
    Bool,
    Integer,
    Float,
    Number,
    Character,
    String,
    Symbol,
    ByteVector,
    Pair,
    Null,
    Vector,
    // For opaque host objects or other extensions
    Other,
}

/// Abstract interface for Scheme number operations.
/// This decouples the Reader and Inspector from the concrete number representation.
pub trait SchemeNumberOps: Debug + Sized {
    /// The opaque semantic number type used by the backend/expander.
    type Number: Debug + Clone;

    /// The single lowering hook.
    /// The Reader calls this once per number token.
    fn from_literal(lit: &NumberLiteral, span: Span) -> Result<Self::Number, ParseError>;

    /// The semantic equality hook.
    /// Required for `syntax-rules` pattern matching (e.g. matching `1` against `1.0`).
    /// We use a method instead of `Eq` to allow Scheme's specific `eqv?` rules.
    fn eqv(a: &Self::Number, b: &Self::Number) -> bool;
}

/// A simple number representation that can hold integers, floats, or
/// fall back to the raw literal for complex cases.
#[derive(Debug, Clone, PartialEq)]
pub enum SimpleNumber {
    Integer(i64),
    Float(f64),
    // Fallback for big/rational/complex/exact-decimals
    Literal(NumberLiteral),
}

/// Default implementation using `SimpleNumber`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PrimitiveOps;

impl SchemeNumberOps for PrimitiveOps {
    type Number = SimpleNumber;

    fn from_literal(lit: &NumberLiteral, _span: Span) -> Result<Self::Number, ParseError> {
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

        if let NumberValue::Real(real) = &kind.value {
            let sign = real.effective_sign();
            match &real.magnitude {
                RealMagnitude::Finite(finite) => match (kind.exactness, finite.kind) {
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
                            return Ok(SimpleNumber::Literal(lit.clone()));
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
                RealMagnitude::Infinity => {
                    let mut f = f64::INFINITY;
                    if sign == Sign::Negative {
                        f = -f;
                    }
                    return Ok(SimpleNumber::Float(f));
                }
                RealMagnitude::NaN => {
                    let mut f = f64::NAN;
                    if sign == Sign::Negative {
                        f = -f;
                    }
                    return Ok(SimpleNumber::Float(f));
                }
            }
        }

        // Fallback
        Ok(SimpleNumber::Literal(lit.clone()))
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
            (SimpleNumber::Literal(a), SimpleNumber::Literal(b)) => {
                // Fallback: if we haven't lowered them, we can only compare text/structure.
                // This is imperfect for `1` vs `01` but sufficient for initial migration.
                a == b
            }
            _ => false,
        }
    }
}

pub trait DatumInspector: Sized {
    /// Fast type check.
    fn kind(&self) -> DatumKind;

    /// Access the source span, if this implementation tracks it.
    fn span(&self) -> Option<Span>;
    type N: SchemeNumberOps;

    /// Returns the number if this datum is a number.
    fn as_number(&self) -> Option<&<Self::N as SchemeNumberOps>::Number>;

    fn as_char(&self) -> Option<char>;

    /// The type of string ID used by this inspector.
    type StringId<'a>: StringId + 'a
    where
        Self: 'a;

    /// Returns the ID for a symbol.
    /// To get the text, pass this ID to the `Interner`.
    fn as_sym<'a>(&'a self) -> Option<Self::StringId<'a>>;

    /// Returns the ID for a string literal.
    /// To get the text, pass this ID to the `Interner`.
    fn as_str<'a>(&'a self) -> Option<Self::StringId<'a>>;

    fn as_bytes<'a>(&'a self) -> Option<&'a [u8]>;

    // --- Compounds (Recursive Views) ---

    /// Returns references to the head and tail.
    fn as_pair(&self) -> Option<(&Self, &Self)>;

    /// Returns an iterator over vector elements.
    type VectorIter<'a>: Iterator<Item = &'a Self>
    where
        Self: 'a;
    fn vector_iter<'a>(&'a self) -> Option<Self::VectorIter<'a>>;

    // --- Utilities ---

    fn is_null(&self) -> bool {
        matches!(self.kind(), DatumKind::Null)
    }

    /// Helper to iterate a proper list.
    fn list_iter<'a>(&'a self) -> ListIter<'a, Self> {
        ListIter { current: self }
    }
}

/// Standard iterator for walking generic Scheme lists
pub struct ListIter<'a, T: DatumInspector> {
    current: &'a T,
}

impl<'a, T: DatumInspector> Iterator for ListIter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        if let Some((head, tail)) = self.current.as_pair() {
            self.current = tail;
            Some(head)
        } else {
            None
        }
    }
}

pub trait DatumWriter {
    /// The concrete type being built
    type Output;
    type Error;

    /// The type of string ID this writer expects.
    type StringId<'a>: StringId;

    type N: SchemeNumberOps;

    // --- Atoms ---
    fn bool(&mut self, v: bool, s: Span) -> Result<Self::Output, Self::Error>;
    fn number(
        &mut self,
        v: <Self::N as SchemeNumberOps>::Number,
        s: Span,
    ) -> Result<Self::Output, Self::Error>;
    fn char(&mut self, v: char, s: Span) -> Result<Self::Output, Self::Error>;

    // Both strings and symbols now take IDs.
    // The caller (Reader/Expander) must use their Interner to produce these IDs.
    fn string<'a>(&mut self, v: Self::StringId<'a>, s: Span) -> Result<Self::Output, Self::Error>;
    fn symbol<'a>(&mut self, v: Self::StringId<'a>, s: Span) -> Result<Self::Output, Self::Error>;

    fn bytevector(&mut self, v: &[u8], s: Span) -> Result<Self::Output, Self::Error>;
    fn null(&mut self, s: Span) -> Result<Self::Output, Self::Error>;

    // --- Compounds ---

    fn list<I>(&mut self, iter: I, s: Span) -> Result<Self::Output, Self::Error>
    where
        I: IntoIterator<Item = Self::Output>,
        I::IntoIter: ExactSizeIterator;

    fn improper_list<I>(
        &mut self,
        head: I,
        tail: Self::Output,
        s: Span,
    ) -> Result<Self::Output, Self::Error>
    where
        I: IntoIterator<Item = Self::Output>,
        I::IntoIter: ExactSizeIterator;

    fn vector<I>(&mut self, iter: I, s: Span) -> Result<Self::Output, Self::Error>
    where
        I: IntoIterator<Item = Self::Output>,
        I::IntoIter: ExactSizeIterator;

    // --- Optimization Hook ---

    /// Optimized copy from an inspector.
    ///
    /// This method allows the writer to perform a deep copy of the datum
    /// represented by `inspector`.
    ///
    /// # Implementation Notes
    ///
    /// Implementors should check if `I::StringId` matches `Self::StringId`.
    /// If they match (or can be converted cheaply), the copy can be efficient.
    /// If they do not match, the implementation may need to fail or panic,
    /// as this trait does not provide an `Interner` to translate IDs.
    fn copy<I>(&mut self, inspector: &I) -> Result<Self::Output, Self::Error>
    where
        I: DatumInspector;
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteRealMagnitude {
    pub kind: FiniteRealKind,
    /// Signless spelling.
    pub spelling: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RealMagnitude {
    Finite(FiniteRealMagnitude),
    Infinity,
    NaN,
}

/// Representation of `<real R>` values.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RealRepr {
    /// `None` means no explicit sign (implicit positive).
    ///
    /// Invariant: if `magnitude` is `Infinity` or `NaN`, then `sign.is_some()`.
    pub sign: Option<Sign>,
    pub magnitude: RealMagnitude,
}

impl RealRepr {
    /// Returns the effective sign, treating an omitted sign as `+`.
    pub fn effective_sign(&self) -> Sign {
        self.sign.unwrap_or(Sign::Positive)
    }
}

/// Complex-number structure corresponding to `<complex R>`.
///
/// ```text
/// <complex R> ::= <real R>
///                | <real R> @ <real R>
///                | <real R> + <ureal R> i
///                | <real R> - <ureal R> i
///                | <real R> + i
///                | <real R> - i
///                | <real R> <infnan> i
///                | + <ureal R> i
///                | - <ureal R> i
///                | <infnan> i
///                | + i
///                | - i
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NumberValue {
    /// A purely real number `<real R>`.
    Real(RealRepr),
    /// Rectangular complex form `a+bi` / `a-bi` and related
    /// special cases normalized into explicit real and imaginary
    /// parts.
    Rectangular { real: RealRepr, imag: RealRepr },
    /// Polar complex form `r@theta`.
    Polar {
        magnitude: RealRepr,
        angle: RealRepr,
    },
}

/// Full structural classification of a Scheme number literal.
///
/// This mirrors `<num R> ::= <prefix R> <complex R>`: `radix` and
/// `exactness` capture `<prefix R>`, while `value` is the parsed
/// `<complex R>` structure.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NumberLiteralKind {
    pub radix: NumberRadix,
    pub exactness: NumberExactness,
    pub value: NumberValue,
}

/// A number literal, keeping the original spelling from the source.
#[derive(Clone, Debug, PartialEq)]
pub struct NumberLiteral {
    /// Exact token text, including prefixes/suffixes.
    pub text: String,
    pub kind: NumberLiteralKind,
}

// Conversions from lexer number representations to reader-owned numbers.

impl<'a> From<lex::RealRepr<'a>> for RealRepr {
    fn from(lex_real: lex::RealRepr<'a>) -> Self {
        let magnitude = match lex_real.magnitude {
            lex::RealMagnitude::Finite(f) => RealMagnitude::Finite(FiniteRealMagnitude {
                kind: f.kind,
                spelling: f.spelling.to_string(),
            }),
            lex::RealMagnitude::Infinity => RealMagnitude::Infinity,
            lex::RealMagnitude::NaN => RealMagnitude::NaN,
        };

        RealRepr {
            sign: lex_real.sign,
            magnitude,
        }
    }
}

impl<'a> From<lex::NumberValue<'a>> for NumberValue {
    fn from(lex_value: lex::NumberValue<'a>) -> Self {
        match lex_value {
            lex::NumberValue::Real(r) => NumberValue::Real(r.into()),
            lex::NumberValue::Rectangular { real, imag } => NumberValue::Rectangular {
                real: real.into(),
                imag: imag.into(),
            },
            lex::NumberValue::Polar { magnitude, angle } => NumberValue::Polar {
                magnitude: magnitude.into(),
                angle: angle.into(),
            },
        }
    }
}

impl<'a> From<lex::NumberLiteralKind<'a>> for NumberLiteralKind {
    fn from(lex_kind: lex::NumberLiteralKind<'a>) -> Self {
        NumberLiteralKind {
            radix: lex_kind.radix,
            exactness: lex_kind.exactness,
            value: lex_kind.value.into(),
        }
    }
}

impl<'a> From<lex::NumberLiteral<'a>> for NumberLiteral {
    fn from(lex_literal: lex::NumberLiteral<'a>) -> Self {
        NumberLiteral {
            text: lex_literal.text.to_string(),
            kind: lex_literal.kind.into(),
        }
    }
}
