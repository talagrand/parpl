use crate::common::{Interner, Span, StringId};
use crate::scheme::{
    ParseError,
    lex::{self, FiniteRealKind, NumberExactness, Sign},
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
    Labeled,
    LabelRef,
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
    fn from_literal(lit: &lex::NumberLiteral<'_>, span: Span) -> Result<Self::Number, ParseError>;

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
    Literal(String),
}

/// Default implementation using `SimpleNumber`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PrimitiveOps;

impl SchemeNumberOps for PrimitiveOps {
    type Number = SimpleNumber;

    fn from_literal(lit: &lex::NumberLiteral<'_>, _span: Span) -> Result<Self::Number, ParseError> {
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
                            return Ok(SimpleNumber::Literal(lit.text.to_string()));
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
        Ok(SimpleNumber::Literal(lit.text.to_string()))
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
                // Fallback: compare source spellings.
                // This is imperfect for `1` vs `01` but sufficient for the example `SimpleNumber`.
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

    /// The type of a "child" handle.
    /// For ASTs, this can be `&Self`.
    /// For Rc Graphs, this can be `Self` (the Rc itself).
    /// For Arenas, this can be `Self` (the Index).
    type Child<'a>: DatumInspector
    where
        Self: 'a;

    /// Returns references to the head and tail.
    fn as_pair<'a>(&'a self) -> Option<(Self::Child<'a>, Self::Child<'a>)>;

    /// Returns an iterator over vector elements.
    type VectorIter<'a>: Iterator<Item = Self::Child<'a>>
    where
        Self: 'a;
    fn vector_iter<'a>(&'a self) -> Option<Self::VectorIter<'a>>;

    /// Returns the label ID and the inner datum if this is a labeled datum.
    fn as_labeled<'a>(&'a self) -> Option<(u64, Self::Child<'a>)>;

    /// Returns the label ID if this is a label reference.
    fn as_label_ref(&self) -> Option<u64>;

    // --- Utilities ---

    fn is_null(&self) -> bool {
        matches!(self.kind(), DatumKind::Null)
    }

    /// Returns an iterator over list elements (proper or improper).
    type ListIter<'a>: Iterator<Item = Self::Child<'a>>
    where
        Self: 'a;
    
    fn list_iter<'a>(&'a self) -> Self::ListIter<'a>;
}

/// Standard iterator struct for walking generic Scheme lists.
/// Implementations of `DatumInspector` can use this struct for their `ListIter` associated type
/// by implementing `Iterator` for it.
pub struct ListIter<'a, T: DatumInspector + ?Sized>
where
    T: 'a,
{
    pub current: Option<T::Child<'a>>,
}

impl<'a, T: DatumInspector + ?Sized> ListIter<'a, T> {
    pub fn new(start: T::Child<'a>) -> Self {
        Self {
            current: Some(start),
        }
    }
}



pub trait DatumWriter {
    /// The concrete type being built
    type Output;
    type Error;

    /// The interner used by this writer.
    ///
    /// The Reader will call `writer.interner().intern(text)` to obtain IDs
    /// for symbols and strings.
    type Interner: Interner<Id = Self::StringId>;

    /// The stable ID type for interned strings/symbols.
    type StringId: StringId;

    /// Mutable access to the writer's interner.
    fn interner(&mut self) -> &mut Self::Interner;

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
    fn string(&mut self, v: Self::StringId, s: Span) -> Result<Self::Output, Self::Error>;
    fn symbol(&mut self, v: Self::StringId, s: Span) -> Result<Self::Output, Self::Error>;

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

    fn labeled(&mut self, id: u64, inner: Self::Output, s: Span) -> Result<Self::Output, Self::Error>;

    fn label_ref(&mut self, id: u64, s: Span) -> Result<Self::Output, Self::Error>;

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

// NOTE: We intentionally do not define a reader-owned number-literal IR.
// `SchemeNumberOps::from_literal` receives a borrowed lexer `NumberLiteral`.
// If an implementation wants to retain an unknown literal, it can clone the
// raw token text (`lit.text`) into its own representation.
