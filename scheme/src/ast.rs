/// A byte-offset span into the original source.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub fn merge(self, other: Span) -> Span {
        Span {
            start: std::cmp::min(self.start, other.start),
            end: std::cmp::max(self.end, other.end),
        }
    }
}

/// A syntax object: a value paired with its source span.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Syntax<T> {
    pub span: Span,
    pub value: T,
}

impl<T> Syntax<T> {
    #[inline]
    pub fn new(span: Span, value: T) -> Self {
        Self { span, value }
    }
}

/// Radix of a Scheme number literal as specified by `<radix R>`.
///
/// Grammar reference (Formal syntax / `<number>`):
///
/// ```text
/// <radix 2>  ::= #b
/// <radix 8>  ::= #o
/// <radix 10> ::= <empty> | #d
/// <radix 16> ::= #x
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NumberRadix {
    Binary,
    Octal,
    Decimal,
    Hexadecimal,
}

/// Exactness marker of a Scheme number literal.
///
/// ```text
/// <exactness> ::= <empty> | #i | #e
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NumberExactness {
    Exact,
    Inexact,
    /// No explicit `#e`/`#i` prefix; exactness is determined
    /// by the default rules of the report.
    Unspecified,
}

/// The four special infinities / NaNs used by `<infnan>`.
///
/// ```text
/// <infnan> ::= +inf.0 | -inf.0 | +nan.0 | -nan.0
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InfinityNan {
    PositiveInfinity,
    NegativeInfinity,
    PositiveNaN,
    NegativeNaN,
}

/// Finite real-number spellings built from `<ureal R>` and
/// `<decimal 10>`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FiniteRealKind {
    /// A (possibly signed) integer, e.g. "42", "-7".
    Integer,
    /// A (possibly signed) rational, e.g. "3/4", "-5/16".
    Rational,
    /// A (possibly signed) decimal, e.g. "3.14", "-.5", "1e3".
    Decimal,
}

/// Representation of `<real R>` values.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RealRepr {
    /// A finite real built from `<ureal R>` or `<decimal 10>`.
    Finite {
        kind: FiniteRealKind,
        spelling: String,
    },
    /// One of the four `<infnan>` spellings.
    Infnan(InfinityNan),
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

/// Datum syntax as defined in the "External representations" section
/// of `spec/syn.md`.
#[derive(Clone, Debug, PartialEq)]
pub enum Datum {
    Boolean(bool),
    Number(NumberLiteral),
    Character(char),
    String(String),
    Symbol(String),
    ByteVector(Vec<u8>),
    /// The empty list `()`.
    EmptyList,
    /// Proper and improper lists are represented via pairs.
    Pair(Box<Syntax<Datum>>, Box<Syntax<Datum>>),
    Vector(Vec<Syntax<Datum>>),
    /// A labeled datum: #n=datum
    Labeled(u64, Box<Syntax<Datum>>),
    /// A reference to a previously defined label: #n#
    LabelRef(u64),
}
