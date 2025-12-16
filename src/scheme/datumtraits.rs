use crate::common::{Span, StringId};
use std::fmt::Debug;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DatumKind {
    Bool,
    Integer,
    Float,
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

pub trait DatumInspector: Sized {
    /// Fast type check.
    fn kind(&self) -> DatumKind;

    /// Access the source span, if this implementation tracks it.
    fn span(&self) -> Option<Span>;

    // --- Atoms (Zero-Copy) ---

    fn as_bool(&self) -> Option<bool>;
    fn as_i64(&self) -> Option<i64>;
    fn as_f64(&self) -> Option<f64>;
    fn as_char(&self) -> Option<char>;

    /// The type of string ID used by this inspector.
    type StringId<'a>: StringId + 'a where Self: 'a;

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

    // --- Atoms ---
    fn bool(&mut self, v: bool, s: Span) -> Result<Self::Output, Self::Error>;
    fn int(&mut self, v: i64, s: Span) -> Result<Self::Output, Self::Error>;
    fn float(&mut self, v: f64, s: Span) -> Result<Self::Output, Self::Error>;
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


