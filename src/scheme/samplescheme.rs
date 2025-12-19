use crate::common::{Interner, Span, Syntax};
use crate::scheme::datumtraits::{DatumInspector, DatumKind, DatumWriter};
use crate::scheme::primitivenumbers::{PrimitiveOps, SimpleNumber};
use std::collections::HashMap;

/// A simple string ID for our sample implementation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SampleStringId(u32);

// impl StringId for SampleStringId {}

/// A simple interner for our sample implementation.
#[derive(Default)]
pub struct SampleInterner {
    map: HashMap<String, u32>,
    vec: Vec<String>,
}

impl Interner for SampleInterner {
    type Id = SampleStringId;

    fn intern(&mut self, text: &str) -> Self::Id {
        if let Some(&id) = self.map.get(text) {
            return SampleStringId(id);
        }
        let id = self.vec.len() as u32;
        self.vec.push(text.to_string());
        self.map.insert(text.to_string(), id);
        SampleStringId(id)
    }

    fn resolve(&self, id: Self::Id) -> &str {
        self.vec.get(id.0 as usize).map(|s| s.as_str()).unwrap()
    }
}

/// Datum syntax as defined in the "External representations" section
/// of `spec/syn.md`.
#[derive(Clone, Debug, PartialEq)]
pub enum Datum {
    Boolean(bool),
    Number(SimpleNumber),
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

pub struct SampleWriter {
    interner: SampleInterner,
}

impl SampleWriter {
    pub fn new() -> Self {
        Self {
            interner: SampleInterner::default(),
        }
    }
}

impl DatumWriter for SampleWriter {
    type Output = Syntax<Datum>;
    type Error = (); // Infallible for this sample
    type Interner = SampleInterner;
    type StringId = SampleStringId;
    type N = PrimitiveOps;

    fn interner(&mut self) -> &mut Self::Interner {
        &mut self.interner
    }

    fn bool(&mut self, v: bool, s: Span) -> Result<Self::Output, Self::Error> {
        Ok(Syntax::new(s, Datum::Boolean(v)))
    }

    fn number(
        &mut self,
        v: SimpleNumber,
        s: Span,
    ) -> Result<Self::Output, Self::Error> {
        Ok(Syntax::new(s, Datum::Number(v)))
    }

    fn char(&mut self, v: char, s: Span) -> Result<Self::Output, Self::Error> {
        Ok(Syntax::new(s, Datum::Character(v)))
    }

    fn string(&mut self, v: Self::StringId, s: Span) -> Result<Self::Output, Self::Error> {
        let str_val = self.interner.resolve(v).to_string();
        Ok(Syntax::new(s, Datum::String(str_val)))
    }

    fn symbol(&mut self, v: Self::StringId, s: Span) -> Result<Self::Output, Self::Error> {
        let str_val = self.interner.resolve(v).to_string();
        Ok(Syntax::new(s, Datum::Symbol(str_val)))
    }

    fn bytevector(&mut self, v: &[u8], s: Span) -> Result<Self::Output, Self::Error> {
        Ok(Syntax::new(s, Datum::ByteVector(v.to_vec())))
    }

    fn null(&mut self, s: Span) -> Result<Self::Output, Self::Error> {
        Ok(Syntax::new(s, Datum::EmptyList))
    }

    fn list<I>(&mut self, iter: I, s: Span) -> Result<Self::Output, Self::Error>
    where
        I: IntoIterator<Item = Self::Output>,
        I::IntoIter: ExactSizeIterator,
    {
        // We need to build the list. The iterator gives us elements.
        // Standard cons-list is built right-to-left or using a builder.
        // Since we have ExactSizeIterator, we can collect and reverse.
        let elements: Vec<_> = iter.into_iter().collect();
        
        // The span `s` covers the whole list.
        // For the intermediate pairs, we might not have precise spans unless we synthesize them.
        // But `Datum::Pair` takes `Box<Syntax<Datum>>`.
        // The `result` starts as EmptyList. We should probably give it a span?
        // The empty list at the end usually has the span of the closing parenthesis or is implicit.
        // Let's use `s` for the final empty list for now, or a dummy span.
        // Actually, `Datum::EmptyList` is a Datum. `Syntax::new(Datum::EmptyList, ...)`
        
        let mut tail = Syntax::new(s, Datum::EmptyList); // Use the list span for the nil?

        for elem in elements.into_iter().rev() {
            // elem is Syntax<Datum>
            // We create a Pair(elem, tail)
            // What is the span of this pair?
            // Ideally it covers from elem.span.start to tail.span.end.
            // For now, let's use `s` for all generated pairs, or try to be smarter.
            // Using `s` is safe.
            let pair = Datum::Pair(Box::new(elem), Box::new(tail));
            tail = Syntax::new(s, pair);
        }
        
        Ok(tail)
    }

    fn improper_list<I>(
        &mut self,
        head: I,
        tail: Self::Output,
        s: Span,
    ) -> Result<Self::Output, Self::Error>
    where
        I: IntoIterator<Item = Self::Output>,
        I::IntoIter: ExactSizeIterator,
    {
        let mut result_tail = tail;
        let elements: Vec<_> = head.into_iter().collect();
        
        for elem in elements.into_iter().rev() {
            let pair = Datum::Pair(Box::new(elem), Box::new(result_tail));
            result_tail = Syntax::new(s, pair);
        }
        Ok(result_tail)
    }

    fn vector<I>(&mut self, iter: I, s: Span) -> Result<Self::Output, Self::Error>
    where
        I: IntoIterator<Item = Self::Output>,
        I::IntoIter: ExactSizeIterator,
    {
        Ok(Syntax::new(s, Datum::Vector(iter.into_iter().collect())))
    }

    fn labeled(
        &mut self,
        id: u64,
        inner: Self::Output,
        s: Span,
    ) -> Result<Self::Output, Self::Error> {
        Ok(Syntax::new(s, Datum::Labeled(id, Box::new(inner))))
    }

    fn label_ref(&mut self, id: u64, s: Span) -> Result<Self::Output, Self::Error> {
        Ok(Syntax::new(s, Datum::LabelRef(id)))
    }

    fn copy<I>(&mut self, _inspector: &I) -> Result<Self::Output, Self::Error>
    where
        I: DatumInspector,
    {
        Err(())
    }
}

// Implement DatumInspector for Syntax<Datum>
// We need a StringId type. We can use a wrapper around &str.

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct StrId<'a>(&'a str);
// impl<'a> StringId for StrId<'a> {}

pub struct SampleListIter<'a> {
    current: Option<&'a Syntax<Datum>>,
}

impl<'a> Iterator for SampleListIter<'a> {
    type Item = &'a Syntax<Datum>;

    fn next(&mut self) -> Option<Self::Item> {
        let current = self.current?;
        match &current.value {
            Datum::Pair(head, tail) => {
                self.current = Some(tail);
                Some(head)
            }
            Datum::EmptyList => {
                self.current = None;
                None
            }
            _ => {
                // Improper list end. Stop iteration.
                self.current = None;
                None
            }
        }
    }
}

impl<'a> SampleListIter<'a> {
    fn new(start: &'a Syntax<Datum>) -> Self {
        Self {
            current: Some(start),
        }
    }
}

impl<'a> DatumInspector for &'a Syntax<Datum> {
    type N = PrimitiveOps;
    type StringId<'b> = StrId<'b> where Self: 'b;
    type Child<'b> = &'b Syntax<Datum> where Self: 'b;
    type VectorIter<'b> = std::slice::Iter<'b, Syntax<Datum>> where Self: 'b;
    type ListIter<'b> = SampleListIter<'b> where Self: 'b;

    fn kind(&self) -> DatumKind {
        match &self.value {
            Datum::Boolean(_) => DatumKind::Bool,
            Datum::Number(SimpleNumber::Integer(_)) => DatumKind::Integer,
            Datum::Number(SimpleNumber::Float(_)) => DatumKind::Float,
            Datum::Number(SimpleNumber::Literal(_)) => DatumKind::Number,
            Datum::Character(_) => DatumKind::Character,
            Datum::String(_) => DatumKind::String,
            Datum::Symbol(_) => DatumKind::Symbol,
            Datum::ByteVector(_) => DatumKind::ByteVector,
            Datum::EmptyList => DatumKind::Null,
            Datum::Pair(_, _) => DatumKind::Pair,
            Datum::Vector(_) => DatumKind::Vector,
            Datum::Labeled(_, _) => DatumKind::Labeled,
            Datum::LabelRef(_) => DatumKind::LabelRef,
        }
    }

    fn span(&self) -> Option<Span> {
        Some(self.span)
    }

    fn as_number(&self) -> Option<&SimpleNumber> {
        if let Datum::Number(n) = &self.value {
            Some(n)
        } else {
            None
        }
    }

    fn as_char(&self) -> Option<char> {
        if let Datum::Character(c) = &self.value {
            Some(*c)
        } else {
            None
        }
    }

    fn as_sym<'b>(&'b self) -> Option<Self::StringId<'b>> {
        if let Datum::Symbol(s) = &self.value {
            Some(StrId(s.as_str()))
        } else {
            None
        }
    }

    fn as_str<'b>(&'b self) -> Option<Self::StringId<'b>> {
        if let Datum::String(s) = &self.value {
            Some(StrId(s.as_str()))
        } else {
            None
        }
    }

    fn as_bytes<'b>(&'b self) -> Option<&'b [u8]> {
        if let Datum::ByteVector(v) = &self.value {
            Some(v)
        } else {
            None
        }
    }

    fn as_pair<'b>(&'b self) -> Option<(Self::Child<'b>, Self::Child<'b>)> {
        if let Datum::Pair(head, tail) = &self.value {
            Some((head, tail))
        } else {
            None
        }
    }

    fn vector_iter<'b>(&'b self) -> Option<Self::VectorIter<'b>> {
        if let Datum::Vector(v) = &self.value {
            Some(v.iter())
        } else {
            None
        }
    }

    fn as_labeled<'b>(&'b self) -> Option<(u64, Self::Child<'b>)> {
        if let Datum::Labeled(id, inner) = &self.value {
            Some((*id, inner))
        } else {
            None
        }
    }

    fn as_label_ref(&self) -> Option<u64> {
        if let Datum::LabelRef(id) = &self.value {
            Some(*id)
        } else {
            None
        }
    }

    fn list_iter<'b>(&'b self) -> Self::ListIter<'b> {
        SampleListIter::new(self)
    }
}
