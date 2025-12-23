use crate::{
    common::{InternId, Interner, Span, SymbolInterner, Syntax},
    scheme::{
        ParseError,
        datumtraits::{DatumInspector, DatumKind, DatumWriter},
        primitivenumbers::{PrimitiveOps, SimpleNumber},
    },
};
use bumpalo::Bump;

/// Datum syntax as defined in the "External representations" section
/// of `spec/syn.md`.
#[derive(Clone, Debug, PartialEq)]
pub enum Datum<'a> {
    Boolean(bool),
    Number(SimpleNumber),
    Character(char),
    String(String),
    Symbol(String),
    ByteVector(Vec<u8>),
    /// The empty list `()`.
    EmptyList,
    /// Proper and improper lists are represented via pairs.
    Pair(&'a Syntax<Datum<'a>>, &'a Syntax<Datum<'a>>),
    Vector(Vec<Syntax<Datum<'a>>>),
    /// A labeled datum: #n=datum
    Labeled(u64, &'a Syntax<Datum<'a>>),
    /// A reference to a previously defined label: #n#
    LabelRef(u64),
}

pub struct SampleWriter<'a> {
    interner: SymbolInterner,
    arena: &'a Bump,
}

impl<'a> SampleWriter<'a> {
    pub fn new(arena: &'a Bump) -> Self {
        Self {
            interner: SymbolInterner::default(),
            arena,
        }
    }
}

impl<'a> DatumWriter for SampleWriter<'a> {
    type Output = Syntax<Datum<'a>>;
    type Error = (); // Infallible for this sample
    type Interner = SymbolInterner;
    type StringId = InternId;
    type N = PrimitiveOps;

    fn interner(&mut self) -> &mut Self::Interner {
        &mut self.interner
    }

    fn bool(&mut self, v: bool, s: Span) -> Result<Self::Output, Self::Error> {
        Ok(Syntax::new(s, Datum::Boolean(v)))
    }

    fn number(&mut self, v: SimpleNumber, s: Span) -> Result<Self::Output, Self::Error> {
        Ok(Syntax::new(s, Datum::Number(v)))
    }

    fn char(&mut self, v: char, s: Span) -> Result<Self::Output, Self::Error> {
        Ok(Syntax::new(s, Datum::Character(v)))
    }

    fn string(&mut self, v: Self::StringId, s: Span) -> Result<Self::Output, Self::Error> {
        let str_val = self
            .interner
            .resolve(&v)
            .unwrap_or("<unresolved>")
            .to_string();
        Ok(Syntax::new(s, Datum::String(str_val)))
    }

    fn symbol(&mut self, v: Self::StringId, s: Span) -> Result<Self::Output, Self::Error> {
        let str_val = self
            .interner
            .resolve(&v)
            .unwrap_or("<unresolved>")
            .to_string();
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
        let elements: Vec<_> = iter.into_iter().collect();
        let mut tail = Syntax::new(s, Datum::EmptyList);

        for elem in elements.into_iter().rev() {
            let span = Span::new(elem.span.start, s.end);
            let pair = Datum::Pair(self.arena.alloc(elem), self.arena.alloc(tail));
            tail = Syntax::new(span, pair);
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
            let span = Span::new(elem.span.start, s.end);
            let pair = Datum::Pair(self.arena.alloc(elem), self.arena.alloc(result_tail));
            result_tail = Syntax::new(span, pair);
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
        Ok(Syntax::new(s, Datum::Labeled(id, self.arena.alloc(inner))))
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

pub struct SampleListIter<'a, 'd> {
    current: Option<&'a Syntax<Datum<'d>>>,
    len: usize,
}

impl<'a, 'd> Iterator for SampleListIter<'a, 'd> {
    type Item = &'a Syntax<Datum<'d>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            return None;
        }
        let current = self.current?;
        match &current.value {
            Datum::Pair(head, tail) => {
                self.len -= 1;
                self.current = Some(tail);
                Some(head)
            }
            _ => {
                // Should not happen if len > 0 and structure is immutable/consistent
                self.len = 0;
                self.current = None;
                None
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<'a, 'd> ExactSizeIterator for SampleListIter<'a, 'd> {}

impl<'a, 'd> SampleListIter<'a, 'd> {
    fn new(start: &'a Syntax<Datum<'d>>) -> Self {
        let mut len = 0;
        let mut curr = start;
        while let Datum::Pair(_, tail) = &curr.value {
            len += 1;
            curr = tail;
        }
        Self {
            current: Some(start),
            len,
        }
    }
}

impl<'d> DatumInspector for &Syntax<Datum<'d>> {
    type N = PrimitiveOps;
    type StringId<'b>
        = StrId<'b>
    where
        Self: 'b;
    type Child<'b>
        = &'b Syntax<Datum<'d>>
    where
        Self: 'b;
    type VectorIter<'b>
        = std::slice::Iter<'b, Syntax<Datum<'d>>>
    where
        Self: 'b;
    type ListIter<'b>
        = SampleListIter<'b, 'd>
    where
        Self: 'b;

    fn kind(&self) -> DatumKind {
        match &self.value {
            Datum::Boolean(_) => DatumKind::Bool,
            Datum::Number(SimpleNumber::Integer(_)) => DatumKind::Integer,
            Datum::Number(SimpleNumber::Float(_)) => DatumKind::Float,
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

    fn as_bytes(&self) -> Option<&[u8]> {
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

    fn improper_tail<'b>(&'b self) -> Option<Self::Child<'b>> {
        let mut curr = *self;
        loop {
            match &curr.value {
                Datum::Pair(_, tail) => curr = tail,
                Datum::EmptyList => return None,
                _ => return Some(curr),
            }
        }
    }
}

pub fn read<'a>(source: &str, arena: &'a Bump) -> Result<Syntax<Datum<'a>>, ParseError> {
    read_with_max_depth(source, arena, 64)
}

pub fn read_with_max_depth<'a>(
    source: &str,
    arena: &'a Bump,
    max_depth: u32,
) -> Result<Syntax<Datum<'a>>, ParseError> {
    let lexer = crate::scheme::lex::lex_with_config(
        source,
        crate::scheme::lex::LexConfig {
            reject_fold_case: true,
            reject_comments: true,
        },
    );
    let mut stream = crate::scheme::reader::TokenStream::new(lexer);
    let mut writer = SampleWriter::new(arena);
    stream
        .parse_datum_with_max_depth(&mut writer, max_depth)
        .map(|(datum, _span)| datum)
}
