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
