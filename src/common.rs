#[derive(Clone, Copy, Debug, Default)]
pub struct Span{ pub start: usize, pub end: usize }

impl Span {
    pub fn empty() -> Self {
        Self { start: 0, end: 0 }
    }

    pub fn intersect<Span: Into<Self>>(&self, other: Span) -> Self {
        let other: Self = other.into();
        
        let start = std::cmp::max(self.start, other.start);
        let end = std::cmp::min(self.end, other.end);

        Self { start, end }
    }

    pub fn first(&self) -> Option<usize> {
        (self.start..self.end).next()
    }

    pub fn last(&self) -> Option<usize> {
        (self.start..self.end).last()
    }

    pub fn is_empty(&self) -> bool {
        self.start >= self.end
    }
}

impl From<std::ops::Range<usize>> for Span {
    fn from(value: std::ops::Range<usize>) -> Self {
        Self { start: value.start, end: value.end }
    }
}

impl From<Span> for std::ops::Range<usize> {
    fn from(val: Span) -> Self {
        val.start..val.end
    }
}

impl chumsky::Span for Span {
    type Context = ();

    type Offset = usize;

    fn new(context: Self::Context, range: std::ops::Range<Self::Offset>) -> Self {
        range.into()
    }

    fn context(&self) -> Self::Context {
    }

    fn start(&self) -> Self::Offset {
        self.start
    }

    fn end(&self) -> Self::Offset {
        self.end
    }
}

impl chumsky::zero_copy::span::Span for Span {
    type Context = ();

    type Offset = usize;
}