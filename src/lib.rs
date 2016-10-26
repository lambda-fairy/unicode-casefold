/// Iterators for case folding text. Provides "simple" and "full" algorithms,
/// with Turkic language options on both.
///
/// See [this W3C article][1] for how case folding differs from `.to_lowercase()`.
///
/// [1]: https://www.w3.org/International/wiki/Case_folding

mod tables;
use tables::{Buffer, COMMON_TABLE, FULL_TABLE, SIMPLE_TABLE};

pub use tables::UNICODE_VERSION;

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Locale {
    NonTurkic,
    Turkic,
}

impl Default for Locale {
    fn default() -> Locale { Locale::NonTurkic }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Variant {
    Full,
    Simple,
}

impl Default for Variant {
    fn default() -> Variant { Variant::Full }
}

#[derive(Copy, Clone, Debug)]
pub struct CaseFold<I> {
    inner: I,
    buffer: Buffer,
    locale: Locale,
    variant: Variant,
}

impl<I: Iterator<Item=char>> CaseFold<I> {
    fn run(&mut self, c: char) -> char {
        if self.locale == Locale::Turkic && c == 'I' {
            '\u{131}'
        } else if self.locale == Locale::Turkic && c == '\u{130}' {
            'i'
        } else {
            if let Ok(i) = COMMON_TABLE.binary_search_by_key(&c, |x| x.0) {
                COMMON_TABLE[i].1
            } else if self.variant == Variant::Full {
                if let Ok(i) = FULL_TABLE.binary_search_by_key(&c, |x| x.0) {
                    let (r, b) = FULL_TABLE[i].1;
                    self.buffer = b;
                    r
                } else { c }
            } else {
                if let Ok(i) = SIMPLE_TABLE.binary_search_by_key(&c, |x| x.0) {
                    SIMPLE_TABLE[i].1
                } else { c }
            }
        }
    }
}

impl<I: Iterator<Item=char>> Iterator for CaseFold<I> {
    type Item = char;
    fn next(&mut self) -> Option<char> {
        match self.buffer {
            Buffer::Zero => {
                if let Some(c) = self.inner.next() {
                    Some(self.run(c))
                } else {
                    None
                }
            },
            Buffer::One(a) => {
                self.buffer = Buffer::Zero;
                Some(a)
            },
            Buffer::Two(a, b) => {
                self.buffer = Buffer::One(b);
                Some(a)
            },
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let (lo, hi) = self.inner.size_hint();
        (lo, hi.map(|hi| match self.variant {
            Variant::Full => 3 * hi,
            Variant::Simple => hi,
        }))
    }
}
