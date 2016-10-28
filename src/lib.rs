/// Iterators for case folding text. Provides "simple" and "full" algorithms,
/// with Turkic language options on both.
///
/// See [this W3C article][1] for how case folding differs from `.to_lowercase()`.
///
/// [1]: https://www.w3.org/International/wiki/Case_folding

use std::iter::{self, Once};
use std::str::Chars;

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

/// An iterator over case folded characters.
#[derive(Copy, Clone, Debug)]
pub struct CaseFold<I> {
    inner: I,
    buffer: Buffer,
    variant: Variant,
    locale: Locale,
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
        let extra = match self.buffer {
            Buffer::Zero => 0,
            Buffer::One(..) => 1,
            Buffer::Two(..) => 2,
        };
        let (lo, hi) = self.inner.size_hint();
        let lo = lo.saturating_add(extra);
        let hi = hi.and_then(|hi| match self.variant {
            Variant::Full => hi.checked_mul(3),
            Variant::Simple => Some(hi),
        }).and_then(|hi| hi.checked_add(extra));
        (lo, hi)
    }
}

/// Methods for case folding text.
pub trait UnicodeCaseFold<I: Iterator<Item=char>>: Sized {
    /// Returns an iterator over the case folded characters of `self`.
    ///
    /// This is a convenient shorthand for
    /// `.case_fold(Variant::Full, Locale::NonTurkic)`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use unicode_casefold::{Locale, Variant, UnicodeCaseFold};
    /// let s = "Alan Turing".case_fold().collect::<String>();
    /// assert_eq!(s, "alan turing");
    /// ```
    fn case_fold(self) -> CaseFold<I> {
        self.case_fold_with(Default::default(), Default::default())
    }

    /// Returns an iterator over the case folded characters of `self`.
    ///
    /// # Parameters
    ///
    /// The `Variant` can be either:
    ///
    /// * `Variant::Full` (recommended), which may expand to a longer string.
    ///   For example, the full case folded version of `ß` (one character) is
    ///   `ss` (two characters).
    ///
    /// * `Variant::Simple`, a simpler variant which always expands to a string
    ///   with the same number of characters. This is more efficient, but less
    ///   complete.
    ///
    /// The `Locale` can be either:
    ///
    /// * `Locale::NonTurkic` (default), which maps `I` to `i`.
    ///
    /// * `Locale::Turkic`, which maps `I` to `ı` (dotless i), as is the case
    ///   in Turkic languages.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use unicode_casefold::{Locale, Variant, UnicodeCaseFold};
    /// let name = "Inigo Montoya";
    /// let turkic = name.case_fold_with(Variant::Full, Locale::Turkic).collect::<String>();
    /// let non_turkic = name.case_fold_with(Variant::Full, Locale::NonTurkic).collect::<String>();
    /// assert_eq!(turkic, "ınigo montoya");  // note the dotless i
    /// assert_eq!(non_turkic, "inigo montoya");
    /// ```
    fn case_fold_with(self, Variant, Locale) -> CaseFold<I>;
}

impl<I: Iterator<Item=char>> UnicodeCaseFold<I> for I {
    fn case_fold_with(self, variant: Variant, locale: Locale) -> CaseFold<I> {
        CaseFold {
            inner: self,
            buffer: Buffer::Zero,
            variant: variant,
            locale: locale,
        }
    }
}

impl<'a> UnicodeCaseFold<Chars<'a>> for &'a str {
    fn case_fold_with(self, variant: Variant, locale: Locale) -> CaseFold<Chars<'a>> {
        CaseFold {
            inner: self.chars(),
            buffer: Buffer::Zero,
            variant: variant,
            locale: locale,
        }
    }
}

impl UnicodeCaseFold<Once<char>> for char {
    fn case_fold_with(self, variant: Variant, locale: Locale) -> CaseFold<Once<char>> {
        CaseFold {
            inner: iter::once(self),
            buffer: Buffer::Zero,
            variant: variant,
            locale: locale,
        }
    }
}

#[cfg(test)]
mod test {
    use {Locale, Variant, UnicodeCaseFold};

    #[test]
    fn simple() {
        assert_eq!("".case_fold().collect::<String>(), "");
        assert_eq!("AaBbCcDdEe".case_fold().collect::<String>(), "aabbccddee");
    }

    #[test]
    fn turkic() {
        assert_eq!("I\u{131}\u{130}i".case_fold_with(Variant::Full, Locale::NonTurkic).collect::<String>(), "i\u{131}i\u{307}i");
        assert_eq!("I\u{131}\u{130}i".case_fold_with(Variant::Simple, Locale::NonTurkic).collect::<String>(), "i\u{131}\u{130}i");
        assert_eq!("I\u{131}\u{130}i".case_fold_with(Variant::Full, Locale::Turkic).collect::<String>(), "\u{131}\u{131}ii");
        assert_eq!("I\u{131}\u{130}i".case_fold_with(Variant::Simple, Locale::Turkic).collect::<String>(), "\u{131}\u{131}ii");
    }

    #[test]
    fn no_case() {
        for &s in &["西遊記", "((!))", "サーナイト"] {
            assert_eq!(s.case_fold().collect::<String>(), s);
        }
    }

    #[test]
    fn size_hint() {
        let mut ss = vec!['ß'].into_iter().case_fold();
        assert_eq!(ss.size_hint(), (1, Some(3)));
        ss.next();
        assert_eq!(ss.size_hint(), (1, Some(1)));
    }
}
