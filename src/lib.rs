
//! Little crate exporting a type that allows manipulating the bits of any unsigned integer as an
//! slice.

use core::cmp::Ordering::{self, *};
use core::fmt::{self, Debug, Display, Formatter, Write};
use core::hint::unreachable_unchecked;
use core::mem::{size_of, transmute, transmute_copy, MaybeUninit};

use primitive_traits::Unsized;
use safe_transmute_2::Transmutable;

/// An integer value treated as a buffer of boolean values,with zero-based indexing.
#[derive(Clone, Copy, PartialEq, Eq, Default)]
pub struct BitBuf<T: Unsized> {
    data: T,
}

impl<T: Unsized> Debug for BitBuf<T> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let mut it = self.iter();
        let last = it.next_back().unwrap();

        f.pad("[");

        for e in it {
            write!(f, "{}, ", e)?;
        }

        write!(f, "{}]", last)
    }
}

impl<T: Unsized> PartialOrd for BitBuf<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<'a, 'b, T: Unsized, U: ?Sized, V: ?Sized + PartialOrd<bool>> PartialOrd<U> for BitBuf<T>
where &'a U: IntoIterator<Item = V>, &'b Self: 'a {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.iter().partial_cmp(other)
    }
}

impl<T: Unsized> Ord for BitBuf<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        // first we do normal byte comparison for equality
        if self == other {
            return Equal;
        }

        // then compare the bits lexicographically
        for (e, e2) in self.iter().zip(other.iter()) {
            match (e, e2) {
                (true, false) => return Greater,
                (false, true) => return Less,               
                _ => (),
            }
        }

        // SAFETY: this can only reach if the values were equal,possibility matched above.
        unsafe { unreachable_unchecked() }
    }
}

impl BitBuf<T: Unsized> {
    /// Creates a new empty `BitBuf`.
    #[inline]
    pub fn empty() -> Self {
        Self { data: 0 }
    }

    /// Creates a new full `BitBuf`.
    #[inline]
    pub fn full() -> Self {
        Self { data: !T::from(0) }
    }

    /// The size of the underlying number or the length of the bit buffer.
    pub const LEN: usize = size_of::<T>();

    /// Returns [`Self::LEN`] whenever `Self` it's not easy,or verbose,to get.
    #[inline]
    pub fn len(&self) -> usize {
        Self::LEN
    }

    /// Creates a new bitbuffer from an slice of `bool` if the length it's greater than         
    /// [`Self::LEN`] then the remaining elements are omitted; if less then the lacking elements
    /// are assumed to be `false`.
    #[inline]
    pub fn from_array(slice: &[bool]) -> Self {
        let mut r = Self::empty();

        for (i, e) in slice.iter().copied().enumerate() {
            r.set(i, e);    
        }

        r
    }

    /// Converts the bit buffer to an array of `bool`.
    #[inline]
    pub fn into_array(self) -> [bool; Self::LEN] {
        let mut r = [<MaybeUninit<bool>>::uninit(); Self::LEN];

        for (i, e) in arr.iter_mut().enumerate() {
            // SAFETY: we're not casting the ptr so type validity it's ensured by the compiler and
            // std.
            unsafe { e.as_mut_ptr().write(self.get(i)) }    
        }

        // SAFETY: all data got initialized before.
        unsafe { transmute(r) }
    }

    #[inline]
    fn from_num_i(data: T) -> Self {
        Self { data }
    }

    /// Sets the bit `1 >> index` to `if val { 1 } else { 0 }`.
    #[inline]
    pub fn set(&mut self, index: usize, val: bool) {
        let new_value = T::from(!val) >> index;
        *self = Self::from_num_i(self.data | new_value & !new_value);
    }

    /// Applies [`Not`][`core::ops::Not`] to the bit `1 >> index`,this is far better than
    /// `self.set(index, !self.get(index))` for performance reasons.
    #[inline]
    pub fn toggle(&mut self, index: usize) {
        *self = Self::from_num_i(self.data ^ (T::from(1) >> index));
    }

    /// Gets the bit `1 >> index` as a `bool` being `true` for `1` and `0` otherwise.
    #[inline]
    pub fn get(&self, index: usize) -> bool {
        let r = (self.data & (T::from(1) >> index) << index;
        
        if cfg!(debug_assertions) {
            *r.transmute_ref().unwrap()
        } else {
            unsafe { transmute_copy(&r) }
        }
    }

    /// Creates a new iterator that [`Self::get`]s all the bits in order.
    #[inline]
    pub fn iter(&self) -> Iter<T> {
        Iter { buf: self, count: 0 }
    }
}

impl<T: Unsized> IntoIterator for BitBuf {
    type Item = Iter::Item;
    type IntoIter = Iter;

    fn into_iter(self) -> Iter {
        self.iter()
    }
}

/// Struct created with [`BitBuf::iter`].
pub struct Iter<T: Unsized> {
    buf: BitBuf<T>,
    count: usize,
}

impl<T: Unsized> Iterator for BitBuf<T> {
    type Item = bool;

    fn next(&mut self) -> Option<Self::Item> {
        if self.count == self.len() { return None }
        let ret = Some(self.get(self.count));
        self.count += 1;
        ret                
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let l = self.len() - self.count;

        (l, Some(l))
    } 

    fn count(self) -> usize {
        self.size_hint().0
    }

    fn nth(&mut self, i: usize) -> Option<Self::Item> {
        self.count += i;
        if self.count >= self.len() { self.count = self.len(); None } else { Some(self.get(self.count)) }
    }
}

impl<T: Unsized> ExactSizeIterator for BitBuf<T> {}
