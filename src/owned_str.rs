use core::{
    borrow::{Borrow, BorrowMut},
    fmt::{Debug, Display, Write},
    mem::MaybeUninit,
    ops::{AddAssign, Deref, DerefMut, Index, IndexMut},
    slice::SliceIndex,
    str::FromStr,
};

use crate::unsized_str::UnsizedStr;

/// Represent an error that can happen when pushing a value into an [`OwnedStr`] if it lack the capacity for it.
#[derive(Debug, Clone, Copy)]
pub struct Error {
    /// The number of bytes remaining in the buffer
    /// this is `self.capacity() - self.len()`.
    pub spare_capacity: usize,
    /// The number of byte that was needed to add the value.
    pub needed_capacity: usize,
}

/// The Result of a push operation
pub type Result<T, E = Error> = core::result::Result<T, E>;

/// A `String` like buffer of a given size that can be stack allocated and also allows const operations.
/// This type should mostly be used only to allocate the stack space, but be manipulated via the unsized version [`UnsizedStr`]:
///
/// # Example
///
/// ```
/// use owned_str::{OwnedStr, UnsizedStr};
///
/// let mut os = OwnedStr::<16>::new();
///
/// const fn push_things(s: &mut UnsizedStr) {
///     s.push_str("Hello");
///     s.push(' ');
///     s.push_str("world!");
/// }
///
/// push_things(&mut os);
///
/// assert_eq!(os, "Hello world!");
///
/// ```
#[derive(Clone, Copy)]
#[repr(C)]
pub struct OwnedStr<const SIZE: usize> {
    len: usize,
    buff: [MaybeUninit<u8>; SIZE],
}

impl<const SIZE: usize> OwnedStr<SIZE> {
    /// Construct an empty `OwnedStr` of a given `SIZE`.
    pub const fn new() -> Self {
        OwnedStr {
            buff: [MaybeUninit::uninit(); SIZE],
            len: 0,
        }
    }

    /// Construct an `OwnedStr` of a given `SIZE` from a string slice.
    ///
    /// This is equivalent to `OwnedStr::new()` and pushing the string.
    ///
    /// Return an error if there is not enough space.
    pub const fn try_new_from_str(s: &str) -> Result<Self> {
        let mut this = Self::new();
        match this.unsize_mut().try_push_str(s) {
            Ok(_) => Ok(this),
            Err(err) => Err(err),
        }
    }

    /// Construct an `OwnedStr` of a given `SIZE` from a string slice.
    ///
    /// This is equivalent to `OwnedStr::new()` and pushing the string.
    #[track_caller]
    pub const fn new_from_str(s: &str) -> Self {
        #[track_caller]
        #[cold]
        const fn new_from_str_failed() -> ! {
            panic!("Tried to create a OwnedStr with a str exceeding capacity.")
        }
        match Self::try_new_from_str(s) {
            Ok(this) => this,
            Err(_) => new_from_str_failed(),
        }
    }

    /// Construct an `OwnedStr` of a given `SIZE` from another `OwnedStr`.
    ///
    /// This is equivalent to `OwnedStr::new()` and pushing the string of the other.
    ///
    /// Return an error if there is not enough space.
    pub const fn try_new_from_other<const SIZE_SRC: usize>(
        other: &OwnedStr<SIZE_SRC>,
    ) -> Result<Self> {
        Self::try_new_from_other_ref(other.unsize_ref())
    }

    /// Construct an `OwnedStr` of a given `SIZE` from a `&UnsizedStr`.
    ///
    /// This is equivalent to `OwnedStr::new()` and pushing the string of the other.
    ///
    /// Return an error if there is not enough space.
    pub const fn try_new_from_other_ref(other: &UnsizedStr) -> Result<Self> {
        Self::try_new_from_str(other.as_str())
    }

    /// Convert self to a [`str`].
    ///
    /// [`str`]: str
    pub const fn as_str(&self) -> &str {
        self.unsize_ref().as_str()
    }

    /// Convert self to a mutable [`str`].
    ///
    /// [`str`]: str
    pub const fn as_str_mut(&mut self) -> &mut str {
        self.unsize_mut().as_str_mut()
    }

    /// Return a size erased version of `Self`.
    pub const fn unsize_ref(&self) -> &UnsizedStr {
        UnsizedStr::from_owned_str_ref(self)
    }

    /// Return a mutable size erased version of `Self`.
    pub const fn unsize_mut(&mut self) -> &mut UnsizedStr {
        UnsizedStr::from_owned_str_mut(self)
    }
}

impl<const SIZE: usize> Debug for OwnedStr<SIZE> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        <str as Debug>::fmt(self, f)
    }
}

impl<const SIZE: usize> Display for OwnedStr<SIZE> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        <str as Display>::fmt(self, f)
    }
}

impl<const SIZE: usize> Default for OwnedStr<SIZE> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const SIZE: usize, T: AsRef<str> + ?Sized> PartialEq<T> for OwnedStr<SIZE> {
    fn eq(&self, other: &T) -> bool {
        self.as_str() == other.as_ref()
    }
}

impl<const SIZE: usize> Eq for OwnedStr<SIZE> {}

impl<const SIZE: usize, T: AsRef<str> + ?Sized> PartialOrd<T> for OwnedStr<SIZE> {
    fn partial_cmp(&self, other: &T) -> Option<core::cmp::Ordering> {
        self.as_str().partial_cmp(other.as_ref())
    }
}

impl<const SIZE: usize> Ord for OwnedStr<SIZE> {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.as_str().cmp(other.as_str())
    }
}

impl<const SIZE: usize, T: ?Sized> AsRef<T> for OwnedStr<SIZE>
where
    str: AsRef<T>,
{
    fn as_ref(&self) -> &T {
        self.as_str().as_ref()
    }
}

impl<const SIZE: usize> AsRef<UnsizedStr> for OwnedStr<SIZE> {
    fn as_ref(&self) -> &UnsizedStr {
        self.unsize_ref()
    }
}

impl<const SIZE: usize, T: ?Sized> AsMut<T> for OwnedStr<SIZE>
where
    str: AsMut<T>,
{
    fn as_mut(&mut self) -> &mut T {
        self.as_str_mut().as_mut()
    }
}

impl<const SIZE: usize> AsMut<UnsizedStr> for OwnedStr<SIZE> {
    fn as_mut(&mut self) -> &mut UnsizedStr {
        self.unsize_mut()
    }
}

impl<const SIZE: usize> Deref for OwnedStr<SIZE> {
    type Target = UnsizedStr;
    fn deref(&self) -> &Self::Target {
        self.unsize_ref()
    }
}

impl<const SIZE: usize> DerefMut for OwnedStr<SIZE> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.unsize_mut()
    }
}

impl<const SIZE: usize> AddAssign<&'_ str> for OwnedStr<SIZE> {
    fn add_assign(&mut self, rhs: &'_ str) {
        self.push_str(rhs);
    }
}

impl<const SIZE: usize> AddAssign<char> for OwnedStr<SIZE> {
    fn add_assign(&mut self, rhs: char) {
        self.push(rhs);
    }
}

impl<const SIZE: usize, T: ?Sized> Borrow<T> for OwnedStr<SIZE>
where
    str: Borrow<T>,
{
    fn borrow(&self) -> &T {
        self.as_str().borrow()
    }
}

impl<const SIZE: usize, T: ?Sized> BorrowMut<T> for OwnedStr<SIZE>
where
    str: BorrowMut<T>,
{
    fn borrow_mut(&mut self) -> &mut T {
        self.as_str_mut().borrow_mut()
    }
}

impl<const SIZE: usize> Borrow<UnsizedStr> for OwnedStr<SIZE> {
    fn borrow(&self) -> &UnsizedStr {
        self.unsize_ref()
    }
}

impl<const SIZE: usize> BorrowMut<UnsizedStr> for OwnedStr<SIZE> {
    fn borrow_mut(&mut self) -> &mut UnsizedStr {
        self.unsize_mut()
    }
}

impl<const SIZE: usize> FromStr for OwnedStr<SIZE> {
    type Err = Error;

    fn from_str(s: &str) -> core::result::Result<Self, Self::Err> {
        Self::try_new_from_str(s)
    }
}

impl<const SIZE: usize, I: SliceIndex<str>> Index<I> for OwnedStr<SIZE> {
    type Output = <I as SliceIndex<str>>::Output;

    fn index(&self, index: I) -> &Self::Output {
        Index::index(self.as_str(), index)
    }
}

impl<const SIZE: usize, I: SliceIndex<str>> IndexMut<I> for OwnedStr<SIZE> {
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        IndexMut::index_mut(self.as_str_mut(), index)
    }
}

impl<const SIZE: usize> TryFrom<&'_ UnsizedStr> for OwnedStr<SIZE> {
    type Error = Error;

    fn try_from(value: &'_ UnsizedStr) -> core::result::Result<Self, Self::Error> {
        Self::try_new_from_other_ref(value)
    }
}

impl<const SIZE: usize> TryFrom<&'_ str> for OwnedStr<SIZE> {
    type Error = Error;
    fn try_from(value: &'_ str) -> core::result::Result<Self, Self::Error> {
        Self::try_new_from_str(value)
    }
}

impl<const SIZE: usize> Write for OwnedStr<SIZE> {
    fn write_char(&mut self, c: char) -> core::fmt::Result {
        match self.try_push(c) {
            Ok(_) => Ok(()),
            Err(_) => Err(core::fmt::Error),
        }
    }

    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        match self.try_push_str(s) {
            Ok(_) => Ok(()),
            Err(_) => Err(core::fmt::Error),
        }
    }
}

#[cfg(feature = "serde")]
mod serde_impl {
    use super::OwnedStr;
    use serde::{de::Visitor, Deserialize, Serialize};

    impl<const SIZE: usize> Serialize for OwnedStr<SIZE> {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: serde::Serializer,
        {
            <str as Serialize>::serialize(self.as_str(), serializer)
        }
    }

    impl<'de, const SIZE: usize> Deserialize<'de> for OwnedStr<SIZE> {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: serde::Deserializer<'de>,
        {
            deserializer.deserialize_str(OwnedStrVisitor)
        }
    }

    struct OwnedStrVisitor<const SIZE: usize>;

    impl<const SIZE: usize> Visitor<'_> for OwnedStrVisitor<SIZE> {
        type Value = OwnedStr<SIZE>;

        fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
        where
            E: serde::de::Error,
        {
            match OwnedStr::try_new_from_str(v) {
                Ok(v) => Ok(v),
                Err(err) => Err(E::custom(err)),
            }
        }

        fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
            write!(formatter, "a string of maximum len {}", SIZE)
        }
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "Push exceeded capacity, needed space for {} bytes but only had {} bytes left.",
            self.needed_capacity, self.spare_capacity
        )
    }
}

impl core::error::Error for Error {}

#[cfg(test)]
mod tests {
    use super::*;

    #[allow(unused)]
    const fn make_str() -> OwnedStr<8> {
        let mut os = OwnedStr::new_from_str("test");
        let s = os.unsize_mut();
        s.push('t');
        s.push_str("est");
        os
    }

    const _: &str = make_str().as_str();

    #[test]
    fn test_pop() {
        let c = OwnedStr::<1>::new_from_str("s").pop();
        assert_eq!(c, Some('s'));

        let c = OwnedStr::<2>::new_from_str("é").pop();
        assert_eq!(c, Some('é'));

        let mut s = OwnedStr::<16>::new_from_str("és");
        assert_eq!(s.len(), 3);
        let c = s.pop();
        assert_eq!(s.len(), 2);
        assert_eq!(c, Some('s'));
        let c = s.pop();
        assert_eq!(s.len(), 0);
        assert_eq!(c, Some('é'));
    }

    #[test]
    fn test_c_str() {
        let mut s = OwnedStr::<2>::new_from_str("s");
        let s = s.make_cstr().unwrap();
        assert_eq!(s.to_bytes_with_nul(), b"s\0");

        let mut s = OwnedStr::<16>::new_from_str("s");
        s.push('\0'); // already have a null byte
        let s = s.make_cstr();
        assert_eq!(s, None);
    }
}
