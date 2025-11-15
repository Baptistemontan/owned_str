use core::{
    borrow::{Borrow, BorrowMut},
    fmt::{Debug, Display, Write},
    mem::MaybeUninit,
    ops::{AddAssign, Deref, DerefMut, Index, IndexMut},
    slice::SliceIndex,
    str::FromStr,
};
use std::{mem, usize};

use crate::owned_vec::unsized_vec::UnsizedVec;

mod unsized_vec;

// use crate::unsized_str::UnsizedStr;

/// Represent an error that can happen when pushing a value into an [`OwnedVec`] if it lack the capacity for it.
#[derive(Debug, Clone, Copy)]
pub struct Error<T> {
    /// The number of bytes remaining in the buffer
    /// this is `self.capacity() - self.len()`.
    pub spare_capacity: usize,
    /// The number of byte that was needed to add the value.
    pub needed_capacity: Option<usize>,
    /// the value(s) tried to be added
    pub value: T,
}

/// The Result of a push operation
pub type Result<T, V> = core::result::Result<T, Error<V>>;

/// A `Vec` like buffer of a given size that can be stack allocated and also allows const operations.
/// This type should mostly be used only to allocate the stack space, but be manipulated via the unsized version [`UnsizedStr`]:
///
/// # Example
///
/// ```
/// use owned_str::{OwnedVec, UnsizedVec};
///
/// let mut ov = OwnedVec::<16, i32>::new();
///
/// const fn push_things(s: &mut OwnedVec<i32>) {
///     s.push(4)
///     s.push(6);
///     s.push(89);
/// }
///
/// push_things(&mut ov);
///
/// assert_eq!(ov, &[4, 6, 89]);
///
/// ```
#[repr(C)]
pub struct OwnedVec<T, const SIZE: usize> {
    len: usize,
    buff: [MaybeUninit<T>; SIZE],
}

impl<const SIZE: usize, T: Clone> Clone for OwnedVec<T, SIZE> {
    fn clone(&self) -> Self {
        let mut cloned = Self::new();
        for x in self.as_slice() {
            cloned.push(x.clone());
        }
        cloned
    }
}

impl<const SIZE: usize, T: Copy> Copy for OwnedVec<T, SIZE> {}

impl<const SIZE: usize, T: Sized> OwnedVec<T, SIZE> {
    /// Construct an empty `OwnedStr` of a given `SIZE`.
    pub const fn new() -> Self {
        OwnedVec {
            buff: [const { MaybeUninit::uninit() }; SIZE],
            len: 0,
        }
    }

    pub const fn new_from_array(arr: [T; SIZE]) -> Self {
        let buff = unsafe {
            let buff_ptr = mem::transmute::<*const [T; SIZE], *const [MaybeUninit<T>; SIZE]>(&arr);
            buff_ptr.read()
        };
        mem::forget(arr);
        OwnedVec { len: SIZE, buff }
    }

    /// Convert self to a [`[T]`].
    ///
    /// [`[T]`]: [T]
    pub const fn as_slice(&self) -> &[T] {
        self.unsize_ref().as_slice()
    }

    /// Convert self to a mutable [`[T]`].
    ///
    /// [`[T]`]: [T]
    pub const fn as_slice_mut(&mut self) -> &mut [T] {
        self.unsize_mut().as_slice_mut()
    }

    /// Return a size erased version of `Self`.
    pub const fn unsize_ref(&self) -> &UnsizedVec<T> {
        UnsizedVec::from_owned_vec_ref(self)
    }

    /// Return a mutable size erased version of `Self`.
    pub const fn unsize_mut(&mut self) -> &mut UnsizedVec<T> {
        UnsizedVec::from_owned_vec_mut(self)
    }
}

impl<const SIZE: usize, T: Debug> Debug for OwnedVec<T, SIZE> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        <[T] as Debug>::fmt(self.as_slice(), f)
    }
}

impl<T, const SIZE: usize> Default for OwnedVec<T, SIZE> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const SIZE: usize, T: PartialEq, U: AsRef<[T]> + ?Sized> PartialEq<U> for OwnedVec<T, SIZE> {
    fn eq(&self, other: &U) -> bool {
        self.as_slice() == other.as_ref()
    }
}

impl<const SIZE: usize, T: Eq> Eq for OwnedVec<T, SIZE> {}

impl<const SIZE: usize, T: PartialOrd, U: AsRef<[T]> + ?Sized> PartialOrd<U> for OwnedVec<T, SIZE> {
    fn partial_cmp(&self, other: &U) -> Option<core::cmp::Ordering> {
        self.as_slice().partial_cmp(other.as_ref())
    }
}

impl<const SIZE: usize, T: Ord> Ord for OwnedVec<T, SIZE> {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.as_slice().cmp(other.as_slice())
    }
}

impl<const SIZE: usize, T, U: ?Sized> AsRef<U> for OwnedVec<T, SIZE>
where
    [T]: AsRef<U>,
{
    fn as_ref(&self) -> &U {
        self.as_slice().as_ref()
    }
}

impl<const SIZE: usize, T> AsRef<UnsizedVec<T>> for OwnedVec<T, SIZE> {
    fn as_ref(&self) -> &UnsizedVec<T> {
        self.unsize_ref()
    }
}

impl<const SIZE: usize, T, U: ?Sized> AsMut<U> for OwnedVec<T, SIZE>
where
    [T]: AsMut<U>,
{
    fn as_mut(&mut self) -> &mut U {
        self.as_slice_mut().as_mut()
    }
}

impl<const SIZE: usize, T> AsMut<UnsizedVec<T>> for OwnedVec<T, SIZE> {
    fn as_mut(&mut self) -> &mut UnsizedVec<T> {
        self.unsize_mut()
    }
}

impl<const SIZE: usize, T> Deref for OwnedVec<T, SIZE> {
    type Target = UnsizedVec<T>;
    fn deref(&self) -> &Self::Target {
        self.unsize_ref()
    }
}

impl<const SIZE: usize, T> DerefMut for OwnedVec<T, SIZE> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.unsize_mut()
    }
}

impl<const SIZE: usize, T, U: ?Sized> Borrow<U> for OwnedVec<T, SIZE>
where
    [T]: Borrow<U>,
{
    fn borrow(&self) -> &U {
        self.as_slice().borrow()
    }
}

impl<const SIZE: usize, T, U: ?Sized> BorrowMut<U> for OwnedVec<T, SIZE>
where
    [T]: BorrowMut<U>,
{
    fn borrow_mut(&mut self) -> &mut U {
        self.as_slice_mut().borrow_mut()
    }
}

impl<const SIZE: usize, T> Borrow<UnsizedVec<T>> for OwnedVec<T, SIZE> {
    fn borrow(&self) -> &UnsizedVec<T> {
        self.unsize_ref()
    }
}

impl<const SIZE: usize, T> BorrowMut<UnsizedVec<T>> for OwnedVec<T, SIZE> {
    fn borrow_mut(&mut self) -> &mut UnsizedVec<T> {
        self.unsize_mut()
    }
}

impl<const SIZE: usize, T, I: SliceIndex<[T]>> Index<I> for OwnedVec<T, SIZE> {
    type Output = <I as SliceIndex<[T]>>::Output;

    fn index(&self, index: I) -> &Self::Output {
        Index::index(self.as_slice(), index)
    }
}

impl<const SIZE: usize, T, I: SliceIndex<[T]>> IndexMut<I> for OwnedVec<T, SIZE> {
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        IndexMut::index_mut(self.as_slice_mut(), index)
    }
}

// impl<const SIZE: usize> Write for OwnedVec<SIZE> {
//     fn write_char(&mut self, c: char) -> core::fmt::Result {
//         match self.try_push(c) {
//             Ok(_) => Ok(()),
//             Err(_) => Err(core::fmt::Error),
//         }
//     }

//     fn write_str(&mut self, s: &str) -> core::fmt::Result {
//         match self.try_push_str(s) {
//             Ok(_) => Ok(()),
//             Err(_) => Err(core::fmt::Error),
//         }
//     }
// }

// #[cfg(feature = "serde")]
// mod serde_impl {
//     use super::OwnedStr;
//     use serde::{de::Visitor, Deserialize, Serialize};

//     impl<const SIZE: usize> Serialize for OwnedVec<SIZE> {
//         fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
//         where
//             S: serde::Serializer,
//         {
//             <str as Serialize>::serialize(self.as_str(), serializer)
//         }
//     }

//     impl<'de, const SIZE: usize> Deserialize<'de> for OwnedVec<SIZE> {
//         fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
//         where
//             D: serde::Deserializer<'de>,
//         {
//             deserializer.deserialize_str(OwnedStrVisitor)
//         }
//     }

//     struct OwnedStrVisitor<const SIZE: usize>;

//     impl<const SIZE: usize> Visitor<'_> for OwnedStrVisitor<SIZE> {
//         type Value = OwnedVec<SIZE>;

//         fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
//         where
//             E: serde::de::Error,
//         {
//             match OwnedVec::try_new_from_str(v) {
//                 Ok(v) => Ok(v),
//                 Err(err) => Err(E::custom(err)),
//             }
//         }

//         fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
//             write!(formatter, "a string of maximum len {}", SIZE)
//         }
//     }
// }

impl<T> Display for Error<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "Push exceeded capacity, needed space for {} bytes but only had {} bytes left.",
            self.needed_capacity.unwrap_or(usize::MAX),
            self.spare_capacity
        )
    }
}

impl<T: Debug> core::error::Error for Error<T> {}

// #[cfg(test)]
// mod tests {
//     use super::*;

//     #[allow(unused)]
//     const fn make_str() -> OwnedVec<8> {
//         let mut os = OwnedVec::new_from_str("test");
//         let s = os.unsize_mut();
//         s.push('t');
//         s.push_str("est");
//         os
//     }

//     const _: &str = make_str().as_str();

//     #[test]
//     fn test_pop() {
//         let c = OwnedVec::<1>::new_from_str("s").pop();
//         assert_eq!(c, Some('s'));

//         let c = OwnedVec::<2>::new_from_str("é").pop();
//         assert_eq!(c, Some('é'));

//         let mut s = OwnedVec::<16>::new_from_str("és");
//         assert_eq!(s.len(), 3);
//         let c = s.pop();
//         assert_eq!(s.len(), 2);
//         assert_eq!(c, Some('s'));
//         let c = s.pop();
//         assert_eq!(s.len(), 0);
//         assert_eq!(c, Some('é'));
//     }

//     #[test]
//     fn test_c_str() {
//         let mut s = OwnedVec::<2>::new_from_str("s");
//         let s = s.make_cstr().unwrap();
//         assert_eq!(s.to_bytes_with_nul(), b"s\0");

//         let mut s = OwnedVec::<16>::new_from_str("s");
//         s.push('\0'); // already have a null byte
//         let s = s.make_cstr();
//         assert_eq!(s, None);
//     }
// }
