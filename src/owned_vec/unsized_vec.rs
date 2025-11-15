use core::{
    borrow::{Borrow, BorrowMut},
    ffi::CStr,
    fmt::{Debug, Display, Write},
    hash::Hash,
    mem::{ManuallyDrop, MaybeUninit},
    ops::{AddAssign, Deref, DerefMut, Index, IndexMut},
    slice::SliceIndex,
};
use std::mem;

use super::{Error, OwnedVec, Result};

/// Helper struct used as an intermediate step to unsize `OwnedVec`.
/// See `UnsizedVec::from_owned_str_ref` and `UnsizedVec::from_owned_str_mut` implementations
#[repr(C)]
struct Helper<T: ?Sized> {
    len: usize,
    buff: T,
}

/// A size erased version of [`OwnedVec`], it is not [`Sized`] so is always behind a reference or a pointer.
///
/// To obtain one you can either:
/// - Deref an [`OwnedVec`]
/// - <code>[AsRef]<[UnsizedVec]></code> is implemented for [`OwnedVec`]
/// - Call [`unsize_*`] on [`OwnedVec`] which is `const`
/// - Use [`UnsizedVec::from_owned_vec_*`] which is also `const`
///
/// We advice users to pretty much always use this type and use [`OwnedVec`] to only create the stack space.
///
/// [`OwnedVec`]: OwnedVec
/// [`Sized`]: Sized
/// [`UnsizedVec::from_owned_vec_*`]: Self::from_owned_vec_ref
/// [`unsize_*`]: OwnedVec::unsize_ref
/// [UnsizedVec]: Self
/// [AsRef]: AsRef
#[repr(C)]
pub struct UnsizedVec<T> {
    len: usize,
    buff: [MaybeUninit<T>],
}

impl<T: Debug> Debug for UnsizedVec<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        <[T] as Debug>::fmt(self.as_slice(), f)
    }
}

// impl<T> Default for &'_ UnsizedVec<T> {
//     fn default() -> Self {
//         const DEFAULT_REF: &UnsizedVec<T> = OwnedVec::<0, T>::new().unsize_ref();
//         DEFAULT_REF
//     }
// }

impl<T: PartialEq, U: AsRef<[T]> + ?Sized> PartialEq<U> for UnsizedVec<T> {
    fn eq(&self, other: &U) -> bool {
        self.as_slice() == other.as_ref()
    }
}

impl<T: Eq> Eq for UnsizedVec<T> {}

impl<T: PartialOrd, U: AsRef<[T]> + ?Sized> PartialOrd<U> for UnsizedVec<T> {
    fn partial_cmp(&self, other: &U) -> Option<core::cmp::Ordering> {
        self.as_slice().partial_cmp(other.as_ref())
    }
}

impl<T: Ord> Ord for UnsizedVec<T> {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.as_slice().cmp(other.as_slice())
    }
}

impl<T: Hash> Hash for UnsizedVec<T> {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        <[T] as Hash>::hash(self.as_slice(), state);
    }
}

impl<T> UnsizedVec<T> {
    /// Cast a <code>&[OwnedVec]</code> to a size erased <code>&[UnsizedVec]</code>.
    ///
    /// [OwnedVec]: OwnedVec
    /// [UnsizedVec]: Self
    pub const fn from_owned_vec_ref<const SIZE: usize>(s: &OwnedVec<T, SIZE>) -> &Self {
        // The idea is to create a fat pointer to the `OwnedVec` with the buff size as the metadata,
        // The cleanest way I found was to have an intermediate struct that only serve as unsizing the inner buffer
        // we can then cast the ptr and take a ref
        // This is safe because `OwnedVec<SIZE, T>` and `Helper<[MaybeUninit<T>; SIZE]>` have the same layout (with #[repr(C)])
        // And the same goes for `Helper<[MaybeUninit<T>]>` and `UnsizedVec<T>` (with #[repr(C)] also).
        let p: *const Helper<[MaybeUninit<T>]> =
            s as *const OwnedVec<T, SIZE> as *const Helper<[MaybeUninit<T>; SIZE]>;
        let p = p as *const UnsizedVec<T>;
        unsafe { &*p }
    }

    /// Cast a <code>&mut [OwnedVec]</code> to a size erased <code>&mut [UnsizedVec]</code>.
    ///
    /// [OwnedVec]: OwnedVec
    /// [UnsizedVec]: Self
    pub const fn from_owned_vec_mut<const SIZE: usize>(s: &mut OwnedVec<T, SIZE>) -> &mut Self {
        // See `from_owned_str_ref` comments
        let p: *mut Helper<[MaybeUninit<T>]> =
            s as *mut OwnedVec<T, SIZE> as *mut Helper<[MaybeUninit<T>; SIZE]>;
        let p = p as *mut UnsizedVec<T>;
        unsafe { &mut *p }
    }

    /// Downcast a <code>&[UnsizedVec]</code> to a <code>&[OwnedVec]</code> of the given `SIZE`.
    ///
    /// # Safety
    ///
    /// This function does not perform any checks, the caller must ensure that `SIZE` is in the range <code>[[self.len()], [self.capacity()]]</code>.
    ///
    /// For a safe and checked version, see [`downcast`].
    ///
    /// [OwnedVec]: OwnedVec
    /// [UnsizedVec]: UnsizedVec
    /// [self.len()]: Self::len
    /// [self.capacity()]: Self::capacity
    /// [`downcast`]: Self::downcast
    pub const unsafe fn downcast_unchecked<const SIZE: usize>(this: &Self) -> &OwnedVec<T, SIZE> {
        // Safety
        // if SIZE is in the range `[len, cap]` then it is safe to do this cast
        // SIZE check is relagated to the caller.
        let p = this as *const Self as *const OwnedVec<T, SIZE>;
        unsafe { &*p }
    }

    /// Attempt to downcast a <code>&[UnsizedVec]</code> to a <code>&[OwnedVec]</code> of the given `SIZE`.
    ///
    /// This version is leniant on the size as it does'nt have to *exactly* match the one of the original,
    /// if `SIZE` is in the range <code>[[self.len()], [self.capacity()]]</code> then it is considered safe to perform this cast.
    ///
    /// If you want to have an exact match, you can use [`downcast_exact`].
    ///
    /// [OwnedVec]: OwnedVec
    /// [UnsizedVec]: UnsizedVec
    /// [self.len()]: Self::len
    /// [self.capacity()]: Self::capacity
    /// [`downcast_exact`]: Self::downcast_exact
    /// [`downcast_truncate`]: Self::downcast_truncate
    pub const fn downcast<const SIZE: usize>(this: &Self) -> Option<&OwnedVec<T, SIZE>> {
        if SIZE < this.len || SIZE > this.buff.len() {
            None
        } else {
            // SIZE validity is checked above
            Some(unsafe { Self::downcast_unchecked(this) })
        }
    }

    /// Attempt to downcast a <code>&[UnsizedVec]</code> to a <code>&[OwnedVec]</code> of the given `SIZE`.
    ///
    /// Contrary to [`downcast`], this version is strict on the target `SIZE`,
    /// It has to exactly match the one of the original [`OwnedVec`].
    ///
    /// [OwnedVec]: OwnedVec
    /// [UnsizedVec]: UnsizedVec
    /// [`downcast`]: Self::downcast
    /// [`OwnedVec`]: OwnedVec
    pub const fn downcast_exact<const SIZE: usize>(this: &Self) -> Option<&OwnedVec<T, SIZE>> {
        if SIZE != this.buff.len() {
            None
        } else {
            // SIZE validity is checked above
            Some(unsafe { Self::downcast_unchecked(this) })
        }
    }

    /// Downcast a <code>&mut [UnsizedVec]</code> to a <code>&mut [OwnedVec]</code> of the given `SIZE`.
    ///
    /// # Safety
    ///
    /// This function does not perform any checks, the caller must ensure that `SIZE` is in the range <code>[[self.len()], [self.capacity()]]</code>.
    ///
    /// For a safe and checked version, see [`downcast_mut`].
    ///
    /// [OwnedVec]: OwnedVec
    /// [UnsizedVec]: UnsizedVec
    /// [self.len()]: Self::len
    /// [self.capacity()]: Self::capacity
    /// [`downcast_mut`]: Self::downcast_mut
    pub const unsafe fn downcast_unchecked_mut<const SIZE: usize>(
        this: &mut Self,
    ) -> &mut OwnedVec<T, SIZE> {
        // Same reasoning as `downcast_unchecked`.
        let p = this as *mut Self as *mut OwnedVec<T, SIZE>;
        unsafe { &mut *p }
    }

    /// Attempt to downcast a <code>&mut [UnsizedVec]</code> to a <code>&mut [OwnedVec]</code> of the given `SIZE`.
    ///
    ///
    /// This version is leniant on the size as it does'nt have to *exactly* match the one of the original,
    /// if `SIZE` is in the range <code>[[self.len()], [self.capacity()]]</code> then it is considered safe to perform this cast.
    ///
    /// If you want to have an exact match, you can use [`downcast_exact_mut`].
    ///
    /// # Example
    ///
    /// ```
    /// use owned_str::{OwnedVec, UnsizedVec};
    ///
    /// let mut os = OwnedVec::<16>::new_from_slice_copy("Hello");
    /// let s: &mut UnsizedVec = &mut os;
    /// let mut os_ref = UnsizedVec::downcast_mut::<12>(s).unwrap();
    /// os_ref.push_str(" world!");
    /// assert_eq!(os, "Hello world!");
    /// ```
    ///
    /// [OwnedVec]: OwnedVec
    /// [UnsizedVec]: UnsizedVec
    /// [self.len()]: Self::len
    /// [self.capacity()]: Self::capacity
    /// [`downcast_exact_mut`]: Self::downcast_exact_mut
    pub const fn downcast_mut<const SIZE: usize>(
        this: &mut Self,
    ) -> Option<&mut OwnedVec<T, SIZE>> {
        if SIZE < this.len || SIZE > this.buff.len() {
            None
        } else {
            // SIZE validity is checked above
            Some(unsafe { Self::downcast_unchecked_mut(this) })
        }
    }

    /// Attempt to downcast a <code>&mut [UnsizedVec]</code> to a <code>&mut [OwnedVec]</code> of the given `SIZE`.
    ///
    /// Contrary to [`downcast`], this version is strict on the target `SIZE`,
    /// It has to exactly match the one of the original [`OwnedVec`].
    ///
    /// # Example
    ///
    /// ```
    /// use owned_str::{OwnedVec, UnsizedVec};
    ///
    /// let mut os = OwnedVec::<16>::new_from_slice_copy("Hello");
    /// let s: &mut UnsizedVec = &mut os;
    /// let mut os_ref = UnsizedVec::downcast_exact_mut::<16>(s).unwrap();
    /// os_ref.push_str(" world!");
    /// assert_eq!(os, "Hello world!");
    ///
    /// // Reject valid but not exact SIZE.
    /// assert!(UnsizedVec::downcast_exact_mut::<15>(&mut os).is_none());
    /// ```
    ///
    /// [OwnedVec]: OwnedVec
    /// [UnsizedVec]: UnsizedVec
    /// [`downcast`]: Self::downcast
    /// [`OwnedVec`]: OwnedVec
    pub const fn downcast_exact_mut<const SIZE: usize>(
        this: &mut Self,
    ) -> Option<&mut OwnedVec<T, SIZE>> {
        if SIZE != this.buff.len() {
            None
        } else {
            // SIZE validity is checked above
            Some(unsafe { Self::downcast_unchecked_mut(this) })
        }
    }

    /// Attempt to downcast a <code>&[UnsizedVec]</code> to a <code>&[OwnedVec]</code> of the given `SIZE`.
    ///
    /// This version is even more relaxed than [`downcast_mut`] on what `SIZE` can be, as it also accept `SIZE < self.len()`.
    /// If it is the case, it will set the length to `SIZE`, truncating the vec.
    ///
    /// Doesn't drop the truncated content to stay a const function, for a non-const but dropping version see [`downcast_truncate`].
    ///
    /// If you want to have a less relaxed version, see [`downcast_exact_mut`] or [`downcast_mut`].
    ///
    /// [OwnedVec]: OwnedVec
    /// [UnsizedVec]: UnsizedVec
    /// [self.len()]: Self::len
    /// [self.capacity()]: Self::capacity
    /// [`downcast_exact_mut`]: Self::downcast_exact
    /// [`downcast_mut`]: Self::downcast_mut
    /// [`downcast_truncate`]: Self::downcast_truncate
    pub const fn downcast_truncate_forget<const SIZE: usize>(
        this: &mut Self,
    ) -> Option<&mut OwnedVec<T, SIZE>> {
        if SIZE > this.buff.len() {
            return None;
        }
        this.truncate_forget(SIZE);
        // SIZE validity is checked above
        Some(unsafe { Self::downcast_unchecked_mut(this) })
    }

    /// Attempt to downcast a <code>&[UnsizedVec]</code> to a <code>&[OwnedVec]</code> of the given `SIZE`.
    ///
    /// This version is even more relaxed than [`downcast_mut`] on what `SIZE` can be, as it also accept `SIZE < self.len()`.
    /// If it is the case, it will set the length to `SIZE`, truncating the vec.
    ///
    /// Can't be a const function because of Drop call, for a const but non-dropping version see [`downcast_truncate_forget`].
    ///
    /// If you want to have a less relaxed version, see [`downcast_exact_mut`] or [`downcast_mut`].
    ///
    /// [OwnedVec]: OwnedVec
    /// [UnsizedVec]: UnsizedVec
    /// [self.len()]: Self::len
    /// [self.capacity()]: Self::capacity
    /// [`downcast_exact_mut`]: Self::downcast_exact
    /// [`downcast_mut`]: Self::downcast_mut
    /// [`downcast_truncate_forget`]: Self::downcast_truncate_forget
    pub fn downcast_truncate<const SIZE: usize>(this: &mut Self) -> Option<&mut OwnedVec<T, SIZE>> {
        if SIZE > this.buff.len() {
            return None;
        }
        this.truncate(SIZE);
        // SIZE validity is checked above
        Some(unsafe { Self::downcast_unchecked_mut(this) })
    }

    /// Clear the buffer without dropping content.
    ///
    /// This function does'nt actually modify the buffer but just set the len to 0.
    /// This does'nt drop content so it can be used in a const context, if you want to clear the buffer with calls to drop, use the non-const version [clear].
    ///
    /// If for some reason you want to actually erase the buffer you can use [`spare_capacity_mut`] after this call
    /// to get a <code>&mut [\[MaybeUninit&lt;T&gt;\]]</code> to the underlying buffer and erase it yourself.
    ///
    /// # Example
    ///
    /// ```
    /// use owned_str::OwnedVec;
    ///
    /// let mut s = OwnedVec::<3, i32>::new_from_slice_copy("abc");
    /// assert_eq!(s, "abc");
    /// s.clear();
    /// assert_eq!(s, "");
    /// ```
    ///
    /// [`spare_bytes_mut`]: Self::spare_bytes_mut
    /// [\[MaybeUninit&lt;u8&gt;\]]: MaybeUninit<u8>
    /// [clear]: Self::clear
    pub const fn clear_forget(&mut self) {
        self.len = 0;
    }

    /// Clear the buffer and drop the content.
    ///
    /// This function can't be const as `Drop` is not const, for a const, non-dropping variant see [clear_forget]
    ///
    /// If for some reason you want to actually erase the buffer you can use [`spare_capacity_mut`] after this call
    /// to get a <code>&mut [\[MaybeUninit&lt;T&gt;\]]</code> to the underlying buffer and erase it yourself.
    ///
    /// # Example
    ///
    /// ```
    /// use owned_str::OwnedVec;
    ///
    /// let mut s = OwnedVec::<3, i32>::new_from_slice_copy("abc");
    /// assert_eq!(s, "abc");
    /// s.clear();
    /// assert_eq!(s, "");
    /// ```
    ///
    /// [`spare_bytes_mut`]: Self::spare_bytes_mut
    /// [\[MaybeUninit&lt;u8&gt;\]]: MaybeUninit<u8>
    /// [clear_forget]: Self::clear_forget
    pub fn clear(&mut self) {
        let len = self.len;
        // SAFETY: it is important to set len to 0 *before* dropping the content in case drop panic.
        self.len = 0;
        unsafe {
            for el in self.buff.get_unchecked_mut(0..len).into_iter().rev() {
                el.assume_init_drop();
            }
        }
    }

    /// Tries to truncate the vec to the given length without dropping the removed content.
    ///
    /// Does'nt do anything if `len >= self.len()`.
    ///
    /// Does'nt drop the content so the function can be const. if you want to actually drop the content see [truncate].
    ///
    /// [truncate]: Self::truncate
    pub const fn truncate_forget(&mut self, len: usize) -> &mut Self {
        if len < self.len {
            self.len = len;
        }
        self
    }

    /// Tries to truncate the vec to the given length and drop the removed content.
    ///
    /// Does'nt do anything if `len >= self.len()`.
    ///
    /// Can not be const because of the drop. if you want a const version see [truncate_forget].
    ///
    /// [truncate_forget]: Self::truncate_forget
    pub fn truncate(&mut self, len: usize) -> &mut Self {
        if len < self.len {
            let current_len = self.len;
            // SAFETY: pre-set the len in case drop panic
            self.len = len;
            unsafe {
                for el in self
                    .buff
                    .get_unchecked_mut(len..current_len)
                    .iter_mut()
                    .rev()
                {
                    el.assume_init_drop();
                }
            }
        }
        self
    }

    /// Convert self to a slice.
    pub const fn as_slice(&self) -> &[T] {
        // The only footgun here would be if part of buff as not been initialized,
        // but we know that the buffer is initialized for at least `len` elements.
        // So this is safe
        let ptr = self.buff.as_ptr().cast::<T>();
        unsafe { core::slice::from_raw_parts(ptr, self.len) }
    }

    /// Convert self to a mutable slice.
    pub const fn as_slice_mut(&mut self) -> &mut [T] {
        // The only footgun here would be if part of buff as not been initialized,
        // but we know that the buffer is initialized for at least `len` bytes.
        // So this is safe
        let ptr = self.buff.as_mut_ptr().cast::<T>();
        unsafe { core::slice::from_raw_parts_mut(ptr, self.len) }
    }

    /// Return a mutable reference to the spare capacity of the buffer.
    pub const fn spare_capacity_mut(&mut self) -> &mut [MaybeUninit<T>] {
        // Safety: we know that len is less than buff.len()
        unsafe { self.buff.split_at_mut_unchecked(self.len).1 }
    }

    /// Convert self to a mutable byte slice, also containing the spare bytes.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the content of the slice is initialized until at least `self.len()`
    /// before the borrow ends and the underlying slice is used.
    ///
    /// Use of a [`OwnedVec`] whose contents are initialized is undefined behavior.
    ///
    /// [`OwnedVec`]: OwnedVec
    pub const unsafe fn as_buffer_mut(&mut self) -> &mut [MaybeUninit<T>] {
        &mut self.buff
    }

    /// Return the total capacity of the underlying buffer.
    ///
    /// This is the `SIZE` of the original [`OwnedVec`].
    ///
    /// # Example
    ///
    /// ```
    /// use owned_str::{OwnedVec, UnsizedVec};
    ///
    /// let s = OwnedVec::<16, i32>::new_from_slice_copy(&[1, 3, 7]);
    /// assert_eq!(s.capacity(), 16);
    ///
    /// let s: &UnsizedVec = &s;
    /// assert_eq!(s.capacity(), 16);
    /// ```
    ///
    /// [`OwnedVec`]: OwnedVec
    pub const fn capacity(&self) -> usize {
        self.buff.len()
    }

    /// Set the len to the given new len.
    ///
    /// # Safety
    ///
    /// The caller must uphold 2 invariants when calling this function:
    /// 1. That `len <= SIZE`.
    /// 2. That the underlying buffer is a valid array for `len` elements,
    ///     so each element must have been properly initialized.
    pub const unsafe fn set_len(&mut self, len: usize) {
        self.len = len;
    }

    /// Returns the length of self.
    ///
    /// # Examples
    ///
    /// ```
    /// use owned_str::OwnedVec;
    ///
    /// let s = OwnedVec::<16, i32>::new_from_slice_copy(&[1, 2, 7]);
    /// assert_eq!(s.len(), 3);
    ///
    /// let s = OwnedVec::<16, i32>::new_from_slice_copy(&[2, 4, 8, 0]);
    /// assert_eq!(s.len(), 4);
    /// ```
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Returns true if self has a length of zero element.
    ///
    /// # Examples
    ///
    /// ```
    /// use owned_str::OwnedVec;
    ///
    /// let s = OwnedVec::<16, i32>::new_from_slice_copy(&[]);
    /// assert!(s.is_empty());
    ///
    /// let s = OwnedVec::<16, i32>::new_from_slice_copy(&[1, 3, 5]);
    /// assert!(!s.is_empty());
    /// ```
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Appends the given value to the end.
    ///
    /// Panic if exceed the capacity.
    ///
    /// For a non-panicking variant, see [`try_push`]
    ///
    /// # Example
    ///
    /// ```
    /// use owned_str::OwnedVec;
    ///
    /// let mut v = OwnedVec::<i32, 2>::new();
    ///
    /// v.push(1).push(2);
    ///
    /// assert_eq!(v, &[1, 2]);
    /// ```
    ///
    /// *note*: To keep this function const, if the function fails `value` is not dropped, for a dropping variant use [`try_push`] and unwrap the result.
    ///
    /// [`try_push`]: Self::try_push
    #[track_caller]
    pub const fn push(&mut self, value: T) -> &mut Self {
        let res = ManuallyDrop::new(self.try_push(value));
        let res_ref = unsafe {
            mem::transmute::<&ManuallyDrop<Result<&mut Self, T>>, &Result<&mut Self, T>>(&res)
        };
        if res_ref.is_err() {
            push_panic()
        }
        self
    }

    /// Tries to append the given element to the end.
    ///
    /// Return an error if there is'nt enough space.
    ///
    /// # Example
    ///
    /// ```
    /// use owned_str::OwnedVec;
    ///
    /// let mut s = OwnedVec::<2, i32>::new();
    ///
    /// s.try_push(1)
    ///     .unwrap()
    ///     .try_push(2)
    ///     .unwrap();
    ///
    /// assert_eq!(s, &[1, 2]);
    ///
    /// let err = s.try_push(3);
    ///
    /// assert!(err.is_err());
    /// ```
    pub const fn try_push(&mut self, value: T) -> Result<&mut Self, T> {
        match self.len.checked_add(1) {
            // check that the new len does not overflow on addition and is in the capacity
            Some(new_len) if new_len <= self.buff.len() => {}
            needed_capacity => {
                return Err(Error {
                    spare_capacity: self.buff.len() - self.len,
                    needed_capacity,
                    value,
                });
            }
        };

        // Capacity has been checked above.
        Ok(unsafe { self.push_array_unchecked([value]) })
    }

    /// Append a given value onto the end without performing any checks.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the buffer has enough spare capacity to write this value.
    pub const unsafe fn push_unchecked(&mut self, value: T) -> &mut Self {
        // capacity check is relegated to the caller.
        unsafe { self.push_array_unchecked([value]) }
    }

    /// Append a given array onto the end without performing any checks.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the buffer has enough spare capacity to write this array.
    pub const unsafe fn push_array_unchecked<const S: usize>(&mut self, arr: [T; S]) -> &mut Self {
        // possible overflow checks are relegated to the caller.
        unsafe {
            let src = arr.as_ptr();
            let dest = self.buff.as_mut_ptr().cast::<T>().add(self.len);
            // s and buff can't overlap for 2 reasons:
            // - aliasing: can't have a mutable ref to self AND a string ref into it.
            // - end of buff is not initialized, can't have a str ref into it without unsafe.
            core::ptr::copy_nonoverlapping(src, dest, arr.len());
        }

        self.len += arr.len();

        core::mem::forget(arr);

        self
    }

    /// Removes the last value from the buffer and returns it.
    ///
    /// Returns [`None`] if empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use owned_str::OwnedVec;
    ///
    /// let mut s = OwnedVec::<i32, 3>::new_from_array([1, 2, 3]);
    ///
    /// assert_eq!(s.pop(), Some(3));
    /// assert_eq!(s.pop(), Some(2));
    /// assert_eq!(s.pop(), Some(1));
    ///
    /// assert_eq!(s.pop(), None);
    /// ```
    pub const fn pop(&mut self) -> Option<T> {
        if self.is_empty() {
            None
        } else {
            self.len -= 1;
            let value = unsafe { self.buff.as_ptr().cast::<T>().add(self.len).read() };
            Some(value)
        }
    }

    // /// Return true if `s` is in the string.
    // ///
    // /// This is equivalent to `s.find_str(s).is_some()`
    // ///
    // /// # Example
    // ///
    // /// ```
    // /// use owned_str::OwnedVec;
    // ///
    // /// let s = OwnedVec::<16>::new_from_slice_copy("abc");
    // /// assert_eq!(s.contain_str("bc"), true);
    // /// assert_eq!(s.contain_str("ad"), false);
    // /// ```
    // pub const fn contain_str(&self, s: &str) -> bool {
    //     self.find_str(s).is_some()
    // }

    // /// Return the position of the first occurence of `s` in the string, if any.
    // ///
    // /// # Example
    // ///
    // /// ```
    // /// use owned_str::OwnedVec;
    // ///
    // /// let s = OwnedVec::<16>::new_from_slice_copy("abc");
    // /// assert_eq!(s.find_str("ab"), Some(0));
    // /// assert_eq!(s.find_str("bc"), Some(1));
    // /// assert_eq!(s.find_str("ad"), None);
    // /// ```
    // pub const fn find_str(&self, s: &str) -> Option<usize> {
    //     crate::utils::find_str(self.as_bytes(), s)
    // }

    // /// Return true if `c` is in the string.
    // ///
    // /// This is equivalent to `s.find_char(c).is_some()`
    // ///
    // /// # Example
    // ///
    // /// ```
    // /// use owned_str::OwnedVec;
    // ///
    // /// let s = OwnedVec::<16>::new_from_slice_copy("abc");
    // /// assert_eq!(s.contain_char('b'), true);
    // /// assert_eq!(s.contain_char('d'), false);
    // /// ```
    // pub const fn contain_char(&self, c: char) -> bool {
    //     self.find_char(c).is_some()
    // }

    // /// Return the position of the first occurence of `c` in the string, if any.
    // ///
    // /// # Example
    // ///
    // /// ```
    // /// use owned_str::OwnedVec;
    // ///
    // /// let s = OwnedVec::<16>::new_from_slice_copy("abc");
    // /// assert_eq!(s.find_char('b'), Some(1));
    // /// assert_eq!(s.find_char('d'), None);
    // /// ```
    // pub const fn find_char(&self, c: char) -> Option<usize> {
    //     crate::utils::find_char(self.as_bytes(), c)
    // }

    // /// Return the number of chars.
    // ///
    // /// This is typicaly done with `s.chars().count()`, which is still the recommanded way to do it,
    // /// The only reason to use this function is in a const context, as iterators can't be used there.
    // ///
    // /// # Example
    // ///
    // /// ```
    // /// use owned_str::OwnedVec;
    // ///
    // /// let s = OwnedVec::<16>::new_from_slice_copy("abc");
    // /// assert_eq!(s.len(), 3);
    // /// assert_eq!(s.char_count(), 3);
    // ///
    // /// let s = OwnedVec::<16>::new_from_slice_copy("é");
    // /// assert_eq!(s.len(), 2);
    // /// assert_eq!(s.char_count(), 1);
    // /// ```
    // pub const fn char_count(&self) -> usize {
    //     let mut i = 0;
    //     let mut count = 0;
    //     while i < self.len {
    //         // SAFETY: utf8 validity requires that the string must contain
    //         // the continuation bytes (if any)
    //         i += crate::utils::utf8_char_width(unsafe { self.get_byte_unchecked(i) });
    //         count += 1;
    //     }
    //     count
    // }
}

impl<T, U: ?Sized> AsRef<U> for UnsizedVec<T>
where
    [T]: AsRef<U>,
{
    fn as_ref(&self) -> &U {
        self.as_slice().as_ref()
    }
}

impl<T, U: ?Sized> AsMut<U> for UnsizedVec<T>
where
    [T]: AsMut<U>,
{
    fn as_mut(&mut self) -> &mut U {
        self.as_slice_mut().as_mut()
    }
}

impl<T> Deref for UnsizedVec<T> {
    type Target = [T];
    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl<T> DerefMut for UnsizedVec<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_slice_mut()
    }
}

impl<T, U: ?Sized> Borrow<U> for UnsizedVec<T>
where
    [T]: Borrow<U>,
{
    fn borrow(&self) -> &U {
        self.as_slice().borrow()
    }
}

impl<T, U: ?Sized> BorrowMut<U> for UnsizedVec<T>
where
    [T]: BorrowMut<U>,
{
    fn borrow_mut(&mut self) -> &mut U {
        self.as_slice_mut().borrow_mut()
    }
}

impl<T, I: SliceIndex<[T]>> Index<I> for UnsizedVec<T> {
    type Output = <I as SliceIndex<[T]>>::Output;

    fn index(&self, index: I) -> &Self::Output {
        Index::index(self.as_slice(), index)
    }
}

impl<T, I: SliceIndex<[T]>> IndexMut<I> for UnsizedVec<T> {
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        IndexMut::index_mut(self.as_slice_mut(), index)
    }
}

// impl Write for UnsizedVec {
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

#[cfg(feature = "serde")]
mod serde_impl {
    use super::UnsizedVec;
    use serde::Serialize;

    impl Serialize for UnsizedVec {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: serde::Serializer,
        {
            <str as Serialize>::serialize(self.as_str(), serializer)
        }
    }
}

#[track_caller]
#[cold]
const fn push_panic() -> ! {
    panic!("Tried to push a value to a OwnedVec but exceeded capacity.")
}

// #[cfg(test)]
// mod tests {
//     use super::*;

//     #[test]
//     fn test_downcast() {
//         let os = OwnedVec::<10>::new_from_slice_copy("test");
//         let s = os.unsize_ref();
//         let os_ref = UnsizedVec::downcast::<5>(s).unwrap();
//         assert_eq!(os_ref, "test")
//     }
// }
