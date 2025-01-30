use core::{
    borrow::{Borrow, BorrowMut},
    ffi::CStr,
    fmt::{Debug, Display, Write},
    hash::Hash,
    mem::MaybeUninit,
    ops::{AddAssign, Deref, DerefMut, Index, IndexMut},
    slice::SliceIndex,
};

use crate::owned_str::{Error, OwnedStr, Result};

/// Helper struct used as an intermediate step to unsize `OwnedStr`.
/// See `UnsizedStr::from_owned_str_ref` and `UnsizedStr::from_owned_str_mut` implementations
#[repr(C)]
struct Helper<T: ?Sized> {
    len: usize,
    buff: T,
}

/// A size erased version of [`OwnedStr`], it is not [`Sized`] so is always behind a reference or a pointer.
///
/// To obtain one you can either:
/// - Deref an [`OwnedStr`]
/// - <code>[AsRef]<[UnsizedStr]></code> is implemented for [`OwnedStr`]
/// - Call [`unsize_*`] on [`OwnedStr`] which is `const`
/// - Use [`UnsizedStr::from_owned_str_*`] which is also `const`
///
/// We advice users to pretty much always use this type and use [`OwnedStr`] to only create the stack space.
///
/// [`OwnedStr`]: OwnedStr
/// [`Sized`]: Sized
/// [`UnsizedStr::from_owned_str_*`]: Self::from_owned_str_ref
/// [`unsize_*`]: OwnedStr::unsize_ref
/// [UnsizedStr]: Self
/// [AsRef]: AsRef
#[repr(C)]
pub struct UnsizedStr {
    len: usize,
    buff: [MaybeUninit<u8>],
}

impl Debug for UnsizedStr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        <str as Debug>::fmt(self, f)
    }
}

impl Display for UnsizedStr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        <str as Display>::fmt(self, f)
    }
}

impl Default for &'_ UnsizedStr {
    fn default() -> Self {
        const DEFAULT_REF: &UnsizedStr = OwnedStr::<0>::new().unsize_ref();
        DEFAULT_REF
    }
}

impl<T: AsRef<str> + ?Sized> PartialEq<T> for UnsizedStr {
    fn eq(&self, other: &T) -> bool {
        self.as_str() == other.as_ref()
    }
}

impl Eq for UnsizedStr {}

impl<T: AsRef<str> + ?Sized> PartialOrd<T> for UnsizedStr {
    fn partial_cmp(&self, other: &T) -> Option<core::cmp::Ordering> {
        self.as_str().partial_cmp(other.as_ref())
    }
}

impl Ord for UnsizedStr {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.as_str().cmp(other.as_str())
    }
}

impl Hash for UnsizedStr {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        <str as Hash>::hash(self, state);
    }
}

impl UnsizedStr {
    /// Cast a <code>&[OwnedStr&lt;SIZE&gt;]</code> to a size erased <code>&[UnsizedStr]</code>.
    ///
    /// [OwnedStr&lt;SIZE&gt;]: OwnedStr
    /// [UnsizedStr]: UnsizedStr
    pub const fn from_owned_str_ref<const SIZE: usize>(s: &OwnedStr<SIZE>) -> &Self {
        // The idea is to create a fat pointer to the `OwnedStr` with the buff size as the metadata,
        // The cleanest way I found was to have an intermediate struct that only serve as unsizing the inner buffer
        // we can then cast the ptr and take a ref
        // This is safe because `OwnedStr<SIZE>` and `Helper<[MaybeUninit<u8>; SIZE]>` have the same layout (with #[repr(C)])
        // And the same goes for `Helper<[MaybeUninit<u8>]>` and `UnsizedStr` (with #[repr(C)] also).
        let p: *const Helper<[MaybeUninit<u8>]> =
            s as *const OwnedStr<SIZE> as *const Helper<[MaybeUninit<u8>; SIZE]>;
        let p = p as *const UnsizedStr;
        unsafe { &*p }
    }

    /// Cast a <code>&mut [OwnedStr&lt;SIZE&gt;]</code> to a size erased <code>&mut [UnsizedStr]</code>.
    ///
    /// [OwnedStr&lt;SIZE&gt;]: OwnedStr
    /// [UnsizedStr]: UnsizedStr
    pub const fn from_owned_str_mut<const SIZE: usize>(s: &mut OwnedStr<SIZE>) -> &mut Self {
        // See `from_owned_str_ref` comments
        let p: *mut Helper<[MaybeUninit<u8>]> =
            s as *mut OwnedStr<SIZE> as *mut Helper<[MaybeUninit<u8>; SIZE]>;
        let p = p as *mut UnsizedStr;
        unsafe { &mut *p }
    }

    /// Downcast a <code>&[UnsizedStr]</code> to a <code>&[OwnedStr&lt;SIZE&gt;]</code> of the given `SIZE`.
    ///
    /// # Safety
    ///
    /// This function does not perform any checks, the caller must ensure that `SIZE` is in the range <code>[[self.len()], [self.capacity()]]</code>.
    ///
    /// For a safe and checked version, see [`downcast`].
    ///
    /// [OwnedStr&lt;SIZE&gt;]: OwnedStr
    /// [UnsizedStr]: UnsizedStr
    /// [self.len()]: Self::len
    /// [self.capacity()]: Self::capacity
    /// [`downcast`]: Self::downcast
    pub const unsafe fn downcast_unchecked<const SIZE: usize>(this: &Self) -> &OwnedStr<SIZE> {
        // Safety
        // if SIZE is in the range `[len, cap]` then it is safe to do this cast
        // SIZE check is relagated to the caller.
        let p = this as *const Self as *const OwnedStr<SIZE>;
        unsafe { &*p }
    }

    /// Attempt to downcast a <code>&[UnsizedStr]</code> to a <code>&[OwnedStr&lt;SIZE&gt;]</code> of the given `SIZE`.
    ///
    /// This version is leniant on the size as it does'nt have to *exactly* match the one of the original,
    /// if `SIZE` is in the range <code>[[self.len()], [self.capacity()]]</code> then it is considered safe to perform this cast.
    ///
    /// If you want to have an exact match, you can use [`downcast_exact`].
    ///
    /// [OwnedStr&lt;SIZE&gt;]: OwnedStr
    /// [UnsizedStr]: UnsizedStr
    /// [self.len()]: Self::len
    /// [self.capacity()]: Self::capacity
    /// [`downcast_exact`]: Self::downcast_exact
    /// [`downcast_truncate`]: Self::downcast_truncate
    pub const fn downcast<const SIZE: usize>(this: &Self) -> Option<&OwnedStr<SIZE>> {
        if SIZE < this.len || SIZE > this.buff.len() {
            None
        } else {
            // SIZE validity is checked above
            Some(unsafe { Self::downcast_unchecked(this) })
        }
    }

    /// Attempt to downcast a <code>&[UnsizedStr]</code> to a <code>&[OwnedStr&lt;SIZE&gt;]</code> of the given `SIZE`.
    ///
    /// Contrary to [`downcast`], this version is strict on the target `SIZE`,
    /// It has to exactly match the one of the original [`OwnedStr`].
    ///
    /// [OwnedStr&lt;SIZE&gt;]: OwnedStr
    /// [UnsizedStr]: UnsizedStr
    /// [`downcast`]: Self::downcast
    /// [`OwnedStr`]: OwnedStr
    pub const fn downcast_exact<const SIZE: usize>(this: &Self) -> Option<&OwnedStr<SIZE>> {
        if SIZE != this.buff.len() {
            None
        } else {
            // SIZE validity is checked above
            Some(unsafe { Self::downcast_unchecked(this) })
        }
    }

    /// Downcast a <code>&mut [UnsizedStr]</code> to a <code>&mut [OwnedStr&lt;SIZE&gt;]</code> of the given `SIZE`.
    ///
    /// # Safety
    ///
    /// This function does not perform any checks, the caller must ensure that `SIZE` is in the range <code>[[self.len()], [self.capacity()]]</code>.
    ///
    /// For a safe and checked version, see [`downcast_mut`].
    ///
    /// [OwnedStr&lt;SIZE&gt;]: OwnedStr
    /// [UnsizedStr]: UnsizedStr
    /// [self.len()]: Self::len
    /// [self.capacity()]: Self::capacity
    /// [`downcast_mut`]: Self::downcast_mut
    pub const unsafe fn downcast_unchecked_mut<const SIZE: usize>(
        this: &mut Self,
    ) -> &mut OwnedStr<SIZE> {
        // Same reasoning as `downcast_unchecked`.
        let p = this as *mut Self as *mut OwnedStr<SIZE>;
        unsafe { &mut *p }
    }

    /// Attempt to downcast a <code>&mut [UnsizedStr]</code> to a <code>&mut [OwnedStr&lt;SIZE&gt;]</code> of the given `SIZE`.
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
    /// use owned_str::{OwnedStr, UnsizedStr};
    ///
    /// let mut os = OwnedStr::<16>::new_from_str("Hello");
    /// let s: &mut UnsizedStr = &mut os;
    /// let mut os_ref = UnsizedStr::downcast_mut::<12>(s).unwrap();
    /// os_ref.push_str(" world!");
    /// assert_eq!(os, "Hello world!");
    /// ```
    ///
    /// [OwnedStr&lt;SIZE&gt;]: OwnedStr
    /// [UnsizedStr]: UnsizedStr
    /// [self.len()]: Self::len
    /// [self.capacity()]: Self::capacity
    /// [`downcast_exact_mut`]: Self::downcast_exact_mut
    pub const fn downcast_mut<const SIZE: usize>(this: &mut Self) -> Option<&mut OwnedStr<SIZE>> {
        if SIZE < this.len || SIZE > this.buff.len() {
            None
        } else {
            // SIZE validity is checked above
            Some(unsafe { Self::downcast_unchecked_mut(this) })
        }
    }

    /// Attempt to downcast a <code>&mut [UnsizedStr]</code> to a <code>&mut [OwnedStr&lt;SIZE&gt;]</code> of the given `SIZE`.
    ///
    /// Contrary to [`downcast`], this version is strict on the target `SIZE`,
    /// It has to exactly match the one of the original [`OwnedStr`].
    ///
    /// # Example
    ///
    /// ```
    /// use owned_str::{OwnedStr, UnsizedStr};
    ///
    /// let mut os = OwnedStr::<16>::new_from_str("Hello");
    /// let s: &mut UnsizedStr = &mut os;
    /// let mut os_ref = UnsizedStr::downcast_exact_mut::<16>(s).unwrap();
    /// os_ref.push_str(" world!");
    /// assert_eq!(os, "Hello world!");
    ///
    /// // Reject valid but not exact SIZE.
    /// assert!(UnsizedStr::downcast_exact_mut::<15>(&mut os).is_none());
    /// ```
    ///
    /// [OwnedStr&lt;SIZE&gt;]: OwnedStr
    /// [UnsizedStr]: UnsizedStr
    /// [`downcast`]: Self::downcast
    /// [`OwnedStr`]: OwnedStr
    pub const fn downcast_exact_mut<const SIZE: usize>(
        this: &mut Self,
    ) -> Option<&mut OwnedStr<SIZE>> {
        if SIZE != this.buff.len() {
            None
        } else {
            // SIZE validity is checked above
            Some(unsafe { Self::downcast_unchecked_mut(this) })
        }
    }

    /// Attempt to downcast a <code>&[UnsizedStr]</code> to a <code>&[OwnedStr&lt;SIZE&gt;]</code> of the given `SIZE`.
    ///
    /// This version is even more relaxed than [`downcast_mut`] on what `SIZE` can be, as it also accept `SIZE < self.len()` if it lands on a char boundary.
    /// If it is the case, it will set the length to `SIZE`, truncating the string.
    ///
    /// If you want to have a less relaxed version, see [`downcast_exact_mut`] or [`downcast_mut`].
    ///
    /// [OwnedStr&lt;SIZE&gt;]: OwnedStr
    /// [UnsizedStr]: UnsizedStr
    /// [self.len()]: Self::len
    /// [self.capacity()]: Self::capacity
    /// [`downcast_exact_mut`]: Self::downcast_exact
    /// [`downcast_mut`]: Self::downcast_mut
    pub const fn downcast_truncate<const SIZE: usize>(
        this: &mut Self,
    ) -> Option<&mut OwnedStr<SIZE>> {
        if SIZE > this.buff.len() {
            return None;
        }
        if SIZE < this.len {
            if this.is_char_boundary(SIZE) {
                this.len = SIZE
            } else {
                return None;
            }
        }
        // SIZE validity is checked above
        Some(unsafe { Self::downcast_unchecked_mut(this) })
    }

    /// Clear the buffer.
    ///
    /// This function does'nt actually modify the buffer but just set the len to 0.
    ///
    /// If for some reason you want to actually erase the buffer you can use [`spare_bytes_mut`] after this call
    /// to get a <code>&mut [\[MaybeUninit&lt;u8&gt;\]]</code> to the underlying buffer and erase it yourself.
    ///
    /// # Example
    ///
    /// ```
    /// use owned_str::OwnedStr;
    ///
    /// let mut s = OwnedStr::<3>::new_from_str("abc");
    /// assert_eq!(s, "abc");
    /// s.clear();
    /// assert_eq!(s, "");
    /// ```
    ///
    /// [`spare_bytes_mut`]: Self::spare_bytes_mut
    /// [\[MaybeUninit&lt;u8&gt;\]]: MaybeUninit<u8>
    pub const fn clear(&mut self) {
        self.len = 0;
    }

    /// Tries to truncate the string to the given length.
    ///
    /// Return `None` if `len < self.len()` but is not a char boundary.
    ///
    /// Return `Some(Self)` without modifying the length if `len > self.len()`
    pub const fn try_truncate(&mut self, len: usize) -> Option<&mut Self> {
        if len < self.len {
            if self.is_char_boundary(len) {
                self.len = len;
            } else {
                return None;
            }
        }
        Some(self)
    }

    /// Convert self to a byte slice.
    ///
    /// This is equivalent to `self.as_str().as_bytes()`.
    pub const fn as_bytes(&self) -> &[u8] {
        // The only footgun here would be if part of buff as not been initialized,
        // but we know that the buffer is initialized for at least `len` bytes.
        // So this is safe
        let ptr = self.buff.as_ptr().cast::<u8>();
        unsafe { core::slice::from_raw_parts(ptr, self.len) }
    }

    /// Convert self to a mutable byte slice.
    ///
    /// This is equivalent to `self.as_str_mut().as_bytes_mut()`.
    /// # Safety
    ///
    /// The caller must ensure that the content of the slice is valid UTF-8
    /// before the borrow ends and the underlying `str` is used.
    ///
    /// Use of a `OwnedStr` whose contents are not valid UTF-8 is undefined behavior.
    pub const unsafe fn as_bytes_mut(&mut self) -> &mut [u8] {
        // The only footgun here would be if part of buff as not been initialized,
        // but we know that the buffer is initialized for at least `len` bytes.
        // So this is safe
        let ptr = self.buff.as_mut_ptr().cast::<u8>();
        unsafe { core::slice::from_raw_parts_mut(ptr, self.len) }
    }

    /// Return a mutable reference to the spare bytes of the buffer.
    ///
    /// # Safety
    ///
    /// This function is marked safe as modifications to the spare bytes have no impact on the `str` integrity.
    ///
    /// When using a `String` you would normally call `as_mut_vec` and modify the underlying byte vector to freely write to it
    /// But [`OwnedStr`] use a fixed sized array as a buffer, so you can write directly to the end of the buffer then call
    /// [`set_len`] when done writing.
    ///
    /// If you want access to the full buffer, you can use [`as_buffer_mut`]
    ///
    /// [`OwnedStr`]: OwnedStr
    /// [`set_len`]: Self::set_len
    /// [`as_buffer_mut`]: Self::as_buffer_mut
    pub const fn spare_bytes_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        // Safety: we know that len is less than buff.len()
        unsafe { self.buff.split_at_mut_unchecked(self.len).1 }
    }

    /// Convert self to a mutable byte slice, also containing the spare bytes.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the content of the slice is valid UTF-8 until at least `self.len()`
    /// before the borrow ends and the underlying `str` is used.
    ///
    /// Use of a [`OwnedStr`] whose contents are not valid UTF-8 is undefined behavior.
    ///
    /// [`OwnedStr`]: OwnedStr
    pub const unsafe fn as_buffer_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        &mut self.buff
    }

    /// Convert self to a [`str`].
    ///
    /// [`str`]: str
    pub const fn as_str(&self) -> &str {
        // Safety: The buffer is valid UTF8.
        let bytes = Self::as_bytes(self);
        unsafe { core::str::from_utf8_unchecked(bytes) }
    }

    /// Convert self to a [`str`].
    ///
    /// [`str`]: str
    pub const fn as_str_mut(&mut self) -> &mut str {
        // Safety: The buffer is valid UTF8.
        unsafe {
            let bytes = Self::as_bytes_mut(self);
            core::str::from_utf8_unchecked_mut(bytes)
        }
    }

    /// Return the total capacity of the underlying buffer.
    ///
    /// This is the `SIZE` of the original [`OwnedStr`].
    ///
    /// # Example
    ///
    /// ```
    /// use owned_str::{OwnedStr, UnsizedStr};
    ///
    /// let s = OwnedStr::<16>::new_from_str("abc");
    /// assert_eq!(s.capacity(), 16);
    ///
    /// let s: &UnsizedStr = &s;
    /// assert_eq!(s.capacity(), 16);
    /// ```
    ///
    /// [`OwnedStr`]: OwnedStr
    pub const fn capacity(&self) -> usize {
        self.buff.len()
    }

    /// Set the len to the given new len.
    ///
    /// # Safety
    ///
    /// The caller must uphold 2 invariants when calling this function:
    /// 1. That `len <= SIZE`.
    /// 2. That the underlying buffer is a valid str for `len` bytes,
    ///     so it must be valid UTF8, each bytes must have been properly initialized.
    ///
    /// Be cautious with UTF-8 char boundary.
    pub const unsafe fn set_len(&mut self, len: usize) {
        self.len = len;
    }

    /// Returns the length of self.
    ///
    /// This length is in bytes, not chars or graphemes. In other words, it might not be what a human considers the length of the string.
    ///
    /// # Examples
    ///
    /// ```
    /// use owned_str::OwnedStr;
    ///
    /// let s = OwnedStr::<16>::new_from_str("abc");
    /// assert_eq!(s.len(), 3);
    ///
    /// let s = OwnedStr::<16>::new_from_str("éä");
    /// assert_eq!(s.len(), 4);
    /// ```
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Returns true if self has a length of zero bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// use owned_str::OwnedStr;
    ///
    /// let s = OwnedStr::<16>::new_from_str("");
    /// assert!(s.is_empty());
    ///
    /// let s = OwnedStr::<16>::new_from_str("abc");
    /// assert!(!s.is_empty());
    /// ```
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Tries to append the given [`char`] to the end.
    ///
    /// Return an error if there is'nt enough space.
    ///
    /// # Example
    ///
    /// ```
    /// use owned_str::OwnedStr;
    ///
    /// let mut s = OwnedStr::<2>::new();
    ///
    /// s.try_push('a')
    ///     .unwrap()
    ///     .try_push('b')
    ///     .unwrap();
    ///
    /// assert_eq!(s, "ab");
    ///
    /// let err = s.try_push('c');
    ///
    /// assert!(err.is_err());
    /// ```
    pub const fn try_push(&mut self, c: char) -> Result<&mut Self> {
        self.try_push_str(c.encode_utf8(&mut [0; 4]))
    }

    /// Appends the given [`char`] to the end.
    ///
    /// Panic if exceed the capacity.
    ///
    /// For a non-panicking variant, see [`try_push`]
    ///
    /// # Example
    ///
    /// ```
    /// use owned_str::OwnedStr;
    ///
    /// let mut s = OwnedStr::<2>::new();
    ///
    /// s.push('a').push('b');
    ///
    /// assert_eq!(s, "ab");
    /// ```
    ///
    /// [`try_push`]: Self::try_push
    #[track_caller]
    pub const fn push(&mut self, c: char) -> &mut Self {
        if self.try_push(c).is_err() {
            push_panic()
        }
        self
    }

    /// Append a given char onto the end without performing any checks.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the buffer has enough spare capacity to write this value.
    pub const unsafe fn push_unchecked(&mut self, c: char) -> &mut Self {
        // capacity check is relegated to the caller.
        unsafe { self.push_str_unchecked(c.encode_utf8(&mut [0; 4])) }
    }

    /// Tries to append a given string slice onto the end.
    ///
    /// Return an error if there is'nt enough space.
    ///
    /// # Example
    ///
    /// ```
    /// use owned_str::OwnedStr;
    ///
    /// let mut s = OwnedStr::<16>::new();
    ///
    /// s.try_push_str("Hello ")
    ///     .unwrap()
    ///     .try_push_str("world")
    ///     .unwrap();
    ///
    /// assert_eq!(s, "Hello world");
    ///
    /// let err = s.try_push_str("Very long string that definitely exceed capacity");
    ///
    /// assert!(err.is_err());
    /// ```
    pub const fn try_push_str(&mut self, s: &str) -> Result<&mut Self> {
        match s.len().checked_add(self.len) {
            // check that the new len does not overflow on addition and is in the capacity
            Some(new_len) if new_len <= self.buff.len() => {}
            _ => {
                return Err(Error {
                    spare_capacity: self.buff.len() - self.len,
                    needed_capacity: s.len(),
                });
            }
        };

        // Capacity has been checked above.
        Ok(unsafe { self.push_str_unchecked(s) })
    }

    /// Append a given string slice onto the end without performing any checks.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the buffer has enough spare capacity to write this value.
    pub const unsafe fn push_str_unchecked(&mut self, s: &str) -> &mut Self {
        // s is valid UTF8 so it can be copied at the end of the buffer,
        // possible overflow checks are relegated to the caller.
        unsafe {
            let src = s.as_bytes().as_ptr();
            let dest = self.buff.as_mut_ptr().cast::<u8>().add(self.len);
            // s and buff can't overlap for 2 reasons:
            // - aliasing: can't have a mutable ref to self AND a string ref into it.
            // - end of buff is not initialized, can't have a str ref into it without unsafe.
            core::ptr::copy_nonoverlapping(src, dest, s.len());
        }

        self.len += s.len();

        self
    }

    /// Appends a given string slice onto the end.
    ///
    /// Panic if exceed the capacity.
    ///
    /// For a non-panicking variant, see [`try_push_str`]
    ///
    /// # Example
    ///
    /// ```
    /// use owned_str::OwnedStr;
    ///
    /// let mut s = OwnedStr::<32>::new();
    ///
    /// s.push_str("Hello ").push_str("world");
    ///
    /// assert_eq!(s, "Hello world");
    /// ```
    ///
    /// [`try_push_str`]: Self::try_push_str
    #[track_caller]
    pub const fn push_str(&mut self, s: &str) -> &mut Self {
        if self.try_push_str(s).is_err() {
            push_panic()
        }
        self
    }

    /// Return the byte at the given index without perfoming any checks
    ///
    /// # Safety
    ///
    /// Caller must ensure that `index <= self.len`.
    const unsafe fn get_byte_unchecked(&self, index: usize) -> u8 {
        unsafe { self.buff.as_ptr().cast::<u8>().add(index).read() }
    }

    /// Checks that `index`-th byte is the first byte in a UTF-8 code point
    /// sequence or the end of the string.
    ///
    /// The start and end of the string (when `index == self.len()`) are
    /// considered to be boundaries.
    ///
    /// Returns `false` if `index` is greater than `self.len()`.
    ///
    /// # Examples
    ///
    /// ```
    /// use owned_str::OwnedStr;
    ///
    /// let s = OwnedStr::<32>::new_from_str("Löwe 老虎 Léopard");
    /// assert!(s.is_char_boundary(0));
    /// // start of `老`
    /// assert!(s.is_char_boundary(6));
    /// assert!(s.is_char_boundary(s.len()));
    ///
    /// // second byte of `ö`
    /// assert!(!s.is_char_boundary(2));
    ///
    /// // third byte of `老`
    /// assert!(!s.is_char_boundary(8));
    /// ```
    pub const fn is_char_boundary(&self, index: usize) -> bool {
        if index == 0 {
            true
        } else if index >= self.len {
            index == self.len
        } else {
            // index is in the range of the initialized part of the buffer, we can read the byte there.
            crate::utils::is_utf8_char_boundary(unsafe { self.get_byte_unchecked(index) })
        }
    }

    /// Removes the last character from the string buffer and returns it.
    ///
    /// Returns [`None`] if empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use owned_str::OwnedStr;
    ///
    /// let mut s = OwnedStr::<8>::new_from_str("abč");
    ///
    /// assert_eq!(s.pop(), Some('č'));
    /// assert_eq!(s.pop(), Some('b'));
    /// assert_eq!(s.pop(), Some('a'));
    ///
    /// assert_eq!(s.pop(), None);
    /// ```
    pub const fn pop(&mut self) -> Option<char> {
        if self.is_empty() {
            None
        } else {
            // We know bytes are valid UTF8 and we checked the length above.
            let c = unsafe { crate::utils::next_code_point_rev(self.as_bytes()) };
            let c = unsafe { char::from_u32_unchecked(c) };
            self.len -= c.len_utf8();
            Some(c)
        }
    }

    /// Tries to divides self into two at an index.
    ///
    /// The argument, `mid`, should be a byte offset from the start of the
    /// string. It must also be on the boundary of a UTF-8 code point.
    ///
    /// The two slices returned go from the start of the string slice to `mid`,
    /// and from `mid` to the end of the string slice.
    ///
    /// To get mutable string slices instead, see the [`try_split_at_mut`]
    /// method.
    ///
    /// Return `None` if `mid` is not on a UTF-8 code point boundary, or if it is past
    /// the end of the last code point of the string slice.
    ///
    /// This does the same things as [`str::split_at_checked`] but is unstable at the moment in a const context.
    /// If you can use the `str` method, we advise you to do.
    ///
    /// # Examples
    ///
    /// ```
    /// use owned_str::OwnedStr;
    ///
    /// let s = OwnedStr::<16>::new_from_str("Per Martin-Löf");
    ///
    /// let (first, last) = s.try_split_at(3).unwrap();
    ///
    /// assert_eq!("Per", first);
    /// assert_eq!(" Martin-Löf", last);
    /// ```
    ///
    /// [`try_split_at_mut`]: Self::try_split_at_mut
    pub const fn try_split_at(&self, mid: usize) -> Option<(&str, &str)> {
        if mid > self.len || !self.is_char_boundary(mid) {
            return None;
        }
        // mid is inside the string and is a char boundary, it is safe to split here.
        unsafe {
            let (a, b) = self.as_bytes().split_at_unchecked(mid);
            Some((
                core::str::from_utf8_unchecked(a),
                core::str::from_utf8_unchecked(b),
            ))
        }
    }

    /// Tries to divides self into two at an index.
    ///
    /// The argument, `mid`, should be a byte offset from the start of the
    /// string. It must also be on the boundary of a UTF-8 code point.
    ///
    /// The two slices returned go from the start of the string slice to `mid`,
    /// and from `mid` to the end of the string slice.
    ///
    /// To get immutable string slices instead, see the [`try_split_at`] method.
    ///
    /// Return `None` if `mid` is not on a UTF-8 code point boundary, or if it is past
    /// the end of the last code point of the string slice.
    ///
    /// This does the same things as [`str::split_at_checked_mut`] but is unstable at the moment in a const context.
    /// If you can use the `str` method, we advise you to do.
    ///
    /// # Examples
    ///
    /// ```
    /// use owned_str::OwnedStr;
    ///
    /// let mut s = OwnedStr::<16>::new_from_str("Per Martin-Löf");
    /// {
    ///     let (first, last) = s.try_split_at_mut(3).unwrap();
    ///     first.make_ascii_uppercase();
    ///     assert_eq!(first, "PER");
    ///     assert_eq!(last, " Martin-Löf");
    /// }
    /// assert_eq!(s, "PER Martin-Löf");
    /// ```
    ///
    /// [`try_split_at`]: Self::try_split_at
    pub const fn try_split_at_mut(&mut self, mid: usize) -> Option<(&mut str, &mut str)> {
        if mid > self.len || !self.is_char_boundary(mid) {
            return None;
        }
        // mid is inside the string and is a char boundary, it is safe to split here.
        unsafe {
            let (a, b) = self.as_bytes_mut().split_at_mut_unchecked(mid);
            Some((
                core::str::from_utf8_unchecked_mut(a),
                core::str::from_utf8_unchecked_mut(b),
            ))
        }
    }

    /// Tries to add a null byte at the end of the buffer and return a borrowed C string.
    ///
    /// Also return `None` if a null byte is already present.
    ///
    /// This does not change the size of self, it only adds the null byte to the underlying buffer.
    ///
    /// If you already have a null byte you can use [`CStr::from_bytes_until_nul`] and pass it `self.as_bytes()`.
    ///
    /// # Example
    ///
    /// ```
    /// use owned_str::OwnedStr;
    ///
    /// let mut s = OwnedStr::<16>::new_from_str("abc");
    /// let c_str = s.make_cstr().unwrap();
    /// assert_eq!(c_str.to_bytes_with_nul(), b"abc\0");
    ///
    /// // Already a null byte in the sequence
    /// let mut s = OwnedStr::<16>::new_from_str("abc\0");
    /// let c_str = s.make_cstr();
    /// assert_eq!(c_str, None);
    ///
    /// // Exceed capacity:
    /// let mut s = OwnedStr::<3>::new_from_str("abc");
    /// let c_str = s.make_cstr();
    /// assert_eq!(c_str, None);
    /// ```
    pub const fn make_cstr(&mut self) -> Option<&CStr> {
        if self.len == self.buff.len() {
            return None;
        }

        let bytes = unsafe {
            // we have capacity to push the null byte, but we don't want to push it, just that it exist
            // We can write it at the end of the buffer
            core::ptr::write(
                self.buff.as_mut_ptr().add(self.len),
                MaybeUninit::new(b'\0'),
            );
            // now that the byte has been initialized, we can take a byte slice ending with the null byte.
            let ptr = self.buff.as_ptr().cast::<u8>();
            core::slice::from_raw_parts(ptr, self.len + 1)
        };
        match CStr::from_bytes_with_nul(bytes) {
            Ok(c_str) => Some(c_str),
            Err(_) => None,
        }
    }

    // pub const fn floor_char_boundary(&self, mut index: usize) -> usize {
    //     if index > self.len {
    //         return self.len;
    //     }
    //     while !self.is_char_boundary(index) {
    //         index -= 1;
    //     }
    //     index
    // }

    // pub const fn ceil_char_boundary(&self, mut index: usize) -> usize {
    //     if index > self.len {
    //         return self.len;
    //     }
    //     while !self.is_char_boundary(index) {
    //         index += 1;
    //     }
    //     index
    // }

    /// Return true if `s` is in the string.
    ///
    /// This is equivalent to `s.find_str(s).is_some()`
    ///
    /// # Example
    ///
    /// ```
    /// use owned_str::OwnedStr;
    ///
    /// let s = OwnedStr::<16>::new_from_str("abc");
    /// assert_eq!(s.contain_str("bc"), true);
    /// assert_eq!(s.contain_str("ad"), false);
    /// ```
    pub const fn contain_str(&self, s: &str) -> bool {
        self.find_str(s).is_some()
    }

    /// Return the position of the first occurence of `s` in the string, if any.
    ///
    /// # Example
    ///
    /// ```
    /// use owned_str::OwnedStr;
    ///
    /// let s = OwnedStr::<16>::new_from_str("abc");
    /// assert_eq!(s.find_str("ab"), Some(0));
    /// assert_eq!(s.find_str("bc"), Some(1));
    /// assert_eq!(s.find_str("ad"), None);
    /// ```
    pub const fn find_str(&self, s: &str) -> Option<usize> {
        crate::utils::find_str(self.as_bytes(), s)
    }

    /// Return true if `c` is in the string.
    ///
    /// This is equivalent to `s.find_char(c).is_some()`
    ///
    /// # Example
    ///
    /// ```
    /// use owned_str::OwnedStr;
    ///
    /// let s = OwnedStr::<16>::new_from_str("abc");
    /// assert_eq!(s.contain_char('b'), true);
    /// assert_eq!(s.contain_char('d'), false);
    /// ```
    pub const fn contain_char(&self, c: char) -> bool {
        self.find_char(c).is_some()
    }

    /// Return the position of the first occurence of `c` in the string, if any.
    ///
    /// # Example
    ///
    /// ```
    /// use owned_str::OwnedStr;
    ///
    /// let s = OwnedStr::<16>::new_from_str("abc");
    /// assert_eq!(s.find_char('b'), Some(1));
    /// assert_eq!(s.find_char('d'), None);
    /// ```
    pub const fn find_char(&self, c: char) -> Option<usize> {
        crate::utils::find_char(self.as_bytes(), c)
    }

    /// Return the number of chars.
    ///
    /// This is typicaly done with `s.chars().count()`, which is still the recommanded way to do it,
    /// The only reason to use this function is in a const context, as iterators can't be used there.
    ///
    /// # Example
    ///
    /// ```
    /// use owned_str::OwnedStr;
    ///
    /// let s = OwnedStr::<16>::new_from_str("abc");
    /// assert_eq!(s.len(), 3);
    /// assert_eq!(s.char_count(), 3);
    ///
    /// let s = OwnedStr::<16>::new_from_str("é");
    /// assert_eq!(s.len(), 2);
    /// assert_eq!(s.char_count(), 1);
    /// ```
    pub const fn char_count(&self) -> usize {
        let mut i = 0;
        let mut count = 0;
        while i < self.len {
            // SAFETY: utf8 validity requires that the string must contain
            // the continuation bytes (if any)
            i += crate::utils::utf8_char_width(unsafe { self.get_byte_unchecked(i) });
            count += 1;
        }
        count
    }
}

impl<T: ?Sized> AsRef<T> for UnsizedStr
where
    str: AsRef<T>,
{
    fn as_ref(&self) -> &T {
        self.as_str().as_ref()
    }
}

impl<T: ?Sized> AsMut<T> for UnsizedStr
where
    str: AsMut<T>,
{
    fn as_mut(&mut self) -> &mut T {
        self.as_str_mut().as_mut()
    }
}

impl Deref for UnsizedStr {
    type Target = str;
    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl DerefMut for UnsizedStr {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_str_mut()
    }
}

impl AddAssign<&'_ str> for UnsizedStr {
    fn add_assign(&mut self, rhs: &'_ str) {
        self.push_str(rhs);
    }
}

impl AddAssign<char> for UnsizedStr {
    fn add_assign(&mut self, rhs: char) {
        self.push(rhs);
    }
}

impl<T: ?Sized> Borrow<T> for UnsizedStr
where
    str: Borrow<T>,
{
    fn borrow(&self) -> &T {
        self.as_str().borrow()
    }
}

impl<T: ?Sized> BorrowMut<T> for UnsizedStr
where
    str: BorrowMut<T>,
{
    fn borrow_mut(&mut self) -> &mut T {
        self.as_str_mut().borrow_mut()
    }
}

impl<I: SliceIndex<str>> Index<I> for UnsizedStr {
    type Output = <I as SliceIndex<str>>::Output;

    fn index(&self, index: I) -> &Self::Output {
        Index::index(self.as_str(), index)
    }
}

impl<I: SliceIndex<str>> IndexMut<I> for UnsizedStr {
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        IndexMut::index_mut(self.as_str_mut(), index)
    }
}

impl Write for UnsizedStr {
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

#[track_caller]
#[cold]
const fn push_panic() -> ! {
    panic!("Tried to push a value to a OwnedStr but exceeded capacity.")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_downcast() {
        let os = OwnedStr::<10>::new_from_str("test");
        let s = os.unsize_ref();
        let os_ref = UnsizedStr::downcast::<5>(s).unwrap();
        assert_eq!(os_ref, "test")
    }
}
