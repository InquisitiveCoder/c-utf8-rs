use core::fmt;
use core::str::{self, Utf8Error};

#[cfg(feature = "std")]
use std::ffi::{CStr, OsStr};

#[cfg(feature = "std")]
use std::path::Path;

use c_char;
use error::Error;
use ext::is_nul_terminated;

/// Like [`CStr`](https://doc.rust-lang.org/std/ffi/struct.CStr.html), except
/// with the guarantee of being encoded as valid [UTF-8].
///
/// Use the [`c_utf8!`](macro.c_utf8.html) macro to conveniently create static
/// instances.
///
/// # Guarantees
///
/// This type guarantees that instances are:
///
/// - [Nul (Ø) terminated C strings](https://en.wikipedia.org/wiki/Null-terminated_string)
///   in order for C APIs to safely access memory that is properly owned. It is
///   generally preferable for there to be no other nul byte prior to the very
///   end of the string.
///
/// - Encoded as valid [UTF-8], which allows for passing around native Rust
///   [`str`](https://doc.rust-lang.org/std/primitive.str.html) strings with
///   ease.
///
/// [UTF-8]: https://en.wikipedia.org/wiki/UTF-8
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct CUtf8(str);

#[cfg(feature = "try_from")]
mod try_from {
    use super::*;
    use core::convert::TryFrom;

    impl<'a> TryFrom<&'a [u8]> for &'a CUtf8 {
        type Error = Error;

        #[inline]
        fn try_from(bytes: &[u8]) -> Result<&CUtf8, Self::Error> {
            CUtf8::from_bytes(bytes)
        }
    }

    #[cfg(feature = "std")]
    impl<'a> TryFrom<&'a CStr> for &'a CUtf8 {
        type Error = Utf8Error;

        #[inline]
        fn try_from(c: &CStr) -> Result<&CUtf8, Self::Error> {
            CUtf8::from_c_str(c)
        }
    }

    impl<'a> TryFrom<&'a str> for &'a CUtf8 {
        type Error = Error;

        #[inline]
        fn try_from(s: &str) -> Result<&CUtf8, Self::Error> {
            CUtf8::from_str(s)
        }
    }
}

impl AsRef<str> for CUtf8 {
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

#[cfg(feature = "std")]
impl AsRef<CStr> for CUtf8 {
    #[inline]
    fn as_ref(&self) -> &CStr {
        self.as_c_str()
    }
}

impl AsRef<[u8]> for CUtf8 {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

#[cfg(feature = "std")]
impl AsRef<Path> for CUtf8 {
    #[inline]
    fn as_ref(&self) -> &Path {
        self.as_str().as_ref()
    }
}

#[cfg(feature = "std")]
impl AsRef<OsStr> for CUtf8 {
    #[inline]
    fn as_ref(&self) -> &OsStr {
        self.as_str().as_ref()
    }
}

impl fmt::Debug for CUtf8 {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.as_str_with_nul().fmt(f)
    }
}

impl fmt::Display for CUtf8 {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.as_str().fmt(f)
    }
}

impl<'a> Default for &'a CUtf8 {
    #[inline]
    fn default() -> &'a CUtf8 { CUtf8::EMPTY }
}

// Without this, the documentation shows the macro expansion, which is noisy
const EMPTY: &CUtf8 = c_utf8!("");

impl CUtf8 {
    /// A static &#8220;empty&#8221; borrowed C string.
    ///
    /// The string is still nul-terminated, which makes it safe to pass to C.
    pub const EMPTY: &'static CUtf8 = EMPTY;

    /// Returns a C string containing `bytes`, or an error if a nul byte is in
    /// an unexpected position or if the bytes are not encoded as UTF-8.
    ///
    /// # Examples
    /// ```
    /// use c_utf8::{c_utf8, CUtf8, Error};
    ///
    /// let ok = &[0x6F, 0x6B, 0x00];
    /// assert_eq!(CUtf8::from_bytes(ok), Ok(c_utf8!("ok")));
    ///
    /// let not_terminated = &[0x6F, 0x6B];
    /// assert_eq!(CUtf8::from_bytes(not_terminated), Err(Error::Nul));
    ///
    /// let not_utf8 = &[0xFF, 0x00];
    /// assert!(matches!(CUtf8::from_bytes(not_utf8), Err(Error::Utf8(_))));
    /// ```
    #[inline]
    pub const fn from_bytes(bytes: &[u8]) -> Result<&CUtf8, Error> {
        // Can't use ? operator or Result::map in const functions
        match str::from_utf8(bytes) {
            Ok(str) => CUtf8::from_str(str),
            Err(err) => Err(Error::Utf8(err))
        }
    }

    /// Returns the UTF-8 string if it is terminated by a nul byte.
    #[inline]
    pub const fn from_str(s: &str) -> Result<&CUtf8, Error> {
        if is_nul_terminated(s.as_bytes()) {
            unsafe { Ok(CUtf8::from_str_unchecked(s)) }
        } else {
            Err(Error::Nul)
        }
    }

    /// Returns the C string if it is valid UTF-8.
    ///
    /// # Examples
    /// ```
    /// use std::ffi::CStr;
    /// use std::str::Utf8Error;
    /// use c_utf8::*;
    ///
    /// let utf8 = CStr::from_bytes_with_nul(&[0x6F, 0x6B, 0x00]).unwrap();
    /// assert_eq!(CUtf8::from_c_str(utf8), Ok(c_utf8!("ok")));
    ///
    /// let not_utf8 = CStr::from_bytes_with_nul(&[0xFF, 0x00]).unwrap();
    /// assert_eq!(CUtf8::from_c_str(not_utf8).err(), not_utf8.to_str().err());
    /// ```
    #[cfg(feature = "std")]
    #[inline]
    pub const fn from_c_str(c: &CStr) -> Result<&CUtf8, Utf8Error> {
        // Can't use ? operator or Result::map in const contexts
        match str::from_utf8(c.to_bytes_with_nul()) {
            Ok(s) => unsafe { Ok(CUtf8::from_str_unchecked(s)) }
            Err(err) => Err(err)
        }
    }

    /// Returns the raw C string if it is valid UTF-8 up to the first nul byte.
    ///
    /// # Safety
    /// `raw` must satisfy all the safety requirements of [`CStr::from_ptr`].
    #[inline]
    pub unsafe fn from_ptr<'a>(raw: *const c_char) -> Result<&'a CUtf8, Utf8Error> {
        #[cfg(feature = "std")] {
            CUtf8::from_c_str(CStr::from_ptr(raw))
        }
        #[cfg(not(feature = "std"))] {
            use core::slice;

            extern {
                fn strlen(cs: *const c_char) -> usize;
            }

            let n = strlen(raw) + 1;
            let s = str::from_utf8(slice::from_raw_parts(raw as *const u8, n))?;
            Ok(CUtf8::from_str_unchecked(s))
        }
    }

    /// Returns the number of bytes without taking into account the trailing nul
    /// byte.
    ///
    /// This behavior is the same as that of
    /// [`str::len`](https://doc.rust-lang.org/std/primitive.str.html#method.len)
    /// where the length is not measured in
    /// [`char`](https://doc.rust-lang.org/std/primitive.char.html)s.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # #[macro_use] extern crate c_utf8; fn main() {
    /// let s = c_utf8!("Hey");
    ///
    /// assert_eq!(s.len(), 3);
    /// # }
    /// ```
    #[inline]
    pub const fn len(&self) -> usize {
        self.0.len().wrapping_sub(1)
    }

    /// Returns `true` if `self` contains 0 bytes, disregarding the trailing nul
    /// byte.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let s = c_utf8::CUtf8::EMPTY;
    ///
    /// assert!(s.is_empty());
    /// assert_eq!(s.len(), 0);
    /// ```
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.0.len() == 1
    }

    /// Returns a C string without checking UTF-8 validity or for a trailing
    /// nul byte.
    ///
    /// # Safety
    /// `b` must be a nul-terminated UTF-8 string.
    #[inline]
    pub const unsafe fn from_bytes_unchecked(b: &[u8]) -> &CUtf8 {
        &*(b as *const [u8] as *const CUtf8)
    }

    /// Returns a C string without checking for a trailing nul byte.
    ///
    /// # Safety
    /// `s` must be nul-terminated.
    #[inline]
    pub const unsafe fn from_str_unchecked(s: &str) -> &CUtf8 {
        &*(s as *const str as *const CUtf8)
    }

    /// Returns a mutable C string without checking for a trailing nul byte.
    ///
    /// # Safety
    /// `s` must be nul-terminated.
    #[inline]
    pub unsafe fn from_str_unchecked_mut(s: &mut str) -> &mut CUtf8 {
        &mut *(s as *mut str as *mut CUtf8)
    }

    /// Returns a C string without checking UTF-8 validity.
    ///
    /// # Safety
    /// `c.to_bytes_with_null()` must be valid UTF-8.
    #[cfg(feature = "std")]
    #[inline]
    pub const unsafe fn from_c_str_unchecked(c: &CStr) -> &CUtf8 {
        Self::from_bytes_unchecked(c.to_bytes_with_nul())
    }

    /// Returns a pointer to the start of the raw C string.
    #[inline]
    pub const fn as_ptr(&self) -> *const c_char {
        self.as_bytes().as_ptr() as *const c_char
    }

    /// Returns `self` as a normal C string.
    #[cfg(feature = "std")]
    #[inline]
    pub const fn as_c_str(&self) -> &CStr {
        unsafe { CStr::from_bytes_with_nul_unchecked(self.as_bytes_with_nul()) }
    }

    /// Returns `self` as a normal UTF-8 encoded string.
    ///
    /// # Examples
    /// ```
    /// use c_utf8::c_utf8;
    /// assert_eq!(c_utf8!("hello").as_str(), "hello");
    /// assert_ne!(c_utf8!("hello").as_str(), "hello\x00");
    /// ```
    #[inline]
    pub const fn as_str(&self) -> &str {
        // Remove nul
        let len = self.0.len().saturating_sub(1);
        unsafe {
            // Equivalent to get_unchecked(..len) but works in const contexts
            let bytes: &[u8] = core::slice::from_raw_parts(self.0.as_ptr(), len);
            str::from_utf8_unchecked(bytes)
        }
    }

    /// Returns `self` as a UTF-8 encoded string with a trailing 0 byte.
    ///
    /// # Examples
    /// ```
    /// use c_utf8::c_utf8;
    ///
    /// assert_eq!(c_utf8!("hello").as_str_with_nul(), "hello\x00");
    /// assert_ne!(c_utf8!("hello").as_str_with_nul(), "hello");
    /// ```
    #[inline]
    pub const fn as_str_with_nul(&self) -> &str {
        &self.0
    }

    /// Returns the bytes of `self` without a trailing 0 byte.
    #[inline]
    pub const fn as_bytes(&self) -> &[u8] {
        self.as_str().as_bytes()
    }

    /// Returns the bytes of `self` with a trailing 0 byte.
    #[inline]
    pub const fn as_bytes_with_nul(&self) -> &[u8] {
        self.as_str_with_nul().as_bytes()
    }
}

#[cfg(all(test, nightly))]
mod benches {
    use super::*;
    use test::{Bencher, black_box};

    #[bench]
    fn from_bytes(b: &mut Bencher) {
        let s = "abcdéfghîjklmnöpqrstúvwxÿz\0";
        b.iter(|| {
            let s = black_box(s.as_bytes());
            black_box(CUtf8::from_bytes(s).unwrap());
        });
    }
}
