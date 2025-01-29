#![no_std]
#![forbid(missing_docs)]
//! # Owned Str
//!
//! This crate offers a stack equivalent to a `String` where you can choose the buffer size.
//!
//! This as 2 benefits:
//!
//! - No allocation, so it is 100% `#![no_std]`.
//! - A lot of functions can be marked `const`, so you can create/manipulate strings at compile time.
//!
//! ```rust
//! use owned_str::{OwnedStr, UnsizedStr};
//!
//! const fn make_str() -> OwnedStr<16> {
//!     let mut buff = OwnedStr::new();
//!     let s: &mut UnsizedStr = buff.unsize_mut(); // you can use `unsize_mut` to get a size erased handle
//!     s.push_str("hello");
//!     push_world(s);
//!     buff
//! }
//!
//! const fn push_world(s: &mut UnsizedStr) {
//!     s.push(' ');
//!     s.push_str("world");
//!     s.pop();
//! }
//!
//! const S: &str = make_str().as_str();
//!
//! fn main() {
//!     assert_eq!(S, "hello worl");
//!
//!     // allow stack based string formatting
//!     use std::fmt::Write;
//!     let mut buff = OwnedStr::<32>::new();
//!     write!(&mut buff, "format {} arguments", "some").unwrap();
//!     assert_eq!(buff, "format some arguments");
//! }
//! ```

mod owned_str;
mod unsized_str;
mod utils;

pub use owned_str::*;
pub use unsized_str::*;
