// Some functions are shamelessly stolen from the rust std source code https://doc.rust-lang.org/src/core/str/validations.rs.html

// https://tools.ietf.org/html/rfc3629
const UTF8_CHAR_WIDTH: &[u8; 256] = &[
    // 1  2  3  4  5  6  7  8  9  A  B  C  D  E  F
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, // 0
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, // 1
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, // 2
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, // 3
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, // 4
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, // 5
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, // 6
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, // 7
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, // 8
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, // 9
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, // A
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, // B
    0, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, // C
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, // D
    3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, // E
    4, 4, 4, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, // F
];

#[must_use]
#[inline]
pub const fn utf8_char_width(b: u8) -> usize {
    UTF8_CHAR_WIDTH[b as usize] as usize
}

pub const fn is_utf8_char_boundary(c: u8) -> bool {
    // This is bit magic equivalent to: b < 128 || b >= 192
    (c as i8) >= -0x40
}

/// Caller must guarantee that `to_cmp` length is less or equal to `bytes` length.
pub const unsafe fn cmp_bytes(bytes: *const u8, to_cmp: &[u8]) -> bool {
    let mut i = 0;
    let len = to_cmp.len();
    let ptr = to_cmp.as_ptr();
    while i < len {
        unsafe {
            if *ptr.add(i) != *bytes.add(i) {
                return false;
            }
        }
        i += 1;
    }
    true
}

pub const fn find(bytes: &[u8], to_find: &[u8]) -> Option<usize> {
    if to_find.is_empty() || bytes.len() < to_find.len() {
        return None;
    }

    let max_iter = bytes.len() - to_find.len() + 1;
    let mut i = 0;
    let ptr = bytes.as_ptr();
    while i < max_iter {
        unsafe {
            if cmp_bytes(ptr.add(i), to_find) {
                return Some(i);
            }
        }
        i += 1;
    }

    None
}

pub const fn find_str(bytes: &[u8], s: &str) -> Option<usize> {
    find(bytes, s.as_bytes())
}

pub const fn find_char(bytes: &[u8], c: char) -> Option<usize> {
    let mut buff = [0; 4];
    let to_find = c.encode_utf8(&mut buff);
    find_str(bytes, to_find)
}

/// Mask of the value bits of a continuation byte.
const CONT_MASK: u8 = 0b0011_1111;

/// Returns the initial codepoint accumulator for the first byte.
/// The first byte is special, only want bottom 5 bits for width 2, 4 bits
/// for width 3, and 3 bits for width 4.
#[inline]
pub const fn utf8_first_byte(byte: u8, width: u32) -> u32 {
    (byte & (0x7F >> width)) as u32
}

/// Returns the value of `ch` updated with continuation byte `byte`.
#[inline]
pub const fn utf8_acc_cont_byte(ch: u32, byte: u8) -> u32 {
    (ch << 6) | (byte & CONT_MASK) as u32
}

/// Checks whether the byte is a UTF-8 continuation byte (i.e., starts with the
/// bits `10`).
#[inline]
pub const fn utf8_is_cont_byte(byte: u8) -> bool {
    (byte as i8) < -64
}

/// Caller must ensure that buff is valid UTF8 and not empty.
#[inline(never)]
pub const unsafe fn next_code_point_rev(buff: &[u8]) -> u32 {
    #[inline(always)]
    const unsafe fn get_unchecked(buff: &[u8], rev_index: usize) -> u8 {
        unsafe { *buff.as_ptr().add(buff.len() - 1 - rev_index) }
    }
    // Decode UTF-8
    let w = match unsafe { get_unchecked(buff, 0) } {
        next_byte if next_byte < 128 => return next_byte as u32,
        back_byte => back_byte,
    };

    // Multibyte case follows
    // Decode from a byte combination out of: [x [y [z w]]]
    let mut ch;
    // SAFETY: `buff` is an UTF-8-like array,
    // so it must contain a value here.
    let z = unsafe { get_unchecked(buff, 1) };
    ch = utf8_first_byte(z, 2);
    if utf8_is_cont_byte(z) {
        // SAFETY: `buff` is an UTF-8-like array,
        // so it must contain a value here.
        let y = unsafe { get_unchecked(buff, 2) };
        ch = utf8_first_byte(y, 3);
        if utf8_is_cont_byte(y) {
            // SAFETY: `buff` is an UTF-8-like array,
            // so it must contain a value here.
            let x = unsafe { get_unchecked(buff, 3) };
            ch = utf8_first_byte(x, 4);
            ch = utf8_acc_cont_byte(ch, y);
        }
        ch = utf8_acc_cont_byte(ch, z);
    }

    utf8_acc_cont_byte(ch, w)
}
