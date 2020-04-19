//! This crate provides for converting arbitrary byte streams into valid
//! C-language identifiers ("mangled names") and back again.
//!
//! # Rationale
//! The functionality of this crate was hoisted out of a compiler that needed to translate
//! identifiers for Java symbols (e.g. method names and signatures) into symbols valid for the
//! generated assembly language. Although the mangling process can encode any stream of bytes into
//! a (longer) string of ASCII characters, and then convert the output back again, it is not
//! intended to provide general encoding/decoding facilities. Instead, it is meant to provide an
//! easy, reliable way for compiler writers to generate human-recognizable identifiers without
//! having to invent their own mangling scheme.
//!
//! # Requirements
//! 1. Totality (every byte stream can be encoded into a unique mangled name)
//! 1. Injectivity (each mangled name can be decoded to a unique byte stream)
//!
//! # Goals
//! 1. Correctness (the implementation matches its documented behavior)
//! 1. Consistency (the implementation behaves in a predictable manner)
//! 1. Readability (mangled names are visibly related to input streams)
//! 1. Compactness (mangled names are comparable in length to inputs)
//! 1. Performance (processing is computationally efficient in time and space)
#![deny(clippy::cmp_null)]
#![deny(clippy::extra_unused_lifetimes)]
#![deny(clippy::missing_safety_doc)]
#![deny(clippy::transmute_ptr_to_ptr)]

use std::error::Error;
use std::str::FromStr;

/// A generic Result type for functions in this module
pub type ManglingResult<T> = std::result::Result<T, Box<dyn Error>>;

pub mod clib;

#[cfg(test)]
mod test;

/// Takes an `IntoIterator` over `u8` and produces a `String` that is safe to
/// use as an identifier in the C language.
///
/// The length N of the output in bytes, relative to the input length K, follows these rules, which
/// are considered to be requirements on future implementations:
/// - N > K
/// - N ≤ 5 * K + 1
/// - N ≤ ceil(3.5 * K) + 2 when K > 1
///
/// Additionally, the current implementation satisfies these additional constraints:
/// - N = 1 + ceil(log10(K + 1)) + K when input matches `^[A-Za-z_]*$`
/// - N = 2 + ceil(log10(K + 1)) + 2 * K when input matches `^[^A-Za-z_]+$`
///
/// # Examples
/// ```
/// # use mangling::mangle;
/// let mangle_list = &[
///     (""                , "_"                           ),
///     ("_123"            , "_4_123"                      ),
///     ("123"             , "_03_313233"                  ),
///     ("(II)I"           , "_01_282II01_291I"            ),
///     ("<init>"          , "_01_3c4init01_3e"            ),
///     ("<init>:()V"      , "_01_3c4init04_3e3a28291V"    ),
///     ("GCD"             , "_3GCD"                       ),
///     ("StackMapTable"   , "_13StackMapTable"            ),
///     ("java/lang/Object", "_4java01_2f4lang01_2f6Object"),
/// ];
///
/// for &(before, after) in mangle_list {
///     assert_eq!(after, mangle(before.bytes()));
/// }
///
/// ```
///
/// # Implementation details
/// The resulting symbol begins with an underscore character `_`, and is
/// followed by zero or more groups of two types: printables and non-printables.
/// The content of the input byte stream determines which type of group comes
/// first, after which the two types alternate strictly.
///
/// - A printable group corresponds to the longest substring of the input that
/// can be consumed while matching the (case-insensitive) regular expression
/// `[a-z][a-z0-9_]*`. The mangled form is `Naaa` where `N` is the unbounded
/// decimal length of the substring in the original input, and `aaa` is the
/// literal substring.
/// - A non-printable group represents the shortest substring in the input that
/// can be consumed before a printable substring begins to match. The mangled
/// form is `0N_xxxxxx` where `0` and `_` are literal, `N` is the unbounded
/// decimal length of the substring in the original input, and `xxxxxx` is the
/// lowercase hexadecimal expansion of the original bytes (two hexadecimal
/// digits per input byte, most significant nybble first).
///
/// Note that despite the description above, the current implementation does not
/// actually use regular expressions for matching.
pub fn mangle<T>(name : impl IntoIterator<Item = T>) -> String
where
    T : core::borrow::Borrow<u8>,
{
    use std::cell::Cell;
    use std::rc::Rc;

    type Many = Rc<Cell<usize>>;

    let begin_ok = |x : char| x.is_ascii_alphabetic() || x == '_';
    let within_ok = |x : char| begin_ok(x) || x.is_ascii_digit();

    let start = (None, true, Rc::new(Cell::new(0))); // word v. nonword ; begin v. nonbegin ; count

    // For now, we need to collect into a vector so that Rc<> pointers are viewed after all updates
    // have occurred, rather than just as they are created.
    let result : Vec<_> = name
        .into_iter()
        .scan(start, |st : &mut (Option<bool>, bool, Many), item| {
            let item = *item.borrow();
            let ch = char::from(item);
            let increment = || {
                let c = Rc::clone(&st.2);
                c.set(c.get() + 1);
                c
            };
            let switch = || Rc::new(Cell::new(1));
            *st = match (st.0, begin_ok(ch), within_ok(ch)) {
                (Some(tf @ true), _, true) | (Some(tf @ false), false, _) => {
                    (Some(tf), false, increment())
                },
                (_, tf, _) => (Some(tf), true, switch()),
            };
            Some((st.clone(), item))
        })
        .collect();

    let out = {
        let mut out = Vec::with_capacity(result.len() * 2); // heuristic
        out.push(b'_');
        out
    };
    let result = result
        .into_iter()
        .fold(out, |mut vec, ((wordlike, beginning, count), ch)| {
            match (wordlike, beginning) {
                (Some(true), true) => vec.extend(count.get().to_string().bytes()),
                (Some(false), true) => vec.extend(format!("0{}_", count.get()).bytes()),
                _ => {},
            };
            match wordlike {
                Some(true) => vec.push(ch),
                Some(false) => vec.extend(&hexify(ch)),
                None => unreachable!(), // fold will not iterate unless result has items
            };
            vec
        });

    // This unsafe block is demonstrated safe because our constructed Vec contains only bytes which
    // either match is_ascii_alphabetic or is_ascii_digit, or which are the result of converting to
    // hexadecimal.
    unsafe { String::from_utf8_unchecked(result) }
}

/// Takes a string slice corresponding to a symbol as converted by the `mangle`
/// function, and returns a vector of bytes corresponding to the original input
/// to the `mangle` function.
///
/// # Failures
/// An `Err` result will be returned if the input is not exactly a validly
/// mangled symbol, in its entirety and nothing more.
pub fn demangle(name : &str) -> ManglingResult<Vec<u8>> {
    fn demangle_inner(name : &[u8], mut from : Vec<u8>) -> ManglingResult<Vec<u8>> {
        if name.is_empty() {
            from.shrink_to_fit();
            Ok(from)
        } else if let Some((not_num, _)) =
            name.iter().enumerate().find(|(_, x)| !x.is_ascii_digit())
        {
            use std::borrow::Cow;

            let (num_str, name) = name.split_at(not_num);
            let len = usize::from_str(core::str::from_utf8(num_str)?)?;

            let hexlen = len.checked_mul(2).ok_or("Index too big");
            let (piece, remainder) = match (num_str, name) {
                ([b'0', ..], [b'_', rest @ ..]) => (
                    rest.get(..hexlen?)
                        .map(dehexify)
                        .transpose()?
                        .map(Cow::Owned),
                    rest.get(hexlen?..).map(Cow::Borrowed),
                ),
                ([b'0', ..], ..) => return Err("Bad identifier (expected `_`)".into()),
                (_, [rest @ ..]) => (
                    rest.get(..len).map(Cow::Borrowed),
                    rest.get(len..).map(Cow::Borrowed),
                ),
            };

            let check = |x| match x {
                None => ManglingResult::Err("Input ended too soon".into()),
                Some(y) => ManglingResult::Ok(y),
            };
            from.extend(check(piece)?.as_ref());
            demangle_inner(check(remainder)?.as_ref(), from)
        } else {
            Err("did not find a number".into())
        }
    }

    match name.get(..).map(str::as_bytes) {
        Some([b'_', rest @ ..]) => demangle_inner(rest, Vec::with_capacity(rest.len())),
        _ => Err("Bad identifier (expected `_`)".into()),
    }
}

fn hexify(byte : u8) -> [u8; 2] {
    let hex = |b| match b & 0xf {
        c @ 0..=9 => b'0' + c,
        c => b'a' + c - 10,
    };
    [hex(byte >> 4), hex(byte)]
}

fn dehexify(string : &[u8]) -> ManglingResult<Vec<u8>> {
    string
        .chunks(2)
        .map(std::str::from_utf8)
        .map(|v| u8::from_str_radix(v?, 16).map_err(Into::into))
        .collect()
}
