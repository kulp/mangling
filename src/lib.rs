//! This module provides for converting arbitrary byte streams into valid
//! C-language identifiers and back again.
//!
//! The resulting symbol begins with an underscore character `_`, and is
//! followed by zero or more groups of two types: printables and non-printables.
//! The content of the input byte stream determines which type of group comes
//! first, after which the two types alternate strictly.
//!
//! - A printable group corresponds to the longest substring of the input that
//! can be consumed while matching the (case-insensitive) regular expression
//! `[a-z][a-z0-9_]*`. The mangled form is `Naaa` where `N` is the unbounded
//! decimal length of the substring in the original input, and `aaa` is the
//! literal substring.
//! - A non-printable group represents the shortest substring in the input that
//! can be consumed before a printable substring begins to match. The mangled
//! form is `0N_xxxxxx` where `0` and `_` are literal, `N` is the unbounded
//! decimal length of the substring in the original input, and `xxxxxx` is the
//! lowercase hexadecimal expansion of the original bytes (two hexadecimal
//! digits per input byte, most significant nybble first).
//!
//! Note that despite the description above, the current implementation does not
//! actually use regular expressions for matching.
//!
//! For example:
//! ```
//! # use mangling;
//! let input = "abc/123x".as_bytes();
//! let expect = "_3abc04_2f3132331x";
//!
//! let output = mangling::mangle(input.to_vec()).unwrap();
//! assert_eq!(output, expect);
//!
//! let reverse = mangling::demangle(expect).unwrap();
//! assert_eq!(reverse, input);
//! ```
#[cfg(test)]
use quickcheck::quickcheck;

use std::error::Error;
use std::str::FromStr;

/// A generic Result type for functions in this module
pub type ManglingResult<T> = std::result::Result<T, Box<dyn Error>>;

#[cfg(test)]
const MANGLE_LIST : &[(&str, &str)] = &[
    ( ""                           , "_"                                                     ),
    ( "123"                        , "_03_313233"                                            ),
    ( "_123"                       , "_4_123"                                                ),
    ( "()V"                        , "_02_28291V"                                            ),
    ( "(II)I"                      , "_01_282II01_291I"                                      ),
    ( "<init>"                     , "_01_3c4init01_3e"                                      ),
    ( "<init>:()V"                 , "_01_3c4init04_3e3a28291V"                              ),
    ( "Code"                       , "_4Code"                                                ),
    ( "GCD"                        , "_3GCD"                                                 ),
    ( "StackMapTable"              , "_13StackMapTable"                                      ),
    ( "gcd"                        , "_3gcd"                                                 ),
    ( "java/lang/Object"           , "_4java01_2f4lang01_2f6Object"                          ),
    ( "java/lang/Object.<init>:()V", "_4java01_2f4lang01_2f6Object02_2e3c4init04_3e3a28291V" ),
];

#[test]
fn test_mangle() -> ManglingResult<()> {
    for (unmangled, mangled) in MANGLE_LIST {
        assert_eq!(&mangle(unmangled.bytes())?, mangled);
    }
    Ok(())
}

/// Takes an `IntoIterator` over `u8` and produces a `String` that is safe to
/// use as an identifier in the C language.
pub fn mangle(name : impl IntoIterator<Item=u8>) -> ManglingResult<String> {
    use std::rc::Rc;
    use std::cell::Cell;

    #[derive(Copy, Clone, Debug)]
    enum What {
        Invalid,
        Word,
        NonWord,
    }
    #[derive(Copy, Clone, Debug)]
    enum How {
        Initial,
        Begin,
        Continue,
    }
    type Many = Rc<Cell<usize>>;

    let begin_ok = |x : char| x.is_ascii_alphabetic() || x == '_';
    let within_ok = |x : char| begin_ok(x) || x.is_ascii_digit();

    let start = (What::Invalid, How::Initial, Rc::new(Cell::new(0)));
    // For now, we need to collect into a vector so that Rc<> pointers are viewed after all updates
    // have occurred, rather than just as they are created.
    let result : Vec<_> = name.into_iter().scan(start, |st : &mut (What, How, Many), item| {
            use What::*;
            use How::*;
            let ch = char::from(item);
            let increment = || { let c = Rc::clone(&st.2); c.set(c.get() + 1); c };
            *st = match (st.0, begin_ok(ch), within_ok(ch)) {
                (Word   , _    , true ) => (Word   , Continue, increment()),
                (NonWord, false, _    ) => (NonWord, Continue, increment()),

                (_, true , _)           => (Word   , Begin, Rc::new(Cell::new(1))),
                (_, false, _)           => (NonWord, Begin, Rc::new(Cell::new(1))),
            };
            Some((st.clone(), item))
        }).collect();

    let out = {
        let mut out = Vec::with_capacity(result.len() * 2); // heuristic
        out.push(b'_');
        out
    };
    let result = result.into_iter()
        .try_fold(out, |mut vec, ((what, how, count), ch)| {
            match (what, how) {
                (What::Word   , How::Begin) => vec.extend(count.get().to_string().bytes()),
                (What::NonWord, How::Begin) => vec.extend(format!("0{}_", count.get()).bytes()),
                _ => {},
            };
            match what {
                What::Word    => vec.push(ch),
                What::NonWord => vec.extend(&hexify(ch)),
                _ => return Err("Bad state encountered during mangle"),
            };
            Ok(vec)
        });

    String::from_utf8(result?).map_err(Into::into)
}

#[test]
fn test_demangle() -> ManglingResult<()> {
    for (unmangled, mangled) in MANGLE_LIST {
        let got : Vec<u8> = demangle(mangled)?;
        let want : Vec<u8> = unmangled.to_string().into();
        assert_eq!(want, got);
    }

    assert!(demangle("bad").is_err());
    Ok(())
}

/// Takes a string slice corresponding to a symbol as converted by the `mangle`
/// function, and returns a vector of bytes corresponding to the original input
/// to the `mangle` function.
///
/// # Failures
/// An `Err` result will be returned if the input is not exactly a validly
/// mangled symbol, in its entirety and nothing more.
pub fn demangle(name : &str) -> ManglingResult<Vec<u8>> {
    fn demangle_inner(mut out : &mut Vec<u8>, name : &str) -> ManglingResult<()> {
        if name.is_empty() {
            Ok(())
        } else if let Some((not_num, _)) = name.chars().enumerate().find(|(_, x)| !x.is_ascii_digit()) {
            let (num_str, new_name) = name.split_at(not_num);
            let len = usize::from_str(num_str)?;

            if &name[..1] == "0" {
                if &new_name[..1] != "_" {
                    return Err("Bad identifier (expected `_`)".into());
                }
                let new_name = &new_name[1..];
                let len = 2 * len;
                let (before, after) = new_name.split_at(len);
                out.append(&mut dehexify(before)?);
                demangle_inner(&mut out, after)
            } else {
                let (before, after) = new_name.split_at(len);
                out.append(&mut Vec::from(before));
                demangle_inner(&mut out, after)
            }
        } else {
            Err("did not find a number".into())
        }
    }

    if &name[..1] == "_" {
        let mut out = Vec::with_capacity(name.len());
        demangle_inner(&mut out, &name[1..])?;
        Ok(out)
    } else {
        Err("Bad identifier (expected `_`)".into())
    }
}

#[cfg(test)]
quickcheck! {
    #[allow(clippy::result_unwrap_used)]
    fn test_demangled_mangle(rs : Vec<u8>) -> bool {
        rs == demangle(&mangle(rs.clone()).unwrap()).unwrap()
    }
}

fn hexify(byte : u8) -> [u8 ; 2] {
    const HEX : [u8 ; 16] = [
        b'0', b'1', b'2', b'3', b'4', b'5', b'6', b'7', b'8', b'9', b'a', b'b', b'c', b'd', b'e', b'f'
    ];
    [
        HEX[((byte & 0xf0) >> 4) as usize],
        HEX[( byte & 0x0f      ) as usize],
    ]
}

fn dehexify(string : &str) -> ManglingResult<Vec<u8>> {
    string
        .as_bytes()
        .chunks(2)
        .map(|v| std::str::from_utf8(v))
        .map(|v| u8::from_str_radix(v?, 16).map_err(Into::into))
        .collect()
}
