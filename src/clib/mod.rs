//! Provides C-compatible interfaces to `mangle` and `demangle` functions.
//!
//! Although the code is written such that it should be possible to mangle and demangle in-place
//! (using the same location for in- and out-pointers), the declaration of the parameter types
//! (using Rust references), prohibits such aliasing, so it is not safe to do so. If significant
//! cause is found to support processing in place, the Rust function declaration could potentially
//! be changed (without changing the C interface) to allow it.
use std::os::raw::{c_char, c_int};

use crate::{demangle, mangle};

#[cfg(test)]
mod test;

/// Provides a C-compatible interface to the `mangle` function.
///
/// This function is compatible with the C function declaration:
/// ```c
/// int mangling_mangle(size_t insize, const char *inptr, size_t *outsize, char *outstr);
/// ```
///
/// This function:
/// - returns a zero value upon success and a non-zero value on error,
/// - has well-defined behavior for any combination of null pointer arguments,
/// - copies a sequence of non-NUL bytes into a buffer provided by the caller,
/// - writes no more bytes than specified in `outsize`, and
/// - updates the size referenced by `outsize` with the number of bytes copied through `outstr`.
///
/// An error is indicated with a non-zero exit code under the following conditions:
/// - a null pointer was passed in for the `inptr` argument but the `insize` is nonzero.
///
/// Specifically, it is not an error to supply an output buffer that is too small; in such a case,
/// the output will simply be truncated to the provided length.
///
/// The output is never NUL-terminated. If NUL termination is desired, and the `outstr` buffer is
/// big enough, simply perform `outstr[*outsize] = '\0';` after `mangling_mangle`.
///
/// # Examples
/// Some of the examples below are shown in (doctested) Rust code to demonstrate correctness, but
/// it is not expected that Rust users will use the C interfaces.
///
/// Null pointers (`None` in the Rust interface) are not inherently erroneous:
/// ```
/// # use mangling::clib::*;
/// let success = mangling_mangle(0, None, None, None);
/// assert_eq!(0, success);
/// ```
/// This behavior can be used to determine the correct size of buffer to allocate (here
/// demonstrated with Rust code):
/// ```
/// # use mangling::clib::*;
/// # use std::os::raw::c_char;
/// let input = "hello, world";
/// let mut len = std::usize::MAX;
/// let inptr = unsafe { &*(input.as_ptr() as *const c_char) };
/// let success = mangling_mangle(input.len(), Some(inptr), Some(&mut len), None);
/// assert_eq!(0, success);
///
/// // Now the required buffer size is known in `len` and can be used for allocation
/// let mut v: Vec<u8> = Vec::with_capacity(len);
/// let outptr = unsafe { &mut *(v.as_mut_ptr() as *mut c_char) };
/// let success = mangling_mangle(input.len(), Some(inptr), Some(&mut len), Some(outptr));
/// unsafe { v.set_len(len); }
/// assert_eq!(&v[..], "_5hello02_2c205world".as_bytes());
/// assert_eq!(0, success);
/// ```
/// Similar C code might look like this:
/// ```c
/// size_t need = -1;
/// int rc = mangling_mangle(strlen(input), input, &need, NULL);
/// if (rc != 0) return;
/// char *buf = malloc(need);
/// rc = mangling_mangle(strlen(input), input, &need, buf);
/// ```
///
/// However, if the `insize` parameter indicates that some data should be expected, then a null
/// pointer is an error, though still safe:
/// ```
/// # use mangling::clib::*;
/// let success = mangling_mangle(1, None, None, None);
/// assert_ne!(0, success);
/// ```
///
/// In C, if the output buffer is sized safely according to the bounds specified in the `mangle`
/// documentation, then a mangling call can be as simple as the following:
/// ```c
/// char input[16] = "hello, world",
/// char result[1 + 5 * sizeof input]; // Worst-case length
/// size_t outsize = sizeof result;
/// int success = mangling_mangle(strlen(input), input, &outsize, result);
/// fwrite(result, 1, outsize, stdout);
/// ```
#[no_mangle]
pub extern "C" fn mangling_mangle(
    insize : usize,
    inptr : Option<&c_char>,
    outsize : Option<&mut usize>,
    outstr : Option<&mut c_char>,
) -> c_int {
    match (inptr, insize) {
        (None, 0) | (Some(_), _) => {
            let inptr = match inptr {
                Some(inptr) => unsafe {
                    let inptr = inptr as *const c_char as *const u8;
                    std::slice::from_raw_parts(inptr, insize)
                },
                None => &[],
            };
            let mangled = mangle(inptr);
            let len = match (outsize, mangled.len()) {
                (None, _) => 0,
                (Some(need), have) => {
                    *need = (*need).min(have);
                    *need
                },
            };
            if let Some(outstr) = outstr {
                let raw = mangled.as_ptr() as *mut c_char;
                unsafe {
                    raw.copy_to_nonoverlapping(outstr, len);
                }
            }

            0 // indicate success
        },
        _ => 1, // null pointer with non-zero length is an error
    }
}

/// Provides a C-compatible interface to the `demangle` function.
///
/// This function is compatible with the C function declaration:
/// ```c
/// int mangling_demangle(size_t insize, const char *instr, size_t *outsize, char *outptr);
/// ```
///
/// This function:
/// - returns a zero value upon success and a non-zero value on error,
/// - has well-defined behavior for any combination of null pointer arguments,
/// - copies a sequence of bytes (possibly including NUL) into a buffer provided by the caller,
/// - writes no more bytes than specified in `outsize`,
/// - updates the size referenced by `outsize` with the number of bytes copied through `outptr`.
///
/// An error is indicated with a non-zero exit code under the following conditions:
/// - the input string was not a valid mangled name.
///
/// Specifically, it is not an error to supply an output buffer that is too small; in such a case,
/// the output will simply be truncated to the provided length.
///
/// A null input pointer (`None` in the Rust interface) is not an error *per se*, but since at best
/// (when `insize` is 0) it can represent only an empty string, which is never demanglable, an
/// error is reported:
/// ```
/// # use mangling::clib::*;
/// // Demangling an empty string is not meaningful, and must fail
/// let success = mangling_demangle(0, None, None, None);
/// assert_ne!(success, 0);
/// ```
///
/// # Example
/// In C:
/// ```c
/// char result[128];
/// size_t outsize = sizeof result;
/// int success = mangling_demangle(strlen(argv[1]), argv[1], &outsize, result);
/// fwrite(result, 1, outsize, stdout);
/// ```
#[no_mangle]
pub extern "C" fn mangling_demangle(
    insize : usize,
    instr : Option<&c_char>,
    outsize : Option<&mut usize>,
    outptr : Option<&mut c_char>,
) -> c_int {
    match instr {
        None => 1, // null pointer input is considered an error
        Some(instr) => {
            let instr = unsafe {
                let instr = instr as *const c_char as *const u8;
                std::slice::from_raw_parts(instr, insize)
            };
            let instr = core::str::from_utf8(instr);
            let orig = instr.map(demangle);

            match orig {
                Ok(Ok(x)) => {
                    let len = match (outsize, x.len()) {
                        (None, _) => 0,
                        (Some(need), have) => {
                            *need = (*need).min(have);
                            *need
                        },
                    };
                    if let Some(outptr) = outptr {
                        let raw = x.as_ptr() as *mut c_char;
                        unsafe {
                            core::intrinsics::copy_nonoverlapping(raw, outptr, len);
                        }
                    }

                    0 // indicate success
                },
                _ => 1, // indicate failure
            }
        },
    }
}
