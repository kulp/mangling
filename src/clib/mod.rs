use std::os::raw::{c_char, c_int};

use crate::{mangle, demangle};

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
/// - writes no more bytes than specified in `outsize`,
/// - updates the size referenced by `outsize` with the number of bytes copied through `outstr`.
///
/// Failure is indicated with a non-zero exit code under the following conditions:
/// - a null pointer was passed in for the `inptr` argument but the `insize` is nonzero.
///
/// # Example
/// ```c
/// char result[128];
/// size_t outsize = sizeof result;
/// int success = mangling_mangle(strlen(argv[1]), argv[1], &outsize, result);
/// fwrite(result, 1, outsize, stdout);
/// ```
///
/// # Safety
/// In order to avoid undefined behavior, this function must be called with `inptr` pointing to a
/// string of bytes at least `insize` in length, or else `inptr` must be a null pointer. No
/// requirement is levied on the contents of the referenced memory, besides that it must be
/// readable.
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
/// Failure is indicated with a non-zero exit code under the following conditions:
/// - a null pointer was passed in for the `instr` argument but the `insize` is nonzero, or
/// - the input string was not a valid mangled name.
///
/// # Example
/// ```c
/// char result[128];
/// size_t outsize = sizeof result;
/// int success = mangling_demangle(strlen(argv[1]), argv[1], &outsize, result);
/// fwrite(result, 1, outsize, stdout);
/// ```
///
/// # Safety
/// In order to avoid undefined behavior, this function must be called with `instr` pointing to a
/// string of bytes at least `insize` in length, or else `instr` must be a null pointer. No
/// requirement is levied on the contents of the referenced memory, besides that it must be
/// readable.
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

