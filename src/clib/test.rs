/// Implements tests for the C-compatible interfaces to the `mangle` and `demangle` functions.
use super::*;

use quickcheck::quickcheck;

use crate::test::MANGLE_LIST;
use crate::test::DEMANGLE_BAD;

#[test]
fn mangling() {
    for (unmangled, mangled) in MANGLE_LIST {
        let want = mangled;

        let got = {
            // worst-case upper bound is 5x the input length
            // (asymptotic upper bound is 3.5x the input length)
            let mut result : Vec<u8> = Vec::with_capacity(want.len() * 5);
            let mut len : usize = result.capacity();
            let input = match unmangled.len() {
                0 => None,
                _ => Some(unsafe { &*(unmangled.as_ptr() as *const c_char) }),
            };
            let ptr = unsafe { &mut *(result.as_mut_ptr() as *mut c_char) };
            let success = mangling_mangle(unmangled.len(), input, Some(&mut len), Some(ptr));
            assert_eq!(success, 0);
            assert!(len <= result.capacity());
            unsafe {
                result.set_len(len);
            }
            String::from_utf8(result).unwrap()
        };
        assert_eq!(want, &got);
    }

    let success = mangling_mangle(1, None, None, None);
    assert_ne!(success, 0);

    let success = mangling_mangle(0, None, None, None);
    assert_eq!(success, 0);
}

#[test]
fn demangling() {
    for (unmangled, mangled) in MANGLE_LIST {
        let want : Vec<u8> = (*unmangled).to_string().into();

        assert_eq!(0, try_demangle(mangled, Some(&mut 0), None));
        // worst-case upper bound is 1x the input length, with a lower bound of 1
        let mut result : Vec<u8> = Vec::with_capacity(1 + want.len());
        let ptr = unsafe { &mut *(result.as_mut_ptr() as *mut c_char) };
        assert_eq!(0, try_demangle(mangled, None, Some(ptr)));

        let got = {
            // worst-case upper bound is 1x the input length, with a lower bound of 1
            let mut result : Vec<u8> = Vec::with_capacity(1 + want.len());
            let mut len : usize = result.capacity();
            let ptr = unsafe { &mut *(result.as_mut_ptr() as *mut c_char) };
            assert_eq!(0, try_demangle(mangled, Some(&mut len), Some(ptr)));
            assert!(len <= result.capacity());
            unsafe {
                result.set_len(len);
            }
            result
        };
        assert_eq!(want, got);
    }

    for mangled in DEMANGLE_BAD {
        let mut len = 0;
        assert_ne!(0, try_demangle(mangled, Some(&mut len), None));
    }
}

fn try_demangle(m : &str, up : Option<&mut usize>, rp : Option<&mut c_char>) -> c_int {
    let input = match m.len() {
        0 => None,
        _ => Some(unsafe { &*(m.as_ptr() as *const c_char) }),
    };
    mangling_demangle(m.len(), input, up, rp)
}

quickcheck! {
    fn demangling_corrupted(deletion : usize) -> () {
        for (_, mangled) in MANGLE_LIST {
            let (_, v) : (Vec<_>, Vec<_>) = mangled.chars().enumerate().filter(|&(i, _)| i != deletion % mangled.len()).unzip();
            let m : String = v.into_iter().collect();
            assert!(demangle(&m).is_err());

            let mut len = 0;
            assert_ne!(0, try_demangle(&m, Some(&mut len), None));
            assert_ne!(0, try_demangle(&m, None, None));

            // Capacity is arbitrary as long as there is some minimal backing in place
            let mut result : Vec<u8> = Vec::with_capacity(1);
            let ptr = unsafe { &mut *(result.as_mut_ptr() as *mut c_char) };
            assert_ne!(0, try_demangle(&m, Some(&mut len), Some(ptr)));
            assert_ne!(0, try_demangle(&m, None, Some(ptr)));
        }
    }
}

