/// Implements tests for the Rust and C-compatible interfaces to the `mangle` and `demangle`
/// functions.
use super::*;

use quickcheck::quickcheck;

#[rustfmt::skip]
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

const DEMANGLE_BAD : &[&str] = &["bad", "_1", "_0", "_03x", "_\u{0}"];

#[test]
fn test_mangle_native() {
    for (unmangled, mangled) in MANGLE_LIST {
        let want = mangled;

        let got = mangle(unmangled.bytes());
        assert_eq!(want, &got);
    }
}

#[test]
fn test_mangle_extern() {
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
}

#[test]
fn test_demangle_native() -> ManglingResult<()> {
    for (unmangled, mangled) in MANGLE_LIST {
        let want : Vec<u8> = (*unmangled).to_string().into();
        let got : Vec<u8> = demangle(mangled)?;
        assert_eq!(want, got);
    }

    Ok(())
}

#[test]
fn test_demangle_extern() {
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
        assert!(demangle(mangled).is_err());
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
    #[allow(clippy::result_unwrap_used)]
    fn test_mangling_roundtrip(rs : Vec<u8>) -> bool {
        rs == demangle(&mangle(rs.clone())).unwrap()
    }

    fn test_demangled_corrupted_native(deletion : usize) -> () {
        for (_, mangled) in MANGLE_LIST {
            let (_, v) : (Vec<_>, Vec<_>) = mangled.chars().enumerate().filter(|&(i, _)| i != deletion % mangled.len()).unzip();
            let m : String = v.into_iter().collect();
            assert!(demangle(&m).is_err());
        }
    }

    fn test_demangled_corrupted_extern(deletion : usize) -> () {
        for (_, mangled) in MANGLE_LIST {
            let (_, v) : (Vec<_>, Vec<_>) = mangled.chars().enumerate().filter(|&(i, _)| i != deletion % mangled.len()).unzip();
            let m : String = v.into_iter().collect();
            assert!(demangle(&m).is_err());

            let mut len = 0;
            assert_ne!(0, try_demangle(&m, Some(&mut len), None));
            assert_ne!(0, try_demangle(&m, None, None));

            let mut result : Vec<u8> = Vec::with_capacity(128);
            let ptr = unsafe { &mut *(result.as_mut_ptr() as *mut c_char) };
            assert_ne!(0, try_demangle(&m, Some(&mut len), Some(ptr)));
            assert_ne!(0, try_demangle(&m, None, Some(ptr)));
        }
    }
}

quickcheck! {
    #[allow(clippy::result_unwrap_used)]
    fn test_hexify(byte : u8) -> () {
        let got = hexify(byte);
        let want = format!("{:02x}", byte);
        assert_eq!(got, want.as_bytes());
    }
}
