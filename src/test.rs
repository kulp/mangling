/// Implements tests for the Rust `mangle` and `demangle` functions, as well as for private helper
/// functions.
use super::*;

use quickcheck::quickcheck;

#[rustfmt::skip]
pub(crate) const MANGLE_LIST : &[(&str, &str)] = &[
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

pub(crate) const DEMANGLE_BAD : &[&str] = &["bad", "_1", "_0", "_03x", "_\u{0}"];

#[test]
fn mangling() {
    for (unmangled, mangled) in MANGLE_LIST {
        let want = mangled;

        let got = mangle(unmangled.bytes());
        assert_eq!(want, &got);
    }
}

#[test]
fn demangling() -> ManglingResult<()> {
    for (unmangled, mangled) in MANGLE_LIST {
        let want : Vec<u8> = (*unmangled).to_string().into();
        let got : Vec<u8> = demangle(mangled)?;
        assert_eq!(want, got);
    }

    for mangled in DEMANGLE_BAD {
        assert!(demangle(mangled).is_err());
    }

    Ok(())
}

quickcheck! {
    #[allow(clippy::result_unwrap_used)]
    fn mangling_roundtrip(rs : Vec<u8>) -> bool {
        rs == demangle(&mangle(rs.clone())).unwrap()
    }

    fn length_promises(orig : Vec<u8>) -> () {
        let k = orig.len();
        let mangled = mangle(orig);
        let n = mangled.len();
        assert!(n > k);
        assert!(n <= 5 * k + 1);
        assert!(k <= 1 || n <= (3.5 * k as f64).ceil() as usize + 2);
    }

    fn demangling_corrupted(deletion : usize) -> () {
        for (_, mangled) in MANGLE_LIST {
            let (_, v) : (Vec<_>, Vec<_>) = mangled.chars().enumerate().filter(|&(i, _)| i != deletion % mangled.len()).unzip();
            let m : String = v.into_iter().collect();
            assert!(demangle(&m).is_err());
        }
    }
}

quickcheck! {
    #[allow(clippy::result_unwrap_used)]
    fn hexing(byte : u8) -> () {
        let got = hexify(byte);
        let want = format!("{:02x}", byte);
        assert_eq!(got, want.as_bytes());
    }
}
