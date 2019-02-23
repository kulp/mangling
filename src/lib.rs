use lazy_static::lazy_static;
use regex::Regex;

#[cfg(test)]
const MANGLE_LIST : &[(&str, &str)] = &[
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
fn test_mangle() {
    for (unmangled, mangled) in MANGLE_LIST {
        assert_eq!(&mangle(unmangled), mangled);
    }
}

pub fn mangle(name : &str) -> String {
    let mut offset = 0;
    let mut out = String::with_capacity(2 * name.len()); // heuristic
    lazy_static! {
        static ref RE_TOKEN    : Regex = Regex::new(r"^(?i)[a-z_]\w*").unwrap();
        static ref RE_NONTOKEN : Regex = Regex::new(r"^[0-9]*\W*").unwrap();
    }

    out.push('_');

    while offset < name.len() {
        if let Some(m) = RE_TOKEN.find(&name[offset..]) {
            let s = m.as_str();
            let len = s.len();
            offset += len;
            out.push_str(&format!("{}{}", len, s));
        }
        if let Some(m) = RE_NONTOKEN.find(&name[offset..]) {
            if m.as_str().len() > 0 {
                let s = m.as_str();
                let len = s.len();
                offset += len;
                out.push_str(&format!("0{}_{}", len, hexify(&s)));
            } else if offset < name.len() {
                panic!("Unable to progress");
            }
        }
    }

    out.shrink_to_fit();
    return out;
}

#[test]
fn test_demangle() {
    for (unmangled, mangled) in MANGLE_LIST {
        assert_eq!(unmangled, &demangle(mangled));
    }
}

pub fn demangle(name : &str) -> String { // TODO Option<String>
    let mut offset = 0;
    let mut out = String::with_capacity(name.len());
    lazy_static! { static ref NUM : Regex = Regex::new(r"^\d+").unwrap(); }

    if &name[0..1] != "_" {
        panic!("Bad identifier (expected `_`)");
    } else {
        offset += 1;
    }

    let mut is_hex = false;
    while offset < name.len() {
        if &name[offset..offset+1] == "0" {
            offset += 1;
            is_hex = true;
        }
        let m = NUM.find(&name[offset..])
                   .expect("Bad identifier (expected number)");
        let len = usize::from_str_radix(m.as_str(), 10)
            .expect("Hex parse failure");
        offset += m.as_str().len();
        if is_hex {
            if &name[offset..offset+1] != "_" {
                panic!("Bad identifier (expected `_`)");
            }
            offset += 1;
            let nybbles = 2 * len;
            let vec = dehexify(&name[offset..offset+nybbles]);
            let utf8 = String::from_utf8(vec)
                .expect("Expected UTF-8 string");
            out.push_str(&utf8);
            offset += nybbles;
        } else {
            out.push_str(&name[offset..offset+len]);
            offset += len;
        }
        is_hex = false;
    }

    out.shrink_to_fit();
    return out;
}

fn hexify(s : &str) -> String {
    let mut out = String::new();
    let bytes = s.as_bytes();

    for &b in bytes {
        out.push_str(&format!("{:02x}", &b));
    }

    return out;
}

fn dehexify(s : &str) -> Vec<u8> {
    let mut out = Vec::with_capacity(s.len() / 2);

    for i in 0..(s.len() / 2) {
        let hex = u8::from_str_radix(&s[i*2..i*2+2], 16)
                    .expect("Hex parse failure");
        out.push(hex);
    }

    return out;
}

