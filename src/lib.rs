#![allow(dead_code)]

#[cfg(test)]
use rand::distributions::{Distribution, Normal, Standard};
#[cfg(test)]
use rand::{thread_rng, Rng};

use std::str::FromStr;

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
        assert_eq!(&mangle(unmangled.as_ref()), mangled);
    }
}

pub fn mangle(name : &[u8]) -> String {
    let mut out = String::with_capacity(2 * name.len()); // heuristic

    out.push('_');

    let begin_ok = |x : char| x.is_ascii_alphabetic() || x == '_';
    let within_ok = |x : char| begin_ok(x) || x.is_ascii_digit();

    let mut remain = name.iter().peekable();

    loop {
        let mut v = Vec::new();
        match remain.peek() {
            Some(&&r) if begin_ok(char::from(r)) => {
                loop {
                    match remain.peek() {
                        Some(&&r) if within_ok(char::from(r)) => {
                            v.push(r);
                            remain.next();
                        },
                        _ => break,
                    }
                }
                out.push_str(&format!("{}{}", v.len(), String::from_utf8(v).unwrap()));
            },
            Some(_) => {
                loop {
                    match remain.peek() {
                        Some(&&r) if !begin_ok(char::from(r)) => {
                            v.push(r);
                            remain.next();
                        },
                        _ => break,
                    }
                }
                out.push_str(&format!("0{}_{}", v.len(), hexify(v.as_ref())));
            },
            _ => {
                out.shrink_to_fit();
                return out;
            }
        }
    }
}

use std::error::Error;
type Result<T> = std::result::Result<T, Box<Error>>;

#[test]
fn test_demangle() -> Result<()> {
    for (unmangled, mangled) in MANGLE_LIST {
        let got : Vec<u8> = demangle(mangled)?;
        let want : Vec<u8> = unmangled.to_owned().to_string().into();
        assert_eq!(want, got);
    }
    Ok(())
}

pub fn demangle(name : &str) -> Result<Vec<u8>> {
    if &name[..1] != "_" {
        panic!("Bad identifier (expected `_`)");
    } else {
        let mut out = Vec::with_capacity(name.len());
        demangle_inner(&mut out, &name[1..])?;
        return Ok(out);
    }

    fn demangle_inner(mut out : &mut Vec<u8>, name : &str) -> Result<()> {
        if name.is_empty() {
            return Ok(());
        } else if let Some((not_num, _)) = name.chars().enumerate().find(|(_, x)| !x.is_ascii_digit()) {
            let (num_str, new_name) = name.split_at(not_num);
            let len = usize::from_str(num_str).unwrap();

            if &name[..1] == "0" {
                if &new_name[..1] != "_" {
                    panic!("Bad identifier (expected `_`)");
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
            panic!("did not find a number");
        }
    }
}

#[test]
fn test_round_trip() {
    let mut rng = thread_rng();
    let norm = Normal::new(20.0, 5.0);
    for _ in 1..10 {
        let len = norm.sample(&mut rng) as usize;
        let rs : Vec<u8> = rng.sample_iter(&Standard).take(len).collect();

        assert_eq!(rs, demangle(&mangle(&rs.as_ref())).unwrap());
    }
}

fn hexify(bytes : &[u8]) -> String {
    bytes.iter().map(|b| format!("{:02x}", &b)).collect::<Vec<_>>().concat()
}

fn dehexify(s : &str) -> Result<Vec<u8>> {
    let parse = |v| u8::from_str_radix(std::str::from_utf8(v).unwrap(), 16).expect("Hex parse failure");
    Ok(s.as_bytes().chunks(2).map(parse).collect())
}

