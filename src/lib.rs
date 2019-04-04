#![allow(dead_code)]

#[cfg(test)]
use rand::distributions::{Distribution, Normal, Standard};
#[cfg(test)]
use rand::{thread_rng, Rng};

use std::error::Error;
use std::fmt;
use std::str::FromStr;

type Result<T> = std::result::Result<T, Box<Error>>;

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
fn test_mangle() -> Result<()> {
    for (unmangled, mangled) in MANGLE_LIST {
        assert_eq!(&mangle(unmangled.bytes())?, mangled);
    }
    Ok(())
}

pub fn mangle<T>(name : T) -> Result<String>
    where T : IntoIterator<Item=u8>
{
    let begin_ok = |x : char| x.is_ascii_alphabetic() || x == '_';
    let within_ok = |x : char| begin_ok(x) || x.is_ascii_digit();

    use std::rc::Rc;
    use std::cell::Cell;

    #[derive(Copy,Clone,Debug)]
    enum What { Invalid, Word, NonWord }
    #[derive(Copy,Clone,Debug)]
    enum How { Initial, Begin, Continue }
    type Many = Rc<Cell<usize>>;

    let start = (What::Invalid, How::Initial, Rc::new(Cell::new(0)));
    // For now, we need to collect into a vector so that Rc<> pointers are viewed after all updates
    // have occurred, rather than just as they are created.
    let result : Vec<_> = name.into_iter().scan(start, |st : &mut (What, How, Many), item| {
            use What::*;
            use How::*;
            let ch = char::from(item);
            let increment = || { let c = Rc::clone(&st.2); c.set(c.get() + 1); c };
            *st = match (&*st, begin_ok(ch), within_ok(ch)) {
                ((Word,    ..), _, true ) => (Word   , Continue, increment() ),
                ((NonWord, ..), _, false) => (NonWord, Continue, increment() ),

                (_, true , _)             => (Word   , Begin, Rc::new(Cell::new(1))),
                (_, false, _)             => (NonWord, Begin, Rc::new(Cell::new(1))),
            };
            Some((st.clone(), item))
        }).collect();

    let out = {
        let mut out = Vec::with_capacity(result.len() * 2); // heuristic
        out.push('_' as u8);
        out
    };
    let result = result.into_iter()
        .try_fold(out, |mut vec, ((what, how, count), ch)| {
            use What::*;
            use How::*;
            match (what, how) {
                (Word   , Begin) => vec.extend(count.get().to_string().bytes()),
                (NonWord, Begin) => vec.extend(format!("0{}_", count.get()).bytes()),
                _ => {},
            };
            match what {
                Word    => vec.push(ch),
                NonWord => vec.extend(hexify(ch)),
                _ => return Err(Box::new(MangleError::new("Bad state encountered during mangle"))),
            };
            Ok(vec)
        });

    let result = {
        let mut r = result?;
        r.shrink_to_fit();
        r
    };
    String::from_utf8(result).map_err(|e| e.into())
}

#[derive(Debug)]
pub struct MangleError(String);

impl MangleError {
    fn new(msg: &str) -> MangleError {
        MangleError(msg.to_string())
    }
}

impl fmt::Display for MangleError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Error for MangleError {
    fn description(&self) -> &str { &self.0 }
}

#[test]
fn test_demangle() -> Result<()> {
    for (unmangled, mangled) in MANGLE_LIST {
        let got : Vec<u8> = demangle(mangled)?;
        let want : Vec<u8> = unmangled.to_owned().to_string().into();
        assert_eq!(want, got);
    }

    assert!(demangle("bad").is_err());
    Ok(())
}

pub fn demangle(name : &str) -> Result<Vec<u8>> {
    if &name[..1] != "_" {
        return Err(Box::new(MangleError::new("Bad identifier (expected `_`)")));
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
            let len = usize::from_str(num_str)?;

            if &name[..1] == "0" {
                if &new_name[..1] != "_" {
                    return Err(Box::new(MangleError::new("Bad identifier (expected `_`)")));
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
            return Err(Box::new(MangleError::new("did not find a number")));
        }
    }
}

#[test]
fn test_round_trip() -> Result<()> {
    let mut rng = thread_rng();
    let norm = Normal::new(20.0, 5.0);
    for _ in 1..10 {
        let len = norm.sample(&mut rng) as usize;
        let rs : Vec<u8> = rng.sample_iter(&Standard).take(len).collect();

        assert_eq!(rs, demangle(&mangle(rs.clone())?)?); // TODO obviate .clone() here
    }
    Ok(())
}

fn hexify(byte : u8) -> Vec<u8> {
    format!("{:02x}", byte).into_bytes()
}

fn dehexify(s : &str) -> Result<Vec<u8>> {
    let stringify = |v| std::str::from_utf8(v).map_err::<Box<Error>,_>(|e| e.into());
    let parse = |v| u8::from_str_radix(v?, 16).map_err(|e| e.into());
    s.as_bytes().chunks(2).map(stringify).map(parse).collect()
}

