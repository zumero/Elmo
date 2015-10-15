﻿/*
    Copyright 2014-2015 Zumero, LLC

    Licensed under the Apache License, Version 2.0 (the "License");
    you may not use this file except in compliance with the License.
    You may obtain a copy of the License at

        http://www.apache.org/licenses/LICENSE-2.0

    Unless required by applicable law or agreed to in writing, software
    distributed under the License is distributed on an "AS IS" BASIS,
    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
    See the License for the specific language governing permissions and
    limitations under the License.
*/

#![feature(box_syntax)]
#![feature(convert)]
#![feature(associated_consts)]
#![feature(vec_push_all)]
#![feature(clone_from_slice)]
#![feature(drain)]
#![feature(iter_arith)]

// TODO turn the following warnings back on later
#![allow(non_snake_case)]
#![allow(non_camel_case_types)]

extern crate misc;

use misc::endian;
use misc::varint;

use std::sync::mpsc;
use std::thread;

use std::io;
use std::io::Seek;
use std::io::Read;
use std::io::Write;
use std::io::SeekFrom;
use std::cmp::Ordering;
use std::fs::File;
use std::fs::OpenOptions;
use std::collections::HashMap;
use std::collections::HashSet;

use std::hash::Hash;
use std::hash::Hasher;
use std::hash::SipHasher;

const SIZE_32: usize = 4; // like std::mem::size_of::<u32>()
const SIZE_16: usize = 2; // like std::mem::size_of::<u16>()

pub type PageNum = u32;
// type PageSize = u32;

// TODO also perhaps the type representing size of a value, u32
// size of a value should NOT be usize, right?

// TODO there is code which assumes that PageNum is u32.
// but that's the nature of the file format.  the type alias
// isn't so much so that we can change it, but rather, to make
// reading the code easier.

pub enum Blob {
    Stream(Box<Read>),
    Array(Box<[u8]>),
    Tombstone,
    // TODO Graveyard?  (considered a delete of anything with the prefix?)
}

impl Blob {
    fn is_tombstone(&self) -> bool {
        match self {
            &Blob::Tombstone => true,
            &Blob::Stream(_) => false,
            &Blob::Array(_) => false,
        }
    }
}

#[derive(Debug)]
pub enum Error {
    // TODO remove Misc
    Misc(String),

    // TODO more detail within CorruptFile
    CorruptFile(&'static str),

    Io(std::io::Error),
    Utf8(std::str::Utf8Error),

    CursorNotValid,
    InvalidPageNumber,
    InvalidPageType(u8),
    RootPageNotInSegmentBlockList,
    Poisoned,
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match *self {
            Error::Io(ref err) => write!(f, "IO error: {}", err),
            Error::Utf8(ref err) => write!(f, "Utf8 error: {}", err),
            Error::Misc(ref s) => write!(f, "Misc error: {}", s),
            Error::CorruptFile(s) => write!(f, "Corrupt file: {}", s),
            Error::Poisoned => write!(f, "Poisoned"),
            Error::CursorNotValid => write!(f, "Cursor not valid"),
            Error::InvalidPageNumber => write!(f, "Invalid page number"),
            Error::InvalidPageType(b) => write!(f, "Invalid page type: {}", b),
            Error::RootPageNotInSegmentBlockList => write!(f, "Root page not in segment block list"),
        }
    }
}

impl std::error::Error for Error {
    fn description(&self) -> &str {
        match *self {
            Error::Io(ref err) => std::error::Error::description(err),
            Error::Utf8(ref err) => std::error::Error::description(err),
            Error::Misc(ref s) => s.as_str(),
            Error::CorruptFile(s) => s,
            Error::Poisoned => "poisoned",
            Error::CursorNotValid => "cursor not valid",
            Error::InvalidPageNumber => "invalid page number",
            Error::InvalidPageType(b) => "invalid page type",
            Error::RootPageNotInSegmentBlockList => "Root page not in segment block list",
        }
    }

    // TODO cause
}

pub fn wrap_err<E: std::error::Error + 'static>(err: E) -> Error {
    Error::Misc(format!("{}", err))
}

impl From<io::Error> for Error {
    fn from(err: io::Error) -> Error {
        Error::Io(err)
    }
}

impl From<std::str::Utf8Error> for Error {
    fn from(err: std::str::Utf8Error) -> Error {
        Error::Utf8(err)
    }
}

impl<T> From<std::sync::PoisonError<T>> for Error {
    fn from(_err: std::sync::PoisonError<T>) -> Error {
        Error::Poisoned
    }
}

pub type Result<T> = std::result::Result<T, Error>;

pub enum NoMaybe {
    No,
    Maybe,
}

pub enum YesNoMaybe {
    Yes,
    No,
    Maybe,
}

struct Bloom {
    bits: Vec<u8>,
    funcs: Vec<SipHasher>,
}

impl Bloom {
    fn new(bits: Vec<u8>, count_funcs: usize) -> Self {
        let mut funcs = vec![];
        for i in 0 .. count_funcs {
            let k0 = i * count_funcs;
            let k1 = (i + 1) * count_funcs;
            funcs.push(SipHasher::new_with_keys(k0 as u64, k1 as u64));
        }
        Bloom {
            bits: bits,
            funcs: funcs,
        }
    }

    fn into_bytes(self) -> Vec<u8> {
        self.bits
    }

    fn count_funcs(&self) -> usize {
        self.funcs.len()
    }

    fn find_bit(i: u64) -> (usize, u8) {
        let i = i / 8;
        let j = i % 8;
        let m = 1 << j;
        (i as usize, m as u8)
    }

    fn do_hash(&self, fi: usize, v1: &[u8], v2: &[u8]) -> (usize, u8) {
        // TODO this clone is so very sad
        let mut f = self.funcs[fi].clone();
        f.write(v1);
        f.write(v2);
        let h = f.finish();
        let num_bits = (self.bits.len() * 8) as u64;
        let b = h % num_bits;
        let (i, m) = Self::find_bit(b);
        //println!("k: {:?}/{:?} for func {} bits.len {} funcs.len {} goes to {}, {}, {}", v1, v2, fi, self.bits.len(), self.funcs.len(), h, i, m);
        (i, m)
    }

    fn set(&mut self, v1: &[u8], v2: &[u8]) {
        //println!("setting: {:?}/{:?}", v1, v2);
        for fi in 0 .. self.funcs.len() {
            let (i, m) = self.do_hash(fi, v1, v2);
            //println!("bits[{}] before: {}", i, self.bits[i]);
            self.bits[i] = self.bits[i] | m;
            //println!("bits[{}] after: {}", i, self.bits[i]);
        }
    }

    fn check(&self, v1: &[u8], v2: &[u8]) -> NoMaybe {
        //println!("checking: {:?}/{:?}", v1, v2);
        for fi in 0 .. self.funcs.len() {
            let (i, m) = self.do_hash(fi, v1, v2);
            //println!("bits[{}] check: {}", i, self.bits[i]);
            if 0 == self.bits[i] & m {
                //println!("    false");
                return NoMaybe::No;;
            }
        }
        //println!("    true");
        return NoMaybe::Maybe;;
    }

    fn check_keyref(&self, k: &KeyRef) -> NoMaybe {
        match k {
            &KeyRef::Overflowed(ref a) => self.check(&a, &[]),
            &KeyRef::Prefixed(front, back) => self.check(front, back),
            &KeyRef::Array(a) => self.check(a, &[]),
        }
    }

}

#[test]
fn bloom_test_1() {
    let mut blm = Bloom::new(vec![0; 32], 4);
    let k = [1, 3, 5, 7, 9];
    assert!(!blm.check(&k));
    blm.set(&k);
    assert!(blm.check(&k));
}


// kvp is the struct used to provide key-value pairs downward,
// for storage into the database.
pub struct kvp {
    Key : Box<[u8]>,
    Value : Blob,
}

#[derive(Debug)]
struct PendingSegment {
    blockList: Vec<PageBlock>,
    segnum: SegmentNum,
}

// TODO this is experimental.  it might not be very useful unless
// it can be used everywhere a regular slice can be used.  but we
// obviously don't want to just pass around an Index<Output=u8>
// trait object if that forces us into dynamic dispatch everywhere.
#[cfg(remove_me)]
struct SplitSlice<'a> {
    front: &'a [u8],
    back: &'a [u8],
}

#[cfg(remove_me)]
impl<'a> SplitSlice<'a> {
    fn new(front: &'a [u8], back: &'a [u8]) -> SplitSlice<'a> {
        SplitSlice {front: front, back: back}
    }

    fn len(&self) -> usize {
        self.front.len() + self.back.len()
    }

    fn into_boxed_slice(self) -> Box<[u8]> {
        let mut k = Vec::with_capacity(self.front.len() + self.back.len());
        k.push_all(&self.front);
        k.push_all(&self.back);
        k.into_boxed_slice()
    }
}

#[cfg(remove_me)]
impl<'a> Index<usize> for SplitSlice<'a> {
    type Output = u8;

    fn index(&self, _index: usize) -> &u8 {
        if _index >= self.front.len() {
            &self.back[_index - self.front.len()]
        } else {
            &self.front[_index]
        }
    }
}

fn split3<T>(a: &mut [T], i: usize) -> (&mut [T], &mut [T], &mut [T]) {
    let (before, a2) = a.split_at_mut(i);
    let (islice, after) = a2.split_at_mut(1);
    (before, islice, after)
}

pub enum KeyRef<'a> {
    // for an overflowed key, we just punt and read it into memory
    Overflowed(Box<[u8]>),

    // the other two are references into the page
    Prefixed(&'a [u8],&'a [u8]),
    Array(&'a [u8]),
}

impl<'a> std::fmt::Debug for KeyRef<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::result::Result<(), std::fmt::Error> {
        match *self {
            KeyRef::Overflowed(ref a) => write!(f, "Overflowed, a={:?}", a),
            KeyRef::Prefixed(front,back) => write!(f, "Prefixed, front={:?}, back={:?}", front, back),
            KeyRef::Array(a) => write!(f, "Array, val={:?}", a),
        }
    }
}

impl<'a> KeyRef<'a> {
    pub fn len(&self) -> usize {
        match *self {
            KeyRef::Overflowed(ref a) => a.len(),
            KeyRef::Array(a) => a.len(),
            KeyRef::Prefixed(front, back) => front.len() + back.len(),
        }
    }

    pub fn u8_at(&self, i: usize) -> Result<u8> {
        match self {
            &KeyRef::Overflowed(ref a) => {
                if i < a.len() {
                    Ok(a[i])
                } else {
                    Err(Error::Misc(String::from("u8_at: out of range 1")))
                }
            },
            &KeyRef::Array(a) => {
                if i < a.len() {
                    Ok(a[i])
                } else {
                    Err(Error::Misc(String::from("u8_at: out of range 2")))
                }
            },
            &KeyRef::Prefixed(front, back) => {
                if i < front.len() {
                    Ok(front[i])
                } else {
                    let i = i - front.len();
                    if i < back.len() {
                        Ok(back[i])
                    } else {
                        Err(Error::Misc(String::from("u8_at: out of range 3")))
                    }
                }
            },
        }
    }

    pub fn compare_with(&self, k: &[u8]) -> Ordering {
        match self {
            &KeyRef::Overflowed(ref a) => {
                bcmp::Compare(&a, &k)
            },
            &KeyRef::Array(a) => {
                bcmp::Compare(&a, &k)
            },
            &KeyRef::Prefixed(front, back) => {
                Self::compare_px_y(front, back, k)
            },
        }
    }

    pub fn starts_with(&self, k: &[u8]) -> bool {
        if self.len() < k.len() {
            return false;
        } else {
            match self {
                &KeyRef::Overflowed(ref a) => {
                    k == &a[0 .. k.len()]
                },
                &KeyRef::Array(a) => {
                    k == &a[0 .. k.len()]
                },
                &KeyRef::Prefixed(front, back) => {
                    if k.len() <= front.len() {
                        k == &front[0 .. k.len()]
                    } else {
                        &k[0 .. front.len()] == &front[0 .. front.len()]
                        && 
                        &k[front.len() ..] == &back[0 .. k.len() - front.len()]
                    }
                },
            }
        }
    }

    /// A KeyRef is conceptually just a bunch of bytes, but it can be represented in
    /// three different ways, depending on whether the key in the page was overflowed
    /// or prefixed or neither.  This function accepts a func which is to be applied
    /// to a range of the key.  Whenever possible, the func is called without allocation.
    /// But if the requested range crosses the front/back boundary of a prefixed key,
    /// then an alloc+copy will be needed.
    pub fn map_range<T, F: Fn(&[u8]) -> Result<T>>(&self, begin: usize, end: usize, func: F) -> Result<T> {
        if end <= begin {
            return Err(Error::Misc(String::from("illegal range")));
        }
        match self {
            &KeyRef::Array(a) => {
                if end <= a.len() {
                    let t = try!(func(&a[begin .. end]));
                    Ok(t)
                } else {
                    Err(Error::Misc(String::from("map_range: out of range 1")))
                }
            },
            &KeyRef::Overflowed(ref a) => {
                if end <= a.len() {
                    let t = try!(func(&a[begin .. end]));
                    Ok(t)
                } else {
                    Err(Error::Misc(String::from("map_range: out of range 2")))
                }
            },
            &KeyRef::Prefixed(front, back) => {
                if end <= front.len() {
                    let t = try!(func(&front[begin .. end]));
                    Ok(t)
                } else if begin >= front.len() {
                    let begin = begin - front.len();
                    let end = end - front.len();
                    if end <= back.len() {
                        let t = try!(func(&back[begin .. end]));
                        Ok(t)
                    } else {
                        Err(Error::Misc(String::from("map_range: out of range 3")))
                    }
                } else {
                    // the range we want is split across the front and back.
                    // in this case we have to alloc.
                    let mut a = Vec::with_capacity(end - begin);
                    a.push_all(&front[begin .. ]);
                    let end = end - front.len();
                    if end <= back.len() {
                        a.push_all(&back[0 .. end]);
                        let t = try!(func(&a));
                        Ok(t)
                    } else {
                        Err(Error::Misc(String::from("map_range: out of range 4")))
                    }
                }
            },
        }
    }

    pub fn from_boxed_slice(k: Box<[u8]>) -> KeyRef<'a> {
        KeyRef::Overflowed(k)
    }

    pub fn for_slice(k: &[u8]) -> KeyRef {
        KeyRef::Array(k)
    }

    pub fn into_boxed_slice(self) -> Box<[u8]> {
        match self {
            KeyRef::Overflowed(a) => {
                a
            },
            KeyRef::Array(a) => {
                let mut k = Vec::with_capacity(a.len());
                k.push_all(a);
                k.into_boxed_slice()
            },
            KeyRef::Prefixed(front,back) => {
                let mut k = Vec::with_capacity(front.len() + back.len());
                k.push_all(front);
                k.push_all(back);
                k.into_boxed_slice()
            },
        }
    }

    // TODO move this to the bcmp module?
    fn compare_px_py(px: &[u8], x: &[u8], py: &[u8], y: &[u8]) -> Ordering {
        let xlen = px.len() + x.len();
        let ylen = py.len() + y.len();
        let len = std::cmp::min(xlen, ylen);
        for i in 0 .. len {
            let xval = 
                if i<px.len() {
                    px[i]
                } else {
                    x[i - px.len()]
                };
            let yval = 
                if i<py.len() {
                    py[i]
                } else {
                    y[i - py.len()]
                };
            let c = xval.cmp(&yval);
            if c != Ordering::Equal {
                return c;
            }
        }
        return xlen.cmp(&ylen);
    }

    // TODO move this to the bcmp module?
    fn compare_px_y(px: &[u8], x: &[u8], y: &[u8]) -> Ordering {
        let xlen = px.len() + x.len();
        let ylen = y.len();
        let len = std::cmp::min(xlen, ylen);
        for i in 0 .. len {
            let xval = 
                if i<px.len() {
                    px[i]
                } else {
                    x[i - px.len()]
                };
            let yval = y[i];
            let c = xval.cmp(&yval);
            if c != Ordering::Equal {
                return c;
            }
        }
        return xlen.cmp(&ylen);
    }

    // TODO move this to the bcmp module?
    fn compare_x_py(x: &[u8], py: &[u8], y: &[u8]) -> Ordering {
        let xlen = x.len();
        let ylen = py.len() + y.len();
        let len = std::cmp::min(xlen, ylen);
        for i in 0 .. len {
            let xval = x[i];
            let yval = 
                if i<py.len() {
                    py[i]
                } else {
                    y[i - py.len()]
                };
            let c = xval.cmp(&yval);
            if c != Ordering::Equal {
                return c;
            }
        }
        return xlen.cmp(&ylen);
    }

    pub fn cmp(x: &KeyRef, y: &KeyRef) -> Ordering {
        match (x,y) {
            (&KeyRef::Overflowed(ref x_k), &KeyRef::Overflowed(ref y_k)) => {
                bcmp::Compare(&x_k, &y_k)
            },
            (&KeyRef::Overflowed(ref x_k), &KeyRef::Prefixed(ref y_p, ref y_k)) => {
                Self::compare_x_py(&x_k, y_p, y_k)
            },
            (&KeyRef::Overflowed(ref x_k), &KeyRef::Array(ref y_k)) => {
                bcmp::Compare(&x_k, &y_k)
            },
            (&KeyRef::Prefixed(ref x_p, ref x_k), &KeyRef::Overflowed(ref y_k)) => {
                Self::compare_px_y(x_p, x_k, &y_k)
            },
            (&KeyRef::Array(ref x_k), &KeyRef::Overflowed(ref y_k)) => {
                bcmp::Compare(&x_k, &y_k)
            },
            (&KeyRef::Prefixed(ref x_p, ref x_k), &KeyRef::Prefixed(ref y_p, ref y_k)) => {
                Self::compare_px_py(x_p, x_k, y_p, y_k)
            },
            (&KeyRef::Prefixed(ref x_p, ref x_k), &KeyRef::Array(ref y_k)) => {
                Self::compare_px_y(x_p, x_k, y_k)
            },
            (&KeyRef::Array(ref x_k), &KeyRef::Prefixed(ref y_p, ref y_k)) => {
                Self::compare_x_py(x_k, y_p, y_k)
            },
            (&KeyRef::Array(ref x_k), &KeyRef::Array(ref y_k)) => {
                bcmp::Compare(&x_k, &y_k)
            },
        }
    }
}


/// Like a ValueRef, but cannot represent a tombstone.  Available
/// only from a LivingCursor.
pub enum LiveValueRef<'a> {
    Array(&'a [u8]),
    Overflowed(usize, Box<Read>),
}

impl<'a> LiveValueRef<'a> {
    pub fn len(&self) -> usize {
        match *self {
            LiveValueRef::Array(a) => a.len(),
            LiveValueRef::Overflowed(len, _) => len,
        }
    }

    pub fn into_blob(self) -> Blob {
        match self {
            LiveValueRef::Array(a) => {
                let mut k = Vec::with_capacity(a.len());
                k.push_all(a);
                Blob::Array(k.into_boxed_slice())
            },
            LiveValueRef::Overflowed(_, r) => Blob::Stream(r),
        }
    }

    // dangerous function if len() is big
    pub fn into_boxed_slice(self) -> Result<Box<[u8]>> {
        match self {
            LiveValueRef::Array(a) => {
                let mut v = Vec::with_capacity(a.len());
                v.push_all(a);
                Ok(v.into_boxed_slice())
            },
            LiveValueRef::Overflowed(len, mut strm) => {
                let mut a = Vec::with_capacity(len);
                try!(strm.read_to_end(&mut a));
                Ok(a.into_boxed_slice())
            },
        }
    }

    /// A LiveValueRef is conceptually just a bunch of bytes, but it can be represented in
    /// two different ways, depending on whether the value in the page was overflowed
    /// or not.  This function accepts a func which is to be applied to the value.
    /// If the value was overflowed, it will be read into memory.  Otherwise, the func
    /// gets called without alloc or copy.
    pub fn map<T, F: Fn(&[u8]) -> Result<T>>(self, func: F) -> Result<T> {
        match self {
            LiveValueRef::Array(a) => {
                let t = try!(func(a));
                Ok(t)
            },
            LiveValueRef::Overflowed(len, mut strm) => {
                let mut a = Vec::with_capacity(len);
                try!(strm.read_to_end(&mut a));
                assert!(len == a.len());
                let t = try!(func(&a));
                Ok(t)
            },
        }
    }
}

impl<'a> std::fmt::Debug for LiveValueRef<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::result::Result<(), std::fmt::Error> {
        match *self {
            LiveValueRef::Array(a) => write!(f, "Array, len={:?}", a),
            LiveValueRef::Overflowed(klen,_) => write!(f, "Overflowed, len={}", klen),
        }
    }
}

pub enum ValueRef<'a> {
    Array(&'a [u8]),
    Overflowed(usize, Box<Read>),
    Tombstone,
}

impl<'a> ValueRef<'a> {
    pub fn len(&self) -> Option<usize> {
        match *self {
            ValueRef::Array(a) => Some(a.len()),
            ValueRef::Overflowed(len, _) => Some(len),
            ValueRef::Tombstone => None,
        }
    }

    pub fn into_blob(self) -> Blob {
        match self {
            ValueRef::Array(a) => {
                let mut k = Vec::with_capacity(a.len());
                k.push_all(a);
                Blob::Array(k.into_boxed_slice())
            },
            ValueRef::Overflowed(_, r) => Blob::Stream(r),
            ValueRef::Tombstone => Blob::Tombstone,
        }
    }

}

impl<'a> std::fmt::Debug for ValueRef<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::result::Result<(), std::fmt::Error> {
        match *self {
            ValueRef::Array(a) => write!(f, "Array, len={:?}", a),
            ValueRef::Overflowed(klen,_) => write!(f, "Overflowed, len={}", klen),
            ValueRef::Tombstone => write!(f, "Tombstone"),
        }
    }
}

// TODO consider putting this into a module so we can keep firstPage and lastPage private and
// expose methods to modify them so that we can assert when they become invalid.

#[derive(Hash,PartialEq,Eq,Copy,Clone,Debug)]
pub struct PageBlock {
    firstPage: PageNum,
    lastPage: PageNum,
}

impl PageBlock {
    fn new(first: PageNum, last: PageNum) -> PageBlock {
        assert!(first <= last);
        PageBlock { firstPage: first, lastPage: last }
    }

    fn count_pages(&self) -> PageNum {
        self.lastPage - self.firstPage + 1
    }

    fn contains_page(&self, pgnum: PageNum) -> bool {
        (pgnum >= self.firstPage) && (pgnum <= self.lastPage)
    }
}

fn block_list_contains_page(blocks: &Vec<PageBlock>, pgnum: PageNum) -> bool {
    for blk in blocks.iter() {
        if blk.contains_page(pgnum) {
            return true;
        }
    }
    return false;
}

pub type SegmentNum = u64;

trait IPages {
    fn PageSize(&self) -> usize;
    fn Begin(&self) -> Result<PendingSegment>;
    fn GetBlock(&self, token: &mut PendingSegment) -> Result<PageBlock>;
    fn End(&self, token: PendingSegment, unused_page: PageNum, root_page: PageNum) -> Result<SegmentNum>;
}

#[derive(PartialEq,Copy,Clone)]
pub enum SeekOp {
    SEEK_EQ = 0,
    SEEK_LE = 1,
    SEEK_GE = 2,
}

struct CursorIterator {
    csr: Box<ICursor>,
}

impl CursorIterator {
    fn new(it: Box<ICursor>) -> CursorIterator {
        CursorIterator { csr: it }
    }
}

impl Iterator for CursorIterator {
    type Item = Result<kvp>;
    fn next(&mut self) -> Option<Result<kvp>> {
        if self.csr.IsValid() {
            let k = {
                let k = self.csr.KeyRef();
                if k.is_err() {
                    return Some(Err(k.err().unwrap()));
                }
                let k = k.unwrap().into_boxed_slice();
                k
            };
            let v = {
                let v = self.csr.ValueRef();
                if v.is_err() {
                    return Some(Err(v.err().unwrap()));
                }
                let v = v.unwrap().into_blob();
                v
            };
            let r = self.csr.Next();
            if r.is_err() {
                return Some(Err(r.err().unwrap()));
            }
            Some(Ok(kvp{Key:k, Value:v}))
        } else {
            return None;
        }
    }
}

#[derive(Copy,Clone,Debug,PartialEq)]
pub enum SeekResult {
    Invalid,
    Unequal,
    Equal,
}

impl SeekResult {
    fn from_cursor<T: ICursor>(csr: &T, k: &KeyRef) -> Result<SeekResult> {
        if csr.IsValid() {
            let kc = try!(csr.KeyRef());
            if Ordering::Equal == KeyRef::cmp(&kc, k) {
                Ok(SeekResult::Equal)
            } else {
                Ok(SeekResult::Unequal)
            }
        } else {
            Ok(SeekResult::Invalid)
        }
    }

    fn is_valid(self) -> bool {
        match self {
            SeekResult::Invalid => false,
            SeekResult::Unequal => true,
            SeekResult::Equal => true,
        }
    }

    fn is_valid_and_equal(self) -> bool {
        match self {
            SeekResult::Invalid => false,
            SeekResult::Unequal => false,
            SeekResult::Equal => true,
        }
    }
}

pub trait ICursor {
    fn SeekRef(&mut self, k: &KeyRef, sop: SeekOp) -> Result<SeekResult>;
    fn First(&mut self) -> Result<()>;
    fn Last(&mut self) -> Result<()>;
    fn Next(&mut self) -> Result<()>;
    fn Prev(&mut self) -> Result<()>;

    fn IsValid(&self) -> bool;

    fn KeyRef<'a>(&'a self) -> Result<KeyRef<'a>>;
    fn ValueRef<'a>(&'a self) -> Result<ValueRef<'a>>;

    // TODO maybe rm ValueLength.  but LivingCursor uses it as a fast
    // way to detect whether a value is a tombstone or not.
    fn ValueLength(&self) -> Result<Option<usize>>; // tombstone is None

}

//#[derive(Copy,Clone)]
pub struct DbSettings {
    pub AutoMergeEnabled : bool,
    pub AutoMergeMinimumPages : PageNum,
    pub DefaultPageSize : usize,
    pub PagesPerBlock : PageNum,
}

pub const DEFAULT_SETTINGS: DbSettings = 
    DbSettings {
        AutoMergeEnabled : true,
        AutoMergeMinimumPages : 4,
        DefaultPageSize : 4096,
        PagesPerBlock : 256,
    };

#[derive(Debug,Clone)]
// TODO might not want to leave this stuff pub
pub struct SegmentInfo {
    pub root_page: PageNum,
    pub age: u32,

    // TODO does this grow?  shouldn't it be a boxed array?
    // yes, but then derive clone complains.
    // ideally we could just stop cloning this struct.
    pub blocks: Vec<PageBlock> 
}

pub mod utils {
    use std::io::Seek;
    use std::io::SeekFrom;
    use super::PageNum;
    use super::Error;
    use super::Result;

    pub fn SeekPage(strm: &mut Seek, pgsz: usize, pageNumber: PageNum) -> Result<u64> {
        if 0==pageNumber { 
            // TODO should this panic?
            return Err(Error::InvalidPageNumber);
        }
        let pos = ((pageNumber as u64) - 1) * (pgsz as u64);
        let v = try!(strm.seek(SeekFrom::Start(pos)));
        Ok(v)
    }

}

mod bcmp {
    use std::cmp::Ordering;
    use std::cmp::min;

    // this fn is actually kinda handy to make sure that we are comparing
    // what we are supposed to be comparing.  if we just use cmp, we
    // can end up comparing two things that happen to match each other's
    // type but which do not match &[u8].  this function makes the type
    // checking more explicit.
    #[inline(always)]
    pub fn Compare(x: &[u8], y: &[u8]) -> Ordering {
        x.cmp(y)
    }

    pub fn PrefixMatch(x: &[u8], y: &[u8], max: usize) -> usize {
        let len = min(x.len(), y.len());
        let lim = min(len, max);
        let mut i = 0;
        while i<lim && x[i]==y[i] {
            i = i + 1;
        }
        i
    }

    #[cfg(remove_me)]
    fn StartsWith(x: &[u8], y: &[u8], max: usize) -> bool {
        if x.len() < y.len() {
            false
        } else {
            let len = y.len();
            let mut i = 0;
            while i<len && x[i]==y[i] {
                i = i + 1;
            }
            i==len
        }
    }
}

struct PageBuilder {
    cur : usize,
    buf : Box<[u8]>,
}

// TODO bundling cur with the buf almost seems sad, because there are
// cases where we want buf to be mutable but not cur.  :-)

impl PageBuilder {
    fn new(pgsz : usize) -> PageBuilder { 
        let ba = vec![0;pgsz as usize].into_boxed_slice();
        PageBuilder { cur: 0, buf:ba } 
    }

    fn Reset(&mut self) {
        self.cur = 0;
    }

    fn Write(&self, strm: &mut Write) -> io::Result<()> {
        strm.write_all(&*self.buf)
    }

    #[cfg(remove_me)]
    fn PageSize(&self) -> usize {
        self.buf.len()
    }

    fn Buffer(&self) -> &[u8] {
        &self.buf
    }
    
    #[cfg(remove_me)]
    fn Position(&self) -> usize {
        self.cur
    }

    fn Available(&self) -> usize {
        self.buf.len() - self.cur
    }

    fn SetPageFlag(&mut self, x: u8) {
        self.buf[1] = self.buf[1] | (x);
    }

    fn PutByte(&mut self, x: u8) {
        self.buf[self.cur] = x;
        self.cur = self.cur + 1;
    }

    fn PutStream2(&mut self, s: &mut Read, len: usize) -> io::Result<usize> {
        let n = try!(misc::io::read_fully(s, &mut self.buf[self.cur .. self.cur + len]));
        self.cur = self.cur + n;
        let res : io::Result<usize> = Ok(n);
        res
    }

    #[cfg(remove_me)]
    fn PutStream(&mut self, s: &mut Read, len: usize) -> io::Result<usize> {
        let n = try!(self.PutStream2(s, len));
        // TODO if n != len fail, which may mean a different result type here
        let res : io::Result<usize> = Ok(len);
        res
    }

    fn PutArray(&mut self, ba: &[u8]) {
        self.buf[self.cur .. self.cur + ba.len()].clone_from_slice(ba);
        self.cur = self.cur + ba.len();
    }

    fn PutArrayAt(&mut self, at: usize, ba: &[u8]) {
        self.buf[at .. at + ba.len()].clone_from_slice(ba);
    }

    fn PutInt32(&mut self, ov: u32) {
        let at = self.cur;
        // TODO just self.buf?  instead of making 4-byte slice.
        misc::bytes::copy_into(&endian::u32_to_bytes_be(ov), &mut self.buf[at .. at + SIZE_32]);
        self.cur = self.cur + SIZE_32;
    }

    fn SetLastInt32(&mut self, page: u32) {
        let len = self.buf.len();
        let at = len - 1 * SIZE_32;
        if self.cur > at { panic!("SetLastInt32 is squashing data"); }
        // TODO just self.buf?  instead of making 4-byte slice.
        misc::bytes::copy_into(&endian::u32_to_bytes_be(page), &mut self.buf[at .. at + SIZE_32]);
    }

    fn PutInt16(&mut self, ov: u16) {
        let at = self.cur;
        // TODO just self.buf?  instead of making 2-byte slice.
        misc::bytes::copy_into(&endian::u16_to_bytes_be(ov), &mut self.buf[at .. at + SIZE_16]);
        self.cur = self.cur + SIZE_16;
    }

    #[cfg(remove_me)]
    fn PutInt16At(&mut self, at: usize, ov: u16) {
        write_u16_be(&mut self.buf[at .. at + SIZE_16], ov);
    }

    fn PutVarint(&mut self, ov: u64) {
        varint::write(&mut *self.buf, &mut self.cur, ov);
    }

}

#[derive(PartialEq,Copy,Clone)]
enum Direction {
    FORWARD = 0,
    BACKWARD = 1,
    WANDERING = 2,
}

struct MultiCursor { 
    subcursors: Box<[SegmentCursor]>, 
    sorted: Box<[(usize, Option<Ordering>)]>,
    cur: Option<usize>, 
    dir: Direction,
}

impl MultiCursor {
    fn sort(&mut self, want_max: bool) -> Result<()> {
        if self.subcursors.is_empty() {
            return Ok(())
        }

        // TODO this memory allocation is expensive.

        // get a KeyRef for all the cursors
        let mut ka = Vec::with_capacity(self.subcursors.len());
        for c in self.subcursors.iter() {
            if c.IsValid() {
                ka.push(Some(try!(c.KeyRef())));
            } else {
                ka.push(None);
            }
        }

        // TODO consider converting ka to a boxed slice here?

        // init the orderings to None.
        // the invalid cursors will stay that way.
        for i in 0 .. self.sorted.len() {
            self.sorted[i].1 = None;
        }

        for i in 1 .. self.sorted.len() {
            let mut j = i;
            while j > 0 {
                let nj = self.sorted[j].0;
                let nprev = self.sorted[j - 1].0;
                match (&ka[nj], &ka[nprev]) {
                    (&Some(ref kj), &Some(ref kprev)) => {
                        let c = {
                            if want_max {
                                KeyRef::cmp(kprev, kj)
                            } else {
                                KeyRef::cmp(kj, kprev)
                            }
                        };
                        match c {
                            Ordering::Greater => {
                                self.sorted[j].1 = Some(Ordering::Greater);
                                break;
                            },
                            Ordering::Equal => {
                                match nj.cmp(&nprev) {
                                    Ordering::Equal => {
                                        unreachable!();
                                    },
                                    Ordering::Greater => {
                                        self.sorted[j].1 = Some(Ordering::Equal);
                                        break;
                                    },
                                    Ordering::Less => {
                                        self.sorted[j - 1].1 = Some(Ordering::Equal);
                                        // keep going
                                    },
                                }
                            },
                            Ordering::Less => {
                                // keep going
                                self.sorted[j - 1].1 = Some(Ordering::Greater);
                            },
                        }
                    },
                    (&Some(_), &None) => {
                        // keep going
                    },
                    (&None, &Some(_)) => {
                        break;
                    },
                    (&None, &None) => {
                        match nj.cmp(&nprev) {
                            Ordering::Equal => {
                                unreachable!();
                            },
                            Ordering::Greater => {
                                break;
                            },
                            Ordering::Less => {
                                // keep going
                            },
                        }
                    }
                };
                self.sorted.swap(j, j - 1);
                j = j - 1;
            }
        }

        // fix the first one
        if self.sorted.len() > 0 {
            let n = self.sorted[0].0;
            if ka[n].is_some() {
                self.sorted[0].1 = Some(Ordering::Equal);
            }
        }

        /*
        println!("{:?} : {}", self.sorted, if want_max { "backward" } else {"forward"} );
        for i in 0 .. self.sorted.len() {
            let (n, ord) = self.sorted[i];
            println!("    {:?}", ka[n]);
        }
        */
        Ok(())
    }

    fn sorted_first(&self) -> Option<usize> {
        let n = self.sorted[0].0;
        if self.sorted[0].1.is_some() {
            Some(n)
        } else {
            None
        }
    }

    fn findMin(&mut self) -> Result<Option<usize>> {
        self.dir = Direction::FORWARD;
        if self.subcursors.is_empty() {
            Ok(None)
        } else {
            try!(self.sort(false));
            Ok(self.sorted_first())
        }
    }

    fn findMax(&mut self) -> Result<Option<usize>> {
        self.dir = Direction::BACKWARD; 
        if self.subcursors.is_empty() {
            Ok(None)
        } else {
            try!(self.sort(true));
            Ok(self.sorted_first())
        }
    }

    fn Create(subs: Vec<SegmentCursor>) -> MultiCursor {
        let s = subs.into_boxed_slice();
        let mut sorted = Vec::with_capacity(s.len());
        for i in 0 .. s.len() {
            sorted.push((i, None));
        }
        MultiCursor { 
            subcursors: s, 
            sorted: sorted.into_boxed_slice(), 
            cur: None, 
            dir: Direction::WANDERING,
        }
    }

}

impl ICursor for MultiCursor {
    fn IsValid(&self) -> bool {
        match self.cur {
            Some(i) => self.subcursors[i].IsValid(),
            None => false
        }
    }

    fn First(&mut self) -> Result<()> {
        for i in 0 .. self.subcursors.len() {
            try!(self.subcursors[i].First());
        }
        self.cur = try!(self.findMin());
        Ok(())
    }

    fn Last(&mut self) -> Result<()> {
        for i in 0 .. self.subcursors.len() {
            try!(self.subcursors[i].Last());
        }
        self.cur = try!(self.findMax());
        Ok(())
    }

    fn KeyRef<'a>(&'a self) -> Result<KeyRef<'a>> {
        match self.cur {
            None => Err(Error::CursorNotValid),
            Some(icur) => self.subcursors[icur].KeyRef(),
        }
    }

    fn ValueRef<'a>(&'a self) -> Result<ValueRef<'a>> {
        match self.cur {
            None => Err(Error::CursorNotValid),
            Some(icur) => self.subcursors[icur].ValueRef(),
        }
    }

    fn ValueLength(&self) -> Result<Option<usize>> {
        match self.cur {
            None => Err(Error::CursorNotValid),
            Some(icur) => self.subcursors[icur].ValueLength(),
        }
    }

    fn Next(&mut self) -> Result<()> {
        match self.cur {
            None => Err(Error::CursorNotValid),
            Some(icur) => {
                // we need to fix every cursor to point to its min
                // value > icur.

                // if perf didn't matter, this would be simple.
                // call Next on icur.  and call Seek(GE) (and maybe Next)
                // on every other cursor.

                // but there are several cases where we can do a lot
                // less work than a Seek.  And we have the information
                // to identify those cases.  So, this function is
                // pretty complicated, but it's fast.

                // --------

                // the current cursor (icur) is easy.  it just needs Next().
                // we'll do it last, so we can use it for comparisons.
                // for now we deal with all the others.

                // the current direction of the multicursor tells us
                // something about the state of all the others.

                if self.dir == Direction::FORWARD {
                    // this is the happy case.  each cursor is at most
                    // one step away.

                    // direction is FORWARD, so we know that every valid cursor
                    // is pointing at a key which is either == to icur, or
                    // it is already the min key > icur.

                    assert!(icur == self.sorted[0].0);
                    // immediately after that, there may (or may not be) some
                    // entries which were Ordering:Equal to cur.  call Next on
                    // each of these.

                    for i in 1 .. self.sorted.len() {
                        //println!("sorted[{}] : {:?}", i, self.sorted[i]);
                        let (n, c) = self.sorted[i];
                        match c {
                            None => {
                                break;
                            },
                            Some(c) => {
                                if c == Ordering::Equal {
                                    try!(self.subcursors[n].Next());
                                } else {
                                    break;
                                }
                            },
                        }
                    }

                } else {
                    // TODO consider simplifying all the stuff below.
                    // all this complexity may not be worth it.

                    fn half(dir: Direction, ki: &KeyRef, subs: &mut [SegmentCursor]) -> Result<()> {
                        match dir {
                            Direction::FORWARD => {
                                unreachable!();
                            },
                            Direction::BACKWARD => {
                                // this case isn't too bad.  each cursor is either
                                // one step away or two.
                                
                                // every other cursor is either == icur or it is the
                                // max value < icur.

                                for csr in subs {
                                    if csr.IsValid() {
                                        let cmp = {
                                            let k = try!(csr.KeyRef());
                                            let cmp = KeyRef::cmp(&k, ki);
                                            cmp
                                        };
                                        match cmp {
                                            Ordering::Less => {
                                                try!(csr.Next());
                                                // we moved one step.  let's see if we need to move one more.
                                                if csr.IsValid() {
                                                    let cmp = {
                                                        let k = try!(csr.KeyRef());
                                                        let cmp = KeyRef::cmp(&k, ki);
                                                        cmp
                                                    };
                                                    match cmp {
                                                        Ordering::Less => {
                                                            // should never happen.  we should not have
                                                            // been more than one step away from icur.
                                                            unreachable!();
                                                        },
                                                        Ordering::Greater => {
                                                            // done
                                                        },
                                                        Ordering::Equal => {
                                                            // and one more step
                                                            try!(csr.Next());
                                                        },
                                                    }
                                                }
                                            },
                                            Ordering::Greater => {
                                                // should never happen, because BACKWARD
                                                unreachable!();
                                            },
                                            Ordering::Equal => {
                                                // one step away
                                                try!(csr.Next());
                                            },
                                        }
                                    } else {
                                        let sr = try!(csr.SeekRef(&ki, SeekOp::SEEK_GE));
                                        if sr.is_valid_and_equal() {
                                            try!(csr.Next());
                                        }
                                    }
                                }

                                Ok(())
                            },
                            Direction::WANDERING => {
                                // we have no idea where all the other cursors are.
                                // so we have to do a seek on each one.

                                for j in 0 .. subs.len() {
                                    let csr = &mut subs[j];
                                    let sr = try!(csr.SeekRef(&ki, SeekOp::SEEK_GE));
                                    if sr.is_valid_and_equal() {
                                        try!(csr.Next());
                                    }
                                }
                                Ok(())
                            },
                        }
                    }

                    {
                        let (before, middle, after) = split3(&mut *self.subcursors, icur);
                        let icsr = &middle[0];
                        let ki = try!(icsr.KeyRef());
                        try!(half(self.dir, &ki, before));
                        try!(half(self.dir, &ki, after));
                    }
                }

                // now the current cursor
                try!(self.subcursors[icur].Next());

                // now re-sort
                self.cur = try!(self.findMin());
                Ok(())
            },
        }
    }

    // TODO fix Prev like Next
    fn Prev(&mut self) -> Result<()> {
        match self.cur {
            None => Err(Error::CursorNotValid),
            Some(icur) => {
                let k = {
                    let k = try!(self.subcursors[icur].KeyRef());
                    let k = k.into_boxed_slice();
                    let k = KeyRef::from_boxed_slice(k);
                    k
                };
                for j in 0 .. self.subcursors.len() {
                    let csr = &mut self.subcursors[j];
                    if (self.dir != Direction::BACKWARD) && (icur != j) { 
                        try!(csr.SeekRef(&k, SeekOp::SEEK_LE));
                    }
                    if csr.IsValid() {
                        let eq = {
                            let kc = try!(csr.KeyRef());
                            Ordering::Equal == KeyRef::cmp(&kc, &k)
                        };
                        if eq {
                            try!(csr.Prev());
                        }
                    }
                }
                self.cur = try!(self.findMax());
                Ok(())
            },
        }
    }

    fn SeekRef(&mut self, k: &KeyRef, sop: SeekOp) -> Result<SeekResult> {
        self.cur = None;
        self.dir = Direction::WANDERING;
        for j in 0 .. self.subcursors.len() {
            let sr = try!(self.subcursors[j].SeekRef(k, sop));
            if sr.is_valid_and_equal() { 
                self.cur = Some(j);
                return Ok(sr);
            }
        }
        match sop {
            SeekOp::SEEK_GE => {
                self.cur = try!(self.findMin());
                match self.cur {
                    Some(i) => {
                        SeekResult::from_cursor(&self.subcursors[i], k)
                    },
                    None => {
                        Ok(SeekResult::Invalid)
                    },
                }
            },
            SeekOp::SEEK_LE => {
                self.cur = try!(self.findMax());
                match self.cur {
                    Some(i) => {
                        SeekResult::from_cursor(&self.subcursors[i], k)
                    },
                    None => {
                        Ok(SeekResult::Invalid)
                    },
                }
            },
            SeekOp::SEEK_EQ => {
                Ok(SeekResult::Invalid)
            },
        }
    }

}

pub struct LivingCursor { 
    chain: MultiCursor
}

impl LivingCursor {
    pub fn LiveValueRef<'a>(&'a self) -> Result<LiveValueRef<'a>> {
        match try!(self.chain.ValueRef()) {
            ValueRef::Array(a) => Ok(LiveValueRef::Array(a)),
            ValueRef::Overflowed(len, r) => Ok(LiveValueRef::Overflowed(len, r)),
            ValueRef::Tombstone => Err(Error::Misc(String::from("LiveValueRef tombstone TODO unreachable"))),
        }
    }

    fn skipTombstonesForward(&mut self) -> Result<()> {
        while self.chain.IsValid() && try!(self.chain.ValueLength()).is_none() {
            try!(self.chain.Next());
        }
        Ok(())
    }

    fn skipTombstonesBackward(&mut self) -> Result<()> {
        while self.chain.IsValid() && try!(self.chain.ValueLength()).is_none() {
            try!(self.chain.Prev());
        }
        Ok(())
    }

    fn Create(ch : MultiCursor) -> LivingCursor {
        LivingCursor { chain : ch }
    }
}

impl ICursor for LivingCursor {
    fn First(&mut self) -> Result<()> {
        try!(self.chain.First());
        try!(self.skipTombstonesForward());
        Ok(())
    }

    fn Last(&mut self) -> Result<()> {
        try!(self.chain.Last());
        try!(self.skipTombstonesBackward());
        Ok(())
    }

    fn KeyRef<'a>(&'a self) -> Result<KeyRef<'a>> {
        self.chain.KeyRef()
    }

    fn ValueRef<'a>(&'a self) -> Result<ValueRef<'a>> {
        self.chain.ValueRef()
    }

    fn ValueLength(&self) -> Result<Option<usize>> {
        self.chain.ValueLength()
    }

    fn IsValid(&self) -> bool {
        self.chain.IsValid() 
            && {
                let r = self.chain.ValueLength();
                if r.is_ok() {
                    r.unwrap().is_some()
                } else {
                    false
                }
            }
    }

    fn Next(&mut self) -> Result<()> {
        try!(self.chain.Next());
        try!(self.skipTombstonesForward());
        Ok(())
    }

    fn Prev(&mut self) -> Result<()> {
        try!(self.chain.Prev());
        try!(self.skipTombstonesBackward());
        Ok(())
    }

    fn SeekRef(&mut self, k: &KeyRef, sop:SeekOp) -> Result<SeekResult> {
        let sr = try!(self.chain.SeekRef(k, sop));
        match sop {
            SeekOp::SEEK_GE => {
                if sr.is_valid() && self.chain.ValueLength().unwrap().is_none() {
                    try!(self.skipTombstonesForward());
                    SeekResult::from_cursor(&self.chain, k)
                } else {
                    Ok(sr)
                }
            },
            SeekOp::SEEK_LE => {
                if sr.is_valid() && self.chain.ValueLength().unwrap().is_none() {
                    try!(self.skipTombstonesBackward());
                    SeekResult::from_cursor(&self.chain, k)
                } else {
                    Ok(sr)
                }
            },
            SeekOp::SEEK_EQ => Ok(sr),
        }
    }

}

pub struct FilterTombstonesCursor { 
    chain: MultiCursor,
    behind: Vec<(Option<std::sync::Arc<Bloom>>, SegmentCursor)>,
}

impl FilterTombstonesCursor {
    fn can_skip(&mut self) -> Result<bool> {
        if self.chain.IsValid() && try!(self.chain.ValueLength()).is_none() {
            let k = try!(self.chain.KeyRef());
            // TODO would it be faster to just keep behind moving Next() along with chain?
            // then we could optimize cases where we already know that the key is not present
            // in behind because, for example, we hit the max key in behind already.

            for pair in self.behind.iter_mut() {
                let bloom = &pair.0;
                match bloom {
                    &Some(ref bloom) => {
                        match bloom.check_keyref(&k) {
                            NoMaybe::No => {
                            },
                            NoMaybe::Maybe => {
                                return Ok(false);
                            },
                        }
                    },
                    &None => {
                        let cursor = &mut pair.1;
                        if SeekResult::Equal == try!(cursor.SeekRef(&k, SeekOp::SEEK_EQ)) {
                            // TODO if the value was found but it is another tombstone, then it is actually
                            // not found
                            return Ok(false);
                        }
                    },
                }
            }
            Ok(true)
        } else {
            Ok(false)
        }
    }

    fn skipTombstonesForward(&mut self) -> Result<()> {
        while try!(self.can_skip()) {
            try!(self.chain.Next());
        }
        Ok(())
    }

    fn skipTombstonesBackward(&mut self) -> Result<()> {
        while try!(self.can_skip()) {
            try!(self.chain.Prev());
        }
        Ok(())
    }

    fn new(ch: MultiCursor, behind: Vec<(Option<std::sync::Arc<Bloom>>, SegmentCursor)>) -> FilterTombstonesCursor {
        FilterTombstonesCursor { 
            chain: ch,
            behind: behind,
        }
    }
}

impl ICursor for FilterTombstonesCursor {
    fn First(&mut self) -> Result<()> {
        try!(self.chain.First());
        try!(self.skipTombstonesForward());
        Ok(())
    }

    fn Last(&mut self) -> Result<()> {
        try!(self.chain.Last());
        try!(self.skipTombstonesBackward());
        Ok(())
    }

    fn KeyRef<'a>(&'a self) -> Result<KeyRef<'a>> {
        self.chain.KeyRef()
    }

    fn ValueRef<'a>(&'a self) -> Result<ValueRef<'a>> {
        self.chain.ValueRef()
    }

    fn ValueLength(&self) -> Result<Option<usize>> {
        self.chain.ValueLength()
    }

    fn IsValid(&self) -> bool {
        self.chain.IsValid() 
    }

    fn Next(&mut self) -> Result<()> {
        try!(self.chain.Next());
        try!(self.skipTombstonesForward());
        Ok(())
    }

    fn Prev(&mut self) -> Result<()> {
        try!(self.chain.Prev());
        try!(self.skipTombstonesBackward());
        Ok(())
    }

    fn SeekRef(&mut self, k: &KeyRef, sop:SeekOp) -> Result<SeekResult> {
        let sr = try!(self.chain.SeekRef(k, sop));
        match sop {
            SeekOp::SEEK_GE => {
                if sr.is_valid() && self.chain.ValueLength().unwrap().is_none() {
                    try!(self.skipTombstonesForward());
                    SeekResult::from_cursor(&self.chain, k)
                } else {
                    Ok(sr)
                }
            },
            SeekOp::SEEK_LE => {
                if sr.is_valid() && self.chain.ValueLength().unwrap().is_none() {
                    try!(self.skipTombstonesBackward());
                    SeekResult::from_cursor(&self.chain, k)
                } else {
                    Ok(sr)
                }
            },
            SeekOp::SEEK_EQ => Ok(sr),
        }
    }

}

#[derive(PartialEq,Copy,Clone,Debug)]
pub enum OpLt {
    LT,
    LTE,
}

#[derive(PartialEq,Copy,Clone,Debug)]
pub enum OpGt {
    GT,
    GTE,
}

#[derive(Debug)]
pub struct Min {
    k: Box<[u8]>,
    cmp: OpGt,
}

impl Min {
    pub fn new(k: Box<[u8]>, cmp: OpGt) -> Self {
        Min {
            k: k,
            cmp: cmp,
        }
    }

    fn is_in_bounds(&self, k: &KeyRef) -> bool {
        let c = k.compare_with(&self.k);
        match (self.cmp, c) {
            (OpGt::GT, Ordering::Greater) => true,
            (OpGt::GT, Ordering::Less) => false,
            (OpGt::GT, Ordering::Equal) => false,
            (OpGt::GTE, Ordering::Greater) => true,
            (OpGt::GTE, Ordering::Less) => false,
            (OpGt::GTE, Ordering::Equal) => true,
        }
    }
}

#[derive(Debug)]
pub struct Max {
    k: Box<[u8]>,
    cmp: OpLt,
}

impl Max {
    pub fn new(k: Box<[u8]>, cmp: OpLt) -> Self {
        Max {
            k: k,
            cmp: cmp,
        }
    }

    fn is_in_bounds(&self, k: &KeyRef) -> bool {
        let c = k.compare_with(&self.k);
        match (self.cmp, c) {
            (OpLt::LT, Ordering::Greater) => false,
            (OpLt::LT, Ordering::Less) => true,
            (OpLt::LT, Ordering::Equal) => false,
            (OpLt::LTE, Ordering::Greater) => false,
            (OpLt::LTE, Ordering::Less) => true,
            (OpLt::LTE, Ordering::Equal) => true,
        }
    }
}

pub struct RangeCursor { 
    chain: LivingCursor,
    min: Min,
    max: Max,
}

impl RangeCursor {
    pub fn new(ch: LivingCursor, min: Min, max: Max) -> RangeCursor {
        //println!("RangeCursor min: {:?}", min);
        //println!("RangeCursor max: {:?}", max);
        RangeCursor { 
            chain : ch,
            min: min,
            max: max,
        }
    }

    pub fn KeyRef<'a>(&'a self) -> Result<KeyRef<'a>> {
        if self.IsValid() {
            self.chain.KeyRef()
        } else {
            Err(Error::CursorNotValid)
        }
    }

    pub fn LiveValueRef<'a>(&'a self) -> Result<LiveValueRef<'a>> {
        if self.IsValid() {
            self.chain.LiveValueRef()
        } else {
            Err(Error::CursorNotValid)
        }
    }

    pub fn IsValid(&self) -> bool {
        self.chain.IsValid() 
            && {
                let k = self.chain.KeyRef().unwrap();
                //println!("bounds checking: {:?}", k);
                self.min.is_in_bounds(&k) && self.max.is_in_bounds(&k)
            }
    }

    pub fn First(&mut self) -> Result<()> {
        let sr = try!(self.chain.SeekRef(&KeyRef::for_slice(&self.min.k), SeekOp::SEEK_GE));
        match (sr, self.min.cmp) {
            (SeekResult::Equal, OpGt::GT) => {
                try!(self.chain.Next());
            },
            _ => {
            },
        }
        Ok(())
    }

    pub fn Next(&mut self) -> Result<()> {
        if self.IsValid() {
            self.chain.Next()
        } else {
            Err(Error::CursorNotValid)
        }
    }

    // TODO this one could support Last/Prev I suppose
}

pub struct PrefixCursor<'c> { 
    chain : &'c mut LivingCursor,
    prefix: Box<[u8]>,
}

impl<'c> PrefixCursor<'c> {
    pub fn new(ch: &'c mut LivingCursor, prefix: Box<[u8]>) -> PrefixCursor<'c> {
        PrefixCursor { 
            chain : ch,
            prefix: prefix,
        }
    }

    // TODO lifetimes below should be 'c ?
    pub fn KeyRef<'a>(&'a self) -> Result<KeyRef<'a>> {
        if self.IsValid() {
            self.chain.KeyRef()
        } else {
            Err(Error::CursorNotValid)
        }
    }

    // TODO lifetimes below should be 'c ?
    pub fn LiveValueRef<'a>(&'a self) -> Result<LiveValueRef<'a>> {
        if self.IsValid() {
            self.chain.LiveValueRef()
        } else {
            Err(Error::CursorNotValid)
        }
    }

    pub fn IsValid(&self) -> bool {
        self.chain.IsValid() 
            && 
            self.chain.KeyRef().unwrap().starts_with(&self.prefix)
    }

    pub fn First(&mut self) -> Result<SeekResult> {
        self.chain.SeekRef(&KeyRef::for_slice(&self.prefix), SeekOp::SEEK_GE)
    }

    pub fn Next(&mut self) -> Result<()> {
        if self.IsValid() {
            self.chain.Next()
        } else {
            Err(Error::CursorNotValid)
        }
    }

}

#[derive(Hash,PartialEq,Eq,Copy,Clone,Debug)]
#[repr(u8)]
enum PageType {
    LEAF_NODE,
    PARENT_NODE,
    OVERFLOW_NODE,
}

impl PageType {

    #[inline(always)]
    fn to_u8(self) -> u8 {
        match self {
            PageType::LEAF_NODE => 1,
            PageType::PARENT_NODE => 2,
            PageType::OVERFLOW_NODE => 3,
        }
    }

    #[inline(always)]
    fn from_u8(v: u8) -> Result<PageType> {
        match v {
            1 => Ok(PageType::LEAF_NODE),
            2 => Ok(PageType::PARENT_NODE),
            3 => Ok(PageType::OVERFLOW_NODE),
            _ => Err(Error::InvalidPageType(v)),
        }
    }
}

mod ValueFlag {
    pub const FLAG_OVERFLOW: u8 = 1;
    pub const FLAG_TOMBSTONE: u8 = 2;
}

mod PageFlag {
    pub const FLAG_ROOT_NODE: u8 = 1;
    pub const FLAG_BOUNDARY_NODE: u8 = 2;
    pub const FLAG_ENDS_ON_BOUNDARY: u8 = 4;
}

#[derive(Debug)]
// this struct is used to remember pages we have written.
// for each page, we need to remember a key, and it needs
// to be in a box because the original copy is gone and
// the page has been written out to disk.
struct pgitem {
    page: PageNum,
    key: Box<[u8]>,
}

struct ParentState {
    sofar: usize,
    nextGeneration: Vec<pgitem>,
    blk: PageBlock,
    footer_len: usize,
}

// this enum keeps track of what happened to a key as we
// processed it.  either we determined that it will fit
// inline or we wrote it as an overflow.
#[derive(Debug)]
enum KeyLocation {
    Inline,
    Overflowed(PageNum),
}

// this enum keeps track of what happened to a value as we
// processed it.  it might have already been overflowed.  if
// it's going to fit in the page, we still have the data
// buffer.
#[derive(Debug)]
enum ValueLocation {
    Tombstone,
    // when this is a Buffer, this gets ownership of kvp.Value
    Buffer(Box<[u8]>),
    Overflowed(usize, PageNum),
}

struct LeafPair {
    // key gets ownership of kvp.Key
    key: Box<[u8]>,
    kLoc: KeyLocation,
    vLoc: ValueLocation,
}

struct LeafState {
    sofarLeaf: usize,
    keys_in_this_leaf: Vec<LeafPair>,
    prevLeaf: PageNum,
    prefixLen: usize,
    firstLeaf: PageNum,
    leaves: Vec<pgitem>,
    blk: PageBlock,
}

fn CreateFromSortedSequenceOfKeyValuePairs<I, SeekWrite>(fs: &mut SeekWrite, 
                                                            pageManager: &IPages, 
                                                            source: I,
                                                            estimate_count_keys: usize,
                                                           ) -> Result<SegmentNum> where I: Iterator<Item=Result<kvp>>, SeekWrite: Seek+Write {

    fn writeOverflow<SeekWrite>(startingBlock: PageBlock, 
                                ba: &mut Read, 
                                pageManager: &IPages, 
                                token: &mut PendingSegment,
                                fs: &mut SeekWrite
                               ) -> Result<(usize, PageBlock)> where SeekWrite : Seek+Write {

        fn buildFirstPage(ba: &mut Read, pbFirstOverflow: &mut PageBuilder, pgsz: usize) -> Result<(usize, bool)> {
            pbFirstOverflow.Reset();
            pbFirstOverflow.PutByte(PageType::OVERFLOW_NODE.to_u8());
            pbFirstOverflow.PutByte(0u8); // starts 0, may be changed later
            let room = pgsz - (2 + SIZE_32);
            // something will be put in lastInt32 later
            let put = try!(pbFirstOverflow.PutStream2(ba, room));
            Ok((put, put < room))
        };

        fn buildRegularPage(ba: &mut Read, pbOverflow: &mut PageBuilder, pgsz: usize) -> Result<(usize, bool)> {
            pbOverflow.Reset();
            let room = pgsz;
            let put = try!(pbOverflow.PutStream2(ba, room));
            Ok((put, put < room))
        };

        fn buildBoundaryPage(ba: &mut Read, pbOverflow: &mut PageBuilder, pgsz: usize) -> Result<(usize, bool)> {
            pbOverflow.Reset();
            let room = pgsz - SIZE_32;
            // something will be put in lastInt32 before the page is written
            let put = try!(pbOverflow.PutStream2(ba, room));
            Ok((put, put < room))
        }

        fn writeRegularPages<SeekWrite>(max: PageNum, 
                                        sofar: usize, 
                                        pb: &mut PageBuilder, 
                                        fs: &mut SeekWrite, 
                                        ba: &mut Read, 
                                        pgsz: usize
                                       ) -> Result<(PageNum, usize, bool)> where SeekWrite : Seek+Write {
            let mut i = 0;
            let mut sofar = sofar;
            loop {
                if i < max {
                    let (put, finished) = try!(buildRegularPage(ba, pb, pgsz));
                    if put == 0 {
                        return Ok((i, sofar, true));
                    } else {
                        sofar = sofar + put;
                        try!(pb.Write(fs));
                        if finished {
                            return Ok((i + 1, sofar, true));
                        } else {
                            i = i + 1;
                        }
                    }
                } else {
                    return Ok((i, sofar, false));
                }
            }
        }

        // TODO misnamed
        fn writeOneBlock<SeekWrite>(param_sofar: usize, 
                                    param_firstBlk: PageBlock,
                                    fs: &mut SeekWrite, 
                                    ba: &mut Read, 
                                    pgsz: usize,
                                    pbOverflow: &mut PageBuilder,
                                    pbFirstOverflow: &mut PageBuilder,
                                    pageManager: &IPages,
                                    token: &mut PendingSegment
                                   ) -> Result<(usize, PageBlock)> where SeekWrite : Seek+Write {
            // each trip through this loop will write out one
            // block, starting with the overflow first page,
            // followed by zero-or-more "regular" overflow pages,
            // which have no header.  we'll stop at the block boundary,
            // either because we land there or because the whole overflow
            // won't fit and we have to continue into the next block.
            // the boundary page will be like a regular overflow page,
            // headerless, but it is four bytes smaller.
            let mut loop_sofar = param_sofar;
            let mut loop_firstBlk = param_firstBlk;
            {
                let curpage = (try!(fs.seek(SeekFrom::Current(0))) / (pgsz as u64) + 1) as PageNum;
                assert!(param_firstBlk.firstPage == curpage);
            }
            loop {
                let sofar = loop_sofar;
                let firstBlk = loop_firstBlk;
                {
                    let curpage = (try!(fs.seek(SeekFrom::Current(0))) / (pgsz as u64) + 1) as PageNum;
                    assert!(firstBlk.firstPage == curpage);
                }
                let (putFirst, finished) = try!(buildFirstPage(ba, pbFirstOverflow, pgsz));
                if putFirst == 0 { 
                    return Ok((sofar, firstBlk));
                } else {
                    // note that we haven't written the first page yet.  we may have to fix
                    // a couple of things before it gets written out.
                    let sofar = sofar + putFirst;
                    if firstBlk.firstPage == firstBlk.lastPage {
                        // the first page landed on a boundary.
                        // we can just set the flag and write it now.
                        pbFirstOverflow.SetPageFlag(PageFlag::FLAG_BOUNDARY_NODE);
                        let blk = try!(pageManager.GetBlock(&mut *token));
                        pbFirstOverflow.SetLastInt32(blk.firstPage);
                        try!(pbFirstOverflow.Write(fs));
                        try!(utils::SeekPage(fs, pgsz, blk.firstPage));
                        if !finished {
                            loop_sofar = sofar;
                            loop_firstBlk = blk;
                        } else {
                            return Ok((sofar, blk));
                        }
                    } else {
                        let firstRegularPageNumber = firstBlk.firstPage + 1;
                        if finished {
                            // the first page is also the last one
                            pbFirstOverflow.SetLastInt32(0); 
                            // offset to last used page in this block, which is this one
                            try!(pbFirstOverflow.Write(fs));
                            return Ok((sofar, PageBlock::new(firstRegularPageNumber, firstBlk.lastPage)));
                        } else {
                            // skip writing the first page for now

                            // we need to write more pages,
                            // until the end of the block,
                            // or the end of the stream, 
                            // whichever comes first

                            try!(utils::SeekPage(fs, pgsz, firstRegularPageNumber));

                            // availableBeforeBoundary is the number of pages until the boundary,
                            // NOT counting the boundary page, and the first page in the block
                            // has already been accounted for, so we're just talking about data pages.
                            let availableBeforeBoundary = 
                                if firstBlk.lastPage > 0 { 
                                    firstBlk.lastPage - firstRegularPageNumber
                                } else { 
                                    PageNum::max_value() 
                                };

                            let (numRegularPages, sofar, finished) = 
                                try!(writeRegularPages(availableBeforeBoundary, sofar, pbOverflow, fs, ba, pgsz));

                            if finished {
                                // go back and fix the first page
                                pbFirstOverflow.SetLastInt32(numRegularPages);
                                try!(utils::SeekPage(fs, pgsz, firstBlk.firstPage));
                                try!(pbFirstOverflow.Write(fs));
                                // now reset to the next page in the block
                                let blk = PageBlock::new(firstRegularPageNumber + numRegularPages, firstBlk.lastPage);
                                try!(utils::SeekPage(fs, pgsz, blk.firstPage));
                                return Ok((sofar, blk));
                            } else {
                                // we need to write out a regular page except with a
                                // boundary pointer in it.  and we need to set
                                // FLAG_ENDS_ON_BOUNDARY on the first
                                // overflow page in this block.

                                let (putBoundary, finished) = try!(buildBoundaryPage(ba, pbOverflow, pgsz));
                                if putBoundary == 0 {
                                    // oops.  actually, we didn't need to touch the boundary page after all.
                                    // go back and fix the first page
                                    pbFirstOverflow.SetLastInt32(numRegularPages);
                                    try!(utils::SeekPage(fs, pgsz, firstBlk.firstPage));
                                    try!(pbFirstOverflow.Write(fs));

                                    // now reset to the next page in the block
                                    let blk = PageBlock::new(firstRegularPageNumber + numRegularPages, firstBlk.lastPage);
                                    assert!(blk.firstPage == firstBlk.lastPage);
                                    try!(utils::SeekPage(fs, pgsz, firstBlk.lastPage));
                                    return Ok((sofar, blk));
                                } else {
                                    // write the boundary page
                                    let sofar = sofar + putBoundary;
                                    let blk = try!(pageManager.GetBlock(&mut *token));
                                    pbOverflow.SetLastInt32(blk.firstPage);
                                    try!(pbOverflow.Write(fs));

                                    // go back and fix the first page
                                    pbFirstOverflow.SetPageFlag(PageFlag::FLAG_ENDS_ON_BOUNDARY);
                                    pbFirstOverflow.SetLastInt32(numRegularPages + 1); // TODO is this right?
                                    try!(utils::SeekPage(fs, pgsz, firstBlk.firstPage));
                                    try!(pbFirstOverflow.Write(fs));

                                    // now reset to the first page in the next block
                                    try!(utils::SeekPage(fs, pgsz, blk.firstPage));
                                    if !finished {
                                        loop_sofar = sofar;
                                        loop_firstBlk = blk;
                                    } else {
                                        return Ok((sofar, blk));
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        let pgsz = pageManager.PageSize();
        let mut pbFirstOverflow = PageBuilder::new(pgsz);
        let mut pbOverflow = PageBuilder::new(pgsz);

        writeOneBlock(0, startingBlock, fs, ba, pgsz, &mut pbOverflow, &mut pbFirstOverflow, pageManager, token)
    }

    fn writeLeaves<I,SeekWrite>(leavesBlk: PageBlock,
                                pageManager: &IPages,
                                source: I,
                                estimate_count_keys: usize,
                                vbuf: &mut [u8],
                                fs: &mut SeekWrite, 
                                pb: &mut PageBuilder,
                                token: &mut PendingSegment,
                                ) -> Result<(PageBlock, Vec<pgitem>, PageNum, usize, usize, Bloom)> where I: Iterator<Item=Result<kvp>> , SeekWrite : Seek+Write {
        // 2 for the page type and flags
        // 4 for the prev page
        // 2 for the stored count
        // 4 for lastInt32 (which isn't in pb.Available)
        const LEAF_PAGE_OVERHEAD: usize = 2 + 4 + 2 + 4;

        fn buildLeaf(st: &mut LeafState, pb: &mut PageBuilder) -> Box<[u8]> {
            pb.Reset();
            pb.PutByte(PageType::LEAF_NODE.to_u8());
            pb.PutByte(0u8); // flags
            pb.PutInt32(st.prevLeaf); // prev page num.
            // TODO prefixLen is one byte.  should it be two?
            pb.PutByte(st.prefixLen as u8);
            if st.prefixLen > 0 {
                pb.PutArray(&st.keys_in_this_leaf[0].key[0 .. st.prefixLen]);
            }
            let count_keys_in_this_leaf = st.keys_in_this_leaf.len();
            // TODO should we support more than 64k keys in a leaf?
            // either way, overflow-check this cast.
            pb.PutInt16(count_keys_in_this_leaf as u16);

            fn f(pb: &mut PageBuilder, prefixLen: usize, lp: &LeafPair) {
                match lp.kLoc {
                    KeyLocation::Inline => {
                        pb.PutByte(0u8); // flags
                        pb.PutVarint(lp.key.len() as u64);
                        pb.PutArray(&lp.key[prefixLen .. lp.key.len()]);
                    },
                    KeyLocation::Overflowed(kpage) => {
                        pb.PutByte(ValueFlag::FLAG_OVERFLOW);
                        pb.PutVarint(lp.key.len() as u64);
                        pb.PutInt32(kpage);
                    },
                }
                match lp.vLoc {
                    ValueLocation::Tombstone => {
                        pb.PutByte(ValueFlag::FLAG_TOMBSTONE);
                    },
                    ValueLocation::Buffer(ref vbuf) => {
                        pb.PutByte(0u8);
                        pb.PutVarint(vbuf.len() as u64);
                        pb.PutArray(&vbuf);
                    },
                    ValueLocation::Overflowed(vlen, vpage) => {
                        pb.PutByte(ValueFlag::FLAG_OVERFLOW);
                        pb.PutVarint(vlen as u64);
                        pb.PutInt32(vpage);
                    },
                }
            }

            // deal with all the keys except the last one
            for lp in st.keys_in_this_leaf.drain(0 .. count_keys_in_this_leaf-1) {
                f(pb, st.prefixLen, &lp);
            }
            assert!(st.keys_in_this_leaf.len() == 1);

            let lp = st.keys_in_this_leaf.remove(0); 
            assert!(st.keys_in_this_leaf.is_empty());

            f(pb, st.prefixLen, &lp);
            lp.key
        }

        fn writeLeaf<SeekWrite>(st: &mut LeafState, 
                                isRootPage: bool, 
                                pb: &mut PageBuilder, 
                                fs: &mut SeekWrite, 
                                pgsz: usize,
                                pageManager: &IPages,
                                token: &mut PendingSegment,
                               ) -> Result<()> where SeekWrite : Seek+Write { 
            let last_key = buildLeaf(st, pb);
            assert!(st.keys_in_this_leaf.is_empty());
            let thisPageNumber = st.blk.firstPage;
            let firstLeaf = if st.leaves.is_empty() { thisPageNumber } else { st.firstLeaf };
            let nextBlk = 
                if thisPageNumber == st.blk.lastPage {
                    if isRootPage {
                        // TODO we do not need another block
                        let newBlk = try!(pageManager.GetBlock(&mut *token));
                        newBlk
                    } else {
                        pb.SetPageFlag(PageFlag::FLAG_BOUNDARY_NODE);
                        let newBlk = try!(pageManager.GetBlock(&mut *token));
                        pb.SetLastInt32(newBlk.firstPage);
                        newBlk
                    }
                } else {
                    PageBlock::new(thisPageNumber + 1, st.blk.lastPage)
                };
            try!(pb.Write(fs));
            if nextBlk.firstPage != (thisPageNumber + 1) && !isRootPage {
                try!(utils::SeekPage(fs, pgsz, nextBlk.firstPage));
            }
            let pg = pgitem {page:thisPageNumber, key:last_key};
            st.leaves.push(pg);
            st.sofarLeaf = 0;
            st.prevLeaf = thisPageNumber;
            st.prefixLen = 0;
            st.firstLeaf = firstLeaf;
            st.blk = nextBlk;
            Ok(())
        }

        // TODO can the overflow page number become a varint?
        const NEEDED_FOR_OVERFLOW_PAGE_NUMBER: usize = 4;

        // the max limit of an inline key is when that key is the only
        // one in the leaf, and its value is overflowed.

        let pgsz = pageManager.PageSize();
        let maxKeyInline = 
            pgsz 
            - LEAF_PAGE_OVERHEAD 
            - 1 // prefixLen
            - 1 // key flags
            - varint::space_needed_for(pgsz as u64) // approx worst case inline key len
            - 1 // value flags
            - 9 // worst case varint value len
            - NEEDED_FOR_OVERFLOW_PAGE_NUMBER; // overflowed value page

        fn kLocNeed(k: &[u8], kloc: &KeyLocation, prefixLen: usize) -> usize {
            let klen = k.len();
            match *kloc {
                KeyLocation::Inline => {
                    1 + varint::space_needed_for(klen as u64) + klen - prefixLen
                },
                KeyLocation::Overflowed(_) => {
                    1 + varint::space_needed_for(klen as u64) + NEEDED_FOR_OVERFLOW_PAGE_NUMBER
                },
            }
        }

        fn vLocNeed (vloc: &ValueLocation) -> usize {
            match *vloc {
                ValueLocation::Tombstone => {
                    1
                },
                ValueLocation::Buffer(ref vbuf) => {
                    let vlen = vbuf.len();
                    1 + varint::space_needed_for(vlen as u64) + vlen
                },
                ValueLocation::Overflowed(vlen,_) => {
                    1 + varint::space_needed_for(vlen as u64) + NEEDED_FOR_OVERFLOW_PAGE_NUMBER
                },
            }
        }

        fn leafPairSize(prefixLen: usize, lp: &LeafPair) -> usize {
            kLocNeed(&lp.key, &lp.kLoc, prefixLen)
            +
            vLocNeed(&lp.vLoc)
        }

        fn defaultPrefixLen(k: &[u8]) -> usize {
            // TODO max prefix.  relative to page size?  currently must fit in one byte.
            if k.len() > 255 { 255 } else { k.len() }
        }

        let mut st = LeafState {
            sofarLeaf: 0,
            firstLeaf: 0,
            prevLeaf: 0,
            keys_in_this_leaf:Vec::new(),
            prefixLen: 0,
            leaves:Vec::new(),
            blk:leavesBlk,
            };

        //let mut prev_key: Option<Box<[u8]>> = None;
        let mut count_keys = 0;
        let mut count_tombstones = 0;

        // TODO if we are going to use a whole page to write the filter,
        // we might as well use most of that page FOR the filter.

        // TODO any chance we should decide that all filters are the same size?

        let blm_size_bytes = std::cmp::max(estimate_count_keys * 10 / 8, 128);;

        let blm_count_funcs = 4; // TODO calculate optimal number
        let mut blm = Bloom::new(vec![0; blm_size_bytes], blm_count_funcs);

        for result_pair in source {
            count_keys += 1;

            let mut pair = try!(result_pair);
            let k = pair.Key;
            blm.set(&k, &[]);
            if pair.Value.is_tombstone() {
                count_tombstones += 1;
            }
            /*
               // this code can be used to verify that we are being given kvps in order
            match prev_key {
                None => {
                },
                Some(prev_key) => {
                    let c = k.cmp(&prev_key);
                    if c != Ordering::Greater {
                        println!("prev_key: {:?}", prev_key);
                        println!("k: {:?}", k);
                        panic!("unsorted keys");
                    }
                },
            }
            prev_key = Some(k.clone());
            */

            // TODO is it possible for this to conclude that the key must be overflowed
            // when it would actually fit because of prefixing?

            let (blkAfterKey,kloc) = 
                if k.len() <= maxKeyInline {
                    (st.blk, KeyLocation::Inline)
                } else {
                    let vPage = st.blk.firstPage;
                    let (_,newBlk) = try!(writeOverflow(st.blk, &mut &*k, pageManager, token, fs));
                    (newBlk, KeyLocation::Overflowed(vPage))
                };

            // the max limit of an inline value is when the key is inline
            // on a new page.

            // TODO this is a usize, so it might cause integer underflow.
            let availableOnNewPageAfterKey = 
                pgsz 
                - LEAF_PAGE_OVERHEAD 
                - 1 // prefixLen
                - 1 // key flags
                - varint::space_needed_for(k.len() as u64)
                - k.len() 
                - 1 // value flags
                ;

            // availableOnNewPageAfterKey needs to accomodate the value and its length as a varint.
            // it might already be <=0 because of the key length

            let maxValueInline = 
                if availableOnNewPageAfterKey > 0 {
                    let neededForVarintLen = varint::space_needed_for(availableOnNewPageAfterKey as u64);
                    let avail2 = availableOnNewPageAfterKey - neededForVarintLen;
                    if avail2 > 0 { avail2 } else { 0 }
                } else {
                    0
                };

            let (blkAfterValue, vloc) = 
                match pair.Value {
                    Blob::Tombstone => {
                        (blkAfterKey, ValueLocation::Tombstone)
                    },
                    _ => match kloc {
                         KeyLocation::Inline => {
                            if maxValueInline == 0 {
                                match pair.Value {
                                    Blob::Tombstone => {
                                        (blkAfterKey, ValueLocation::Tombstone)
                                    },
                                    Blob::Stream(ref mut strm) => {
                                        let valuePage = blkAfterKey.firstPage;
                                        let (len,newBlk) = try!(writeOverflow(blkAfterKey, &mut *strm, pageManager, token, fs));
                                        (newBlk, ValueLocation::Overflowed(len, valuePage))
                                    },
                                    Blob::Array(a) => {
                                        if a.is_empty() {
                                            // TODO maybe we need ValueLocation::Empty
                                            (blkAfterKey, ValueLocation::Buffer(a))
                                        } else {
                                            let valuePage = blkAfterKey.firstPage;
                                            let strm = a; // TODO need a Read for this
                                            let (len,newBlk) = try!(writeOverflow(blkAfterKey, &mut &*strm, pageManager, token, fs));
                                            (newBlk, ValueLocation::Overflowed(len, valuePage))
                                        }
                                    },
                                }
                            } else {
                                match pair.Value {
                                    Blob::Tombstone => {
                                        (blkAfterKey, ValueLocation::Tombstone)
                                    },
                                    Blob::Stream(ref mut strm) => {
                                        // not sure reusing vbuf is worth it.  maybe we should just
                                        // alloc here.  ownership will get passed into the
                                        // ValueLocation when it fits.
                                        let vread = try!(misc::io::read_fully(&mut *strm, &mut vbuf[0 .. maxValueInline+1]));
                                        let vbuf = &vbuf[0 .. vread];
                                        if vread < maxValueInline {
                                            // TODO this alloc+copy is unfortunate
                                            let mut va = Vec::with_capacity(vbuf.len());
                                            for i in 0 .. vbuf.len() {
                                                va.push(vbuf[i]);
                                            }
                                            (blkAfterKey, ValueLocation::Buffer(va.into_boxed_slice()))
                                        } else {
                                            let valuePage = blkAfterKey.firstPage;
                                            let (len,newBlk) = try!(writeOverflow(blkAfterKey, &mut (vbuf.chain(strm)), pageManager, token, fs));
                                            (newBlk, ValueLocation::Overflowed (len, valuePage))
                                        }
                                    },
                                    Blob::Array(a) => {
                                        if a.len() < maxValueInline {
                                            (blkAfterKey, ValueLocation::Buffer(a))
                                        } else {
                                            let valuePage = blkAfterKey.firstPage;
                                            let (len,newBlk) = try!(writeOverflow(blkAfterKey, &mut &*a, pageManager, token, fs));
                                            (newBlk, ValueLocation::Overflowed(len, valuePage))
                                        }
                                    },
                                }
                            }
                         },

                         KeyLocation::Overflowed(_) => {
                            match pair.Value {
                                Blob::Tombstone => {
                                    (blkAfterKey, ValueLocation::Tombstone)
                                },
                                Blob::Stream(ref mut strm) => {
                                    let valuePage = blkAfterKey.firstPage;
                                    let (len,newBlk) = try!(writeOverflow(blkAfterKey, &mut *strm, pageManager, token, fs));
                                    (newBlk, ValueLocation::Overflowed(len, valuePage))
                                },
                                Blob::Array(a) => {
                                    if a.is_empty() {
                                        // TODO maybe we need ValueLocation::Empty
                                        (blkAfterKey, ValueLocation::Buffer(a))
                                    } else {
                                        let valuePage = blkAfterKey.firstPage;
                                        let (len,newBlk) = try!(writeOverflow(blkAfterKey, &mut &*a, pageManager, token, fs));
                                        (newBlk, ValueLocation::Overflowed(len, valuePage))
                                    }
                                }
                            }
                         }
                    }
            };

            // whether/not the key/value are to be overflowed is now already decided.
            // now all we have to do is decide if this key/value are going into this leaf
            // or not.  note that it is possible to overflow these and then have them not
            // fit into the current leaf and end up landing in the next leaf.

            st.blk = blkAfterValue;

            // TODO ignore prefixLen for overflowed keys?
            let newPrefixLen = 
                if st.keys_in_this_leaf.is_empty() {
                    defaultPrefixLen(&k)
                } else {
                    bcmp::PrefixMatch(&*st.keys_in_this_leaf[0].key, &k, st.prefixLen)
                };
            let sofar = 
                if newPrefixLen < st.prefixLen {
                    // the prefixLen would change with the addition of this key,
                    // so we need to recalc sofar
                    let sum = st.keys_in_this_leaf.iter().map(|lp| leafPairSize(newPrefixLen, lp)).sum();;
                    sum
                } else {
                    st.sofarLeaf
                };
            let fit = {
                let needed = kLocNeed(&k, &kloc, newPrefixLen) + vLocNeed(&vloc);
                let used = sofar + LEAF_PAGE_OVERHEAD + 1 + newPrefixLen;
                if pgsz > used {
                    let available = pgsz - used;
                    (available >= needed)
                } else {
                    false
                }
            };
            let writeThisPage = (!st.keys_in_this_leaf.is_empty()) && (!fit);

            if writeThisPage {
                try!(writeLeaf(&mut st, false, pb, fs, pgsz, pageManager, &mut *token));
            }

            // TODO ignore prefixLen for overflowed keys?
            let newPrefixLen = 
                if st.keys_in_this_leaf.is_empty() {
                    defaultPrefixLen(&k)
                } else {
                    bcmp::PrefixMatch(&*st.keys_in_this_leaf[0].key, &k, st.prefixLen)
                };
            let sofar = 
                if newPrefixLen < st.prefixLen {
                    // the prefixLen will change with the addition of this key,
                    // so we need to recalc sofar
                    let sum = st.keys_in_this_leaf.iter().map(|lp| leafPairSize(newPrefixLen, lp)).sum();;
                    sum
                } else {
                    st.sofarLeaf
                };
            // note that the LeafPair struct gets ownership of the key provided
            // from above.
            let lp = LeafPair {
                        key:k,
                        kLoc:kloc,
                        vLoc:vloc,
                        };

            st.sofarLeaf=sofar + leafPairSize(newPrefixLen, &lp);
            st.keys_in_this_leaf.push(lp);
            st.prefixLen=newPrefixLen;
        }

        if !st.keys_in_this_leaf.is_empty() {
            let isRootNode = st.leaves.is_empty();
            try!(writeLeaf(&mut st, isRootNode, pb, fs, pgsz, pageManager, &mut *token));
        }
        Ok((st.blk, st.leaves, st.firstLeaf, count_keys, count_tombstones, blm))
    }

    fn writeParentNodes<SeekWrite>(startingBlk: PageBlock, 
                                   children: &mut Vec<pgitem>,
                                   pgsz: usize,
                                   fs: &mut SeekWrite,
                                   pageManager: &IPages,
                                   token: &mut PendingSegment,
                                   footer: &Vec<u8>,
                                   pb: &mut PageBuilder,
                                  ) -> Result<(PageBlock, Vec<pgitem>)> where SeekWrite : Seek+Write {
        // 2 for the page type and flags
        // 2 for the stored count
        // 5 for the extra ptr we will add at the end, a varint, 5 is worst case (page num < 4294967295L)
        const PARENT_PAGE_OVERHEAD: usize = 2 + 2 + 5;

        fn calcAvailable(st: &ParentState, pgsz: usize) -> usize {
            let basicSize = pgsz - st.sofar;
            if st.nextGeneration.is_empty() {
                // TODO can this cause integer overflow?
                basicSize - st.footer_len
            } else if st.blk.firstPage == st.blk.lastPage {
                // TODO can this cause integer overflow?
                basicSize - SIZE_32
            } else {
                basicSize
            }
        }

        fn buildParentPage(items: &mut Vec<pgitem>,
                           lastPtr: PageNum, 
                           overflows: &HashMap<usize,PageNum>,
                           pb : &mut PageBuilder,
                          ) {
            pb.Reset();
            pb.PutByte(PageType::PARENT_NODE.to_u8());
            pb.PutByte(0u8);
            pb.PutInt16(items.len() as u16);
            // store all the keys, n of them
            for (i,x) in items.iter().enumerate() {
                match overflows.get(&i) {
                    Some(pg) => {
                        pb.PutByte(ValueFlag::FLAG_OVERFLOW);
                        pb.PutVarint(x.key.len() as u64);
                        pb.PutInt32(*pg as PageNum);
                    },
                    None => {
                        pb.PutByte(0u8);
                        pb.PutVarint(x.key.len() as u64);
                        pb.PutArray(&x.key);
                    },
                }
            }
            // store all the ptrs, n+1 of them
            for x in items.drain(..) {
                pb.PutVarint(x.page as u64);
            }
            pb.PutVarint(lastPtr as u64);
        }

        fn writeParentPage<SeekWrite>(st: &mut ParentState, 
                                      items: &mut Vec<pgitem>,
                                      overflows: &HashMap<usize,PageNum>,
                                      pgnum: PageNum,
                                      key: Box<[u8]>,
                                      pb: &mut PageBuilder, 
                                      fs: &mut SeekWrite,
                                      pageManager: &IPages,
                                      pgsz: usize,
                                      token: &mut PendingSegment,
                                      root: Option<&Vec<u8>>,
                                     ) -> Result<()> where SeekWrite : Seek+Write {
            // assert st.sofar > 0
            let thisPageNumber = st.blk.firstPage;
            buildParentPage(items, pgnum, &overflows, pb);
            let nextBlk =
                match root {
                    Some(footer) => {
                        pb.SetPageFlag(PageFlag::FLAG_ROOT_NODE);
                        pb.PutArrayAt(pgsz - footer.len(), &footer);
                        if st.blk.firstPage == st.blk.lastPage {
                            // TODO we do not need another block
                            let newBlk = try!(pageManager.GetBlock(&mut *token));
                            newBlk
                        } else {
                            PageBlock::new(thisPageNumber + 1, st.blk.lastPage)
                        }
                    },
                    None => {
                        if st.blk.firstPage == st.blk.lastPage {
                            pb.SetPageFlag(PageFlag::FLAG_BOUNDARY_NODE);
                            let newBlk = try!(pageManager.GetBlock(&mut *token));
                            pb.SetLastInt32(newBlk.firstPage);
                            newBlk
                        } else {
                            PageBlock::new(thisPageNumber + 1,st.blk.lastPage)
                        }
                    },
                };
            try!(pb.Write(fs));
            if nextBlk.firstPage != (thisPageNumber+1) && root.is_none() {
                try!(utils::SeekPage(fs, pgsz, nextBlk.firstPage));
            }
            st.sofar = 0;
            st.blk = nextBlk;
            let pg = pgitem {page:thisPageNumber, key:key};
            st.nextGeneration.push(pg);
            Ok(())
        }

        let mut st = ParentState {
            nextGeneration: Vec::new(),
            sofar: 0,
            blk: startingBlk,
            footer_len: footer.len(),
        };
        let mut items = Vec::new();
        let mut overflows = HashMap::new();
        let count_children = children.len();
        // deal with all the children except the last one
        for pair in children.drain(0 .. count_children - 1) {
            let pgnum = pair.page;

            let neededEitherWay = 1 + varint::space_needed_for(pair.key.len() as u64) + varint::space_needed_for(pgnum as u64);
            let neededForInline = neededEitherWay + pair.key.len();
            let neededForOverflow = neededEitherWay + SIZE_32;

            let available = calcAvailable(&st, pgsz);
            let fitsInline = available >= neededForInline;
            // TODO the + 4 in the next line is to account for the case where the next
            // page might be a boundary page, thus it would need the 4 bytes in lastint32.
            let wouldFitInlineOnNextPage = (pgsz - PARENT_PAGE_OVERHEAD + 4) >= neededForInline;
            let fitsOverflow = available >= neededForOverflow;
            let writeThisPage = (! fitsInline) && (wouldFitInlineOnNextPage || (! fitsOverflow));

            if writeThisPage {
                // assert sofar > 0
                // we need to make a copy of this key because writeParentPage needs to own one,
                // but we still need to put this pair in the items (below).
                let mut copy_key = vec![0; pair.key.len()].into_boxed_slice(); 
                copy_key.clone_from_slice(&pair.key);
                try!(writeParentPage(&mut st, &mut items, &overflows, pair.page, copy_key, pb, fs, pageManager, pgsz, &mut *token, None));
                assert!(items.is_empty());
            }

            if st.sofar == 0 {
                st.sofar = PARENT_PAGE_OVERHEAD;
                assert!(items.is_empty());
            }

            if calcAvailable(&st, pgsz) >= neededForInline {
                st.sofar = st.sofar + neededForInline;
            } else {
                let keyOverflowFirstPage = st.blk.firstPage;
                let (_,newBlk) = try!(writeOverflow(st.blk, &mut &*pair.key, pageManager, token, fs));
                st.sofar = st.sofar + neededForOverflow;
                st.blk = newBlk;
                // items.len() is the index that this pair is about to get, just below
                overflows.insert(items.len(),keyOverflowFirstPage);
            }
            items.push(pair);
        }
        assert!(children.len() == 1);
        let pgitem {page: pgnum, key: key} = children.remove(0);
        assert!(children.is_empty());

        let root =
            if st.nextGeneration.is_empty() {
                Some(footer)
            } else {
                None
            };
        try!(writeParentPage(&mut st, &mut items, &overflows, pgnum, key, pb, fs, pageManager, pgsz, &mut *token, root));
        Ok((st.blk,st.nextGeneration))
    }

    let pgsz = pageManager.PageSize();
    let mut pb = PageBuilder::new(pgsz);
    let mut token = try!(pageManager.Begin());
    let blk = try!(pageManager.GetBlock(&mut token));
    try!(utils::SeekPage(fs, pgsz, blk.firstPage));

    // TODO this is a buffer just for the purpose of being reused
    // in cases where the blob is provided as a stream, and we need
    // read a bit of it to figure out if it might fit inline rather
    // than overflow.
    let mut vbuf = vec![0; pgsz].into_boxed_slice(); 

    let (blk, leaves, firstLeaf, count_keys, count_tombstones, filter) = try!(writeLeaves(blk, pageManager, source, estimate_count_keys, &mut vbuf, fs, &mut pb, &mut token));
    assert!(count_keys > 0);
    assert!(count_keys >= count_tombstones);
    assert!(leaves.len() > 0);

    let filter_count_funcs = filter.count_funcs();
    let filter_bytes = filter.into_bytes();
    //println!("bloom created: {:?}", filter_bytes);

    // all the leaves are written.
    // now write the parent pages.
    // maybe more than one level of them.
    // keep writing until we have written a level which has only one node,
    // which is the root node.

    // TODO deal with the case where there were no leaves?  what if
    // a merge with a filtering cursor ends up filtering everything?

    let lastLeaf = leaves[leaves.len() - 1].page;

    let (root_page, blk) =
        if leaves.len() > 1 {
            let (filter_page, filter_len, blk) =
                // TODO is it always worth writing the filter just because there were more
                // keys than could fit on a single leaf?
                // maybe we should write a bloom filter only when there is more than one
                // generation of parent nodes?
                if leaves.len() > 1 {
                    let filter_page = blk.firstPage;
                    let (_, blk) = try!(writeOverflow(blk, &mut &*filter_bytes, pageManager, &mut token, fs));
                    (filter_page, filter_bytes.len(), blk)
                } else {
                    (0, 0, blk)
                };

            let mut footer = vec![];
            misc::push_varint(&mut footer, firstLeaf as u64);
            misc::push_varint(&mut footer, lastLeaf as u64);
            misc::push_varint(&mut footer, count_keys as u64);
            misc::push_varint(&mut footer, count_tombstones as u64);
            misc::push_varint(&mut footer, filter_page as u64);
            misc::push_varint(&mut footer, filter_len as u64);
            misc::push_varint(&mut footer, filter_count_funcs as u64);
            let len = footer.len();
            assert!(len <= 255);
            footer.push(len as u8);

            let (root_page, blk) = {
                let mut blk = blk;
                let mut children = leaves;
                while children.len() > 1 {
                    let (newBlk, newChildren) = try!(writeParentNodes(blk, &mut children, pgsz, fs, pageManager, &mut token, &footer, &mut pb));
                    assert!(children.is_empty());
                    blk = newBlk;
                    children = newChildren;
                }
                (children[0].page, blk)
            };
            (root_page, blk)
        } else {
            (leaves[0].page, blk)
        };

    /*
    {
        let mut pr = PageBuffer::new(pgsz);
        try!(utils::SeekPage(fs, pgsz, rootPage));
        try!(pr.Read(fs));
        let pt = try!(pr.PageType());
        assert!(pt == PageType::LEAF_NODE || pt == PageType::PARENT_NODE);
    }
    */

    let g = try!(pageManager.End(token, blk.firstPage, root_page));
    Ok(g)
}

struct myOverflowReadStream {
    fs: File,
    len: usize, // same type as ValueLength(), max len of a single value
    firstPage: PageNum, // TODO will be needed later for Seek trait
    buf: Box<[u8]>,
    currentPage: PageNum,
    sofarOverall: usize,
    sofarThisPage: usize,
    firstPageInBlock: PageNum,
    offsetToLastPageInThisBlock: PageNum,
    countRegularDataPagesInBlock: PageNum,
    boundaryPageNumber: PageNum,
    bytesOnThisPage: usize,
    offsetOnThisPage: usize,
}
    
impl myOverflowReadStream {
    fn new(path: &str, pgsz: usize, firstPage: PageNum, len: usize) -> Result<myOverflowReadStream> {
        // TODO I wonder if maybe we should defer the opening of the file until
        // somebody actually tries to read from it?  so that constructing a
        // ValueRef object (which contains one of these) would be a lighter-weight
        // operation.
        let f = try!(OpenOptions::new()
                .read(true)
                .open(path));
        let mut res = 
            // TODO the vec new below is really slow.  use a pool?
            myOverflowReadStream {
                fs: f,
                len: len,
                firstPage: firstPage,
                buf: vec![0; pgsz].into_boxed_slice(),
                currentPage: firstPage,
                sofarOverall: 0,
                sofarThisPage: 0,
                firstPageInBlock: 0,
                offsetToLastPageInThisBlock: 0, // add to firstPageInBlock to get the last one
                countRegularDataPagesInBlock: 0,
                boundaryPageNumber: 0,
                bytesOnThisPage: 0,
                offsetOnThisPage: 0,
            };
        try!(res.ReadFirstPage());
        Ok(res)
    }

    // TODO consider supporting Seek trait

    fn ReadPage(&mut self) -> Result<()> {
        try!(utils::SeekPage(&mut self.fs, self.buf.len(), self.currentPage));
        try!(misc::io::read_fully(&mut self.fs, &mut *self.buf));
        // assert PageType is OVERFLOW
        self.sofarThisPage = 0;
        if self.currentPage == self.firstPageInBlock {
            self.bytesOnThisPage = self.buf.len() - (2 + SIZE_32);
            self.offsetOnThisPage = 2;
        } else if self.currentPage == self.boundaryPageNumber {
            self.bytesOnThisPage = self.buf.len() - SIZE_32;
            self.offsetOnThisPage = 0;
        } else {
            // assert currentPage > firstPageInBlock
            // assert currentPage < boundaryPageNumber OR boundaryPageNumber = 0
            self.bytesOnThisPage = self.buf.len();
            self.offsetOnThisPage = 0;
        }
        Ok(())
    }

    fn GetLastInt32(&self) -> u32 {
        let at = self.buf.len() - SIZE_32;
        // TODO just self.buf?  instead of making 4-byte slice.
        let a = misc::bytes::extract_4(&self.buf[at .. at+4]);
        endian::u32_from_bytes_be(a)
    }

    fn PageType(&self) -> Result<PageType> {
        PageType::from_u8(self.buf[0])
    }

    fn CheckPageFlag(&self, f: u8) -> bool {
        0 != (self.buf[1] & f)
    }

    fn ReadFirstPage(&mut self) -> Result<()> {
        self.firstPageInBlock = self.currentPage;
        try!(self.ReadPage());
        if try!(self.PageType()) != (PageType::OVERFLOW_NODE) {
            return Err(Error::CorruptFile("first overflow page has invalid page type"));
        }
        if self.CheckPageFlag(PageFlag::FLAG_BOUNDARY_NODE) {
            // first page landed on a boundary node
            // lastInt32 is the next page number, which we'll fetch later
            self.boundaryPageNumber = self.currentPage;
            self.offsetToLastPageInThisBlock = 0;
            self.countRegularDataPagesInBlock = 0;
            // TODO I think bytesOnThisPage might be wrong here
        } else {
            self.offsetToLastPageInThisBlock = self.GetLastInt32();
            if self.CheckPageFlag(PageFlag::FLAG_ENDS_ON_BOUNDARY) {
                self.boundaryPageNumber = self.currentPage + self.offsetToLastPageInThisBlock;
                self.countRegularDataPagesInBlock = self.offsetToLastPageInThisBlock - 1;
            } else {
                self.boundaryPageNumber = 0;
                self.countRegularDataPagesInBlock = self.offsetToLastPageInThisBlock;
            }
        }
        Ok(())
    }

    fn Read(&mut self, ba: &mut [u8], offset: usize, wanted: usize) -> Result<usize> {
        if self.sofarOverall >= self.len {
            Ok(0)
        } else {
            let mut direct = false;
            if self.sofarThisPage >= self.bytesOnThisPage {
                if self.currentPage == self.boundaryPageNumber {
                    self.currentPage = self.GetLastInt32();
                    try!(self.ReadFirstPage());
                } else {
                    // we need a new page.  and if it's a full data page,
                    // and if wanted is big enough to take all of it, then
                    // we want to read (at least) it directly into the
                    // buffer provided by the caller.  we already know
                    // this candidate page cannot be the first page in a
                    // block.
                    let maybeDataPage = self.currentPage + 1;
                    let isDataPage = 
                        if self.boundaryPageNumber > 0 {
                            ((self.len - self.sofarOverall) >= self.buf.len()) && (self.countRegularDataPagesInBlock > 0) && (maybeDataPage > self.firstPageInBlock) && (maybeDataPage < self.boundaryPageNumber)
                        } else {
                            ((self.len - self.sofarOverall) >= self.buf.len()) && (self.countRegularDataPagesInBlock > 0) && (maybeDataPage > self.firstPageInBlock) && (maybeDataPage <= (self.firstPageInBlock + self.countRegularDataPagesInBlock))
                        };

                    if isDataPage && (wanted >= self.buf.len()) {
                        // assert (currentPage + 1) > firstPageInBlock
                        //
                        // don't increment currentPage here because below, we will
                        // calculate how many pages we actually want to do.
                        direct = true;
                        self.bytesOnThisPage = self.buf.len();
                        self.sofarThisPage = 0;
                        self.offsetOnThisPage = 0;
                    } else {
                        self.currentPage = self.currentPage + 1;
                        try!(self.ReadPage());
                    }
                }
            }

            if direct {
                // currentPage has not been incremented yet
                //
                // skip the buffer.  note, therefore, that the contents of the
                // buffer are "invalid" in that they do not correspond to currentPage
                //
                let numPagesWanted = (wanted / self.buf.len()) as PageNum;
                // assert countRegularDataPagesInBlock > 0
                let lastDataPageInThisBlock = self.firstPageInBlock + self.countRegularDataPagesInBlock;
                let theDataPage = self.currentPage + 1;
                let numPagesAvailable = 
                    if self.boundaryPageNumber>0 { 
                        self.boundaryPageNumber - theDataPage 
                    } else {
                        lastDataPageInThisBlock - theDataPage + 1
                    };
                let numPagesToFetch = std::cmp::min(numPagesWanted, numPagesAvailable) as PageNum;
                let bytesToFetch = {
                    let bytesToFetch = (numPagesToFetch as usize) * self.buf.len();
                    let available = self.len - self.sofarOverall;
                    if bytesToFetch > available {
                        available
                    } else {
                        bytesToFetch
                    }
                };
                // assert bytesToFetch <= wanted

                try!(utils::SeekPage(&mut self.fs, self.buf.len(), theDataPage));
                try!(misc::io::read_fully(&mut self.fs, &mut ba[offset .. offset + bytesToFetch]));
                self.sofarOverall = self.sofarOverall + bytesToFetch;
                self.currentPage = self.currentPage + numPagesToFetch;
                self.sofarThisPage = self.buf.len();
                Ok(bytesToFetch)
            } else {
                let available = std::cmp::min(self.bytesOnThisPage - self.sofarThisPage, self.len - self.sofarOverall);
                let num = std::cmp::min(available, wanted);
                for i in 0 .. num {
                    ba[offset+i] = self.buf[self.offsetOnThisPage + self.sofarThisPage + i];
                }
                self.sofarOverall = self.sofarOverall + num;
                self.sofarThisPage = self.sofarThisPage + num;
                Ok(num)
            }
        }
    }
}

impl Read for myOverflowReadStream {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let len = buf.len();
        match self.Read(buf, 0, len) {
            Ok(v) => Ok(v),
            Err(e) => {
                // this interface requires io::Result, so we shoehorn the others into it
                match e {
                    Error::Io(e) => Err(e),
                    _ => {
                        use std::error::Error;
                        Err(std::io::Error::new(std::io::ErrorKind::Other, e.description()))
                    }
                }
            },
        }
    }
}

#[cfg(remove_me)]
fn readOverflow(path: &str, pgsz: usize, firstPage: PageNum, buf: &mut [u8]) -> Result<usize> {
    let mut ostrm = try!(myOverflowReadStream::new(path, pgsz, firstPage, buf.len()));
    let res = try!(misc::io::read_fully(&mut ostrm, buf));
    Ok(res)
}

pub struct SegmentCursor {
    path: String,
    fs: File,
    done: Option<Box<Fn() -> ()>>,
    blocks: Vec<PageBlock>,
    rootPage: PageNum,

    pr: misc::Lend<Box<[u8]>>,
    currentPage: PageNum,

    firstLeaf: PageNum,
    lastLeaf: PageNum,
    count_keys: usize,
    count_tombstones: usize,
    filter_page: PageNum,
    filter_len: usize,
    filter_count_funcs: usize,

    leafKeys: Vec<usize>,
    previousLeaf: PageNum,
    prefix: Option<Box<[u8]>>,

    currentKey: Option<usize>,
}

impl SegmentCursor {
    fn new(path: &str, 
           page: misc::Lend<Box<[u8]>>,
           rootPage: PageNum, 
           blocks: Vec<PageBlock>
          ) -> Result<SegmentCursor> {

        // TODO consider not passing in the path, and instead,
        // making the cursor call back to inner.OpenForReading...
        let f = try!(OpenOptions::new()
                .read(true)
                .open(path));

        let mut res = SegmentCursor {
            path: String::from(path),
            fs: f,
            blocks: blocks,
            done: None,
            rootPage: rootPage,
            pr: page,
            currentPage: 0,
            leafKeys: Vec::new(),
            previousLeaf: 0,
            currentKey: None,
            prefix: None,
            firstLeaf: 0, // temporary
            lastLeaf: 0, // temporary
            count_keys: 0, // temporary
            count_tombstones: 0, // temporary
            filter_page: 0, // temporary
            filter_len: 0, // temporary
            filter_count_funcs: 0, // temporary
        };

        // TODO consider keeping the root page around as long as this cursor is around
        try!(res.setCurrentPage(rootPage));

        let pt = try!(res.page_type());
        if pt == PageType::LEAF_NODE {
            res.firstLeaf = rootPage;
            res.lastLeaf = rootPage;
            res.count_keys = res.leafKeys.len();
            let mut count_tombstones = 0;
            for i in 0 .. res.leafKeys.len() {
                let mut pos = res.leafKeys[i];
                res.skipKey(&mut pos);
                let vflag = res.get_byte(&mut pos);
                if 0 != (vflag & ValueFlag::FLAG_TOMBSTONE) {
                    count_tombstones += 1;
                }
            }
            res.count_tombstones = count_tombstones;
        } else if pt == PageType::PARENT_NODE {
            if !res.check_page_flag(PageFlag::FLAG_ROOT_NODE) { 
                return Err(Error::CorruptFile("root page lacks flag"));
            }
            let len_footer = res.pr[res.pr.len()-1] as usize;
            let footer = &res.pr[res.pr.len() - 1 - len_footer ..];
            let mut cur = 0;
            res.firstLeaf = varint::read(footer, &mut cur) as u32;
            assert!(block_list_contains_page(&res.blocks, res.firstLeaf));
            res.lastLeaf = varint::read(footer, &mut cur) as u32;
            assert!(block_list_contains_page(&res.blocks, res.lastLeaf));
            res.count_keys = varint::read(footer, &mut cur) as usize;
            res.count_tombstones = varint::read(footer, &mut cur) as usize;
            assert!(res.count_keys >= res.count_tombstones);
            res.filter_page = varint::read(footer, &mut cur) as PageNum;
            res.filter_len = varint::read(footer, &mut cur) as usize;
            res.filter_count_funcs = varint::read(footer, &mut cur) as usize;
        } else {
            return Err(Error::CorruptFile("root page has invalid page type"));
        }
          
        Ok(res)
    }

    fn set_hook(&mut self, done: Box<Fn() -> ()>) {
        // TODO instead of this thing have a done() hook, should we instead
        // be wrapping it in a Lend?
        self.done = Some(done);
    }

    pub fn count_keys(&self) -> usize {
        self.count_keys
    }

    pub fn count_tombstones(&self) -> usize {
        self.count_tombstones
    }

    pub fn filter_len(&self) -> usize {
        self.filter_len
    }

    fn load_bloom_filter(&self) -> Result<Option<Bloom>> {
        if self.filter_page == 0 {
            Ok(None)
        } else {
            //println!("loading bloom filter at page: {}", self.filter_page);
            let mut strm = try!(myOverflowReadStream::new(&self.path, self.pr.len(), self.filter_page, self.filter_len));
            let mut v = Vec::with_capacity(self.filter_len);
            try!(strm.read_to_end(&mut v));
            //println!("bloom loaded: {:?}", v);
            let blm = Bloom::new(v, self.filter_count_funcs);
            Ok(Some(blm))
        }
    }

    fn readLeaf(&mut self) -> Result<()> {
        let mut cur = 0;
        let pt = try!(PageType::from_u8(self.get_byte(&mut cur)));
        if pt != PageType::LEAF_NODE {
            return Err(Error::CorruptFile("leaf has invalid page type"));
        }
        self.get_byte(&mut cur);
        self.previousLeaf = self.get_u32(&mut cur) as PageNum;
        let prefixLen = self.get_byte(&mut cur) as usize;
        if prefixLen > 0 {
            // TODO should we just remember prefix as a reference instead of box/copy?
            let mut a = vec![0; prefixLen].into_boxed_slice();
            a.clone_from_slice(&self.pr[cur .. cur + prefixLen]);
            cur = cur + prefixLen;
            self.prefix = Some(a);
        } else {
            self.prefix = None;
        }
        let countLeafKeys = self.get_u16(&mut cur) as usize;
        // assert countLeafKeys>0
        // TODO might need to extend capacity here, not just truncate
        self.leafKeys.truncate(countLeafKeys);
        while self.leafKeys.len() < countLeafKeys {
            self.leafKeys.push(0);
        }
        for i in 0 .. countLeafKeys {
            self.leafKeys[i] = cur;
            self.skipKey(&mut cur);
            self.skipValue(&mut cur);
        }
        Ok(())
    }

    fn page_type(&self) -> Result<PageType> {
        PageType::from_u8(self.pr[0])
    }

    fn check_page_flag(&self, f: u8) -> bool {
        0 != (self.pr[1] & f)
    }

    // TODO use buf_advance
    fn get_byte(&self, cur: &mut usize) -> u8 {
        let r = self.pr[*cur];
        *cur = *cur + 1;
        r
    }

    // TODO use buf_advance
    fn get_u32(&self, cur: &mut usize) -> u32 {
        let at = *cur;
        // TODO just self.pr?  instead of making 4-byte slice.
        let a = misc::bytes::extract_4(&self.pr[at .. at + SIZE_32]);
        *cur = *cur + SIZE_32;
        endian::u32_from_bytes_be(a)
    }

    // TODO use buf_advance
    fn get_u16(&self, cur: &mut usize) -> u16 {
        let at = *cur;
        // TODO just self.pr?  instead of making 2-byte slice.
        let a = misc::bytes::extract_2(&self.pr[at .. at + SIZE_16]);
        let r = endian::u16_from_bytes_be(a);
        *cur = *cur + SIZE_16;
        r
    }

    fn get_u32_at(&self, at: usize) -> u32 {
        // TODO just self.pr?  instead of making 4-byte slice.
        let a = misc::bytes::extract_4(&self.pr[at .. at + SIZE_32]);
        endian::u32_from_bytes_be(a)
    }

    fn get_u32_last(&self) -> u32 {
        let len = self.pr.len();
        let at = len - 1 * SIZE_32;
        self.get_u32_at(at)
    }

    fn setCurrentPage(&mut self, pgnum: PageNum) -> Result<()> {
        assert!(block_list_contains_page(&self.blocks, pgnum));

        if self.currentPage != pgnum {
            self.currentPage = pgnum;

            self.leafKeys.clear();
            self.previousLeaf = 0;
            self.currentKey = None;
            self.prefix = None;

            try!(utils::SeekPage(&mut self.fs, self.pr.len(), self.currentPage));
            try!(misc::io::read_fully(&mut self.fs, &mut self.pr));

            match self.page_type() {
                Ok(PageType::LEAF_NODE) => {
                    try!(self.readLeaf());
                },
                _ => {
                },
            }
        }
        Ok(())
    }

    fn nextInLeaf(&mut self) -> bool {
        match self.currentKey {
            Some(cur) => {
                if (cur +1 ) < self.leafKeys.len() {
                    self.currentKey = Some(cur + 1);
                    true
                } else {
                    false
                }
            },
            None => {
                false
            },
        }
    }

    fn prevInLeaf(&mut self) -> bool {
        match self.currentKey {
            Some(cur) => {
                if cur > 0 {
                    self.currentKey = Some(cur - 1);
                    true
                } else {
                    false
                }
            },
            None => {
                false
            },
        }
    }

    fn skipKey(&self, cur: &mut usize) {
        let kflag = self.get_byte(cur);
        let klen = varint::read(&self.pr, cur) as usize;
        if 0 == (kflag & ValueFlag::FLAG_OVERFLOW) {
            let prefixLen = match self.prefix {
                Some(ref a) => a.len(),
                None => 0
            };
            *cur = *cur + (klen - prefixLen);
        } else {
            *cur = *cur + SIZE_32;
        }
    }

    fn skipValue(&self, cur: &mut usize) {
        let vflag = self.get_byte(cur);
        if 0 != (vflag & ValueFlag::FLAG_TOMBSTONE) { 
            ()
        } else {
            let vlen = varint::read(&self.pr, cur) as usize;
            if 0 != (vflag & ValueFlag::FLAG_OVERFLOW) {
                *cur = *cur + SIZE_32;
            } else {
                *cur = *cur + vlen;
            }
        }
    }

    fn keyInLeaf2<'a>(&'a self, n: usize) -> Result<KeyRef<'a>> { 
        let mut cur = self.leafKeys[n as usize];
        let kflag = self.get_byte(&mut cur);
        let klen = varint::read(&self.pr, &mut cur) as usize;
        if 0 == (kflag & ValueFlag::FLAG_OVERFLOW) {
            match self.prefix {
                Some(ref a) => {
                    Ok(KeyRef::Prefixed(&a, &self.pr[cur .. cur + klen - a.len()]))
                },
                None => {
                    Ok(KeyRef::Array(&self.pr[cur .. cur + klen]))
                },
            }
        } else {
            let pgnum = self.get_u32(&mut cur) as PageNum;
            let mut ostrm = try!(myOverflowReadStream::new(&self.path, self.pr.len(), pgnum, klen));
            let mut x_k = Vec::with_capacity(klen);
            try!(ostrm.read_to_end(&mut x_k));
            let x_k = x_k.into_boxed_slice();
            Ok(KeyRef::Overflowed(x_k))
        }
    }

    fn searchLeaf(&mut self, k: &KeyRef, min:usize, max:usize, sop:SeekOp, le: Option<usize>, ge: Option<usize>) -> Result<(Option<usize>,bool)> {
        if max < min {
            match sop {
                SeekOp::SEEK_EQ => Ok((None, false)),
                SeekOp::SEEK_LE => Ok((le, false)),
                SeekOp::SEEK_GE => Ok((ge, false)),
            }
        } else {
            let mid = (max + min) / 2;
            // assert mid >= 0
            let cmp = {
                let q = try!(self.keyInLeaf2(mid));
                KeyRef::cmp(&q, k)
            };
            match cmp {
                Ordering::Equal => Ok((Some(mid), true)),
                Ordering::Less => self.searchLeaf(k, (mid+1), max, sop, Some(mid), ge),
                Ordering::Greater => 
                    // we could just recurse with mid-1, but that would overflow if
                    // mod is 0, so we catch that case here.
                    if mid==0 { 
                        match sop {
                            SeekOp::SEEK_EQ => Ok((None, false)),
                            SeekOp::SEEK_LE => Ok((le, false)),
                            SeekOp::SEEK_GE => Ok((Some(mid), false)),
                        }
                    } else { 
                        self.searchLeaf(k, min, (mid-1), sop, le, Some(mid))
                    },
            }
        }
    }

    fn get_next_from_parent_page(&mut self, kq: &KeyRef) -> Result<PageNum> {
        let mut cur = 0;
        let pt = try!(PageType::from_u8(self.get_byte(&mut cur)));
        if  pt != PageType::PARENT_NODE {
            return Err(Error::CorruptFile("parent page has invalid page type"));
        }
        cur = cur + 1; // page flags
        let count = self.get_u16(&mut cur);
        let mut found = None;
        for i in 0 .. count {
            let kflag = self.get_byte(&mut cur);
            let klen = varint::read(&self.pr, &mut cur) as usize;
            let k =
                if 0 == (kflag & ValueFlag::FLAG_OVERFLOW) {
                    let k = KeyRef::Array(&self.pr[cur .. cur + klen]);
                    cur = cur + klen;
                    k
                } else {
                    let firstPage = self.get_u32(&mut cur) as PageNum;
                    // TODO move the following line outside the loop?
                    let pgsz = self.pr.len();
                    let mut ostrm = try!(myOverflowReadStream::new(&self.path, pgsz, firstPage, klen));
                    let mut x_k = Vec::with_capacity(klen);
                    try!(ostrm.read_to_end(&mut x_k));
                    let x_k = x_k.into_boxed_slice();
                    let k = KeyRef::Overflowed(x_k);
                    k
                };
            let cmp = KeyRef::cmp(kq, &k);
            if cmp != Ordering::Greater {
                found = Some(i);
                break;
            }
        }
        match found {
            None => {
            },
            Some(found) => {
                for _ in found+1 .. count {
                    let kflag = self.get_byte(&mut cur);
                    let klen = varint::read(&self.pr, &mut cur) as usize;
                    if 0 == (kflag & ValueFlag::FLAG_OVERFLOW) {
                        cur = cur + klen;
                    } else {
                        cur = cur + 4;
                    };
                }
            },
        }
        let found = found.unwrap_or(count);
        for _ in 0 .. found {
            let b = self.get_byte(&mut cur);
            let len = misc::varint::first_byte_to_len(b);
            cur = cur + len - 1;
        }
        let pg = varint::read(&self.pr, &mut cur) as PageNum;
        Ok(pg)
    }

    // this is used when moving forward through the leaf pages.
    // we need to skip any overflows.  when moving backward,
    // this is not necessary, because each leaf has a pointer to
    // the leaf before it.
    //
    // TODO it's unfortunate that Next is the slower operation
    // when it is far more common than Prev.  OTOH, the pages
    // are written as we stream through a set of kvp objects,
    // and we don't want to rewind, and we want to write each
    // page only once, and we want to keep the minimum amount
    // of stuff in memory as we go.  and this code only causes
    // a perf difference if there are overflow pages between
    // the leaves.
    fn searchForwardForLeaf(&mut self) -> Result<bool> {
        let pt = try!(self.page_type());
        if pt == PageType::LEAF_NODE { 
            Ok(true)
        } else if pt == PageType::PARENT_NODE { 
            // if we bump into a parent node, that means there are
            // no more leaves.
            Ok(false)
        } else {
            assert!(pt == PageType::OVERFLOW_NODE);

            let lastInt32 = self.get_u32_last() as PageNum;
            //
            // an overflow page has a value in its LastInt32 which
            // is one of two things.
            //
            // if it's a boundary node, it's the page number of the
            // next page in the segment.
            //
            // otherwise, it's the number of pages to skip ahead.
            // this skip might take us to whatever follows this
            // overflow (which could be a leaf or a parent or
            // another overflow), or it might just take us to a
            // boundary page (in the case where the overflow didn't
            // fit).  it doesn't matter.  we just skip ahead.
            //
            if self.check_page_flag(PageFlag::FLAG_BOUNDARY_NODE) {
                try!(self.setCurrentPage(lastInt32));
                self.searchForwardForLeaf()
            } else {
                let lastPage = self.currentPage + lastInt32;
                let endsOnBoundary = self.check_page_flag(PageFlag::FLAG_ENDS_ON_BOUNDARY);
                if endsOnBoundary {
                    try!(self.setCurrentPage(lastPage));
                    let next = self.get_u32_last() as PageNum;
                    try!(self.setCurrentPage(next));
                    self.searchForwardForLeaf()
                } else {
                    try!(self.setCurrentPage(lastPage + 1));
                    self.searchForwardForLeaf()
                }
            }
        }
    }

    fn leafIsValid(&self) -> bool {
        // TODO the bounds check of self.currentKey against self.leafKeys.len() could be an assert
        let ok = (!self.leafKeys.is_empty()) && (self.currentKey.is_some()) && (self.currentKey.expect("just did is_some") as usize) < self.leafKeys.len();
        ok
    }

    fn search(&mut self, pg: PageNum, k: &KeyRef, sop:SeekOp) -> Result<SeekResult> {
        try!(self.setCurrentPage(pg));
        let pt = try!(self.page_type());
        if PageType::LEAF_NODE == pt {
            let tmp_countLeafKeys = self.leafKeys.len();
            let (newCur, equal) = try!(self.searchLeaf(k, 0, (tmp_countLeafKeys - 1), sop, None, None));
            self.currentKey = newCur;
            if SeekOp::SEEK_EQ != sop {
                if ! self.leafIsValid() {
                    // if LE or GE failed on a given page, we might need
                    // to look at the next/prev leaf.
                    if SeekOp::SEEK_GE == sop {
                        let nextPage =
                            if self.check_page_flag(PageFlag::FLAG_BOUNDARY_NODE) { 
                                self.get_u32_last() as PageNum 
                            } else if self.currentPage == self.rootPage { 
                                0 
                            } else { 
                                self.currentPage + 1 
                            };
                        if 0 == nextPage {
                            self.currentKey = None;
                        } else {
                            try!(self.setCurrentPage(nextPage));
                            if try!(self.searchForwardForLeaf()) {
                                self.currentKey = Some(0);
                            }
                        }
                    } else {
                        let tmp_previousLeaf = self.previousLeaf;
                        if 0 == self.previousLeaf {
                            self.currentKey = None;
                        } else {
                            try!(self.setCurrentPage(tmp_previousLeaf));
                            if try!(self.page_type()) != PageType::LEAF_NODE {
                                return Err(Error::Misc(format!("must be a leaf")));
                            }
                            self.currentKey = Some(self.leafKeys.len() - 1);
                        }
                    }
                }
            }
            if self.currentKey.is_none() {
                Ok(SeekResult::Invalid)
            } else if equal {
                Ok(SeekResult::Equal)
            } else {
                Ok(SeekResult::Unequal)
            }
        } else if PageType::PARENT_NODE == pt {
            let next = try!(self.get_next_from_parent_page(k));
            self.search(next, k, sop)
        } else {
            unreachable!();
        }
    }

}

impl Drop for SegmentCursor {
    fn drop(&mut self) {
        match self.done {
            Some(ref f) => {
                f();
            },
            None => {
            },
        }
    }
}

impl ICursor for SegmentCursor {
    fn IsValid(&self) -> bool {
        self.leafIsValid()
    }

    fn SeekRef(&mut self, k: &KeyRef, sop: SeekOp) -> Result<SeekResult> {
        let root_page = self.rootPage;
        self.search(root_page, k, sop)
    }

    fn KeyRef<'a>(&'a self) -> Result<KeyRef<'a>> {
        match self.currentKey {
            None => Err(Error::CursorNotValid),
            Some(currentKey) => self.keyInLeaf2(currentKey),
        }
    }

    fn ValueRef<'a>(&'a self) -> Result<ValueRef<'a>> {
        match self.currentKey {
            None => Err(Error::CursorNotValid),
            Some(currentKey) => {
                let mut pos = self.leafKeys[currentKey as usize];

                self.skipKey(&mut pos);

                let vflag = self.get_byte(&mut pos);
                if 0 != (vflag & ValueFlag::FLAG_TOMBSTONE) {
                    Ok(ValueRef::Tombstone)
                } else {
                    let vlen = varint::read(&self.pr, &mut pos) as usize;
                    if 0 != (vflag & ValueFlag::FLAG_OVERFLOW) {
                        let pgnum = self.get_u32(&mut pos) as PageNum;
                        let strm = try!(myOverflowReadStream::new(&self.path, self.pr.len(), pgnum, vlen));
                        Ok(ValueRef::Overflowed(vlen, box strm))
                    } else {
                        Ok(ValueRef::Array(&self.pr[pos .. pos + vlen]))
                    }
                }
            }
        }
    }

    fn ValueLength(&self) -> Result<Option<usize>> {
        match self.currentKey {
            None => Err(Error::CursorNotValid),
            Some(currentKey) => {
                let mut cur = self.leafKeys[currentKey as usize];

                self.skipKey(&mut cur);

                let vflag = self.get_byte(&mut cur);
                if 0 != (vflag & ValueFlag::FLAG_TOMBSTONE) { 
                    Ok(None)
                } else {
                    let vlen = varint::read(&self.pr, &mut cur) as usize;
                    Ok(Some(vlen))
                }
            }
        }
    }

    fn First(&mut self) -> Result<()> {
        let firstLeaf = self.firstLeaf;
        try!(self.setCurrentPage(firstLeaf));
        if try!(self.page_type()) != PageType::LEAF_NODE {
            return Err(Error::Misc(format!("must be a leaf")));
        }
        self.currentKey = Some(0);
        Ok(())
    }

    fn Last(&mut self) -> Result<()> {
        let lastLeaf = self.lastLeaf;
        try!(self.setCurrentPage(lastLeaf));
        if try!(self.page_type()) != PageType::LEAF_NODE {
            return Err(Error::Misc(format!("must be a leaf")));
        }
        self.currentKey = Some(self.leafKeys.len() - 1);
        Ok(())
    }

    fn Next(&mut self) -> Result<()> {
        if !self.nextInLeaf() {
            let nextPage =
                if self.check_page_flag(PageFlag::FLAG_BOUNDARY_NODE) { 
                    self.get_u32_last() as PageNum 
                } else if try!(self.page_type()) == PageType::LEAF_NODE {
                    if self.currentPage == self.rootPage { 
                        0 
                    } else { 
                        self.currentPage + 1 
                    }
                } else { 
                    0 
                };
            if 0 == nextPage {
                self.currentKey = None;
            } else if !block_list_contains_page(&self.blocks, nextPage) {
                self.currentKey = None;
            } else {
                try!(self.setCurrentPage(nextPage));
                if try!(self.searchForwardForLeaf()) {
                    self.currentKey = Some(0);
                } else {
                    self.currentKey = None;
                }
            }
        }
        Ok(())
    }

    fn Prev(&mut self) -> Result<()> {
        if !self.prevInLeaf() {
            let previousLeaf = self.previousLeaf;
            if 0 == previousLeaf {
                self.currentKey = None;
            } else {
                try!(self.setCurrentPage(previousLeaf));
                if try!(self.page_type()) != PageType::LEAF_NODE {
                    return Err(Error::Misc(format!("must be a leaf")));
                }
                self.currentKey = Some(self.leafKeys.len() - 1);
            }
        }
        Ok(())
    }

}

#[derive(Clone)]
struct HeaderData {
    // TODO currentState is an ordered copy of segments_info.Keys.  eliminate duplication?
    // or add assertions and tests to make sure they never get out of sync?  we wish
    // we had a form of HashMap that kept track of ordering.
    currentState: Vec<SegmentNum>,
    segments_info: HashMap<SegmentNum, SegmentInfo>,
    headerOverflow: Option<PageBlock>,
    changeCounter: u64,
    mergeCounter: u64,
}

const HEADER_SIZE_IN_BYTES: usize = 4096;

impl PendingSegment {
    fn new(num: SegmentNum) -> PendingSegment {
        PendingSegment {
            // TODO maybe set capacity of the blocklist vec to something low
            blockList: Vec::new(), 
            segnum: num,
        }
    }

    fn AddBlock(&mut self, b: PageBlock) {
        //println!("seg {:?} got block {:?}", self.segnum, b);
        let len = self.blockList.len();
        if (! (self.blockList.is_empty())) && (b.firstPage == self.blockList[len-1].lastPage+1) {
            // note that by consolidating blocks here, the segment info list will
            // not have information about the fact that the two blocks were
            // originally separate.  that's okay, since all we care about here is
            // keeping track of which pages are used.  but the btree code itself
            // is still treating the last page of the first block as a boundary
            // page, even though its pointer to the next block goes to the very
            // next page, because its page manager happened to give it a block
            // which immediately follows the one it had.
            self.blockList[len-1].lastPage = b.lastPage;
            assert!(self.blockList[len-1].firstPage <= self.blockList[len-1].lastPage);
        } else {
            self.blockList.push(b);
        }
    }

    fn End(mut self, unused_page: PageNum) -> (SegmentNum, Vec<PageBlock>, Option<PageBlock>) {
        let len = self.blockList.len();
        assert!(self.blockList[len-1].contains_page(unused_page));
        let leftovers = {
            if unused_page > self.blockList[len-1].firstPage {
                let givenLastPage = self.blockList[len-1].lastPage;
                self.blockList[len-1].lastPage = unused_page - 1;
                assert!(self.blockList[len-1].firstPage <= self.blockList[len-1].lastPage);
                Some (PageBlock::new(unused_page, givenLastPage))
            } else {
                // this is one of those dorky cases where we they asked for a block
                // and never used any of it.  TODO
                let blk = self.blockList.pop().unwrap();
                Some(blk)
            }
        };
        // consume self return blockList
        (self.segnum, self.blockList, leftovers)
    }
}

fn readHeader(path: &str) -> Result<(HeaderData, usize, PageNum, SegmentNum)> {
    fn read<R>(fs: &mut R) -> Result<Box<[u8]>> where R : Read {
        let mut pr = vec![0; HEADER_SIZE_IN_BYTES].into_boxed_slice();
        let got = try!(misc::io::read_fully(fs, &mut pr));
        if got < HEADER_SIZE_IN_BYTES {
            Err(Error::CorruptFile("invalid header"))
        } else {
            Ok(pr)
        }
    }

    fn parse<R>(pr: &Box<[u8]>, cur: &mut usize, fs: &mut R) -> Result<(HeaderData, usize)> where R : Read+Seek {
        fn readSegmentList(pr: &Box<[u8]>, cur: &mut usize) -> Result<(Vec<SegmentNum>,HashMap<SegmentNum,SegmentInfo>)> {
            fn readBlockList(prBlocks: &Box<[u8]>, cur: &mut usize) -> Vec<PageBlock> {
                let count = varint::read(&prBlocks, cur) as usize;
                let mut a = Vec::with_capacity(count);
                for _ in 0 .. count {
                    let firstPage = varint::read(&prBlocks, cur) as PageNum;
                    let countPages = varint::read(&prBlocks, cur) as PageNum;
                    // blocks are stored as firstPage/count rather than as
                    // firstPage/lastPage, because the count will always be
                    // smaller as a varint
                    a.push(PageBlock::new(firstPage, firstPage + countPages - 1));
                }
                a
            }

            let count = varint::read(&pr, cur) as usize;
            let mut a = Vec::with_capacity(count);
            let mut m = HashMap::with_capacity(count);
            for _ in 0 .. count {
                let g = varint::read(&pr, cur) as SegmentNum;
                a.push(g);
                let root_page = varint::read(&pr, cur) as PageNum;
                let age = varint::read(&pr, cur) as u32;
                let blocks = readBlockList(pr, cur);
                if !block_list_contains_page(&blocks, root_page) {
                    return Err(Error::RootPageNotInSegmentBlockList);
                }

                let info = SegmentInfo {
                    root_page: root_page,
                    age: age,
                    blocks: blocks
                };
                m.insert(g,info);
            }
            Ok((a,m))
        }

        // --------

        let pgsz = misc::buf_advance::get_u32(&pr, cur) as usize;
        let changeCounter = varint::read(&pr, cur);
        let mergeCounter = varint::read(&pr, cur);
        let lenSegmentList = varint::read(&pr, cur) as usize;

        let overflowed = pr[*cur] != 0u8;
        *cur += 1;
        let (state, segments_info, blk) = 
            if overflowed {
                let lenChunk1 = misc::buf_advance::get_u32(&pr, cur) as usize;
                let lenChunk2 = lenSegmentList - lenChunk1;
                let firstPageChunk2 = misc::buf_advance::get_u32(&pr, cur) as PageNum;
                let extraPages = lenChunk2 / pgsz + if (lenChunk2 % pgsz) != 0 { 1 } else { 0 };
                let extraPages = extraPages as PageNum;
                let lastPageChunk2 = firstPageChunk2 + extraPages - 1;
                let mut pr2 = vec![0; lenSegmentList].into_boxed_slice();
                // TODO chain?
                // copy from chunk1 into pr2
                misc::bytes::copy_into(&pr[*cur .. *cur + lenChunk1], &mut pr2[0 .. lenChunk1]);
                // now get chunk2 and copy it in as well
                try!(utils::SeekPage(fs, pgsz, firstPageChunk2));
                try!(misc::io::read_fully(fs, &mut pr2[lenChunk1 .. lenChunk1 + lenChunk2]));
                let mut cur2 = 0;
                let (state, segments_info) = try!(readSegmentList(&pr2, &mut cur2));
                (state, segments_info, Some (PageBlock::new(firstPageChunk2, lastPageChunk2)))
            } else {
                let (state,segments_info) = try!(readSegmentList(pr, cur));
                (state, segments_info, None)
            };

        let hd = 
            HeaderData {
                currentState: state,
                segments_info: segments_info,
                headerOverflow: blk,
                changeCounter: changeCounter,
                mergeCounter: mergeCounter,
            };

        Ok((hd, pgsz))
    }

    fn calcNextPage(pgsz: usize, len: usize) -> PageNum {
        let numPagesSoFar = (if pgsz > len { 1 } else { len / pgsz }) as PageNum;
        numPagesSoFar + 1
    }

    // --------

    let mut fs = try!(OpenOptions::new()
            .read(true)
            .create(true)
            .open(&path));

    let len = try!(misc::io::seek_len(&mut fs));
    if len > 0 {
        try!(fs.seek(SeekFrom::Start(0 as u64)));
        let pr = try!(read(&mut fs));
        let mut cur = 0;
        let (h, pgsz) = try!(parse(&pr, &mut cur, &mut fs));
        let nextAvailablePage = calcNextPage(pgsz, len as usize);
        let nextAvailableSegmentNum = match h.currentState.iter().max() {
            Some(n) => n+1,
            None => 1,
        };
        Ok((h, pgsz, nextAvailablePage, nextAvailableSegmentNum))
    } else {
        let defaultPageSize = DEFAULT_SETTINGS.DefaultPageSize;
        let h = 
            HeaderData
            {
                segments_info: HashMap::new(),
                currentState: Vec::new(),
                headerOverflow: None,
                changeCounter: 0,
                mergeCounter: 0,
            };
        let nextAvailablePage = calcNextPage(defaultPageSize, HEADER_SIZE_IN_BYTES);
        let nextAvailableSegmentNum = 1;
        Ok((h, defaultPageSize, nextAvailablePage, nextAvailableSegmentNum))
    }

}

fn consolidateBlockList(blocks: &mut Vec<PageBlock>) {
    blocks.sort_by(|a,b| a.firstPage.cmp(&b.firstPage));
    loop {
        if blocks.len()==1 {
            break;
        }
        let mut did = false;
        for i in 1 .. blocks.len() {
            if blocks[i-1].lastPage+1 == blocks[i].firstPage {
                blocks[i-1].lastPage = blocks[i].lastPage;
                blocks.remove(i);
                did = true;
                break;
            }
        }
        if !did {
            break;
        }
    }
}

fn invertBlockList(blocks: &Vec<PageBlock>) -> Vec<PageBlock> {
    let len = blocks.len();
    let mut result = Vec::with_capacity(len);
    for i in 0 .. len {
        result.push(blocks[i]);
    }
    result.sort_by(|a,b| a.firstPage.cmp(&b.firstPage));
    for i in 0 .. len-1 {
        result[i].firstPage = result[i].lastPage+1;
        result[i].lastPage = result[i+1].firstPage-1;
        assert!(result[i].firstPage <= result[i].lastPage);
    }
    result.remove(len-1);
    result
}

fn listAllBlocks(h: &HeaderData, segmentsInWaiting: &HashMap<SegmentNum,SegmentInfo>, pgsz: usize) -> Vec<PageBlock> {
    let headerBlock = PageBlock::new(1, (HEADER_SIZE_IN_BYTES / pgsz) as PageNum);
    let mut blocks = Vec::new();

    fn grab(blocks: &mut Vec<PageBlock>, from: &HashMap<SegmentNum,SegmentInfo>) {
        for info in from.values() {
            for b in info.blocks.iter() {
                blocks.push(*b);
            }
        }
    }

    grab(&mut blocks, &h.segments_info);
    grab(&mut blocks, segmentsInWaiting);
    blocks.push(headerBlock);
    match h.headerOverflow {
        Some(blk) => blocks.push(blk),
        None => ()
    }
    blocks
}

use std::sync::Mutex;

struct NextSeg {
    nextSeg: SegmentNum,
}

struct Space {
    nextPage: PageNum,
    freeBlocks: Vec<PageBlock>,
}

struct SafeSegmentsInWaiting {
    segmentsInWaiting: HashMap<SegmentNum, SegmentInfo>,
}

// TODO
struct PendingMerge {
    old_segments: Vec<SegmentNum>,
    new_segment: Option<SegmentNum>,
    level: u32,
}

struct SafeMergeStuff {
    merging: HashSet<SegmentNum>,
    pendingMerges: HashMap<SegmentNum, Vec<SegmentNum>>,
    blooms: HashMap<SegmentNum, std::sync::Arc<Bloom>>,
}

struct SafeHeader {
    // TODO one level too much nesting
    header: HeaderData,
}

struct SafeCursors {
    nextCursorNum: u64,
    cursors: HashMap<u64, SegmentNum>,

    // a zombie segment is one that was replaced by a merge, but
    // when the merge was done, it could not be reclaimed as free
    // blocks because there was an open cursor on it.
    zombie_segments: HashMap<SegmentNum, SegmentInfo>,

    // we keep a pool of page buffers so we can lend them to a
    // SegmentCursor.
    pagepool: Vec<Box<[u8]>>,
}

// there can be only one InnerPart instance per path
struct InnerPart {
    path: String,
    pgsz: usize,
    settings: DbSettings,

    nextSeg: Mutex<NextSeg>,
    space: Mutex<Space>,
    // TODO should the header mutex be an RWLock?
    header: Mutex<SafeHeader>,
    segmentsInWaiting: Mutex<SafeSegmentsInWaiting>,
    mergeStuff: Mutex<SafeMergeStuff>,
    cursors: Mutex<SafeCursors>,
}

pub struct WriteLock {
    inner: std::sync::Arc<InnerPart>,
    notify_0: mpsc::Sender<Vec<SegmentNum>>,
    notify_merge_others: Vec<mpsc::Sender<SegmentNum>>,
}

impl WriteLock {
    pub fn commitSegments(&self, newSegs: Vec<SegmentNum>) -> Result<()> {
        // TODO avoid clone
        try!(self.inner.commitSegments(newSegs.clone()));
        try!(self.notify_0.send(newSegs).map_err(wrap_err));
        Ok(())
    }

    pub fn commitMerge(&self, newSegNum:SegmentNum) -> Result<()> {
        let age = try!(self.inner.commitMerge(newSegNum));
        assert!(age > 0);
        let age = (age - 1) as usize;
        if age < self.notify_merge_others.len() {
            try!(self.notify_merge_others[age].send(newSegNum).map_err(wrap_err));
        }
        Ok(())
    }
}

// TODO rename this
pub struct db {
    inner: std::sync::Arc<InnerPart>,

    // there can be only one of the following per path
    write_lock: Mutex<WriteLock>,
}

impl db {
    pub fn new(path: String, settings : DbSettings) -> Result<std::sync::Arc<db>> {

        let (header, pgsz, firstAvailablePage, nextAvailableSegmentNum) = try!(readHeader(&path));

        let segmentsInWaiting = HashMap::new();
        let mut blocks = listAllBlocks(&header, &segmentsInWaiting, pgsz);
        consolidateBlockList(&mut blocks);
        let mut freeBlocks = invertBlockList(&blocks);
        freeBlocks.sort_by(|a,b| b.count_pages().cmp(&a.count_pages()));

        let nextSeg = NextSeg {
            nextSeg: nextAvailableSegmentNum,
        };

        let space = Space {
            nextPage: firstAvailablePage, 
            freeBlocks: freeBlocks,
        };

        let segmentsInWaiting = SafeSegmentsInWaiting {
            segmentsInWaiting: segmentsInWaiting,
        };

        let mergeStuff = SafeMergeStuff {
            merging: HashSet::new(),
            pendingMerges: HashMap::new(),
            blooms: HashMap::new(),
        };

        let header = SafeHeader {
            header: header, 
        };

        let cursors = SafeCursors {
            nextCursorNum: 1,
            cursors: HashMap::new(),
            zombie_segments: HashMap::new(),
            pagepool: vec![],
        };

        let (tx_0, rx_0): (mpsc::Sender<Vec<SegmentNum>>, mpsc::Receiver<Vec<SegmentNum>>) = mpsc::channel();

        let mut notify_merge_others = vec![];
        let mut receivers = vec![];
        for age in 1 .. 8 {
            let (tx, rx): (mpsc::Sender<SegmentNum>, mpsc::Receiver<SegmentNum>) = mpsc::channel();
            notify_merge_others.push(tx);
            receivers.push((age, rx));
        }

        let inner = InnerPart {
            path: path,
            pgsz: pgsz,
            settings: settings, 
            header: Mutex::new(header),
            nextSeg: Mutex::new(nextSeg),
            space: Mutex::new(space),
            segmentsInWaiting: Mutex::new(segmentsInWaiting),
            mergeStuff: Mutex::new(mergeStuff),
            cursors: Mutex::new(cursors),
        };

        let inner = std::sync::Arc::new(inner);

        let lck = 
            WriteLock { 
                inner: inner.clone(),
                notify_0: tx_0,
                notify_merge_others: notify_merge_others,
            };

        let res = db {
            inner: inner,
            write_lock: Mutex::new(lck),
        };
        let res = std::sync::Arc::new(res);

        {
            let res = res.clone();
            thread::spawn(move || {
                loop {
                    match rx_0.recv() {
                        Ok(new_segs) => {
                            // TODO there should be a way to send a message to this
                            // thread telling it to stop.
                            res.merge_0(new_segs);
                        },
                        Err(e) => {
                            // TODO what now?
                            panic!();
                        },
                    }
                }
            });

        }

        for (age, rx) in receivers {
            let res = res.clone();
            thread::spawn(move || {
                loop {
                    match rx.recv() {
                        Ok(new_seg) => {
                            // TODO there should be a way to send a message to this
                            // thread telling it to stop.
                            res.merge_others(age, new_seg);
                        },
                        Err(e) => {
                            // TODO what now?
                            panic!();
                        },
                    }
                }
            });

        }

        Ok(res)
    }

    // TODO func to ask for the write lock without blocking?

    pub fn GetWriteLock(&self) -> Result<std::sync::MutexGuard<WriteLock>> {
        let lck = try!(self.write_lock.lock());
        Ok(lck)
    }

    fn after_commit(&self, new_segs: Vec<SegmentNum>) -> Result<()> {
        //println!("got new segs: {:?}", new_segs);
        // TODO tweak this automerge algorithm.  give it options.  etc.
        for i in 0 .. 8 {
            let mut at_least_once_in_this_level = false;
            loop {
                match try!(self.merge(i, i, 4, 8)) {
                    Some(seg) => {
                        let lck = try!(self.GetWriteLock());
                        try!(lck.commitMerge(seg));
                        at_least_once_in_this_level = true;
                    },
                    None => {
                        break;
                    },
                }
            }
            if !at_least_once_in_this_level {
                break;
            }
        }
        Ok(())
    }

    fn merge_0(&self, new_segs: Vec<SegmentNum>) -> Result<()> {
        //println!("got new segs: {:?}", new_segs);
        // TODO tweak this automerge algorithm.  give it options.  etc.
        loop {
            match try!(self.merge(0, 0, 2, 8)) {
                Some(seg) => {
                    let lck = try!(self.GetWriteLock());
                    try!(lck.commitMerge(seg));
                },
                None => {
                    break;
                },
            }
        }
        Ok(())
    }

    fn merge_others(&self, age: u32, new_seg: SegmentNum) -> Result<()> {
        //println!("got new segs: {:?}", new_segs);
        match try!(self.merge(age, age, 4, 8)) {
            Some(seg) => {
                let lck = try!(self.GetWriteLock());
                try!(lck.commitMerge(seg));
            },
            None => {
            },
        }
        Ok(())
    }

    // the following methods are passthrus, exposing inner
    // stuff publicly.

    pub fn OpenCursor(&self) -> Result<LivingCursor> {
        InnerPart::OpenCursor(&self.inner)
    }

    pub fn OpenSegmentCursor(&self, n: SegmentNum) -> Result<SegmentCursor> {
        InnerPart::OpenSegmentCursor(&self.inner, n)
    }

    pub fn WriteSegmentFromSortedSequence<I>(&self, source: I, estimate_keys: usize) -> Result<SegmentNum> where I:Iterator<Item=Result<kvp>> {
        self.inner.WriteSegmentFromSortedSequence(source, estimate_keys)
    }

    pub fn WriteSegment(&self, pairs: HashMap<Box<[u8]>,Box<[u8]>>) -> Result<SegmentNum> {
        self.inner.WriteSegment(pairs)
    }

    // TODO consider whether we could use one of the other rust collections to get
    // sorting as things are inserted.

    pub fn WriteSegment2(&self, pairs: HashMap<Box<[u8]>,Blob>) -> Result<SegmentNum> {
        self.inner.WriteSegment2(pairs)
    }

    pub fn merge(&self, min_level: u32, max_level: u32, min_segs: usize, max_segs: usize) -> Result<Option<SegmentNum>> {
        InnerPart::merge(&self.inner, min_level, max_level, min_segs, max_segs)
    }

    pub fn list_segments(&self) -> Result<(Vec<SegmentNum>,HashMap<SegmentNum,SegmentInfo>)> {
        InnerPart::list_segments(&self.inner)
    }

    pub fn list_free_blocks(&self) -> Result<Vec<PageBlock>> {
        InnerPart::list_free_blocks(&self.inner)
    }

    pub fn get_page(&self, pgnum: PageNum) -> Result<Box<[u8]>> {
        InnerPart::get_page(&self.inner, pgnum)
    }
}

// TODO this could be generic
fn slice_within(sub: &[SegmentNum], within: &[SegmentNum]) -> Result<usize> {
    match within.iter().position(|&g| g == sub[0]) {
        Some(ndx_first) => {
            let count = sub.len();
            if sub == &within[ndx_first .. ndx_first + count] {
                Ok(ndx_first)
            } else {
                Err(Error::Misc(String::from("not contiguous")))
            }
        },
        None => {
            Err(Error::Misc(String::from("not contiguous")))
        },
    }
}

impl InnerPart {

    fn page_done(&self, page: Box<[u8]>) {
        //println!("page_done");
        let mut cursors = self.cursors.lock().unwrap(); // gotta succeed
        cursors.pagepool.push(page);
    }

    fn cursor_dropped(&self, segnum: SegmentNum, csrnum: u64) {
        //println!("cursor_dropped");
        let mut cursors = self.cursors.lock().unwrap(); // gotta succeed
        let seg = cursors.cursors.remove(&csrnum).expect("gotta be there");
        assert_eq!(seg, segnum);
        match cursors.zombie_segments.remove(&segnum) {
            Some(info) => {
                match self.space.try_lock() {
                    Ok(mut space) => {
                        self.addFreeBlocks(&mut space, info.blocks);
                    },
                    Err(_) => {
                        // worst that can happen is that these blocks don't get
                        // reclaimed until some other day.
                    },
                }
            },
            None => {
            },
        }
    }

    fn getBlock(&self, space: &mut Space, specificSizeInPages: PageNum) -> PageBlock {
        if specificSizeInPages > 0 {
            if space.freeBlocks.is_empty() || specificSizeInPages > space.freeBlocks[0].count_pages() {
                let newBlk = PageBlock::new(space.nextPage, space.nextPage+specificSizeInPages-1);
                space.nextPage = space.nextPage + specificSizeInPages;
                newBlk
            } else {
                let headBlk = space.freeBlocks[0];
                if headBlk.count_pages() > specificSizeInPages {
                    // trim the block to size
                    let blk2 = PageBlock::new(headBlk.firstPage,
                                              headBlk.firstPage+specificSizeInPages-1); 
                    space.freeBlocks[0].firstPage = space.freeBlocks[0].firstPage + specificSizeInPages;
                    assert!(space.freeBlocks[0].firstPage <= space.freeBlocks[0].lastPage);
                    // TODO problem: the list is probably no longer sorted.  is this okay?
                    // is a re-sort of the list really worth it?
                    blk2
                } else {
                    space.freeBlocks.remove(0);
                    headBlk
                }
            }
        } else {
            if space.freeBlocks.is_empty() {
                let size = self.settings.PagesPerBlock;
                let newBlk = PageBlock::new(space.nextPage, space.nextPage+size-1) ;
                space.nextPage = space.nextPage + size;
                newBlk
            } else {
                let headBlk = space.freeBlocks[0];
                space.freeBlocks.remove(0);
                headBlk
            }
        }
    }

    fn OpenForWriting(&self) -> io::Result<File> {
        OpenOptions::new()
                .read(true)
                .write(true)
                .open(&self.path)
    }

    fn OpenForReading(&self) -> io::Result<File> {
        OpenOptions::new()
                .read(true)
                .open(&self.path)
    }

    // this code should not be called in a release build.  it helps
    // finds problems by zeroing out pages in blocks that
    // have been freed.
    #[cfg(remove_me)]
    fn stomp(&self, blocks:Vec<PageBlock>) -> Result<()> {
        let bad = vec![0;self.pgsz as usize].into_boxed_slice();
        let mut fs = try!(OpenOptions::new()
                .read(true)
                .write(true)
                .open(&self.path));
        for b in blocks {
            for x in b.firstPage .. b.lastPage+1 {
                try!(utils::SeekPage(&mut fs, self.pgsz, x));
                try!(fs.write(&bad));
            }
        }
        Ok(())
    }

    fn addFreeBlocks(&self, space: &mut Space, blocks:Vec<PageBlock>) {

        // all additions to the freeBlocks list should happen here
        // by calling this function.
        //
        // the list is kept consolidated and sorted by size descending.
        // unfortunately this requires two sorts, and they happen here
        // inside a critical section.  but the benefit is considered
        // worth the trouble.
        
        // TODO it is important that freeBlocks contains no overlaps.
        // add debug-only checks to verify?

        // TODO is there such a thing as a block that is so small we
        // don't want to bother with it?  what about a single-page block?
        // should this be a configurable setting?

        // TODO if the last block of the file is free, consider just
        // moving nextPage back.

        for b in blocks {
            space.freeBlocks.push(b);
        }
        consolidateBlockList(&mut space.freeBlocks);
        space.freeBlocks.sort_by(|a,b| b.count_pages().cmp(&a.count_pages()));
    }

    // a stored segmentinfo for a segment is a single blob of bytes.
    // root page
    // age
    // number of pairs
    // each pair is startBlock,countBlocks
    // all in varints

    fn writeHeader(&self, 
                   st: &mut SafeHeader, 
                   space: &mut Space,
                   fs: &mut File, 
                   mut hdr: HeaderData
                  ) -> Result<Option<PageBlock>> {
        fn spaceNeededForSegmentInfo(info: &SegmentInfo) -> usize {
            let mut a = 0;
            for t in info.blocks.iter() {
                a = a + varint::space_needed_for(t.firstPage as u64);
                a = a + varint::space_needed_for(t.count_pages() as u64);
            }
            a = a + varint::space_needed_for(info.root_page as u64);
            a = a + varint::space_needed_for(info.age as u64);
            a = a + varint::space_needed_for(info.blocks.len() as u64);
            a
        }

        fn spaceForHeader(h: &HeaderData) -> usize {
            let mut a = varint::space_needed_for(h.currentState.len() as u64);
            // TODO use currentState with a lookup into h.segments_info instead?
            // should be the same, right?
            for (g,info) in h.segments_info.iter() {
                a = a + spaceNeededForSegmentInfo(&info) + varint::space_needed_for(*g);
            }
            a
        }

        fn buildSegmentList(h: &HeaderData) -> PageBuilder {
            let space = spaceForHeader(h);
            let mut pb = PageBuilder::new(space);
            // TODO format version number
            pb.PutVarint(h.currentState.len() as u64);
            for g in h.currentState.iter() {
                pb.PutVarint(*g);
                match h.segments_info.get(&g) {
                    Some(info) => {
                        pb.PutVarint(info.root_page as u64);
                        pb.PutVarint(info.age as u64);
                        pb.PutVarint(info.blocks.len() as u64);
                        // we store PageBlock as first/count instead of first/last, since the
                        // count will always compress better as a varint.
                        for t in info.blocks.iter() {
                            pb.PutVarint(t.firstPage as u64);
                            pb.PutVarint(t.count_pages() as u64);
                        }
                    },
                    None => panic!("segment num in currentState but not in segments_info")
                }
            }
            assert!(0 == pb.Available());
            pb
        }

        let mut pb = PageBuilder::new(HEADER_SIZE_IN_BYTES);
        pb.PutInt32(self.pgsz as u32);

        pb.PutVarint(hdr.changeCounter);
        pb.PutVarint(hdr.mergeCounter);

        let pbSegList = buildSegmentList(&hdr);
        let buf = pbSegList.Buffer();
        pb.PutVarint(buf.len() as u64);

        // TODO consider disallowing header overflow
        // how many segments can fit in the header without overflow?
        // do we ever need more than that really?
        let headerOverflow =
            if pb.Available() >= (buf.len() + 1) {
                pb.PutByte(0u8);
                pb.PutArray(buf);
                None
            } else {
                pb.PutByte(1u8);
                let fits = pb.Available() - 4 - 4;
                let extra = buf.len() - fits;
                let extraPages = extra / self.pgsz + if (extra % self.pgsz) != 0 { 1 } else { 0 };
                let blk = self.getBlock(space, extraPages as PageNum);
                try!(utils::SeekPage(fs, self.pgsz, blk.firstPage));
                try!(fs.write(&buf[fits .. buf.len()]));
                pb.PutInt32(fits as u32);
                pb.PutInt32(blk.firstPage);
                pb.PutArray(&buf[0 .. fits]);
                Some(blk)
            };

        try!(fs.seek(SeekFrom::Start(0)));
        try!(pb.Write(fs));
        try!(fs.flush());
        let oldHeaderOverflow = hdr.headerOverflow;
        hdr.headerOverflow = headerOverflow;
        st.header = hdr;
        Ok((oldHeaderOverflow))
    }

    // TODO this function looks for the segment in the header.segments_info,
    // which means it cannot be used to open a cursor on a pendingSegment,
    // which we think we might need in the future.
    fn getCursor(inner: &std::sync::Arc<InnerPart>, 
                 st: &SafeHeader,
                 g: SegmentNum
                ) -> Result<SegmentCursor> {
        match st.header.segments_info.get(&g) {
            None => Err(Error::Misc(String::from("getCursor: segment not found"))),
            Some(seg) => {
                let rootPage = seg.root_page;
                let mut cursors = try!(inner.cursors.lock());
                let csrnum = cursors.nextCursorNum;
                let foo = inner.clone();
                let done = move || -> () {
                    foo.cursor_dropped(g, csrnum);
                };
                let page =
                    match cursors.pagepool.pop() {
                        Some(p) => p,
                        None => vec![0; inner.pgsz].into_boxed_slice(),
                    };
                let foo = inner.clone();
                let done_page = move |p| -> () {
                    foo.page_done(p);
                };
                let lend_page = misc::Lend::new(page, box done_page);
                let mut csr = try!(SegmentCursor::new(&inner.path, lend_page, rootPage, seg.blocks.clone()));

                cursors.nextCursorNum = cursors.nextCursorNum + 1;
                let was = cursors.cursors.insert(csrnum, g);
                assert!(was.is_none());
                csr.set_hook(box done);
                Ok(csr)
            }
        }
    }

    fn OpenSegmentCursor(inner: &std::sync::Arc<InnerPart>, g: SegmentNum) -> Result<SegmentCursor> {
        let st = try!(inner.header.lock());
        let cursor = try!(Self::getCursor(inner, &*st, g));
        Ok(cursor)
    }

    // TODO we also need a way to open a cursor on segments in waiting
    fn OpenCursor(inner: &std::sync::Arc<InnerPart>) -> Result<LivingCursor> {
        // TODO this cursor needs to expose the changeCounter and segment list
        // on which it is based. for optimistic writes. caller can grab a cursor,
        // do their writes, then grab the writelock, and grab another cursor, then
        // compare the two cursors to see if anything important changed.  if not,
        // commit their writes.  if so, nevermind the written segments and start over.

        let st = try!(inner.header.lock());
        let mut clist = Vec::with_capacity(st.header.currentState.len());
        for g in st.header.currentState.iter() {
            clist.push(try!(Self::getCursor(inner, &*st, *g)));
        }
        let mc = MultiCursor::Create(clist);
        let lc = LivingCursor::Create(mc);
        Ok(lc)
    }

    fn get_page(inner: &std::sync::Arc<InnerPart>, pgnum: PageNum) -> Result<Box<[u8]>> {
        let mut f = try!(OpenOptions::new()
                .read(true)
                .create(true)
                .open(&inner.path));
        let mut buf = vec![0; inner.pgsz].into_boxed_slice();
        try!(utils::SeekPage(&mut f, inner.pgsz, pgnum));
        try!(misc::io::read_fully(&mut f, &mut buf));
        Ok(buf)
    }

    fn list_free_blocks(inner: &std::sync::Arc<InnerPart>) -> Result<Vec<PageBlock>> {
        let space = try!(inner.space.lock());
        Ok(space.freeBlocks.clone())
    }

    fn list_segments(inner: &std::sync::Arc<InnerPart>) -> Result<(Vec<SegmentNum>,HashMap<SegmentNum,SegmentInfo>)> {
        let st = try!(inner.header.lock());
        let a = st.header.currentState.clone();
        let b = st.header.segments_info.clone();
        Ok((a,b))
    }

    fn commitSegments(&self, newSegs: Vec<SegmentNum>) -> Result<()> {
        assert_eq!(newSegs.len(), newSegs.iter().map(|g| *g).collect::<HashSet<SegmentNum>>().len());

        let mut st = try!(self.header.lock());
        let mut waiting = try!(self.segmentsInWaiting.lock());
        let mut space = try!(self.space.lock());

        assert!({
            let mut ok = true;
            for newSegNum in newSegs.iter() {
                ok = st.header.currentState.iter().position(|&g| g == *newSegNum).is_none();
                if !ok {
                    break;
                }
            }
            ok
        });

        // self.segmentsInWaiting must contain one seg for each segment num in newSegs.
        // we want those entries to move out and move into the header, currentState
        // and segments_info.  This means taking ownership of those SegmentInfos.  But
        // the others we want to leave.

        let mut newHeader = st.header.clone();
        let mut newSegmentsInWaiting = waiting.segmentsInWaiting.clone();
        for g in newSegs.iter() {
            match newSegmentsInWaiting.remove(&g) {
                Some(info) => {
                    newHeader.segments_info.insert(*g,info);
                },
                None => {
                    return Err(Error::Misc(String::from("commitSegments: segment not found in segmentsInWaiting")));
                },
            }
        }

        // TODO surely there's a better way to insert one vec into another?
        // like insert_all, similar to push_all?
        for i in 0 .. newSegs.len() {
            let g = newSegs[i];
            newHeader.currentState.insert(i, g);
        }

        newHeader.changeCounter = newHeader.changeCounter + 1;

        let mut fs = try!(self.OpenForWriting());
        let oldHeaderOverflow = try!(self.writeHeader(&mut st, &mut space, &mut fs, newHeader));
        waiting.segmentsInWaiting = newSegmentsInWaiting;

        //printfn "after commit, currentState: %A" header.currentState
        //printfn "after commit, segments_info: %A" header.segments_info
        // all the segments we just committed can now be removed from
        // the segments in waiting list
        match oldHeaderOverflow {
            Some(blk) => self.addFreeBlocks(&mut space, vec![ blk ]),
            None => ()
        }
        // note that we intentionally do not release the writeLock here.
        // you can change the segment list more than once while holding
        // the writeLock.  the writeLock gets released when you Dispose() it.

        Ok(())
    }

    // TODO bad fn name
    fn WriteSegmentFromSortedSequence<I>(&self, source: I, estimate_keys: usize) -> Result<SegmentNum> where I:Iterator<Item=Result<kvp>> {
        let mut fs = try!(self.OpenForWriting());
        let g = try!(CreateFromSortedSequenceOfKeyValuePairs(&mut fs, self, source, estimate_keys));
        Ok(g)
    }

    // TODO bad fn name
    // TODO remove this one?
    fn WriteSegment(&self, pairs: HashMap<Box<[u8]>, Box<[u8]>>) -> Result<SegmentNum> {
        let estimate_keys = pairs.len();
        let mut a : Vec<(Box<[u8]>,Box<[u8]>)> = pairs.into_iter().collect();

        a.sort_by(|a,b| {
            let (ref ka,_) = *a;
            let (ref kb,_) = *b;
            bcmp::Compare(&ka,&kb)
        });
        let source = a.into_iter().map(|t| {
            let (k,v) = t;
            Ok(kvp {Key:k, Value:Blob::Array(v)})
        });
        let mut fs = try!(self.OpenForWriting());
        let g = try!(CreateFromSortedSequenceOfKeyValuePairs(&mut fs, self, source, estimate_keys));
        Ok(g)
    }

    // TODO bad fn name
    fn WriteSegment2(&self, pairs: HashMap<Box<[u8]>, Blob>) -> Result<SegmentNum> {
        let estimate_keys = pairs.len();
        let mut a : Vec<(Box<[u8]>,Blob)> = pairs.into_iter().collect();

        a.sort_by(|a,b| {
            let (ref ka,_) = *a;
            let (ref kb,_) = *b;
            bcmp::Compare(&ka,&kb)
        });
        let source = a.into_iter().map(|t| {
            let (k,v) = t;
            Ok(kvp {Key:k, Value:v})
        });
        let mut fs = try!(self.OpenForWriting());
        let g = try!(CreateFromSortedSequenceOfKeyValuePairs(&mut fs, self, source, estimate_keys));
        Ok(g)
    }

    fn do_merge(inner: &std::sync::Arc<InnerPart>, segs: Vec<SegmentNum>, cursor: Box<ICursor>, estimate_keys: usize) -> Result<SegmentNum> {
        let source = CursorIterator::new(cursor);
        let mut fs = try!(inner.OpenForWriting());
        let g = try!(CreateFromSortedSequenceOfKeyValuePairs(&mut fs, &**inner, source, estimate_keys));
        //printfn "merged %A to get %A" segs g
        let mut mergeStuff = try!(inner.mergeStuff.lock());
        mergeStuff.pendingMerges.insert(g, segs);
        Ok(g)
    }

    fn merge(inner: &std::sync::Arc<InnerPart>, min_level: u32, max_level: u32, min_segs: usize, max_segs: usize) -> Result<Option<SegmentNum>> {
        assert!(min_level <= max_level);
        assert!(min_segs <= max_segs);
        let mrg = {
            let st = try!(inner.header.lock());

            if st.header.currentState.len() == 0 {
                return Ok(None)
            }

            //println!("age for merge: {}", level);
            //println!("currentState: {:?}", st.header.currentState);

            let age_group = st.header.currentState.iter().filter(|g| {
                let info = st.header.segments_info.get(&g).unwrap();
                info.age >= min_level && info.age <= max_level
            }).map(|g| *g).collect::<Vec<SegmentNum>>();

            //println!("age_group: {:?}", age_group);

            if age_group.len() == 0 {
                return Ok(None)
            }

            // make sure this is contiguous
            assert!(slice_within(age_group.as_slice(), st.header.currentState.as_slice()).is_ok());

            let mut segs = Vec::new();

            let mut mergeStuff = try!(inner.mergeStuff.lock());

            // we can merge any contiguous set of not-already-being-merged 
            // segments at the end of the group.  if we merge something
            // that is not at the end of the group, we could end up with
            // age groups not being contiguous.

            for g in age_group.iter().rev() {
                if mergeStuff.merging.contains(g) {
                    break;
                } else {
                    segs.push(*g);
                }
            }

            if segs.len() >= min_segs {
                segs.truncate(max_segs);

                // right now the segs list is in reverse order because we searched with a
                // reverse iterator just above.  reverse it again to make it right.
                segs.reverse();

                let mut clist = Vec::with_capacity(segs.len());
                for g in segs.iter() {
                    let cursor = try!(Self::getCursor(inner, &st, *g));
                    clist.push(cursor);
                }

                let estimate_keys = clist.iter().map(
                    |c| {
                        c.count_keys() - c.count_tombstones()
                    }).sum();

                for g in segs.iter() {
                    mergeStuff.merging.insert(*g);
                }

                let cursor = {
                    let mc = MultiCursor::Create(clist);
                    mc
                };

                let last_seg_being_merged = segs[segs.len() - 1];
                let pos_last_seg = st.header.currentState.iter().position(|s| *s == last_seg_being_merged).expect("gotta be there");
                let count_segments_behind = st.header.currentState.len() - (pos_last_seg + 1);

                let cursor: Box<ICursor> =
                    if count_segments_behind == 0 {
                        // we are merging the last segments in the current state.
                        // there is nothing behind.
                        // so all tombstones can be filtered.
                        // so we just wrap in a LivingCursor.
                        let mut cursor = LivingCursor::Create(cursor);
                        box cursor
                    } else if count_segments_behind <= 8 {
                        // TODO arbitrary hard-coded limit in the line above

                        // there are segments behind the ones we are merging.
                        // we can only filter a tombstone if its key is not present behind.

                        // TODO getting all these cursors can be really expensive.

                        // TODO if we knew there were no tombstones in the segments to be merged,
                        // we would not bother with this.

                        // TODO if there are a LOT of segments behind, this will fail because
                        // of opening too many files.

                        // TODO we need a way to cache these cursors.  maybe these "behind"
                        // cursors are special, and are stored here in the header somewhere.
                        // the next time we do a merge, we can reuse them.  they need to get
                        // cleaned up at some point.

                        // TODO capacity
                        let mut behind = vec![];
                        for s in &st.header.currentState[pos_last_seg + 1 ..] {
                            let s = *s;
                            let cursor = try!(Self::getCursor(inner, &st, s));
                            let bloom =
                                match mergeStuff.blooms.entry(s) {
                                    std::collections::hash_map::Entry::Occupied(e) => {
                                        Some(e.get().clone())
                                    },
                                    std::collections::hash_map::Entry::Vacant(e) => {
                                        match try!(cursor.load_bloom_filter()) {
                                            Some(bloom) => {
                                                let bloom = std::sync::Arc::new(bloom);
                                                let result = bloom.clone();
                                                e.insert(bloom);
                                                Some(result)
                                            },
                                            None => {
                                                None
                                            },
                                        }
                                    },
                                };
                            // TODO so actually, the FilterTombstonesCursor needs EITHER the
                            // bloom or the SegmentCursor.  it never needs both.
                            behind.push((bloom, cursor));
                        }
                        // TODO to allow reuse of these behind cursors, we should pass
                        // them as references, don't transfer ownership.  but then they
                        // will need to be owned somewhere else.
                        let mut cursor = FilterTombstonesCursor::new(cursor, behind);
                        box cursor
                    } else {
                        box cursor
                    };

                Some((segs, cursor, estimate_keys))
            } else {
                None
            }
        };

        match mrg {
            Some((segs, mut cursor, estimate_keys)) => {
                // note that cursor.First() should NOT have already been called
                try!(cursor.First());
                if !cursor.IsValid() {
                    println!("TODO HEY this segment is going to be empty");
                }
                let g = try!(Self::do_merge(inner, segs, cursor, estimate_keys));
                // TODO if something goes wrong here, the function will exit with
                // an error but mergeStuff.merging will still contain the segments we are
                // trying to merge, which will prevent them from EVER being merged.
                Ok(Some(g))
            },
            None => {
                Ok(None)
            },
        }
    }

    fn commitMerge(&self, newSegNum:SegmentNum) -> Result<u32> {

        let mut st = try!(self.header.lock());
        let mut waiting = try!(self.segmentsInWaiting.lock());
        let mut space = try!(self.space.lock());
        let mut mergeStuff = try!(self.mergeStuff.lock());

        assert!(st.header.currentState.iter().position(|&g| g == newSegNum).is_none());

        // we need the list of segments which were merged.  we make a copy of
        // so that we're not keeping a reference that inhibits our ability to
        // get other references a little later in the function.

        let old = {
            let maybe = mergeStuff.pendingMerges.get(&newSegNum);
            if maybe.is_none() {
                return Err(Error::Misc(String::from("commitMerge: segment not found in pendingMerges")));
            } else {
                maybe.expect("just checked is_none").clone()
            }
        };

        let oldAsSet : HashSet<SegmentNum> = old.iter().map(|g| *g).collect();
        assert!(oldAsSet.len() == old.len());

        // now we need to verify that the segments being replaced are in currentState
        // and contiguous.

        let ndxFirstOld = try!(slice_within(old.as_slice(), st.header.currentState.as_slice()));

        // now we construct a newHeader

        let mut newHeader = st.header.clone();

        // first, fix the currentState

        for _ in &old {
            newHeader.currentState.remove(ndxFirstOld);
        }
        newHeader.currentState.insert(ndxFirstOld, newSegNum);

        // remove the old segmentinfos, keeping them for later

        let mut segmentsBeingReplaced = HashMap::with_capacity(oldAsSet.len());
        for g in &oldAsSet {
            let info = newHeader.segments_info.remove(g).expect("old seg not found in header.segments_info");
            segmentsBeingReplaced.insert(g, info);
        }

        // now get the segment info for the new segment

        let mut newSegmentInfo = {
            let maybe = waiting.segmentsInWaiting.get(&newSegNum);
            if maybe.is_none() {
                return Err(Error::Misc(String::from("commitMerge: segment not found in segmentsInWaiting")));
            } else {
                maybe.expect("seg not found").clone()
            }
        };

        // and fix its age.

        let age_of_new_segment = {
            let ages: Vec<u32> = segmentsBeingReplaced.values().map(|info| info.age).collect();
            let min_age = *ages.iter().min().expect("this cannot be empty");
            let max_age = *ages.iter().max().expect("this cannot be empty");
            if min_age == max_age {
                // if the ages of the merged segments were all the same,
                // the new one gets 1 plus that age.  it is simply getting
                // promoted to the next level.
                1 + max_age
            } else {
                // if the merge included a range of ages, the new segment
                // gets the same age as the max age of the group, so we
                // don't end up with ages growing forever.
                // TODO do we want the caller to be allowed to say they
                // want 1 added (to promote to the next level) ?
                max_age
            }
        };
        newSegmentInfo.age = age_of_new_segment;

        newHeader.segments_info.insert(newSegNum, newSegmentInfo);

        newHeader.mergeCounter = newHeader.mergeCounter + 1;

        let mut fs = try!(self.OpenForWriting());
        let oldHeaderOverflow = try!(self.writeHeader(&mut st, &mut space, &mut fs, newHeader));

        // the write of the new header has succeeded.

        waiting.segmentsInWaiting.remove(&newSegNum);
        mergeStuff.pendingMerges.remove(&newSegNum);
        for g in old {
            mergeStuff.merging.remove(&g);
        }

        let mut segmentsToBeFreed = segmentsBeingReplaced;
        {
            let mut cursors = try!(self.cursors.lock());
            let segmentsWithACursor : HashSet<SegmentNum> = cursors.cursors.iter().map(|t| {let (_,segnum) = t; *segnum}).collect();
            for g in segmentsWithACursor {
                // don't free any segment that has a cursor
                match segmentsToBeFreed.remove(&g) {
                    Some(z) => {
                        cursors.zombie_segments.insert(g, z);
                    },
                    None => {
                    },
                }
            }
        }
        let mut blocksToBeFreed = Vec::new();
        for info in segmentsToBeFreed.values() {
            // TODO any segment being freed should have its bloom filter removed
            // from the blooms cache.
            blocksToBeFreed.push_all(&info.blocks);
        }
        match oldHeaderOverflow {
            Some(blk) => blocksToBeFreed.push(blk),
            None => (),
        }
        self.addFreeBlocks(&mut space, blocksToBeFreed);

        // note that we intentionally do not release the writeLock here.
        // you can change the segment list more than once while holding
        // the writeLock.  the writeLock gets released when you Dispose() it.
        Ok(age_of_new_segment)
    }

}

impl IPages for InnerPart {
    fn PageSize(&self) -> usize {
        self.pgsz
    }

    fn Begin(&self) -> Result<PendingSegment> {
        let mut lck = try!(self.nextSeg.lock());
        let p = PendingSegment::new(lck.nextSeg);
        lck.nextSeg = lck.nextSeg + 1;
        Ok(p)
    }

    fn GetBlock(&self, ps: &mut PendingSegment) -> Result<PageBlock> {
        let mut space = try!(self.space.lock());
        // specificSize=0 means we don't care how big of a block we get
        let blk = self.getBlock(&mut space, 0);
        ps.AddBlock(blk);
        Ok(blk)
    }

    fn End(&self, ps: PendingSegment, unused_page: PageNum, root_page: PageNum) -> Result<SegmentNum> {
        let (g, blocks, leftovers) = ps.End(unused_page);
        assert!(!block_list_contains_page(&blocks, unused_page));
        assert!(block_list_contains_page(&blocks, root_page));
        let info = SegmentInfo {
            root_page: root_page,

            // age is set to 0 here and changed later for merge segments
            age: 0,
            blocks: blocks,
        };
        let mut waiting = try!(self.segmentsInWaiting.lock());
        let mut space = try!(self.space.lock());
        waiting.segmentsInWaiting.insert(g, info);
        //printfn "wrote %A: %A" g blocks
        match leftovers {
            Some(b) => self.addFreeBlocks(&mut space, vec![b]),
            None => ()
        }
        Ok(g)
    }

}

// ----------------------------------------------------------------

/*

type Database(_io:IDatabaseFile, _settings:DbSettings) =

    let doAutoMerge() = 
        if settings.AutoMergeEnabled then
            for level in 0 .. 3 do // TODO max merge level immediate
                match getPossibleMerge level settings.AutoMergeMinimumPages false with
                | Some f -> 
                    let g = f()
                    commitMerge g
                | None -> 
                    () // printfn "cannot merge level %d" level
            for level in 4 .. 7 do // TODO max merge level
                match getPossibleMerge level settings.AutoMergeMinimumPages false with
                | Some f -> 
                    f |> wrapMergeForLater |> startBackgroundMergeJob
                | None -> 
                    () // printfn "cannot merge level %d" level

        member this.ForgetWaitingSegments(guids:seq<Guid>) =
            // TODO need a test case for this
            let guidsAsSet = Seq.fold (fun acc g -> Set.add g acc) Set.empty guids
            let mySegmentsInWaiting = Map.filter (fun g _ -> Set.contains g guidsAsSet) segmentsInWaiting
            lock critSectionSegmentsInWaiting (fun () ->
                let remainingSegmentsInWaiting = Map.filter (fun g _ -> Set.contains g guidsAsSet |> not) segmentsInWaiting
                segmentsInWaiting <- remainingSegmentsInWaiting
            )
            lock critSectionCursors (fun () -> 
                let segmentsToBeFreed = Map.filter (fun g _ -> not (Map.containsKey g cursors)) mySegmentsInWaiting
                let blocksToBeFreed = Seq.fold (fun acc info -> info.blocks @ acc) List.empty (Map.values segmentsToBeFreed)
                addFreeBlocks blocksToBeFreed
            )

        member this.OpenSegmentCursor(g:Guid) =
            let csr = lock critSectionCursors (fun () ->
                let h = header
                getCursor h.segments g (Some checkForGoneSegment)
            )
            csr

        member this.GetFreeBlocks() = freeBlocks

        member this.PageSize() = pgsz

        member this.ListSegments() =
            (header.currentState, header.segments)

        member this.RequestWriteLock(timeout:int) =
            // TODO need a test case for this
            getWriteLock false timeout (Some doAutoMerge)

        member this.RequestWriteLock() =
            getWriteLock false (-1) (Some doAutoMerge)

    type PairBuffer(_db:IDatabase, _limit:int) =
        let db = _db
        let limit = _limit
        let d = System.Collections.Generic.Dictionary<byte[],Blob>()
        let mutable segs = []
        let emptyByteArray:byte[] = Array.empty
        let emptyBlobValue = Blob.Array emptyByteArray

        member this.Flush() =
            if d.Count > 0 then
                let g = db.WriteSegment(d)
                segs <- g :: segs
                d.Clear()

        member this.AddPair(k:byte[], v:Blob) =
            // TODO dictionary deals with byte[] keys by reference.
            d.[k] <- v
            if d.Count >= limit then
                this.Flush()

        member this.AddEmptyKey(k:byte[]) =
            this.AddPair(k, emptyBlobValue)

        member this.Commit(tx:IWriteLock) =
            tx.CommitSegments segs
            segs <- []
*/

#[cfg(test)]
mod tests {
    use std;
    use super::Result;
    use super::misc;

    #[test]
    fn it_works() {
    }

    #[test]
    #[ignore]
    fn quick() {
        fn tempfile(base: &str) -> String {
            std::fs::create_dir("tmp");
            let file = "tmp/".to_string() + base + "_" + &misc::tid();
            file
        }

        fn f() -> Result<()> {
            //println!("running");
            let db = try!(super::db::new(tempfile("quick"), super::DEFAULT_SETTINGS));

            const NUM : usize = 100000;

            let mut a = Vec::new();
            for i in 0 .. 10 {
                let g = try!(db.WriteSegmentFromSortedSequence(super::GenerateNumbers {cur: i * NUM, end: (i+1) * NUM, step: i+1}, NUM / (i + 1)));
                a.push(g);
            }
            {
                let lck = try!(db.GetWriteLock());
                try!(lck.commitSegments(a.clone()));
            }
            let g3 = try!(db.merge(0, 0, 2, 32));
            assert!(g3.is_some());
            let g3 = g3.unwrap();
            {
                let lck = try!(db.GetWriteLock());
                try!(lck.commitMerge(g3));
            }

            Ok(())
        }
        assert!(f().is_ok());
    }

}

pub struct GenerateNumbers {
    pub cur: usize,
    pub end: usize,
    pub step: usize,
}

impl Iterator for GenerateNumbers {
    type Item = Result<kvp>;
    // TODO allow the number of digits to be customized?
    fn next(&mut self) -> Option<Result<kvp>> {
        if self.cur > self.end {
            None
        }
        else {
            let k = format!("{:08}", self.cur).into_bytes().into_boxed_slice();
            let v = format!("{}", self.cur * 2).into_bytes().into_boxed_slice();
            let r = kvp{Key:k, Value:Blob::Array(v)};
            self.cur = self.cur + self.step;
            Some(Ok(r))
        }
    }
}

pub struct GenerateWeirdPairs {
    pub cur: usize,
    pub end: usize,
    pub klen: usize,
    pub vlen: usize,
}

impl Iterator for GenerateWeirdPairs {
    type Item = Result<kvp>;
    fn next(&mut self) -> Option<Result<kvp>> {
        if self.cur > self.end {
            None
        }
        else {
            fn get_weird(i: usize) -> u8 {
                let f = i as f64;
                let f = f.sin() * 1000.0;
                let f = f.abs();
                let f = f.floor() as u32;
                let f = f & 0xff;
                let f = f as u8;
                f
            }

            let mut k = Vec::new();
            for i in 0 .. self.klen {
                k.push(get_weird(i + self.cur));
            }
            let k = k.into_boxed_slice();

            let mut v = Vec::new();
            for i in 0 .. self.vlen {
                v.push(get_weird(i * 2 + self.cur));
            }
            let v = v.into_boxed_slice();

            let r = kvp{Key:k, Value:Blob::Array(v)};
            self.cur = self.cur + 1;
            Some(Ok(r))
        }
    }
}

