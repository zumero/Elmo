/*
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

use std::collections::BTreeMap;
use std::collections::HashMap;
use std::collections::HashSet;

const SIZE_32: usize = 4; // like std::mem::size_of::<u32>()
const SIZE_16: usize = 2; // like std::mem::size_of::<u16>()

// all new segments start at level 0.
//
// level 0 size limit is 0 because it is unused, because promotion
// out of level 0 is not based on a size threshold.
//
// final level size limit is 0 because it is unused, because nothing ever
// gets promoted out of the last level.
const LEVEL_SIZE_LIMITS_IN_KB: [u64; 4] = [0, 400, 40000, 0];

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

#[derive(Debug)]
pub enum MergePromotionRule {
    Promote,
    Stay,
    Threshold(usize),
}

// kvp is the struct used to provide key-value pairs downward,
// for storage into the database.
struct kvp {
    Key: Box<[u8]>,
    Value: Blob,
}

#[derive(Debug)]
struct PendingSegment {
    blockList: Vec<PageBlock>,
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
    pub fn new(first: PageNum, last: PageNum) -> PageBlock {
        assert!(first <= last);
        PageBlock { firstPage: first, lastPage: last }
    }

    pub fn count_pages(&self) -> PageNum {
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
    fn End(&self, token: PendingSegment, unused_page: PageNum, root_page: PageNum) -> Result<SegmentLocation>;
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
    fn from_cursor(csr: &ICursor, k: &KeyRef) -> Result<SeekResult> {
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
    pub DefaultPageSize: usize,
    pub PagesPerBlock: PageNum,
    pub RangeSplits: usize,
}

pub const DEFAULT_SETTINGS: DbSettings = 
    DbSettings {
        DefaultPageSize: 4096,
        PagesPerBlock: 256,
        RangeSplits: 4,
    };

#[derive(Debug,Clone)]
pub struct SegmentLocation {
    root_page: PageNum,
    // TODO does this grow?  shouldn't it be a boxed array?
    // yes, but then derive clone complains.
    // ideally we could just stop cloning this struct.
    blocks: Vec<PageBlock> 
}

impl SegmentLocation {
    pub fn new(root_page: PageNum, blocks: Vec<PageBlock>) -> Self {
        assert!(block_list_contains_page(&blocks, root_page));
        SegmentLocation {
            root_page: root_page,
            blocks: blocks,
        }
    }

    pub fn count_pages(&self) -> usize {
        self.blocks.iter().map(|pb| pb.count_pages() as usize).sum()
    }

    fn contains_page(&self, pgnum: PageNum) -> bool {
        for blk in self.blocks.iter() {
            if blk.contains_page(pgnum) {
                return true;
            }
        }
        return false;
    }

}

#[derive(Debug,Clone)]
pub struct SegmentInfo {
    level: u32,
    location: SegmentLocation,
}

impl SegmentInfo {
    pub fn count_pages(&self) -> usize {
        self.location.count_pages()
    }
}

// TODO why is this pub?
// TODO why is this even a module?
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

    fn PutVarint(&mut self, ov: u64) {
        varint::write(&mut *self.buf, &mut self.cur, ov);
    }

}

#[derive(PartialEq,Copy,Clone)]
enum Direction {
    // TODO why do we need to assign these specific values?
    Forward = 0,
    Backward = 1,
    Wandering = 2,
}

struct MultiCursor { 
    subcursors: Box<[ConcatCursor]>, 
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
        self.dir = Direction::Forward;
        if self.subcursors.is_empty() {
            Ok(None)
        } else {
            try!(self.sort(false));
            Ok(self.sorted_first())
        }
    }

    fn findMax(&mut self) -> Result<Option<usize>> {
        self.dir = Direction::Backward; 
        if self.subcursors.is_empty() {
            Ok(None)
        } else {
            try!(self.sort(true));
            Ok(self.sorted_first())
        }
    }

    fn Create(subs: Vec<ConcatCursor>) -> MultiCursor {
        let s = subs.into_boxed_slice();
        let mut sorted = Vec::with_capacity(s.len());
        for i in 0 .. s.len() {
            sorted.push((i, None));
        }
        MultiCursor { 
            subcursors: s, 
            sorted: sorted.into_boxed_slice(), 
            cur: None, 
            dir: Direction::Wandering,
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

                if self.dir == Direction::Forward {
                    // this is the happy case.  each cursor is at most
                    // one step away.

                    // direction is Forward, so we know that every valid cursor
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

                    fn half(dir: Direction, ki: &KeyRef, subs: &mut [ConcatCursor]) -> Result<()> {
                        match dir {
                            Direction::Forward => {
                                unreachable!();
                            },
                            Direction::Backward => {
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
                                                // should never happen, because Backward
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
                            Direction::Wandering => {
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
                    if (self.dir != Direction::Backward) && (icur != j) { 
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
        self.dir = Direction::Wandering;
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

struct ConcatCursor { 
    subcursors: Box<[Option<SegmentCursor>]>, 
    cur: Option<usize>, 
}

impl ConcatCursor {
    fn new(subs: Vec<Option<SegmentCursor>>) -> Self {
        let s = subs.into_boxed_slice();
        ConcatCursor { 
            subcursors: s, 
            cur: None, 
        }
    }

    fn current(&self) -> Option<&SegmentCursor> {
        match self.cur {
            Some(i) => {
                self.subcursors[i].as_ref()
            },
            None => {
                None
            },
        }
    }

    fn forward(&mut self, start: usize) -> Result<()> {
        self.cur = None;
        let mut i = start;
        loop {
            if let Some(ref mut c) = self.subcursors[i] {
                self.cur = Some(i);
                try!(c.First());
                break;
            }
            if i + 1 < self.subcursors.len() {
                i += 1;
            } else {
                break;
            }
        }
        Ok(())
    }

    fn backward(&mut self, start: usize) -> Result<()> {
        self.cur = None;
        let mut i = start;
        loop {
            if let Some(ref mut c) = self.subcursors[i] {
                self.cur = Some(i);
                try!(c.Last());
                break;
            }
            if i > 0 {
                i -= 1;
            } else {
                break;
            }
        }
        Ok(())
    }

}

impl ICursor for ConcatCursor {
    fn IsValid(&self) -> bool {
        match self.current() {
            Some(c) => c.IsValid(),
            None => false
        }
    }

    fn First(&mut self) -> Result<()> {
        self.forward(0)
    }

    fn Last(&mut self) -> Result<()> {
        let len = self.subcursors.len();
        self.backward(len - 1)
    }

    fn KeyRef<'a>(&'a self) -> Result<KeyRef<'a>> {
        match self.current() {
            None => Err(Error::CursorNotValid),
            Some(c) => c.KeyRef(),
        }
    }

    fn ValueRef<'a>(&'a self) -> Result<ValueRef<'a>> {
        match self.current() {
            None => Err(Error::CursorNotValid),
            Some(c) => c.ValueRef(),
        }
    }

    fn ValueLength(&self) -> Result<Option<usize>> {
        match self.current() {
            None => Err(Error::CursorNotValid),
            Some(c) => c.ValueLength(),
        }
    }

    fn Next(&mut self) -> Result<()> {
        match self.cur {
            None => Err(Error::CursorNotValid),
            Some(icur) => {
                if 
                    !{
                        let c = self.subcursors[icur].as_mut().unwrap();
                        try!(c.Next());
                        c.IsValid()
                    } 
                {
                    if icur + 1 < self.subcursors.len() {
                        try!(self.forward(icur + 1));
                    } else {
                        self.cur = None;
                    }
                }
                Ok(())
            },
        }
    }

    fn Prev(&mut self) -> Result<()> {
        match self.cur {
            None => Err(Error::CursorNotValid),
            Some(icur) => {
                if
                    !{
                        let c = self.subcursors[icur].as_mut().unwrap();
                        try!(c.Prev());
                        c.IsValid()
                    }
                {
                    if icur > 0 {
                        try!(self.backward(icur - 1));
                    } else {
                        self.cur = None;
                    }
                }
                Ok(())
            },
        }
    }

    fn SeekRef(&mut self, k: &KeyRef, sop: SeekOp) -> Result<SeekResult> {
        self.cur = None;
        // TODO encapsulate mapping of keys to ranges
        let b = try!(k.u8_at(0));
        let i = (b as usize) * self.subcursors.len() / 256;
        if let Some(ref mut c) = self.subcursors[i] {
            self.cur = Some(i);
            c.SeekRef(k, sop)
        } else {
            self.cur = None;
            Ok(SeekResult::Invalid)
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
    behind: Vec<SegmentCursor>,
}

impl FilterTombstonesCursor {
    fn can_skip(&mut self) -> Result<bool> {
        if self.chain.IsValid() && try!(self.chain.ValueLength()).is_none() {
            let k = try!(self.chain.KeyRef());
            // TODO would it be faster to just keep behind moving Next() along with chain?
            // then we could optimize cases where we already know that the key is not present
            // in behind because, for example, we hit the max key in behind already.

            for mut cursor in self.behind.iter_mut() {
                if SeekResult::Equal == try!(cursor.SeekRef(&k, SeekOp::SEEK_EQ)) {
                    // TODO if the value was found but it is another tombstone, then it is actually
                    // not found
                    return Ok(false);
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

    fn new(ch: MultiCursor, behind: Vec<SegmentCursor>) -> FilterTombstonesCursor {
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
struct pgitem {
    page: PageNum,
    first_key: Box<[u8]>,
    last_key: Box<[u8]>,
}

struct ParentState {
    sofar: usize,
    start: usize,
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

fn create_segment<I, SeekWrite>(fs: &mut SeekWrite, 
                                                            pageManager: &IPages, 
                                                            source: I,
                                                           ) -> Result<SegmentLocation> where I: Iterator<Item=Result<kvp>>, SeekWrite: Seek+Write {

    fn write_overflow<SeekWrite>(startingBlock: PageBlock, 
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

    // TODO the tuple return value of this func has gotten out of hand
    fn write_leaves<I,SeekWrite>(leavesBlk: PageBlock,
                                pageManager: &IPages,
                                source: I,
                                vbuf: &mut [u8],
                                fs: &mut SeekWrite, 
                                pb: &mut PageBuilder,
                                token: &mut PendingSegment,
                                ) -> Result<(PageBlock, Vec<pgitem>, PageNum, usize, usize, u64, u64)> where I: Iterator<Item=Result<kvp>> , SeekWrite : Seek+Write {
        // 2 for the page type and flags
        // 4 for the prev page
        // 2 for the stored count
        // 4 for lastInt32 (which isn't in pb.Available)
        const LEAF_PAGE_OVERHEAD: usize = 2 + 4 + 2 + 4;

        // returns the first and last key in the leaf.  if there is only one key
        // in the leaf, it will return two copies of it, which is sad, but that
        // case should be considered pathological.
        fn build_leaf(st: &mut LeafState, pb: &mut PageBuilder) -> (Box<[u8]>, Box<[u8]>) {
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
                        // inline key len is stored * 2, always an even number
                        pb.PutVarint((lp.key.len() * 2) as u64);
                        pb.PutArray(&lp.key[prefixLen .. lp.key.len()]);
                    },
                    KeyLocation::Overflowed(kpage) => {
                        // overflowed key len is stored * 2 + 1, always odd
                        pb.PutVarint((lp.key.len() * 2 + 1) as u64);
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

            // deal with the first key separately
            let lp = st.keys_in_this_leaf.remove(0); 
            assert!(st.keys_in_this_leaf.len() == count_keys_in_this_leaf - 1);
            f(pb, st.prefixLen, &lp);
            let first_key = lp.key;

            if st.keys_in_this_leaf.len() == 0 {
                // there was only one key in this leaf.
                let last_key = first_key.clone();
                (first_key, last_key)
            } else {
                if st.keys_in_this_leaf.len() > 1 {
                    // deal with all the remaining keys except the last one
                    for lp in st.keys_in_this_leaf.drain(0 .. count_keys_in_this_leaf - 2) {
                        f(pb, st.prefixLen, &lp);
                    }
                }
                assert!(st.keys_in_this_leaf.len() == 1);

                // now the last key
                let lp = st.keys_in_this_leaf.remove(0); 
                assert!(st.keys_in_this_leaf.is_empty());
                f(pb, st.prefixLen, &lp);

                let last_key = lp.key;
                (first_key, last_key)
            }
        }

        fn writeLeaf<SeekWrite>(st: &mut LeafState, 
                                isRootPage: bool, 
                                pb: &mut PageBuilder, 
                                fs: &mut SeekWrite, 
                                pgsz: usize,
                                pageManager: &IPages,
                                token: &mut PendingSegment,
                               ) -> Result<()> where SeekWrite : Seek+Write { 
            let (first_key, last_key) = build_leaf(st, pb);
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
            let pg = pgitem {
                page: thisPageNumber, 
                first_key: first_key,
                last_key: last_key
            };
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
            - varint::space_needed_for((pgsz * 2) as u64) // approx worst case inline key len
            - 1 // value flags
            - 9 // worst case varint value len
            - NEEDED_FOR_OVERFLOW_PAGE_NUMBER; // overflowed value page

        fn kLocNeed(k: &[u8], kloc: &KeyLocation, prefixLen: usize) -> usize {
            let klen = k.len();
            match *kloc {
                KeyLocation::Inline => {
                    0
                    + varint::space_needed_for((klen * 2) as u64) 
                    + klen 
                    - prefixLen
                },
                KeyLocation::Overflowed(_) => {
                    0
                    + varint::space_needed_for((klen * 2 + 1) as u64) 
                    + NEEDED_FOR_OVERFLOW_PAGE_NUMBER
                },
            }
        }

        // TODO this could be a method on ValueLocation
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
        let mut total_size_keys = 0;
        let mut total_size_values = 0;

        for result_pair in source {
            count_keys += 1;

            let mut pair = try!(result_pair);
            total_size_keys += pair.Key.len() as u64;

            let k = pair.Key;
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

            let (blkAfterKey, kloc) = 
                if k.len() <= maxKeyInline {
                    (st.blk, KeyLocation::Inline)
                } else {
                    let vPage = st.blk.firstPage;
                    let (_,newBlk) = try!(write_overflow(st.blk, &mut &*k, pageManager, token, fs));
                    (newBlk, KeyLocation::Overflowed(vPage))
                };

            let maxValueInline = {
                // the max limit of an inline value is when the key is inline
                // on a new page.

                let needed_for_key_inline_on_new_page = 
                    LEAF_PAGE_OVERHEAD 
                    + 1 // prefixLen
                    + varint::space_needed_for((k.len() * 2) as u64)
                    + k.len() 
                    + 1 // value flags
                    ;

                if pgsz > needed_for_key_inline_on_new_page {
                    let available = pgsz - needed_for_key_inline_on_new_page;
                    let neededForVarintLen = varint::space_needed_for(available as u64);
                    if available > neededForVarintLen {
                        available - neededForVarintLen
                    } else {
                        0
                    }
                } else {
                    0
                }
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
                                        let (len, newBlk) = try!(write_overflow(blkAfterKey, &mut *strm, pageManager, token, fs));
                                        (newBlk, ValueLocation::Overflowed(len, valuePage))
                                    },
                                    Blob::Array(a) => {
                                        if a.is_empty() {
                                            // TODO maybe we need ValueLocation::Empty
                                            (blkAfterKey, ValueLocation::Buffer(a))
                                        } else {
                                            let valuePage = blkAfterKey.firstPage;
                                            let strm = a; // TODO need a Read for this
                                            let (len,newBlk) = try!(write_overflow(blkAfterKey, &mut &*strm, pageManager, token, fs));
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
                                            let (len,newBlk) = try!(write_overflow(blkAfterKey, &mut (vbuf.chain(strm)), pageManager, token, fs));
                                            (newBlk, ValueLocation::Overflowed (len, valuePage))
                                        }
                                    },
                                    Blob::Array(a) => {
                                        if a.len() < maxValueInline {
                                            (blkAfterKey, ValueLocation::Buffer(a))
                                        } else {
                                            let valuePage = blkAfterKey.firstPage;
                                            let (len,newBlk) = try!(write_overflow(blkAfterKey, &mut &*a, pageManager, token, fs));
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
                                    let (len,newBlk) = try!(write_overflow(blkAfterKey, &mut *strm, pageManager, token, fs));
                                    (newBlk, ValueLocation::Overflowed(len, valuePage))
                                },
                                Blob::Array(a) => {
                                    if a.is_empty() {
                                        // TODO maybe we need ValueLocation::Empty
                                        (blkAfterKey, ValueLocation::Buffer(a))
                                    } else {
                                        let valuePage = blkAfterKey.firstPage;
                                        let (len,newBlk) = try!(write_overflow(blkAfterKey, &mut &*a, pageManager, token, fs));
                                        (newBlk, ValueLocation::Overflowed(len, valuePage))
                                    }
                                }
                            }
                         }
                    }
            };

            let len_value =
                match vloc {
                    ValueLocation::Tombstone => {
                        0
                    },
                    ValueLocation::Buffer(ref vbuf) => {
                        vbuf.len() as u64
                    },
                    ValueLocation::Overflowed(vlen,_) => {
                        vlen as u64
                    },
                };
            total_size_values += len_value;

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
                        key: k,
                        kLoc: kloc,
                        vLoc: vloc,
                        };

            st.sofarLeaf=sofar + leafPairSize(newPrefixLen, &lp);
            st.keys_in_this_leaf.push(lp);
            st.prefixLen=newPrefixLen;
        }

        if !st.keys_in_this_leaf.is_empty() {
            let isRootNode = st.leaves.is_empty();
            try!(writeLeaf(&mut st, isRootNode, pb, fs, pgsz, pageManager, &mut *token));
        }
        Ok((st.blk, st.leaves, st.firstLeaf, count_keys, count_tombstones, total_size_keys, total_size_values))
    }

    fn write_parent_nodes<SeekWrite>(startingBlk: PageBlock, 
                                   children: &Vec<pgitem>,
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

        fn build_parent_page(
                          children: &Vec<pgitem>,
                          first_child_included: usize,
                          first_child_after: usize,
                          overflows: &HashMap<usize, PageNum>,
                          pb : &mut PageBuilder,
                          ) -> (Box<[u8]>, Box<[u8]>) {
            pb.Reset();
            pb.PutByte(PageType::PARENT_NODE.to_u8());
            pb.PutByte(0u8);
            pb.PutInt16((first_child_after - first_child_included) as u16);

            let first_key = children[first_child_included + 1].first_key.clone();
            let last_key = children[first_child_after].first_key.clone();

            // store all the keys, n of them
            for i in first_child_included .. first_child_after {
                let i_next = i + 1;
                let key = &children[i_next].first_key;
                match overflows.get(&i_next) {
                    Some(pg) => {
                        // overflowed key len is stored * 2 + 1, always an odd number
                        pb.PutVarint((key.len() * 2 + 1) as u64);
                        pb.PutInt32(*pg as PageNum);
                    },
                    None => {
                        // inline key len is stored * 2, always an even number
                        pb.PutVarint((key.len() * 2) as u64);
                        pb.PutArray(key);
                    },
                }
            }
            // store all the ptrs, n+1 of them
            for i in first_child_included .. first_child_after + 1 {
                pb.PutVarint(children[i].page as u64);
            }

            (first_key, last_key)
        }

        fn write_parent_page<SeekWrite>(st: &mut ParentState, 
                                      children: &Vec<pgitem>,
                                      first_child_after: usize,
                                      overflows: &HashMap<usize,PageNum>,
                                      pb: &mut PageBuilder, 
                                      fs: &mut SeekWrite,
                                      pageManager: &IPages,
                                      pgsz: usize,
                                      token: &mut PendingSegment,
                                      root: Option<&Vec<u8>>,
                                     ) -> Result<()> where SeekWrite : Seek+Write {
            // assert st.sofar > 0
            let thisPageNumber = st.blk.firstPage;
            let (first_key, last_key) = build_parent_page(children, st.start, first_child_after, &overflows, pb);
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
            let pg = pgitem {
                page: thisPageNumber, 
                first_key: first_key,
                last_key: last_key,
            };
            st.nextGeneration.push(pg);
            Ok(())
        }

        let mut st = ParentState {
            nextGeneration: Vec::new(),
            sofar: 0,
            start: 0,
            blk: startingBlk,
            footer_len: footer.len(),
        };
        let mut overflows = HashMap::new();
        // deal with all the children except the last one
        for i_child in 0 .. children.len() - 1 {
            let this_child = &children[i_child];
            let next_child = &children[i_child + 1];
            let key = &next_child.first_key;

            // to fit this child into this parent page, we need room for the
            // the child's page num, and for the first_key of the next child.

            let neededEitherWay = varint::space_needed_for(this_child.page as u64);
            let neededForInline = neededEitherWay + varint::space_needed_for((key.len() * 2) as u64) + key.len();
            let neededForOverflow = neededEitherWay + varint::space_needed_for((key.len() * 2 + 1) as u64) + SIZE_32;

            let available = calcAvailable(&st, pgsz);
            let fitsInline = available >= neededForInline;
            // TODO the + 4 in the next line is to account for the case where the next
            // page might be a boundary page, thus it would need the 4 bytes in lastint32.
            let wouldFitInlineOnNextPage = (pgsz - PARENT_PAGE_OVERHEAD + 4) >= neededForInline;
            let fitsOverflow = available >= neededForOverflow;
            let writeThisPage = (!fitsInline) && (wouldFitInlineOnNextPage || (!fitsOverflow));

            if writeThisPage {
                assert!(st.sofar > 0);
                assert!(i_child > st.start);
                try!(write_parent_page(&mut st, children, i_child, &overflows, pb, fs, pageManager, pgsz, &mut *token, None));
            }

            if st.sofar == 0 {
                st.sofar = PARENT_PAGE_OVERHEAD;
                st.start = i_child;
            }

            if calcAvailable(&st, pgsz) >= neededForInline {
                st.sofar = st.sofar + neededForInline;
            } else {
                let keyOverflowFirstPage = st.blk.firstPage;
                let (_, newBlk) = try!(write_overflow(st.blk, &mut &**key, pageManager, token, fs));
                st.sofar = st.sofar + neededForOverflow;
                st.blk = newBlk;
                overflows.insert(i_child, keyOverflowFirstPage);
            }
        }

        let root =
            if st.nextGeneration.is_empty() {
                Some(footer)
            } else {
                None
            };
        try!(write_parent_page(&mut st, children, children.len() - 1, &overflows, pb, fs, pageManager, pgsz, &mut *token, root));
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

    let (blk, leaves, firstLeaf, count_keys, count_tombstones, total_size_keys, total_size_values) = try!(write_leaves(blk, pageManager, source, &mut vbuf, fs, &mut pb, &mut token));
    assert!(count_keys > 0);
    assert!(count_keys >= count_tombstones);
    assert!(leaves.len() > 0);

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
            let mut depth = 0;

            let (root_page, blk) = {
                let mut blk = blk;
                let mut children = leaves;
                while children.len() > 1 {
                    depth += 1;

                    let mut footer = vec![];
                    misc::push_varint(&mut footer, firstLeaf as u64);
                    misc::push_varint(&mut footer, lastLeaf as u64);
                    misc::push_varint(&mut footer, count_keys as u64);
                    misc::push_varint(&mut footer, count_tombstones as u64);
                    misc::push_varint(&mut footer, total_size_keys as u64);
                    misc::push_varint(&mut footer, total_size_values as u64);
                    misc::push_varint(&mut footer, depth as u64);
                    // TODO this might be a good place to a checksum hash
                    let len = footer.len();
                    assert!(len <= 255);
                    footer.push(len as u8);

                    // before we write this layer of parent nodes, we trim all the
                    // keys to the shortest prefix that will suffice.

                    for i in 1 .. children.len() {
                        let shorter = {
                            let mut shorter = None;
                            let k = &children[i].first_key;
                            let prev = &children[i - 1].last_key;

                            let mut len = k.len();
                            loop {
                                if len == 0 || Ordering::Greater != bcmp::Compare(&k[ .. len], prev) {
                                    assert!(len < k.len());
                                    shorter = Some(len + 1);
                                    break;
                                }
                                if len > 0 {
                                    len -= 1;
                                } else {
                                    break;
                                }
                            }
                            shorter
                        };

                        if let Some(len) = shorter {
                            if len < children[i].first_key.len() {
                                //println!("can shorten key from {} to {}", children[i].first_key.len(), len);
                                let mut v = Vec::with_capacity(len);
                                v.push_all(&children[i].first_key[ .. len]);
                                children[i].first_key = v.into_boxed_slice();
                            }
                        }
                    }

                    let (newBlk, newChildren) = try!(write_parent_nodes(blk, &children, pgsz, fs, pageManager, &mut token, &footer, &mut pb));
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

struct OverflowReader {
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
    
impl OverflowReader {
    fn new(path: &str, pgsz: usize, firstPage: PageNum, len: usize) -> Result<OverflowReader> {
        // TODO I wonder if maybe we should defer the opening of the file until
        // somebody actually tries to read from it?  so that constructing a
        // ValueRef object (which contains one of these) would be a lighter-weight
        // operation.
        let f = try!(OpenOptions::new()
                .read(true)
                .open(path));
        let mut res = 
            // TODO the vec new below is really slow.  use a pool?
            OverflowReader {
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

impl Read for OverflowReader {
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
    let mut ostrm = try!(OverflowReader::new(path, pgsz, firstPage, buf.len()));
    let res = try!(misc::io::read_fully(&mut ostrm, buf));
    Ok(res)
}

pub struct SegmentCursor {
    path: String,
    f: std::rc::Rc<std::cell::RefCell<File>>,
    done: Option<Box<Fn() -> ()>>,
    location: SegmentLocation,

    pr: misc::Lend<Box<[u8]>>,
    currentPage: PageNum,

    firstLeaf: PageNum,
    lastLeaf: PageNum,
    count_keys: usize,
    count_tombstones: usize,
    total_size_keys: u64,
    total_size_values: u64,
    depth: u32,

    leafKeys: Vec<usize>,
    previousLeaf: PageNum,
    prefix: Option<Box<[u8]>>,

    currentKey: Option<usize>,
}

impl SegmentCursor {
    fn new(path: &str, 
           f: std::rc::Rc<std::cell::RefCell<File>>,
           page: misc::Lend<Box<[u8]>>,
           location: SegmentLocation
          ) -> Result<SegmentCursor> {

        let mut res = SegmentCursor {
            path: String::from(path),
            f: f,
            location: location,
            done: None,
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
            total_size_keys: 0, // temporary
            total_size_values: 0, // temporary
            depth: 0, // temporary
        };

        // TODO consider keeping a copy of the root page around as long as this cursor is around
        let root_page = res.location.root_page;
        try!(res.setCurrentPage(root_page));

        let pt = try!(res.page_type());
        if pt == PageType::LEAF_NODE {
            res.firstLeaf = res.location.root_page;
            res.lastLeaf = res.location.root_page;
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
            assert!(res.location.contains_page(res.firstLeaf));
            res.lastLeaf = varint::read(footer, &mut cur) as u32;
            assert!(res.location.contains_page(res.lastLeaf));
            res.count_keys = varint::read(footer, &mut cur) as usize;
            res.count_tombstones = varint::read(footer, &mut cur) as usize;
            assert!(res.count_keys >= res.count_tombstones);
            res.total_size_keys = varint::read(footer, &mut cur) as u64;
            res.total_size_values = varint::read(footer, &mut cur) as u64;
            res.depth = varint::read(footer, &mut cur) as u32;
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

    pub fn total_size_keys(&self) -> u64 {
        self.total_size_keys
    }

    pub fn total_size_values(&self) -> u64 {
        self.total_size_values
    }

    pub fn depth(&self) -> u32 {
        self.depth
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
        assert!(self.location.contains_page(pgnum));

        if self.currentPage != pgnum {
            self.currentPage = pgnum;

            self.leafKeys.clear();
            self.previousLeaf = 0;
            self.currentKey = None;
            self.prefix = None;

            {
                let f = &mut *(self.f.borrow_mut());
                try!(utils::SeekPage(f, self.pr.len(), self.currentPage));
                try!(misc::io::read_fully(f, &mut self.pr));
            }

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
        let klen = varint::read(&self.pr, cur) as usize;
        let inline = 0 == klen % 2;
        let klen = klen / 2;

        if inline {
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
        let klen = varint::read(&self.pr, &mut cur) as usize;
        let inline = 0 == klen % 2;
        let klen = klen / 2;
        if inline {
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
            let mut ostrm = try!(OverflowReader::new(&self.path, self.pr.len(), pgnum, klen));
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
        cur = cur + 1; // skip the page flags
        let count_keys = self.get_u16(&mut cur);
        let mut found = None;
        for i in 0 .. count_keys {
            let klen = varint::read(&self.pr, &mut cur) as usize;
            let inline = 0 == klen % 2;
            let klen = klen / 2;
            let k =
                if inline {
                    let k = KeyRef::Array(&self.pr[cur .. cur + klen]);
                    cur = cur + klen;
                    k
                } else {
                    let firstPage = self.get_u32(&mut cur) as PageNum;
                    // TODO move the following line outside the loop?
                    let pgsz = self.pr.len();
                    let mut ostrm = try!(OverflowReader::new(&self.path, pgsz, firstPage, klen));
                    let mut x_k = Vec::with_capacity(klen);
                    try!(ostrm.read_to_end(&mut x_k));
                    let x_k = x_k.into_boxed_slice();
                    let k = KeyRef::Overflowed(x_k);
                    k
                };
            let cmp = KeyRef::cmp(kq, &k);
            if cmp == Ordering::Less {
                found = Some(i);
                break;
            }
        }
        match found {
            None => {
            },
            Some(found) => {
                // gotta skip the rest of the keys
                for _ in found + 1 .. count_keys {
                    let klen = varint::read(&self.pr, &mut cur) as usize;
                    let inline = 0 == klen % 2;
                    let klen = klen / 2;
                    if inline {
                        cur = cur + klen;
                    } else {
                        // the page num for overflow is a u32
                        // TODO why not a varint?
                        cur = cur + 4;
                    };
                }
            },
        }
        let found = found.unwrap_or(count_keys);
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
                            } else if self.currentPage == self.location.root_page { 
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
            assert!(next != pg);
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
        let root_page = self.location.root_page;
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
                        let strm = try!(OverflowReader::new(&self.path, self.pr.len(), pgnum, vlen));
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
                    if self.currentPage == self.location.root_page { 
                        0 
                    } else { 
                        self.currentPage + 1 
                    }
                } else { 
                    0 
                };
            if 0 == nextPage {
                self.currentKey = None;
            } else if !self.location.contains_page(nextPage) {
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
pub struct RangeState {
    pub state: Vec<SegmentNum>,
}

impl RangeState {
    fn new() -> Self {
        RangeState {
            state: vec![],
        }
    }
}

#[derive(Clone)]
struct HeaderData {
    // for range splitting, each key range has its own current_state.
    // each range can be merged independently.  
    // cursors become more complicated, as we need to view all the segments
    // in one horizontal row as a single segment.  ConcatCursor does this.

    // TODO could be a boxed slice
    state: Vec<RangeState>,
    segments_info: HashMap<SegmentNum, SegmentInfo>,
    next_segnum: SegmentNum,
    changeCounter: u64,
    mergeCounter: u64,
}

// TODO how big should the header be?  this defines the minimum size of a
// database file.
const HEADER_SIZE_IN_BYTES: usize = 4096;

impl PendingSegment {
    fn new() -> PendingSegment {
        PendingSegment {
            // TODO maybe set capacity of the blocklist vec to something low
            blockList: Vec::new(), 
        }
    }

    fn AddBlock(&mut self, b: PageBlock) {
        //println!("seg {:?} got block {:?}", self.segnum, b);
        let len = self.blockList.len();
        if (! (self.blockList.is_empty())) && (b.firstPage == self.blockList[len - 1].lastPage+1) {
            // note that by consolidating blocks here, the segment info list will
            // not have information about the fact that the two blocks were
            // originally separate.  that's okay, since all we care about here is
            // keeping track of which pages are used.  but the btree code itself
            // is still treating the last page of the first block as a boundary
            // page, even though its pointer to the next block goes to the very
            // next page, because its page manager happened to give it a block
            // which immediately follows the one it had.
            self.blockList[len - 1].lastPage = b.lastPage;
            assert!(self.blockList[len - 1].firstPage <= self.blockList[len - 1].lastPage);
        } else {
            self.blockList.push(b);
        }
    }

    fn End(mut self, unused_page: PageNum) -> (Vec<PageBlock>, Option<PageBlock>) {
        let len = self.blockList.len();
        assert!(self.blockList[len - 1].contains_page(unused_page));
        let leftovers = {
            if unused_page > self.blockList[len - 1].firstPage {
                let givenLastPage = self.blockList[len - 1].lastPage;
                self.blockList[len - 1].lastPage = unused_page - 1;
                assert!(self.blockList[len - 1].firstPage <= self.blockList[len - 1].lastPage);
                Some (PageBlock::new(unused_page, givenLastPage))
            } else {
                // this is one of those dorky cases where we they asked for a block
                // and never used any of it.  TODO
                let blk = self.blockList.pop().unwrap();
                Some(blk)
            }
        };
        // consume self return blockList
        (self.blockList, leftovers)
    }
}

fn read_header(path: &str) -> Result<(HeaderData, usize, PageNum)> {
    fn read<R>(fs: &mut R) -> Result<Box<[u8]>> where R : Read {
        let mut pr = vec![0; HEADER_SIZE_IN_BYTES].into_boxed_slice();
        let got = try!(misc::io::read_fully(fs, &mut pr));
        if got < HEADER_SIZE_IN_BYTES {
            Err(Error::CorruptFile("invalid header"))
        } else {
            Ok(pr)
        }
    }

    fn parse(pr: &Box<[u8]>, cur: &mut usize) -> Result<(HeaderData, usize)> {
        fn readSegmentList(pr: &Box<[u8]>, cur: &mut usize) -> Result<(Vec<RangeState>, HashMap<SegmentNum, SegmentInfo>)> {
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

            let count_ranges = varint::read(&pr, cur) as usize;
            let mut ranges = Vec::with_capacity(count_ranges);
            let mut m = HashMap::new();
            for _ in 0 .. count_ranges {
                let count_segments_in_range = varint::read(&pr, cur) as usize;
                let mut range_segments = Vec::with_capacity(count_segments_in_range);
                for _ in 0 .. count_segments_in_range {
                    let g = varint::read(&pr, cur) as SegmentNum;
                    range_segments.push(g);
                    let root_page = varint::read(&pr, cur) as PageNum;
                    let blocks = readBlockList(pr, cur);
                    let level = varint::read(&pr, cur) as u32;
                    if !block_list_contains_page(&blocks, root_page) {
                        return Err(Error::RootPageNotInSegmentBlockList);
                    }

                    let location = SegmentLocation {
                        root_page: root_page,
                        blocks: blocks
                    };
                    let info = SegmentInfo {
                        location: location,
                        level: level,
                    };
                    m.insert(g,info);
                }
                let range = RangeState {
                    state: range_segments,
                };
                ranges.push(range);
            }
            Ok((ranges, m))
        }

        // --------

        let pgsz = misc::buf_advance::get_u32(&pr, cur) as usize;
        let changeCounter = varint::read(&pr, cur);
        let mergeCounter = varint::read(&pr, cur);
        let next_segnum = varint::read(&pr, cur);

        let (state, segments_info) = try!(readSegmentList(pr, cur));

        let hd = 
            HeaderData {
                state: state,
                segments_info: segments_info,
                changeCounter: changeCounter,
                mergeCounter: mergeCounter,
                next_segnum: next_segnum,
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

    let len = try!(fs.metadata()).len();
    if len > 0 {
        try!(fs.seek(SeekFrom::Start(0 as u64)));
        let pr = try!(read(&mut fs));
        let mut cur = 0;
        let (h, pgsz) = try!(parse(&pr, &mut cur));
        let nextAvailablePage = calcNextPage(pgsz, len as usize);
        Ok((h, pgsz, nextAvailablePage))
    } else {
        // TODO shouldn't this use settings passed in?
        let defaultPageSize = DEFAULT_SETTINGS.DefaultPageSize;
        let h = {
            let mut ranges = vec![];
            for _ in 0 .. DEFAULT_SETTINGS.RangeSplits {
                ranges.push(RangeState::new());
            }
            HeaderData {
                segments_info: HashMap::new(),
                state: ranges,
                changeCounter: 0,
                mergeCounter: 0,
                next_segnum: 1,
            }
        };
        let nextAvailablePage = calcNextPage(defaultPageSize, HEADER_SIZE_IN_BYTES);
        Ok((h, defaultPageSize, nextAvailablePage))
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
            if blocks[i - 1].lastPage+1 == blocks[i].firstPage {
                blocks[i - 1].lastPage = blocks[i].lastPage;
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
    for i in 0 .. len - 1 {
        result[i].firstPage = result[i].lastPage+1;
        result[i].lastPage = result[i+1].firstPage-1;
        assert!(result[i].firstPage <= result[i].lastPage);
    }
    // this function finds the space between the blocks.
    // the last block didn't get touched, and is still a block in use.
    // so remove it.
    result.remove(len - 1);
    result
}

fn listAllBlocks(h: &HeaderData, pgsz: usize) -> Vec<PageBlock> {
    let mut blocks = Vec::new();

    let headerBlock = PageBlock::new(1, (HEADER_SIZE_IN_BYTES / pgsz) as PageNum);
    blocks.push(headerBlock);

    for info in h.segments_info.values() {
        for b in info.location.blocks.iter() {
            blocks.push(*b);
        }
    }

    blocks
}

use std::sync::Mutex;
use std::sync::RwLock;

#[derive(Debug)]
struct Space {
    nextPage: PageNum,
    freeBlocks: Vec<PageBlock>,

    nextCursorNum: u64,
    cursors: HashMap<u64, SegmentNum>,

    // a zombie segment is one that was replaced by a merge, but
    // when the merge was done, it could not be reclaimed as free
    // blocks because there was an open cursor on it.
    zombie_segments: HashMap<SegmentNum, SegmentInfo>,
}

pub struct PendingMerge {
    range: usize,
    old_segments: Vec<SegmentNum>,
    merge_level: u32,
    new_segment: Option<SegmentInfo>,
}

struct SafeMergeStuff {
    // TODO can we design a way to not need the following?
    // it keeps track of which segments are being merged,
    // so we don't try to merge something that is already being merged.
    merging: HashSet<SegmentNum>,
}

struct SafePagePool {
    // we keep a pool of page buffers so we can lend them to
    // SegmentCursors.
    pages: Vec<Box<[u8]>>,
}

// there can be only one InnerPart instance per path
struct InnerPart {
    path: String,
    pgsz: usize,
    settings: DbSettings,

    // TODO count_ranges is only here so we can know how
    // many ranges there are without locking the header.
    count_ranges: usize,

    // TODO are we concerned here about readers starving the
    // writers?  In other words, so many cursors that a merge
    // cannot get committed?
    header: RwLock<HeaderData>,

    space: Mutex<Space>,
    mergeStuff: Mutex<SafeMergeStuff>,
    pagepool: Mutex<SafePagePool>,
}

enum AutomergeMessage {
    NewSegment(usize, SegmentNum, u32),
    Terminate,
}

pub struct WriteLock {
    inner: std::sync::Arc<InnerPart>,
    notify_automerge: Vec<mpsc::Sender<AutomergeMessage>>,
}

impl WriteLock {
    // TODO name.  this is now multiple segments, because of range splits.  generation?
    pub fn commit_segment(&self, set: Vec<Option<SegmentLocation>>) -> Result<()> {
        let segnums = try!(self.inner.commit_segment(set));
        for (rangenum, seg) in segnums.into_iter().enumerate() {
            if let Some(segnum) = seg {
                // TODO note that all ranges within a level share a single automerge thread
                try!(self.notify_automerge[0].send(AutomergeMessage::NewSegment(rangenum, segnum, 0)).map_err(wrap_err));
            }
        }
        Ok(())
    }

    pub fn commit_merge(&self, pm: PendingMerge) -> Result<()> {
        // TODO the following temp var is dorky
        let rangenum = pm.range;
        let notify =
            match pm.new_segment {
                Some(ref info) => {
                    if info.level == pm.merge_level {
                        // we only want to notify if this was a promotion.
                        // this merge was just cleaning up a level and
                        // leaving the resulting segment in that same level.
                        None
                    } else {
                        // this merge resulted in a segment getting promoted
                        // to the next level.  need to notify that level,
                        // because it might need a merge now.
                        Some(info.level)
                    }
                },
                None => {
                    // this merge did not result in a segment.  this happens
                    // because tombstones.
                    None
                },
            };
        let new_segnum = try!(self.inner.commit_merge(pm));
        match notify {
            Some(level) => {
                // the unwrap in the following line is correct.
                // if notify.is_some(), then commit_merge() has to
                // return a segment number.
                let new_segnum = new_segnum.unwrap();

                // nothing gets "promoted" to level 0.
                // new segments start in level 0
                assert!(level > 0);
                assert!((level as usize) < self.notify_automerge.len());
                // TODO note that all ranges within a level share a single automerge thread
                try!(self.notify_automerge[level as usize].send(AutomergeMessage::NewSegment(rangenum, new_segnum, level as u32)).map_err(wrap_err));
            },
            None => {
            },
        }
        Ok(())
    }
}

pub struct DatabaseFile {
    inner: std::sync::Arc<InnerPart>,

    // there can be only one of the following per path
    write_lock: Mutex<WriteLock>,
}

impl DatabaseFile {
    pub fn new(path: String, settings: DbSettings) -> Result<std::sync::Arc<DatabaseFile>> {

        // TODO we should pass in settings to read_header, right?
        let (header, pgsz, first_available_page) = try!(read_header(&path));

        // when we first open the file, we find all the blocks that are in use by
        // an active segment.  all OTHER blocks are considered free.
        let mut blocks = listAllBlocks(&header, pgsz);
        consolidateBlockList(&mut blocks);
        //println!("blocks in use: {:?}", blocks);
        let last_page_used = blocks[blocks.len() - 1].lastPage;
        let mut freeBlocks = invertBlockList(&blocks);
        if first_available_page > (last_page_used + 1) {
            let blk = PageBlock::new(last_page_used + 1, first_available_page - 1);
            freeBlocks.push(blk);
            // TODO it is tempting to truncate the file here.  but this might not
            // be the right place.  we should preserve the ability to open a file
            // read-only.
        }
        //println!("free blocks: {:?}", freeBlocks);
        // we want the largest blocks at the front of the list
        freeBlocks.sort_by(|a,b| b.count_pages().cmp(&a.count_pages()));

        let space = Space {
            // TODO maybe we should just ignore the actual end of the file
            // and set nextPage to last_page_used + 1, and not add the block above
            nextPage: first_available_page, 
            freeBlocks: freeBlocks,
            nextCursorNum: 1,
            cursors: HashMap::new(),
            zombie_segments: HashMap::new(),
        };

        let mergeStuff = SafeMergeStuff {
            merging: HashSet::new(),
        };

        let pagepool = SafePagePool {
            pages: vec![],
        };

        // each merge level is handled by its own thread.  a Rust channel is used to
        // notify that thread that there is merge work to be done.

        let mut senders = vec![];
        let mut receivers = vec![];
        for _level in 0 .. LEVEL_SIZE_LIMITS_IN_KB.len() {
            let (tx, rx): (mpsc::Sender<AutomergeMessage>, mpsc::Receiver<AutomergeMessage>) = mpsc::channel();
            senders.push(tx);
            receivers.push(rx);
        }

        let count_ranges = header.state.len();
        let inner = InnerPart {
            path: path,
            pgsz: pgsz,
            settings: settings, 
            count_ranges: count_ranges,
            header: RwLock::new(header),
            space: Mutex::new(space),
            mergeStuff: Mutex::new(mergeStuff),
            pagepool: Mutex::new(pagepool),
        };

        let inner = std::sync::Arc::new(inner);

        let lck = 
            WriteLock { 
                inner: inner.clone(),
                notify_automerge: senders,
            };

        let db = DatabaseFile {
            inner: inner,
            write_lock: Mutex::new(lck),
        };
        let db = std::sync::Arc::new(db);

        // TODO so when we do send Terminate messages to these threads?
        // impl Drop for DatabaseFile ? 

        for (closure_level, rx) in receivers.into_iter().enumerate() {
            let db = db.clone();
            thread::spawn(move || {
                loop {
                    match rx.recv() {
                        Ok(msg) => {
                            match msg {
                                AutomergeMessage::NewSegment(rangenum, new_segnum, level) => {
                                    assert!(level == (closure_level as u32));
                                    match db.automerge_level(rangenum, new_segnum, level) {
                                        Ok(()) => {
                                        },
                                        Err(e) => {
                                            // TODO what now?
                                            println!("{:?}", e);
                                            panic!();
                                        },
                                    }
                                },
                                AutomergeMessage::Terminate => {
                                    break;
                                },
                            }
                        },
                        Err(e) => {
                            // TODO what now?
                            println!("{:?}", e);
                            panic!();
                        },
                    }
                }
            });

        }

        Ok(db)
    }

    fn automerge_level(&self, rangenum: usize, new_segnum: SegmentNum, level: u32) -> Result<()> {
        assert!((level as usize) < LEVEL_SIZE_LIMITS_IN_KB.len());
        let promotion =
            if level == 0 {
                // all new segments come in at level 0.
                // we want to merge and promote them to level 1 as
                // quickly as possible.
                MergePromotionRule::Promote
            } else if (level as usize) == LEVEL_SIZE_LIMITS_IN_KB.len() - 1 {
                // nothing gets promoted out of the last level.
                MergePromotionRule::Stay
            } else {
                // for all the levels in between, we promote when the
                // level reaches a certain threshold of size.
                let mb = LEVEL_SIZE_LIMITS_IN_KB[level as usize];
                let bytes = mb * 1024;
                let pages = bytes / (self.inner.pgsz as u64);
                MergePromotionRule::Threshold(pages as usize)
            };
        match try!(self.merge(rangenum, level, 2, 8, promotion)) {
            Some(seg) => {
                let lck = try!(self.get_write_lock());
                try!(lck.commit_merge(seg));
            },
            None => {
            },
        }
        Ok(())
    }

    // TODO func to ask for the write lock without blocking?

    pub fn get_write_lock(&self) -> Result<std::sync::MutexGuard<WriteLock>> {
        let lck = try!(self.write_lock.lock());
        Ok(lck)
    }

    // the following methods are passthrus, exposing inner
    // stuff publicly.

    pub fn open_cursor(&self) -> Result<LivingCursor> {
        InnerPart::open_cursor(&self.inner)
    }

    pub fn open_cursor_on_active_segment(&self, n: SegmentNum) -> Result<SegmentCursor> {
        InnerPart::open_cursor_on_active_segment(&self.inner, n)
    }

    pub fn merge_pending_segments(&self, segments: Vec<SegmentLocation>) -> Result<SegmentLocation> {
        InnerPart::merge_pending_segments(&self.inner, segments)
    }

    pub fn open_cursor_on_pending_segment(&self, location: SegmentLocation) -> Result<SegmentCursor> {
        InnerPart::open_cursor_on_pending_segment(&self.inner, location)
    }

    pub fn write_segment(&self, pairs: BTreeMap<Box<[u8]>, Blob>) -> Result<Vec<Option<SegmentLocation>>> {
        self.inner.write_segment(pairs)
    }

    pub fn merge(&self, range: usize, level: u32, min_segs: usize, max_segs: usize, promote: MergePromotionRule) -> Result<Option<PendingMerge>> {
        InnerPart::merge(&self.inner, range, level, min_segs, max_segs, promote)
    }

    pub fn list_segments(&self) -> Result<(Vec<RangeState>, HashMap<SegmentNum, SegmentInfo>)> {
        InnerPart::list_segments(&self.inner)
    }

    pub fn release_pending_segment(&self, location: SegmentLocation) -> Result<()> {
        InnerPart::release_pending_segment(&self.inner, location)
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

    fn return_page_to_pool(&self, page: Box<[u8]>) {
        //println!("return_page_to_pool");
        match self.pagepool.try_lock() {
            Ok(mut pagepool) => {
                //println!("returned a page");
                // TODO arbitrary hard-coded limit
                if pagepool.pages.len() < 100 {
                    pagepool.pages.push(page);
                }
            },
            Err(std::sync::TryLockError::Poisoned(_)) => {
                panic!("poisoned");
            },
            Err(std::sync::TryLockError::WouldBlock) => {
                //println!("could NOT return a page to the pool");
            },
        }
    }

    fn cursor_dropped(&self, segnum: SegmentNum, csrnum: u64) {
        //println!("cursor_dropped");
        let mut space = self.space.lock().unwrap(); // gotta succeed
        let seg = space.cursors.remove(&csrnum).expect("gotta be there");
        assert_eq!(seg, segnum);
        // TODO hey.  actually we can't reclaim this zombie unless we know
        // that the cursor we just dropped was the only cursor on the
        // zombie segment.
        match space.zombie_segments.remove(&segnum) {
            Some(info) => {
                Self::addFreeBlocks(&mut space, &self.path, self.pgsz, info.location.blocks);
            },
            None => {
            },
        }
    }

    fn getBlock(&self, space: &mut Space, specificSizeInPages: PageNum) -> PageBlock {
        if specificSizeInPages > 0 {
            // TODO this code isn't used anymore
            if space.freeBlocks.is_empty() || specificSizeInPages > space.freeBlocks[0].count_pages() {
                let newBlk = PageBlock::new(space.nextPage, space.nextPage + specificSizeInPages - 1);
                space.nextPage = space.nextPage + specificSizeInPages;
                newBlk
            } else {
                let headBlk = space.freeBlocks[0];
                if headBlk.count_pages() > specificSizeInPages {
                    // trim the block to size
                    let blk2 = PageBlock::new(headBlk.firstPage,
                                              headBlk.firstPage + specificSizeInPages - 1); 
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
                let newBlk = PageBlock::new(space.nextPage, space.nextPage + size - 1) ;
                space.nextPage = space.nextPage + size;
//                println!("new block: {:?}  nextPage: {}", newBlk, space.nextPage);
                newBlk
            } else {
                let headBlk = space.freeBlocks[0];
                space.freeBlocks.remove(0);
//                println!("used free block: {:?}", headBlk);
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

    fn open_file_for_cursor(&self) -> io::Result<std::rc::Rc<std::cell::RefCell<File>>> {
        let f = try!(self.OpenForReading());
        let f = std::cell::RefCell::new(f);
        let f = std::rc::Rc::new(f);
        Ok(f)
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

    fn addFreeBlocks(space: &mut Space, path: &str, page_size: usize, blocks:Vec<PageBlock>) -> Result<()> {

        // all additions to the freeBlocks list should happen here
        // by calling this function.
        //
        // the list is kept consolidated and sorted by size descending.
        // unfortunately this requires two sorts, and they happen here
        // inside a critical section.  but the benefit is considered
        // worth the trouble.
        
        // TODO should we instead prefer to give out blocks earlier in
        // the file, rather than giving out the largest blocks?

        // TODO it is important that freeBlocks contains no overlaps.
        // add debug-only checks to verify?

        // TODO is there such a thing as a block that is so small we
        // don't want to bother with it?  what about a single-page block?
        // should this be a configurable setting?

        //println!("adding free blocks: {:?}", blocks);
        for b in blocks {
            space.freeBlocks.push(b);
        }
        consolidateBlockList(&mut space.freeBlocks);
        let mut free_at_end = None;
        for (i, b) in space.freeBlocks.iter().enumerate() {
            if b.lastPage == space.nextPage - 1 {
                // this block can simply be removed and nextPage moved back
                free_at_end = Some(i);
                break;
            }
        }
        if let Some(i) = free_at_end {
            //println!("    killing free_at_end: {:?}", space.freeBlocks[i]);
            space.nextPage = space.freeBlocks[i].firstPage;
            space.freeBlocks.remove(i);
        }

        let file_length = try!(std::fs::metadata(path)).len();
        let page_size = page_size as u64;
        let first_page_beyond = (file_length / page_size + 1) as u32;
        if first_page_beyond > space.nextPage {
            let fs = try!(OpenOptions::new()
                    .read(true)
                    .write(true)
                    .open(&path)
                    );
            try!(fs.set_len(((space.nextPage - 1) as u64) * page_size));
        }

        space.freeBlocks.sort_by(|a,b| b.count_pages().cmp(&a.count_pages()));
        //println!("    space now: {:?}", space);
        Ok(())
    }

    // a stored segmentinfo for a segment is a single blob of bytes.
    // root page
    // number of pairs
    // each pair is startBlock,countBlocks
    // level
    // all in varints

    fn write_header(&self, 
                   dest: &mut HeaderData, 
                   fs: &mut File, 
                   hdr: HeaderData
                  ) -> Result<()> {

        fn build_segment_list(h: &HeaderData) -> Vec<u8> {
            let mut pb = vec![];
            // TODO format version number
            let count_ranges = h.state.len();
            misc::push_varint(&mut pb, count_ranges as u64);
            for range in h.state.iter() {
                let count_segments_in_range = range.state.len();
                misc::push_varint(&mut pb, count_segments_in_range as u64);
                for g in range.state.iter() {
                    misc::push_varint(&mut pb, *g);
                    match h.segments_info.get(&g) {
                        Some(info) => {
                            misc::push_varint(&mut pb, info.location.root_page as u64);
                            misc::push_varint(&mut pb, info.location.blocks.len() as u64);
                            // we store PageBlock as first/count instead of first/last, since the
                            // count will always compress better as a varint.
                            for t in info.location.blocks.iter() {
                                misc::push_varint(&mut pb, t.firstPage as u64);
                                misc::push_varint(&mut pb, t.count_pages() as u64);
                            }
                            misc::push_varint(&mut pb, info.level as u64);
                        },
                        None => panic!("segment num in current state but not in segments_info")
                    }
                }
            }
            pb
        }

        let mut pb = PageBuilder::new(HEADER_SIZE_IN_BYTES);
        pb.PutInt32(self.pgsz as u32);

        pb.PutVarint(hdr.changeCounter);
        pb.PutVarint(hdr.mergeCounter);
        pb.PutVarint(hdr.next_segnum);

        let pbSegList = build_segment_list(&hdr);

        // TODO the + 1 in the following line is probably no longer needed.
        // I think it used to be the flag indicating header overflow.
        if pb.Available() >= (pbSegList.len() + 1) {
            pb.PutArray(&pbSegList);
        } else {
            return Err(Error::Misc(String::from("header too big")));
        }

        try!(fs.seek(SeekFrom::Start(0)));
        try!(pb.Write(fs));
        try!(fs.flush());
        *dest = hdr;
        Ok(())
    }

    fn get_cursor_on_active_segment(
        inner: &std::sync::Arc<InnerPart>, 
        header: &HeaderData,
        g: SegmentNum,
        f: std::rc::Rc<std::cell::RefCell<File>>,
        ) -> Result<SegmentCursor> {

        match header.segments_info.get(&g) {
            None => Err(Error::Misc(String::from("get_cursor_on_active_segment: segment not found"))),
            Some(seg) => {
                let mut space = try!(inner.space.lock());
                let csrnum = space.nextCursorNum;
                let foo = inner.clone();
                // TODO this should use misc::Lend<>
                let done = move || -> () {
                    // TODO this wants to propagate errors
                    foo.cursor_dropped(g, csrnum);
                };
                let page = try!(Self::get_loaner_page(inner));
                let mut csr = try!(SegmentCursor::new(&inner.path, f, page, seg.location.clone()));

                space.nextCursorNum = space.nextCursorNum + 1;
                let was = space.cursors.insert(csrnum, g);
                assert!(was.is_none());
                csr.set_hook(box done);
                Ok(csr)
            }
        }
    }

    fn get_loaner_page(inner: &std::sync::Arc<InnerPart>) -> Result<misc::Lend<Box<[u8]>>> {
        let page = {
            match inner.pagepool.try_lock() {
                Ok(mut pagepool) => {
                    match pagepool.pages.pop() {
                        Some(p) => p,
                        None => vec![0; inner.pgsz].into_boxed_slice(),
                    }
                },
                Err(std::sync::TryLockError::Poisoned(_)) => {
                    return Err(Error::Poisoned);
                },
                Err(std::sync::TryLockError::WouldBlock) => {
                    vec![0; inner.pgsz].into_boxed_slice()
                },
            }
        };
        let foo = inner.clone();
        let done_page = move |p| -> () {
            foo.return_page_to_pool(p);
        };
        let page = misc::Lend::new(page, box done_page);
        Ok(page)
    }

    fn open_cursor_on_active_segment(inner: &std::sync::Arc<InnerPart>, g: SegmentNum) -> Result<SegmentCursor> {
        let st = try!(inner.header.read());
        let f = try!(inner.open_file_for_cursor());
        let cursor = try!(Self::get_cursor_on_active_segment(inner, &*st, g, f));
        Ok(cursor)
    }

    fn open_cursor_on_pending_segment(inner: &std::sync::Arc<InnerPart>, location: SegmentLocation) -> Result<SegmentCursor> {
        let page = try!(Self::get_loaner_page(inner));
        let f = try!(inner.open_file_for_cursor());
        let cursor = try!(SegmentCursor::new(&inner.path, f, page, location));
        // note no set_hook here
        Ok(cursor)
    }

    fn merge_pending_segments(inner: &std::sync::Arc<InnerPart>, segments: Vec<SegmentLocation>) -> Result<SegmentLocation> {
        let cursors = 
            segments
            .into_iter()
            .map(|loc| Self::open_cursor_on_pending_segment(inner, loc))
            .collect::<Result<Vec<_>>>();
        let cursors = try!(cursors);
        let cursors = 
            cursors
            .into_iter()
            .map(|c| ConcatCursor::new(vec![Some(c)]))
            .collect::<Vec<_>>();

        let cursor = box MultiCursor::Create(cursors);
        let location = try!(Self::write_merge_segment(inner, cursor));
        Ok(location)
    }

    fn open_cursor(inner: &std::sync::Arc<InnerPart>) -> Result<LivingCursor> {
        // TODO this cursor needs to expose the changeCounter and segment list
        // on which it is based. for optimistic writes.  caller can grab a cursor,
        // do their writes, then grab the writelock, and grab another cursor, then
        // compare the two cursors to see if anything important changed.  if not,
        // commit their writes.  if so, nevermind the written segments and start over.

        let header = try!(inner.header.read());
        let mut cursors = vec![];
        let mut generation = 0;
        let f = try!(inner.open_file_for_cursor());
        loop {
            let mut cursors_for_this_generation = vec![];
            let mut any = false;
            for rangenum in 0 .. header.state.len() {
                if generation < header.state[rangenum].state.len() {
                    let segnum = header.state[rangenum].state[generation];
                    let cursor = try!(Self::get_cursor_on_active_segment(inner, &header, segnum, f.clone()));
                    cursors_for_this_generation.push(Some(cursor));
                    any = true;
                } else {
                    cursors_for_this_generation.push(None);
                }
            }
            if !any {
                break;
            }
            let cc = ConcatCursor::new(cursors_for_this_generation);
            cursors.push(cc);
            generation += 1;
        }
        let mc = MultiCursor::Create(cursors);
        let lc = LivingCursor::Create(mc);
        Ok(lc)
    }

    fn get_page(inner: &std::sync::Arc<InnerPart>, pgnum: PageNum) -> Result<Box<[u8]>> {
        // OpenForReading?
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

    fn release_pending_segment(inner: &std::sync::Arc<InnerPart>, location: SegmentLocation) -> Result<()> {
        let mut space = try!(inner.space.lock());
        try!(Self::addFreeBlocks(&mut space, &inner.path, inner.pgsz, location.blocks));
        Ok(())
    }

    fn list_segments(inner: &std::sync::Arc<InnerPart>) -> Result<(Vec<RangeState>, HashMap<SegmentNum, SegmentInfo>)> {
        let header = try!(inner.header.read());
        let a = header.state.clone();
        let b = header.segments_info.clone();
        Ok((a, b))
    }

    // TODO name.  commit_generation?
    fn commit_segment(&self, set: Vec<Option<SegmentLocation>>) -> Result<Vec<Option<SegmentNum>>> {
        // TODO check that set.len() is correct
        let mut header = try!(self.header.write());

        // TODO assert new_seg shares no pages with any seg in current state

        let mut newHeader = header.clone();

        let segnums =
            set
            .into_iter()
            .enumerate()
            .map(
                |(rangenum, loc)| {
                    match loc {
                        Some(new_seg) => {
                            // all new segments are given level 0
                            let new_seg = SegmentInfo {
                                location: new_seg,
                                level: 0,
                            };
                            let new_segnum = newHeader.next_segnum;
                            newHeader.next_segnum += 1;
                            newHeader.segments_info.insert(new_segnum, new_seg);
                            newHeader.state[rangenum].state.insert(0, new_segnum);
                            Some(new_segnum)
                        },
                        None => {
                            None
                        },
                    }
                })
            .collect::<Vec<_>>();

        newHeader.changeCounter = newHeader.changeCounter + 1;

        let mut fs = try!(self.OpenForWriting());
        try!(self.write_header(&mut header, &mut fs, newHeader));

        // note that we intentionally do not release the writeLock here.
        // you can change the segment list more than once while holding
        // the writeLock.  the writeLock gets released when you Dispose() it.

        Ok(segnums)
    }

    fn write_segment(&self, pairs: BTreeMap<Box<[u8]>, Blob>) -> Result<Vec<Option<SegmentLocation>>> {
        // TODO this is probably not the happiest way to do this.
        // when we have a pending tx manager layer, it will probably
        // want to accumulate changes into a group of BTreeMaps, not
        // just one.

        // TODO or maybe create_segment() should allow a filter to be
        // specified, such that it will ignore keys outside a range?

        let mut ranges = vec![];
        // TODO using the copy of count_ranges so we don't have to lock the header
        for _ in 0 .. self.count_ranges {
            ranges.push(BTreeMap::new());
        }
        for (k, v) in pairs {
            // TODO encapsulate mapping of key to range
            let i = (k[0] as usize) * self.count_ranges / 256;
            ranges[i].insert(k, v);
        }
        let mut fs = try!(self.OpenForWriting());
        let mut segs = vec![];
        for range in ranges {
            if range.len() > 0 {
                let source = range.into_iter().map(|t| {
                    let (k, v) = t;
                    Ok(kvp {Key:k, Value:v})
                });
                let seg = try!(create_segment(&mut fs, self, source));
                segs.push(Some(seg));
            } else {
                segs.push(None);
            }
        }
        //println!("segs: {:?}", segs);
        Ok(segs)
    }

    fn write_merge_segment(inner: &std::sync::Arc<InnerPart>, cursor: Box<ICursor>) -> Result<SegmentLocation> {
        let source = CursorIterator::new(cursor);
        let mut fs = try!(inner.OpenForWriting());
        let seg = try!(create_segment(&mut fs, &**inner, source));
        Ok(seg)
    }

    fn merge(inner: &std::sync::Arc<InnerPart>, range: usize, merge_level: u32, min_segs: usize, max_segs: usize, promote: MergePromotionRule) -> Result<Option<PendingMerge>> {
        assert!(min_segs <= max_segs);
        //println!("in merge: range = {}", range);
        let step1 = {
            let header = try!(inner.header.read());

            if header.state[range].state.len() == 0 {
                //println!("{}:{} no merge", file!(), line!());
                return Ok(None)
            }

            //println!("merge_level: {}", merge_level);
            //println!("promote: {:?}", promote);
            //println!("state: {:?}", header.state);
            //println!("segments_info: {:?}", header.segments_info);
            // TODO wrong?  confine this to only the current range?
            // probably need per-range settings for promotion.
            let mut level_sizes = HashMap::new();
            for (_, ref info) in header.segments_info.iter() {
                let pages = info.location.count_pages();
                match level_sizes.entry(&info.level) {
                    std::collections::hash_map::Entry::Occupied(mut e) => {
                        let n = e.get_mut();
                        *n = *n + pages;
                    },
                    std::collections::hash_map::Entry::Vacant(e) => {
                        e.insert(pages);
                    },
                };
            }
            //println!("level_sizes: {:?}", level_sizes);

            let level_group = 
                header.state[range].state
                .iter()
                .filter(|g| {
                    let info = header.segments_info.get(&g).unwrap();
                    info.level == merge_level
                })
                .map(|g| *g)
                .collect::<Vec<SegmentNum>>();

            //println!("level_group: {:?}", level_group);
            //println!("segment in level: {}", level_group.len());

            if level_group.len() == 0 {
                //println!("no merge");
                //println!("{}:{} no merge", file!(), line!());
                return Ok(None)
            }

            let pages_in_merge_level = level_sizes[&merge_level];
            //println!("pages_in_merge_level: {:?}", pages_in_merge_level);

            // make sure this is contiguous
            assert!(slice_within(level_group.as_slice(), header.state[range].state.as_slice()).is_ok());

            let mut merge_seg_nums = Vec::new();

            let mut mergeStuff = try!(inner.mergeStuff.lock());

            // we can merge any contiguous set of not-already-being-merged 
            // segments at the end of the group.  if we merge something
            // that is not at the end of the group, we could end up with
            // level groups not being contiguous.  TODO techically, the
            // previous statement is true only if we are promoting the level.

            for g in level_group.iter().rev() {
                if mergeStuff.merging.contains(g) {
                    break;
                } else {
                    merge_seg_nums.push(*g);
                }
            }

            if merge_seg_nums.len() >= min_segs {
                merge_seg_nums.truncate(max_segs);

                // right now the merge_seg_nums list is in reverse order because we searched with a
                // reverse iterator just above.  reverse it again to make it right.
                merge_seg_nums.reverse();

                //println!("segments being merged: {:?}", merge_seg_nums);
                let pages_in_merge_segments: usize = 
                    merge_seg_nums
                    .iter()
                    .map(
                        |g| {
                            let info = header.segments_info.get(g).unwrap();
                            info.location.count_pages()
                        })
                    .sum();
                //println!("pages_in_merge_segments: {}", pages_in_merge_segments);
                assert!(pages_in_merge_segments <= pages_in_merge_level);
                let f = try!(inner.open_file_for_cursor());
                let cursors = 
                    merge_seg_nums
                    .iter()
                    .map(|g| Self::get_cursor_on_active_segment(inner, &header, *g, f.clone()))
                    .collect::<Result<Vec<_>>>();
                let cursors = try!(cursors);
                let cursors = 
                    cursors
                    .into_iter()
                    .map(|c| ConcatCursor::new(vec![Some(c)]))
                    .collect::<Vec<_>>();

                for g in merge_seg_nums.iter() {
                    mergeStuff.merging.insert(*g);
                }

                let cursor = {
                    let mc = MultiCursor::Create(cursors);
                    mc
                };

                let last_seg_being_merged = merge_seg_nums[merge_seg_nums.len() - 1];
                let pos_last_seg = header.state[range].state.iter().position(|s| *s == last_seg_being_merged).expect("gotta be there");
                let count_segments_behind = header.state[range].state.len() - (pos_last_seg + 1);

                let cursor: Box<ICursor> =
                    if count_segments_behind == 0 {
                        // we are merging the last segments in the current state.
                        // there is nothing behind.
                        // so all tombstones can be filtered.
                        // so we just wrap in a LivingCursor.
                        let cursor = LivingCursor::Create(cursor);
                        box cursor
                    } else if count_segments_behind <= 8 {
                        // TODO arbitrary hard-coded limit in the line above

                        // there are segments behind the ones we are merging.
                        // we can only filter a tombstone if its key is not present behind.

                        // TODO getting all these cursors can be really expensive.

                        // TODO if we knew there were no tombstones in the segments to be merged,
                        // we would not bother with this.

                        // TODO we need a way to cache these cursors.  maybe these "behind"
                        // cursors are special, and are stored here in the header somewhere.
                        // the next time we do a merge, we can reuse them.  they need to get
                        // cleaned up at some point.

                        // TODO capacity
                        let mut behind = vec![];
                        for s in &header.state[range].state[pos_last_seg + 1 ..] {
                            let s = *s;
                            let cursor = try!(Self::get_cursor_on_active_segment(inner, &header, s, f.clone()));
                            behind.push(cursor);
                        }
                        // TODO to allow reuse of these behind cursors, we should pass
                        // them as references, don't transfer ownership.  but then they
                        // will need to be owned somewhere else.
                        let cursor = FilterTombstonesCursor::new(cursor, behind);
                        box cursor
                    } else {
                        box cursor
                    };

                Some((merge_seg_nums, pages_in_merge_segments, pages_in_merge_level, cursor))
            } else {
                //println!("{}:{} no merge", file!(), line!());
                //println!("no merge");
                None
            }
        };

        match step1 {
            Some((merge_seg_nums, pages_in_merge_segments, pages_in_merge_level, mut cursor)) => {
                // TODO if something goes wrong here, the function will exit with
                // an error but mergeStuff.merging will still contain the segments we are
                // trying to merge, which will prevent them from EVER being merged.

                // note that cursor.First() should NOT have already been called
                try!(cursor.First());
                let seg = 
                    if cursor.IsValid() {
                        let location = try!(Self::write_merge_segment(inner, cursor));
                        let pages_in_new_segment = location.count_pages();
                        //println!("pages_in_new_segment: {}", pages_in_new_segment);
                        // TODO is the following assert always true?
                        // TODO assert!(pages_in_new_segment <= pages_in_merge_segments);
                        let level =
                            match promote {
                                MergePromotionRule::Promote => {
                                    merge_level + 1
                                },
                                MergePromotionRule::Stay => {
                                    merge_level
                                },
                                MergePromotionRule::Threshold(n) => {
                                    if pages_in_merge_level >= n {
                                        merge_level + 1
                                    } else {
                                        merge_level
                                    }
                                },
                            };
                        let seg =
                            SegmentInfo {
                                location: location,
                                level: level,
                            };
                        Some(seg)
                    } else {
                        None
                    };
                let pm = 
                    PendingMerge {
                        range: range,
                        old_segments: merge_seg_nums,
                        new_segment: seg,
                        merge_level: merge_level,
                    };
                Ok(Some(pm))
            },
            None => {
                Ok(None)
            },
        }
    }

    fn commit_merge(&self, pm: PendingMerge) -> Result<Option<SegmentNum>> {
        let (segmentsBeingReplaced, new_segnum) = {
            let mut header = try!(self.header.write());

            // TODO assert new_seg shares no pages with any seg in current state

            // we need the list of segments which were merged.  we make a copy of
            // so that we're not keeping a reference that inhibits our ability to
            // get other references a little later in the function.

            // TODO why does this Set need to be created?
            let oldAsSet: HashSet<SegmentNum> = pm.old_segments.iter().map(|g| *g).collect();
            assert!(oldAsSet.len() == pm.old_segments.len());

            // now we need to verify that the segments being replaced are in state
            // and contiguous.

            let ndxFirstOld = try!(slice_within(pm.old_segments.as_slice(), header.state[pm.range].state.as_slice()));

            // now we construct a newHeader

            let mut newHeader = header.clone();

            // remove the old segmentinfos, keeping them for later

            let mut segmentsBeingReplaced = HashMap::with_capacity(oldAsSet.len());
            for g in &oldAsSet {
                let info = newHeader.segments_info.remove(g).expect("old seg not found in header.segments_info");
                segmentsBeingReplaced.insert(*g, info);
            }

            // remove old segments from current state

            for _ in &pm.old_segments {
                newHeader.state[pm.range].state.remove(ndxFirstOld);
            }

            let new_segnum =
                match pm.new_segment {
                    None => {
                        None
                        // a merge resulted in what would have been an empty segment.
                        // this happens because tombstones
                    },
                    Some(new_seg) => {
                        let new_segnum = newHeader.next_segnum;
                        newHeader.next_segnum += 1;
                        newHeader.state[pm.range].state.insert(ndxFirstOld, new_segnum);
                        newHeader.segments_info.insert(new_segnum, new_seg);
                        Some(new_segnum)
                    },
                };

            newHeader.mergeCounter = newHeader.mergeCounter + 1;

            let mut fs = try!(self.OpenForWriting());
            try!(self.write_header(&mut header, &mut fs, newHeader));

            (segmentsBeingReplaced, new_segnum)
        };

        {
            let mut mergeStuff = try!(self.mergeStuff.lock());
            for g in pm.old_segments {
                mergeStuff.merging.remove(&g);
            }
        }

        let mut segmentsToBeFreed = segmentsBeingReplaced;
        {
            let mut space = try!(self.space.lock());
            let segmentsWithACursor: HashSet<SegmentNum> = space.cursors.iter().map(|t| {let (_,segnum) = t; *segnum}).collect();
            for g in segmentsWithACursor {
                // don't free any segment that has a cursor.  yet.
                match segmentsToBeFreed.remove(&g) {
                    Some(z) => {
                        //println!("zombie: {:?}", z);
                        space.zombie_segments.insert(g, z);
                    },
                    None => {
                    },
                }
            }
            let mut blocksToBeFreed = Vec::new();
            for info in segmentsToBeFreed.values() {
                blocksToBeFreed.push_all(&info.location.blocks);
            }
            try!(Self::addFreeBlocks(&mut space, &self.path, self.pgsz, blocksToBeFreed));
        }

        // note that we intentionally do not release the writeLock here.
        // you can change the segment list more than once while holding
        // the writeLock.  the writeLock gets released when you Dispose() it.
        Ok(new_segnum)
    }

}

impl IPages for InnerPart {
    fn PageSize(&self) -> usize {
        self.pgsz
    }

    fn Begin(&self) -> Result<PendingSegment> {
        let p = PendingSegment::new();
        Ok(p)
    }

    fn GetBlock(&self, ps: &mut PendingSegment) -> Result<PageBlock> {
        let mut space = try!(self.space.lock());
        // specificSize=0 means we don't care how big of a block we get
        let blk = self.getBlock(&mut space, 0);
        ps.AddBlock(blk);
        Ok(blk)
    }

    fn End(&self, ps: PendingSegment, unused_page: PageNum, root_page: PageNum) -> Result<SegmentLocation> {
        let (blocks, leftovers) = ps.End(unused_page);
        assert!(!block_list_contains_page(&blocks, unused_page));
        assert!(block_list_contains_page(&blocks, root_page));
        let info = SegmentLocation::new(root_page, blocks);
        match leftovers {
            Some(b) => {
                let mut space = try!(self.space.lock());
                try!(Self::addFreeBlocks(&mut space, &self.path, self.pgsz, vec![b]));
            },
            None => {
            },
        }
        Ok(info)
    }

}

// ----------------------------------------------------------------

#[cfg(remove_me)]
pub struct GenerateNumbers {
    pub cur: usize,
    pub end: usize,
    pub step: usize,
}

#[cfg(remove_me)]
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

#[cfg(remove_me)]
pub struct GenerateWeirdPairs {
    pub cur: usize,
    pub end: usize,
    pub klen: usize,
    pub vlen: usize,
}

#[cfg(remove_me)]
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

