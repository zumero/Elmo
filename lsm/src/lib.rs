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
#![feature(clone_from_slice)]
#![feature(iter_arith)]

// TODO turn the following warnings back on later
#![allow(non_snake_case)]
#![allow(non_camel_case_types)]

extern crate misc;
extern crate time;

use misc::endian;
use misc::varint;
use misc::Lend;

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

// the fresh and young levels are not included in the following count

// TODO does this need to be a constant?  maybe we should just allow it
// to grow as needed?  but then we would need to start up new threads
// and channels.
const NUM_LEVELS: usize = 8;

pub type PageNum = u32;
pub type PageCount = u32;
// type PageSize = u32;

// TODO there is code which assumes that PageNum is u32.
// but that's the nature of the file format.  the type alias
// isn't so much so that we can change it, but rather, to make
// reading the code easier.

pub enum Blob {
    Stream(Box<Read>),
    Boxed(Box<[u8]>),
    Tombstone,
    SameFileOverflow(u64, BlockList),
}

impl std::fmt::Debug for Blob {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            &Blob::Tombstone => {
                write!(f, "Tombstone")
            },
            &Blob::Stream(_) => {
                write!(f, "Stream")
            },
            &Blob::Boxed(ref a) => {
                write!(f, "{:?}", a)
            },
            &Blob::SameFileOverflow(_, _) => {
                write!(f, "SameFileOverflow")
            },
        }
    }
}

impl Blob {
    fn is_tombstone(&self) -> bool {
        match self {
            &Blob::Tombstone => true,
            &Blob::Stream(_) => false,
            &Blob::Boxed(_) => false,
            &Blob::SameFileOverflow(_, _) => false,
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
pub enum BlockRequest {
    Any,
    MinimumSize(PageCount),
    StartOrAfterMinimumSize(Vec<PageNum>, PageNum, PageCount),
    StartOrAny(Vec<PageNum>),
}

impl BlockRequest {
    fn start_is(&self, pg: PageNum) -> bool {
        match self {
            &BlockRequest::Any => false,
            &BlockRequest::MinimumSize(_) => false,

            &BlockRequest::StartOrAny(ref v) => v.iter().any(|n| *n == pg),
            &BlockRequest::StartOrAfterMinimumSize(ref v, _, _) => v.iter().any(|n| *n == pg),
        }
    }

    fn get_after(&self) -> Option<PageNum> {
        match self {
            &BlockRequest::Any => None,
            &BlockRequest::MinimumSize(_) => None,

            &BlockRequest::StartOrAny(_) => None,
            &BlockRequest::StartOrAfterMinimumSize(_, after, _) => Some(after),
        }
    }
}

// kvp is the struct used to provide key-value pairs downward,
// for storage into the database.
pub struct kvp {
    // TODO note that there is no provision here for SameFileOverflow from a merge
    Key: Box<[u8]>,
    Value: Blob,
}

#[derive(Debug, Clone)]
pub struct BlockList {
    // TODO we could keep track of how this is sorted if
    // we put this in a module to make the blocks field private.
    pub blocks: Vec<PageBlock>,
}

impl BlockList {
    fn new() -> Self {
        BlockList {
            blocks: vec![],
        }
    }

    fn into_vec(self) -> Vec<PageBlock> {
        self.blocks
    }

    fn is_empty(&self) -> bool {
        self.blocks.is_empty()
    }

    pub fn count_blocks(&self) -> usize {
        self.blocks.len()
    }

    pub fn count_pages(&self) -> PageCount {
        self.blocks.iter().map(|pb| pb.count_pages()).sum()
    }

    fn last_page(&self) -> PageNum {
        // TODO assume it is sorted
        // TODO assuming self.blocks is not empty
        self.blocks[self.blocks.len() - 1].lastPage
    }

    fn first_page(&self) -> PageNum {
        // TODO assume it is sorted
        // TODO assuming self.blocks is not empty
        self.blocks[0].firstPage
    }

    fn remove_block(&mut self, i: usize) -> PageBlock {
        self.blocks.remove(i)
    }

    fn contains_page(&self, pgnum: PageNum) -> bool {
        // TODO if we knew how this were sorted, we could stop the loop earlier
        for blk in self.blocks.iter() {
            if blk.contains_page(pgnum) {
                return true;
            }
        }
        return false;
    }

    fn would_extend_an_existing_block(&self, pg: PageNum) -> bool {
        for i in 0 .. self.blocks.len() {
            if self.blocks[i].lastPage + 1 == pg {
                return true;
            }
        }
        false
    }

    fn add_page_no_reorder(&mut self, pg: PageNum) -> bool {
        for i in 0 .. self.blocks.len() {
            if self.blocks[i].lastPage + 1 == pg {
                self.blocks[i].lastPage = pg;
                return true;
            }
        }

        let b = PageBlock::new(pg, pg);
        self.blocks.push(b);
        return false;
    }

    fn add_block_no_reorder(&mut self, blk: PageBlock) -> bool {
        for i in 0 .. self.blocks.len() {
            if self.blocks[i].lastPage + 1 == blk.firstPage {
                self.blocks[i].lastPage = blk.lastPage;
                return true;
            }
        }

        self.blocks.push(blk);
        return false;
    }

    fn remove_anything_in(&mut self, other: &BlockList) -> BlockList {
        if self.is_empty() || other.is_empty() {
            return BlockList::new();
        }

        //println!("original: {:?}", self);
        //println!("other: {:?}", other);

        // TODO the following algorithm is none too speedy.
        // we do need both lists to be sorted, but we probably
        // don't need to clone self, it could be done in place.
        // we could require/assert/assume that the other blocklist
        // is already sorted
        // however, note that this function is only used for diag
        // purposes.

        let mut sorted_self = self.clone();
        sorted_self.sort_and_consolidate();
        let mut sorted_self = sorted_self.into_vec();

        let mut sorted_other = other.clone();
        sorted_other.sort_and_consolidate();
        let mut sorted_other = sorted_other.into_vec();

        let mut remaining_self = vec![];
        let mut removed = vec![];

        let mut i_self = 0;
        let mut i_other = 0;
        while i_self < sorted_self.len() && i_other < sorted_other.len() {
            let diff = PageBlock::intersect(sorted_self[i_self], sorted_other[i_other]);
            //println!("diff: {:?}", diff);
            if let Some(a_left) = diff.a_left {
                remaining_self.push(a_left);
            }
            if let Some(overlap) = diff.overlap {
                removed.push(overlap);
            }
            if let Some(a_right) = diff.a_right {
                sorted_self[i_self] = a_right;
            } else {
                i_self += 1;
            }
            if let Some(b_right) = diff.b_right {
                sorted_other[i_other] = b_right;
            } else {
                i_other += 1;
            }
        }
        while i_self < sorted_self.len() {
            remaining_self.push(sorted_self[i_self]);
            i_self += 1;
        }

        let mut new_self = BlockList {
            blocks: remaining_self,
        };
        let mut removed = BlockList {
            blocks: removed,
        };

        // TODO not sure either of these sort calls are needed
        new_self.sort_and_consolidate();
        removed.sort_and_consolidate();

        //println!("new_self: {:?}", new_self);
        //println!("removed: {:?}", removed);

        if cfg!(expensive_check) 
        {
            assert!(self.count_pages() == new_self.count_pages() + removed.count_pages());
            for i in 0 .. self.blocks.len() {
                for pg in self.blocks[i].firstPage .. self.blocks[i].lastPage + 1 {
                    if new_self.contains_page(pg) {
                        assert!(!removed.contains_page(pg));
                        assert!(!other.contains_page(pg));
                    } else {
                        assert!(removed.contains_page(pg));
                        assert!(other.contains_page(pg));
                    }
                }
            }
        }

        self.blocks = new_self.into_vec();
        removed
    }

    fn invert(&mut self) {
        let len = self.blocks.len();
        self.blocks.sort_by(|a,b| a.firstPage.cmp(&b.firstPage));
        for i in 0 .. len - 1 {
            self.blocks[i].firstPage = self.blocks[i].lastPage + 1;
            self.blocks[i].lastPage = self.blocks[i + 1].firstPage - 1;
            assert!(self.blocks[i].firstPage <= self.blocks[i].lastPage);
        }
        // this function finds the space between the blocks.
        // the last block didn't get touched, and is still a block in use.
        // so remove it.
        self.blocks.remove(len - 1);
    }

    fn add_blocklist_no_reorder(&mut self, other: &BlockList) {
        // TODO call add_block_no_reorder, and return a bool
        for blk in other.blocks.iter() {
            self.blocks.push(blk.clone());
        }
    }

    fn sort_and_consolidate(&mut self) {
        if self.blocks.len() < 2 {
            return;
        }

        self.blocks.sort_by(|a,b| a.firstPage.cmp(&b.firstPage));
        if cfg!(expensive_check) 
        {
            for i in 1 .. self.blocks.len() {
                assert!(self.blocks[i].firstPage > self.blocks[i - 1].lastPage);
            }
        }
        let mut i = 0;
        loop {
            if i + 1 == self.blocks.len() {
                break;
            }
            if self.blocks[i].lastPage + 1 == self.blocks[i + 1].firstPage {
                self.blocks[i].lastPage = self.blocks[i + 1].lastPage;
                self.blocks.remove(i + 1);
                // leave i here
            } else {
                i += 1;
            }
        }
        // the list is still sorted
    }

    fn sort_by_size_desc_page_asc(&mut self) {
        self.blocks.sort_by(
            |a,b| 
                match b.count_pages().cmp(&a.count_pages()) {
                    Ordering::Equal => a.firstPage.cmp(&b.firstPage),
                    c => c,
                }
                );
    }

    fn encode(&self, pb: &mut PageBuilder) {
        // we store each PageBlock as first/offset instead of first/last, since the
        // offset will always compress better as a varint.
        
        // if there are multiple blocks, we store the firstPage field
        // of all blocks after the first one as offsets from th first one.
        // this requires that the list was sorted before this func was called.

        let len_before = pb.sofar();
        pb.PutVarint( self.blocks.len() as u64);
        if self.blocks.len() > 0 {
            let first_page = self.blocks[0].firstPage;
            pb.PutVarint( self.blocks[0].firstPage as u64);
            pb.PutVarint( (self.blocks[0].lastPage - self.blocks[0].firstPage) as u64);
            if self.blocks.len() > 1 {
                for i in 1 .. self.blocks.len() {
                    assert!(self.blocks[i].firstPage > first_page);
                    pb.PutVarint( (self.blocks[i].firstPage - first_page) as u64);
                    pb.PutVarint( (self.blocks[i].lastPage - self.blocks[i].firstPage) as u64);
                }
            }
        }
        let len_after = pb.sofar();
        assert!(len_after - len_before == self.encoded_len());
    }

    fn encoded_len(&self) -> usize {
        let mut len = 0;
        len += varint::space_needed_for(self.blocks.len() as u64);
        if self.blocks.len() > 0 {
            let first_page = self.blocks[0].firstPage;
            len += varint::space_needed_for(self.blocks[0].firstPage as u64);
            len += varint::space_needed_for((self.blocks[0].lastPage - self.blocks[0].firstPage) as u64);
            if self.blocks.len() > 1 {
                for i in 1 .. self.blocks.len() {
                    assert!(self.blocks[i].firstPage > first_page);
                    len += varint::space_needed_for((self.blocks[i].firstPage - first_page) as u64);
                    len += varint::space_needed_for((self.blocks[i].lastPage - self.blocks[i].firstPage) as u64);
                }
            }
        }
        len
    }

    fn read(pr: &[u8], cur: &mut usize) -> Self {
        let count_blocks = varint::read(pr, cur) as usize;
        let mut list = BlockList {
            blocks: Vec::with_capacity(count_blocks),
        };
        for i in 0 .. count_blocks {
            let first_page = varint::read(pr, cur) as PageNum
                +
                if i > 0 {
                    list.blocks[0].firstPage
                } else {
                    0
                };
            let offset = varint::read(pr, cur) as PageNum;
            let b = PageBlock::new(first_page, first_page + offset);
            list.blocks.push(b);
        }
        list
    }

    #[cfg(remove_me)]
    fn skip(pr: &[u8], cur: &mut usize) {
        // TODO do this without mem alloc
        let unused = Self::read(pr, cur);
    }
}

impl std::ops::Index<usize> for BlockList {
    type Output = PageBlock;

    fn index<'a>(&'a self, i: usize) -> &'a PageBlock {
        &self.blocks[i]
    }
}

fn get_level_size(i: usize) -> u64 {
    let mut n = 1;
    for _ in 0 .. i + 1 {
        // TODO tune this factor.
        // for leveldb, it is 10.
        n *= 10;
    }
    n * 1024 * 1024
}

fn split3<T>(a: &mut [T], i: usize) -> (&mut [T], &mut [T], &mut [T]) {
    let (before, a2) = a.split_at_mut(i);
    let (islice, after) = a2.split_at_mut(1);
    (before, islice, after)
}

pub enum KeyRef<'a> {
    // TODO consider a type representing an overflow reference with len and blocks?
    // TODO should the file and pgsz be in here?
    //Overflowed(String, usize, u64, BlockList),

    Boxed(Box<[u8]>),

    // the other two are references into the page
    Prefixed(&'a [u8],&'a [u8]),

    Slice(&'a [u8]),
}

impl<'a> std::fmt::Debug for KeyRef<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::result::Result<(), std::fmt::Error> {
        match *self {
            KeyRef::Boxed(ref a) => write!(f, "Boxed, a={:?}", a),
            KeyRef::Prefixed(front,back) => write!(f, "Prefixed, front={:?}, back={:?}", front, back),
            KeyRef::Slice(a) => write!(f, "Array, val={:?}", a),
        }
    }
}

impl<'a> KeyRef<'a> {
    pub fn len(&self) -> usize {
        match *self {
            KeyRef::Boxed(ref a) => a.len(),
            KeyRef::Slice(a) => a.len(),
            KeyRef::Prefixed(front, back) => front.len() + back.len(),
        }
    }

    pub fn u8_at(&self, i: usize) -> Result<u8> {
        match self {
            &KeyRef::Boxed(ref a) => {
                if i < a.len() {
                    Ok(a[i])
                } else {
                    Err(Error::Misc(String::from("u8_at: out of range 1")))
                }
            },
            &KeyRef::Slice(a) => {
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

    pub fn min_with(self, k: Box<[u8]>) -> Box<[u8]> {
        if Ordering::Greater == self.compare_with(&k) {
            self.into_boxed_slice()
        } else {
            k
        }
    }

    pub fn max_with(self, k: Box<[u8]>) -> Box<[u8]> {
        if Ordering::Less == self.compare_with(&k) {
            self.into_boxed_slice()
        } else {
            k
        }
    }

    pub fn compare_with(&self, k: &[u8]) -> Ordering {
        match self {
            &KeyRef::Boxed(ref a) => {
                bcmp::Compare(&a, &k)
            },
            &KeyRef::Slice(a) => {
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
                &KeyRef::Boxed(ref a) => {
                    k == &a[0 .. k.len()]
                },
                &KeyRef::Slice(a) => {
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
            &KeyRef::Slice(a) => {
                if end <= a.len() {
                    let t = try!(func(&a[begin .. end]));
                    Ok(t)
                } else {
                    Err(Error::Misc(String::from("map_range: out of range 1")))
                }
            },
            &KeyRef::Boxed(ref a) => {
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
                    a.extend_from_slice(&front[begin .. ]);
                    let end = end - front.len();
                    if end <= back.len() {
                        a.extend_from_slice(&back[0 .. end]);
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
        KeyRef::Boxed(k)
    }

    pub fn for_slice(k: &[u8]) -> KeyRef {
        KeyRef::Slice(k)
    }

    pub fn into_boxed_slice(self) -> Box<[u8]> {
        match self {
            KeyRef::Boxed(a) => {
                a
            },
            KeyRef::Slice(a) => {
                let mut k = Vec::with_capacity(a.len());
                k.extend_from_slice(a);
                k.into_boxed_slice()
            },
            KeyRef::Prefixed(front,back) => {
                let mut k = Vec::with_capacity(front.len() + back.len());
                k.extend_from_slice(front);
                k.extend_from_slice(back);
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
            (&KeyRef::Boxed(ref x_k), &KeyRef::Boxed(ref y_k)) => {
                bcmp::Compare(&x_k, &y_k)
            },
            (&KeyRef::Boxed(ref x_k), &KeyRef::Prefixed(ref y_p, ref y_k)) => {
                Self::compare_x_py(&x_k, y_p, y_k)
            },
            (&KeyRef::Boxed(ref x_k), &KeyRef::Slice(ref y_k)) => {
                bcmp::Compare(&x_k, &y_k)
            },
            (&KeyRef::Prefixed(ref x_p, ref x_k), &KeyRef::Boxed(ref y_k)) => {
                Self::compare_px_y(x_p, x_k, &y_k)
            },
            (&KeyRef::Slice(ref x_k), &KeyRef::Boxed(ref y_k)) => {
                bcmp::Compare(&x_k, &y_k)
            },
            (&KeyRef::Prefixed(ref x_p, ref x_k), &KeyRef::Prefixed(ref y_p, ref y_k)) => {
                Self::compare_px_py(x_p, x_k, y_p, y_k)
            },
            (&KeyRef::Prefixed(ref x_p, ref x_k), &KeyRef::Slice(ref y_k)) => {
                Self::compare_px_y(x_p, x_k, y_k)
            },
            (&KeyRef::Slice(ref x_k), &KeyRef::Prefixed(ref y_p, ref y_k)) => {
                Self::compare_x_py(x_k, y_p, y_k)
            },
            (&KeyRef::Slice(ref x_k), &KeyRef::Slice(ref y_k)) => {
                bcmp::Compare(&x_k, &y_k)
            },
        }
    }
}


pub enum ValueRef<'a> {
    Slice(&'a [u8]),
    Overflowed(std::sync::Arc<PageCache>, u64, BlockList),
    Tombstone,
}

/// Like a ValueRef, but cannot represent a tombstone.  Available
/// only from a LivingCursor.
pub enum LiveValueRef<'a> {
    Slice(&'a [u8]),
    Overflowed(std::sync::Arc<PageCache>, u64, BlockList),
}

impl<'a> ValueRef<'a> {
    pub fn len(&self) -> Option<u64> {
        match *self {
            ValueRef::Slice(a) => Some(a.len() as u64),
            ValueRef::Overflowed(_, len, _) => Some(len),
            ValueRef::Tombstone => None,
        }
    }

    pub fn into_blob_for_merge(self) -> Blob {
        match self {
            ValueRef::Slice(a) => {
                let mut k = Vec::with_capacity(a.len());
                k.extend_from_slice(a);
                Blob::Boxed(k.into_boxed_slice())
            },
            ValueRef::Overflowed(_, len, blocks) => Blob::SameFileOverflow(len, blocks),
            ValueRef::Tombstone => Blob::Tombstone,
        }
    }

}

impl<'a> std::fmt::Debug for ValueRef<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::result::Result<(), std::fmt::Error> {
        match *self {
            ValueRef::Slice(a) => write!(f, "Array, len={:?}", a),
            ValueRef::Overflowed(_, len, _) => write!(f, "Overflowed, len={}", len),
            ValueRef::Tombstone => write!(f, "Tombstone"),
        }
    }
}

impl<'a> LiveValueRef<'a> {
    pub fn len(&self) -> u64 {
        match *self {
            LiveValueRef::Slice(a) => a.len() as u64,
            LiveValueRef::Overflowed(_, len, _) => len,
        }
    }

    pub fn into_blob_for_merge(self) -> Blob {
        match self {
            LiveValueRef::Slice(a) => {
                let mut k = Vec::with_capacity(a.len());
                k.extend_from_slice(a);
                Blob::Boxed(k.into_boxed_slice())
            },
            LiveValueRef::Overflowed(_, len, blocks) => Blob::SameFileOverflow(len, blocks),
        }
    }

    // TODO dangerous function if len() is big
    // TODO change this to return a stream, and require file/pgsz?
    #[cfg(remove_me)]
    pub fn _into_boxed_slice(self) -> Result<Box<[u8]>> {
        match self {
            LiveValueRef::Slice(a) => {
                let mut v = Vec::with_capacity(a.len());
                v.extend_from_slice(a);
                Ok(v.into_boxed_slice())
            },
            LiveValueRef::Overflowed(_, len, ref blocks) => {
                let mut a = Vec::with_capacity(len);
                let mut strm = try!(OverflowReader::new(path, pgsz, blocks.blocks[0].firstPage, len));
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
    // TODO this func is dangerous if len is big
    pub fn map<T, F: Fn(&[u8]) -> Result<T>>(self, func: F) -> Result<T> {
        match self {
            LiveValueRef::Slice(a) => {
                let t = try!(func(a));
                Ok(t)
            },
            LiveValueRef::Overflowed(ref f, len, ref blocks) => {
                let mut a = Vec::with_capacity(len as usize);
                let mut strm = try!(OverflowReader::new(f.clone(), blocks.blocks[0].firstPage, len));
                try!(strm.read_to_end(&mut a));
                assert!((len as usize) == a.len());
                let t = try!(func(&a));
                Ok(t)
            },
        }
    }
}

impl<'a> std::fmt::Debug for LiveValueRef<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::result::Result<(), std::fmt::Error> {
        match *self {
            LiveValueRef::Slice(a) => write!(f, "Array, len={:?}", a),
            LiveValueRef::Overflowed(_, len, _) => write!(f, "Overflowed, len={}", len),
        }
    }
}

// TODO consider putting this into a module so we can keep firstPage and lastPage private and
// expose methods to modify them so that we can assert when they become invalid.

#[derive(Hash,PartialEq,Eq,Copy,Clone,Debug)]
pub struct PageBlock {
    pub firstPage: PageNum,
    pub lastPage: PageNum,
}

#[derive(Debug)]
struct IntersectPageBlocks {
    a_left: Option<PageBlock>,
    b_left: Option<PageBlock>,
    overlap: Option<PageBlock>,
    a_right: Option<PageBlock>,
    b_right: Option<PageBlock>,
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

    fn intersect(a: PageBlock, b: PageBlock) -> IntersectPageBlocks {
        //println!("intersecting: {:?} with {:?}", a, b);
        let a_left = 
            if a.firstPage < b.firstPage {
                let last = std::cmp::min(a.lastPage, b.firstPage - 1);
                if last >= a.firstPage {
                    Some(PageBlock::new(a.firstPage, last))
                } else {
                    None
                }
            } else {
                None
            };
        let b_left = 
            if b.firstPage < a.firstPage {
                let last = std::cmp::min(b.lastPage, a.firstPage - 1);
                if last >= b.firstPage {
                    Some(PageBlock::new(b.firstPage, last))
                } else {
                    None
                }
            } else {
                None
            };
        let a_right = 
            if a.lastPage > b.lastPage {
                let first = std::cmp::max(a.firstPage, b.lastPage + 1);
                if first <= a.lastPage {
                    Some(PageBlock::new(first, a.lastPage))
                } else {
                    None
                }
            } else {
                None
            };
        let b_right = 
            if b.lastPage > a.lastPage {
                let first = std::cmp::max(b.firstPage, a.lastPage + 1);
                if first <= b.lastPage {
                    Some(PageBlock::new(first, b.lastPage))
                } else {
                    None
                }
            } else {
                None
            };
        let overlap = {
            let first = std::cmp::max(a.firstPage, b.firstPage);
            let last = std::cmp::min(a.lastPage, b.lastPage);
            if last >= first {
                Some(PageBlock::new(first, last))
            } else {
                None
            }
        };
        //println!("    a_left: {:?}", a_left);
        //println!("    b_left: {:?}", b_left);
        //println!("    overlap: {:?}", overlap);
        //println!("    a_right: {:?}", a_right);
        //println!("    b_right: {:?}", b_right);

        // TODO more asserts here, but there are, what, 32 cases?
        match (a_left, overlap, a_right) {
            (Some(left), None, None) => {
                assert!(a.count_pages() == left.count_pages());
            },
            (Some(left), Some(overlap), None) => {
                assert!(left.lastPage < overlap.firstPage);
            },
            (Some(left), Some(overlap), Some(right)) => {
                assert!(a.count_pages() == left.count_pages() + overlap.count_pages() + right.count_pages());
                assert!(left.lastPage < overlap.firstPage);
                assert!(overlap.lastPage < right.firstPage);
            },
            (Some(left), None, Some(right)) => {
                unreachable!();
            },
            (None, Some(overlap), Some(right)) => {
                assert!(overlap.lastPage < right.firstPage);
            },
            (None, Some(overlap), None) => {
            },
            (None, None, Some(right)) => {
                assert!(a.count_pages() == right.count_pages());
            },
            (None, None, None) => {
                unreachable!();
            },
        }

        IntersectPageBlocks {
            a_left: a_left,
            b_left: b_left,
            overlap: overlap,
            a_right: a_right,
            b_right: b_right,
        }
    }
}

#[derive(PartialEq,Copy,Clone,Debug)]
pub enum SeekOp {
    SEEK_EQ = 0,
    SEEK_LE = 1,
    SEEK_GE = 2,
}

// TODO consider changing the name of this to make it clear that is only for merge,
// since it uses Blob::SameFileOverflow.
struct CursorIterator {
    csr: MergeCursor,
    peeked: Option<Result<kvp>>,
}

impl CursorIterator {
    fn new(it: MergeCursor) -> CursorIterator {
        CursorIterator { 
            csr: it,
            peeked: None,
        }
    }

    fn count_keys_shadowed(&self) -> usize {
        self.csr.count_keys_shadowed()
    }

    fn count_keys_yielded(&self) -> usize {
        self.csr.count_keys_yielded()
    }

    fn overflows_eaten(self) -> Vec<(PageNum, BlockList)> {
        self.csr.overflows_eaten()
    }

    fn peek(&mut self) -> Option<&Result<kvp>> {
        if self.peeked.is_none() {
            self.peeked = self.get_next();
        }
        match self.peeked {
            Some(ref value) => Some(value),
            None => None,
        }
    }

    fn get_next(&mut self) -> Option<Result<kvp>> {
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
                let v = v.unwrap().into_blob_for_merge();
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

impl Iterator for CursorIterator {
    type Item = Result<kvp>;
    fn next(&mut self) -> Option<Result<kvp>> {
         match self.peeked {
             Some(_) => self.peeked.take(),
             None => self.get_next(),
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
    fn verify(&self, k: &KeyRef, sop: SeekOp, csr: &ICursor) -> Result<()> {
        match self {
            &SeekResult::Invalid => {
                assert!(!csr.IsValid());
            },
            _ => {
                let q = try!(csr.KeyRef());
                let cmp = KeyRef::cmp(&q, k);
                match sop {
                    SeekOp::SEEK_LE => {
                        assert!(cmp == Ordering::Less || cmp == Ordering::Equal);
                    },
                    SeekOp::SEEK_GE => {
                        assert!(cmp == Ordering::Greater || cmp == Ordering::Equal);
                    },
                    SeekOp::SEEK_EQ => {
                        assert!(cmp == Ordering::Equal || cmp == Ordering::Equal);
                    },
                }
            }
        }
        Ok(())
    }

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

pub trait IForwardCursor {
    // TODO does First() belong here?  or should it be implicit in the constructor?
    fn First(&mut self) -> Result<()>;
    fn Next(&mut self) -> Result<()>;

    fn IsValid(&self) -> bool;

    fn KeyRef<'a>(&'a self) -> Result<KeyRef<'a>>;
    fn ValueRef<'a>(&'a self) -> Result<ValueRef<'a>>;

    // TODO maybe rm ValueLength.  but LivingCursor uses it as a fast
    // way to detect whether a value is a tombstone or not.
    fn ValueLength(&self) -> Result<Option<u64>>; // tombstone is None

}

pub trait ICursor : IForwardCursor {
    fn SeekRef(&mut self, k: &KeyRef, sop: SeekOp) -> Result<SeekResult>;
    fn Last(&mut self) -> Result<()>;
    fn Prev(&mut self) -> Result<()>;

}

#[derive(Copy, Clone)]
pub struct DbSettings {
    pub default_page_size: usize,
    pub pages_per_block: PageCount,
    pub sleep_desperate_fresh: u64,
    pub sleep_desperate_young: u64,
    pub sleep_desperate_level: u64,
    pub desperate_fresh: usize,
    pub desperate_young: usize,
    pub desperate_level_factor: u64,
    pub num_leaves_promote: usize,
    // TODO min consecutive recycle
    // TODO fresh free
    // TODO level factor
    // TODO what to promote from level N to N+1
}

pub const DEFAULT_SETTINGS: DbSettings = 
    DbSettings {
        default_page_size: 4096,
        pages_per_block: 256,
        sleep_desperate_fresh: 20,
        sleep_desperate_young: 20,
        sleep_desperate_level: 50,
        desperate_fresh: 128,
        desperate_young: 128,
        desperate_level_factor: 2,
        num_leaves_promote: 16,
    };

#[derive(Clone)]
pub struct SegmentHeaderInfo {
    pub root_page: PageNum,
    buf: std::sync::Arc<Box<[u8]>>,
}

impl std::fmt::Debug for SegmentHeaderInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "SegmentHeaderInfo {{ root_page: {} }}", self.root_page)
    }
}

impl SegmentHeaderInfo {
    pub fn new(root_page: PageNum, buf: std::sync::Arc<Box<[u8]>>) -> Self {
        SegmentHeaderInfo {
            root_page: root_page,
            buf: buf,
        }
    }

    fn count_leaves_for_list_segments(&self) -> Result<PageCount> {
        let pt = try!(PageType::from_u8(self.buf[0]));
        match pt {
            PageType::LEAF_NODE => {
                Ok(1)
            },
            PageType::PARENT_NODE => {
                let (count_leaves, count_tombstones) = try!(ParentPage::count_stuff_for_needs_merge(self.root_page, &self.buf));
                Ok(count_leaves)
            },
        }
    }

    // note that the resulting blocklist here does not include the root page
    fn blocklist_unsorted(&self, 
                          f: &std::sync::Arc<PageCache>,
                          ) -> Result<BlockList> {
        let pt = try!(PageType::from_u8(self.buf[0]));
        let blocks =
            match pt {
                PageType::LEAF_NODE => {
                    let page = try!(LeafPage::new(f.clone(), self.root_page));
                    page.blocklist_unsorted()
                },
                PageType::PARENT_NODE => {
                    let parent = try!(ParentPage::new(f.clone(), self.root_page));
                    try!(parent.blocklist_unsorted())
                },
            };
        Ok(blocks)
    }

    // TODO this is only used for diag purposes
    fn count_keys(&self, 
                          path: &str,
                          f: &std::sync::Arc<PageCache>,
                          ) -> Result<usize> {
        let pt = try!(PageType::from_u8(self.buf[0]));
        let count =
            match pt {
                PageType::LEAF_NODE => {
                    let page = try!(LeafPage::new(f.clone(), self.root_page));
                    page.count_keys()
                },
                PageType::PARENT_NODE => {
                    let parent = try!(ParentPage::new(f.clone(), self.root_page));
                    let mut cursor = try!(ParentCursor::new(parent));
                    let mut count = 0;
                    try!(cursor.First());
                    while cursor.IsValid() {
                        count += 1;
                        try!(cursor.Next());
                    }
                    count
                },
            };
        Ok(count)
    }

}

#[derive(Debug, Clone)]
pub struct SegmentLocation {
    pub root_page: PageNum,
    pub blocks: BlockList,
}

impl SegmentLocation {
    pub fn new(root_page: PageNum, blocks: BlockList) -> Self {
        assert!(!blocks.contains_page(root_page));
        SegmentLocation {
            root_page: root_page,
            blocks: blocks,
        }
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

    pub fn SeekPage<S: Seek>(strm: &mut S, pgsz: usize, pageNumber: PageNum) -> Result<u64> {
        if 0 == pageNumber { 
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
        while i < lim && x[i] == y[i] {
            i = i + 1;
        }
        i
    }

    pub fn prefix_match2(x: &[u8], y: &[u8]) -> usize {
        let len = min(x.len(), y.len());
        let mut i = 0;
        while i < len && x[i] == y[i] {
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
    cur: usize,
    buf: Box<[u8]>,
    last_page_written: PageNum,
}

// TODO bundling cur with the buf almost seems sad, because there are
// cases where we want buf to be mutable but not cur.  :-)

impl PageBuilder {
    fn new(pgsz : usize) -> PageBuilder { 
        let ba = vec![0; pgsz as usize].into_boxed_slice();
        PageBuilder { 
            cur: 0, 
            buf: ba,
            last_page_written: 0,
        } 
    }

    fn buf(&self) -> &[u8] {
        &self.buf
    }

    fn into_buf(self) -> (PageNum, Box<[u8]>) {
        (self.last_page_written, self.buf)
    }

    fn Reset(&mut self) {
        self.cur = 0;
    }

    fn sofar(&self) -> usize {
        self.cur
    }

    fn write_page(&mut self, pw: &mut PageWriter) -> Result<()> {
        self.last_page_written = try!(pw.write_page(self.buf()));
        Ok(())
    }

    fn Write<W: Write>(&self, strm: &mut W) -> io::Result<()> {
        strm.write_all(&*self.buf)
    }

    fn Available(&self) -> usize {
        self.buf.len() - self.cur
    }

    fn PutByte(&mut self, x: u8) {
        self.buf[self.cur] = x;
        self.cur = self.cur + 1;
    }

    fn PutStream2<R: Read>(&mut self, s: &mut R, len: usize) -> io::Result<usize> {
        let n = try!(misc::io::read_fully(s, &mut self.buf[self.cur .. self.cur + len]));
        self.cur = self.cur + n;
        let res : io::Result<usize> = Ok(n);
        res
    }

    fn PutArray(&mut self, ba: &[u8]) {
        self.buf[self.cur .. self.cur + ba.len()].clone_from_slice(ba);
        self.cur = self.cur + ba.len();
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
    subcursors: Box<[PageCursor]>, 
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
                let k = try!(c.KeyRef());
                ka.push(Some(k));
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

    fn new(subs: Vec<PageCursor>) -> MultiCursor {
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

    fn seek(&mut self, k: &KeyRef, sop: SeekOp) -> Result<SeekResult> {
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

impl IForwardCursor for MultiCursor {
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

    fn KeyRef<'a>(&'a self) -> Result<KeyRef<'a>> {
        match self.cur {
            None => {
                Err(Error::CursorNotValid)
            },
            Some(icur) => {
                self.subcursors[icur].KeyRef()
            },
        }
    }

    fn ValueRef<'a>(&'a self) -> Result<ValueRef<'a>> {
        match self.cur {
            None => {
                Err(Error::CursorNotValid)
            },
            Some(icur) => {
                self.subcursors[icur].ValueRef()
            },
        }
    }

    fn ValueLength(&self) -> Result<Option<u64>> {
        match self.cur {
            None => {
                Err(Error::CursorNotValid)
            },
            Some(icur) => {
                self.subcursors[icur].ValueLength()
            },
        }
    }

    fn Next(&mut self) -> Result<()> {
        //println!("MC Next");
        match self.cur {
            None => {
                Err(Error::CursorNotValid)
            },
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

                    fn half(dir: Direction, ki: &KeyRef, subs: &mut [PageCursor]) -> Result<()> {
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

}

impl ICursor for MultiCursor {
    fn Last(&mut self) -> Result<()> {
        for i in 0 .. self.subcursors.len() {
            try!(self.subcursors[i].Last());
        }
        self.cur = try!(self.findMax());
        Ok(())
    }

    // TODO fix Prev like Next
    fn Prev(&mut self) -> Result<()> {
        match self.cur {
            None => {
                Err(Error::CursorNotValid)
            },
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
        //println!("MC SeekRef  k={:?}  sop={:?}", k, sop);
        let sr = try!(self.seek(k, sop));
        if cfg!(expensive_check) 
        {
            try!(sr.verify(k, sop, self));
        }
        Ok(sr)
    }

}

struct MergeCursor { 
    subcursors: Box<[MultiPageCursor]>, 

    // the case where there is only one subcursor is handled specially.
    // there is no need to sort.  sorted is left empty, and cur is Some(0).

    sorted: Box<[(usize, Option<Ordering>)]>,
    cur: Option<usize>, 

    overflows_eaten: Vec<(PageNum, BlockList)>,
    count_keys_yielded: usize,
    count_keys_shadowed: usize,
}

impl MergeCursor {
    fn count_keys_yielded(&self) -> usize {
        self.count_keys_yielded
    }

    fn count_keys_shadowed(&self) -> usize {
        self.count_keys_shadowed
    }

    fn overflows_eaten(self) -> Vec<(PageNum, BlockList)> {
        self.overflows_eaten
    }

    fn sort(&mut self) -> Result<()> {
        // this function should never be called in the case where there is
        // only one subcursor.
        assert!(self.subcursors.len() > 1);

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
                            KeyRef::cmp(kj, kprev)
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

        if cfg!(expensive_check) 
        {
            println!("{:?}", self.sorted);
            for i in 0 .. self.sorted.len() {
                let (n, ord) = self.sorted[i];
                println!("    {:?}", ka[n]);
            }
        }
        Ok(())
    }

    fn findMin(&mut self) -> Result<Option<usize>> {
        // this function should never be called in the case where there is
        // only one subcursor.
        assert!(self.subcursors.len() > 1);

        try!(self.sort());
        let n = self.sorted[0].0;
        if self.sorted[0].1.is_some() {
            Ok(Some(n))
        } else {
            Ok(None)
        }
    }

    fn new(subs: Vec<MultiPageCursor>) -> MergeCursor {
        assert!(subs.len() > 0);
        let s = subs.into_boxed_slice();
        let sorted = 
            if s.len() > 1 {
                let mut sorted = Vec::with_capacity(s.len());
                for i in 0 .. s.len() {
                    sorted.push((i, None));
                }
                sorted
            } else {
                vec![]
            };
        MergeCursor { 
            subcursors: s, 
            sorted: sorted.into_boxed_slice(), 
            cur: None, 
            overflows_eaten: vec![],
            count_keys_shadowed: 0,
            count_keys_yielded: 0,
        }
    }

}

impl IForwardCursor for MergeCursor {
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
        if self.subcursors.len() > 1 {
            self.cur = try!(self.findMin());
        } else {
            self.cur = Some(0);
        }
        Ok(())
    }

    fn KeyRef<'a>(&'a self) -> Result<KeyRef<'a>> {
        match self.cur {
            None => {
                Err(Error::CursorNotValid)
            },
            Some(icur) => {
                self.subcursors[icur].KeyRef()
            },
        }
    }

    fn ValueRef<'a>(&'a self) -> Result<ValueRef<'a>> {
        match self.cur {
            None => {
                Err(Error::CursorNotValid)
            },
            Some(icur) => {
                self.subcursors[icur].ValueRef()
            },
        }
    }

    fn ValueLength(&self) -> Result<Option<u64>> {
        match self.cur {
            None => {
                Err(Error::CursorNotValid)
            },
            Some(icur) => {
                self.subcursors[icur].ValueLength()
            },
        }
    }

    fn Next(&mut self) -> Result<()> {
        match self.cur {
            None => {
                Err(Error::CursorNotValid)
            },
            Some(icur) => {
                self.count_keys_yielded += 1;
                if self.subcursors.len() > 1 {
                    // we need to fix every cursor to point to its min
                    // value > icur.

                    // if perf didn't matter, this would be simple.
                    // call Next on icur.  and call Seek(GE) (and maybe Next)
                    // on every other cursor.

                    // because we keep the list sorted,
                    // each cursor is at most
                    // one step away.

                    // we know that every valid cursor
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
                                    //println!("MergeCursor shadowed: {:?}", k, );
                                    self.count_keys_shadowed += 1;
                                    {
                                        let v = try!(self.subcursors[n].ValueRef());
                                        match v {
                                            ValueRef::Overflowed(_, len, blocks) => {
                                                let k = try!(self.subcursors[n].KeyRef());
                                                //println!("eaten: {:?} -- {:?}", k, blocks);
                                                self.overflows_eaten.push((try!(self.subcursors[n].current_pagenum()), blocks));
                                            },
                                            _ => {
                                            },
                                        }
                                    }
                                    try!(self.subcursors[n].Next());
                                } else {
                                    break;
                                }
                            },
                        }
                    }

                    // now the current cursor
                    try!(self.subcursors[icur].Next());

                    // now re-sort
                    self.cur = try!(self.findMin());
                    Ok(())
                } else {
                    assert!(icur == 0);
                    try!(self.subcursors[icur].Next());
                    Ok(())
                }
            },
        }
    }

}

pub struct LivingCursor { 
    chain: Lend<MultiCursor>,

    // TODO skipped is only for diag purposes
    id: u64,
    skipped: usize,
}

impl Drop for LivingCursor {
    fn drop(&mut self) {
        // TODO skipped is only for diag purposes
        println!("tombstones_skipped,{},{}", self.id, self.skipped);
    }
}

impl LivingCursor {
    pub fn LiveValueRef<'a>(&'a self) -> Result<LiveValueRef<'a>> {
        match try!(self.chain.ValueRef()) {
            ValueRef::Slice(a) => Ok(LiveValueRef::Slice(a)),
            ValueRef::Overflowed(f, len, blocks) => Ok(LiveValueRef::Overflowed(f, len, blocks)),
            ValueRef::Tombstone => Err(Error::Misc(String::from("LiveValueRef tombstone TODO unreachable"))),
        }
    }

    fn skip_tombstones_forward(&mut self) -> Result<()> {
        while self.chain.IsValid() && try!(self.chain.ValueLength()).is_none() {
            self.skipped += 1;
            try!(self.chain.Next());
        }
        Ok(())
    }

    fn skip_tombstones_backward(&mut self) -> Result<()> {
        while self.chain.IsValid() && try!(self.chain.ValueLength()).is_none() {
            self.skipped += 1;
            try!(self.chain.Prev());
        }
        Ok(())
    }

    fn new(id: u64, ch: Lend<MultiCursor>) -> LivingCursor {
        LivingCursor { 
            chain: ch,
            id: id,
            skipped: 0,
        }
    }
}

impl IForwardCursor for LivingCursor {
    fn First(&mut self) -> Result<()> {
        try!(self.chain.First());
        try!(self.skip_tombstones_forward());
        Ok(())
    }

    fn KeyRef<'a>(&'a self) -> Result<KeyRef<'a>> {
        self.chain.KeyRef()
    }

    fn ValueRef<'a>(&'a self) -> Result<ValueRef<'a>> {
        self.chain.ValueRef()
    }

    fn ValueLength(&self) -> Result<Option<u64>> {
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
        //println!("LC Next");
        try!(self.chain.Next());
        try!(self.skip_tombstones_forward());
        Ok(())
    }

}

impl ICursor for LivingCursor {
    fn Last(&mut self) -> Result<()> {
        try!(self.chain.Last());
        try!(self.skip_tombstones_backward());
        Ok(())
    }

    fn Prev(&mut self) -> Result<()> {
        try!(self.chain.Prev());
        try!(self.skip_tombstones_backward());
        Ok(())
    }

    fn SeekRef(&mut self, k: &KeyRef, sop:SeekOp) -> Result<SeekResult> {
        //println!("Living SeekRef  k={:?}  sop={:?}", k, sop);
        let sr = try!(self.chain.SeekRef(k, sop));
        if cfg!(expensive_check) 
        {
            try!(sr.verify(k, sop, self));
        }
        match sop {
            SeekOp::SEEK_GE => {
                if sr.is_valid() && self.chain.ValueLength().unwrap().is_none() {
                    try!(self.skip_tombstones_forward());
                    SeekResult::from_cursor(&*self.chain, k)
                } else {
                    Ok(sr)
                }
            },
            SeekOp::SEEK_LE => {
                if sr.is_valid() && self.chain.ValueLength().unwrap().is_none() {
                    try!(self.skip_tombstones_backward());
                    SeekResult::from_cursor(&*self.chain, k)
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
                //println!("RC bounds checking: {:?}", k);
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
        //println!("PrefixCursor new: {:?}", prefix);
        PrefixCursor { 
            chain : ch,
            prefix: prefix,
        }
    }

    // TODO lifetimes below should be 'c ?
    pub fn KeyRef<'a>(&'a self) -> Result<KeyRef<'a>> {
        if self.IsValid() {
            let k = try!(self.chain.KeyRef());
            //println!("PrefixCursor yielding: {:?}", k);
            //assert!(k.starts_with(&self.prefix));
            Ok(k)
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
            {
                let k = self.chain.KeyRef().unwrap();
                //println!("PrefixCursor chain is valid, its k={:?}", k);
                k.starts_with(&self.prefix)
            }
    }

    pub fn First(&mut self) -> Result<SeekResult> {
        let sr = try!(self.chain.SeekRef(&KeyRef::for_slice(&self.prefix), SeekOp::SEEK_GE));
        Ok(sr)
    }

    pub fn Next(&mut self) -> Result<()> {
        if self.IsValid() {
            try!(self.chain.Next());
            Ok(())
        } else {
            Err(Error::CursorNotValid)
        }
    }

}

#[derive(Hash,PartialEq,Eq,Copy,Clone,Debug)]
#[repr(u8)]
pub enum PageType {
    LEAF_NODE,
    PARENT_NODE,
}

const PAGE_TYPE_OVERFLOW: u8 = 3;

impl PageType {

    #[inline(always)]
    fn to_u8(self) -> u8 {
        match self {
            PageType::LEAF_NODE => 1,
            PageType::PARENT_NODE => 2,
        }
    }

    #[inline(always)]
    fn from_u8(v: u8) -> Result<PageType> {
        match v {
            1 => Ok(PageType::LEAF_NODE),
            2 => Ok(PageType::PARENT_NODE),
            _ => panic!("invalid page type"), // TODO Err(Error::InvalidPageType(v)),
        }
    }
}

mod ValueFlag {
    // TODO remove FLAG_ prefix
    pub const FLAG_OVERFLOW: u8 = 1;
    pub const FLAG_TOMBSTONE: u8 = 2;
}

mod PageFlag {
    // TODO remove FLAG_ prefix
    pub const FLAG_BOUNDARY_NODE: u8 = 2;
}

#[derive(Debug, Clone)]
enum ChildInfo {
    Leaf{
        blocks_overflows: BlockList,
        count_tombstones: u64,
    },
    Parent{
        count_leaves: PageCount, 
        count_tombstones: u64,
    },
}

impl ChildInfo {
    fn need(&self) -> usize {
        match self {
            &ChildInfo::Leaf{
                ref blocks_overflows, 
                count_tombstones,
            } => {
                blocks_overflows.encoded_len()
                + varint::space_needed_for(count_tombstones as u64)
            },
            &ChildInfo::Parent{
                count_leaves, 
                count_tombstones,
            } => {
                varint::space_needed_for(count_leaves as u64)
                + varint::space_needed_for(count_tombstones as u64)
            },
        }
    }

    fn count_leaves(&self) -> PageCount {
        match self {
            &ChildInfo::Leaf{
                ..
            } => {
                1
            },
            &ChildInfo::Parent{
                count_leaves,
                ..
            } => {
                count_leaves
            },
        }
    }

    fn count_tombstones(&self) -> u64 {
        match self {
            &ChildInfo::Leaf{
                count_tombstones,
                ..
            } => {
                count_tombstones
            },
            &ChildInfo::Parent{
                count_tombstones,
                ..
            } => {
                count_tombstones
            },
        }
    }
}

#[derive(Debug, Clone)]
// this struct is used to remember pages we have written, and to
// provide info needed to write parent nodes.
// TODO rename, revisit pub, etc
// TODO ChildItem?
pub struct pgitem {
    pub page: PageNum,
    info: ChildInfo,

    last_key: KeyWithLocation,
}

impl pgitem {
    #[cfg(remove_me)]
    fn new(page: PageNum, blocks: BlockList, last_key: KeyWithLocation) -> pgitem {
        assert!(!blocks.contains_page(page));
        pgitem {
            page: page,
            blocks: blocks,
            last_key: last_key,
        }
    }

    fn need(&self, prefix_len: usize, depth: u8) -> usize {
        let needed = 
            varint::space_needed_for(self.page as u64) 
            + self.info.need()
            + self.last_key.need(prefix_len)
            ;
        needed
    }

}

struct ParentState {
    prefixLen: usize,
    sofar: usize,
    items: Vec<pgitem>,
}

// this enum keeps track of what happened to a key as we
// processed it.  either we determined that it will fit
// inline or we wrote it as an overflow.
#[derive(Debug, Clone)]
enum KeyLocation {
    Inline,
    Overflowed(BlockList),
}

impl ValueLocation {
    fn need(&self) -> usize {
        match self {
            &ValueLocation::Tombstone => {
                1
            },
            &ValueLocation::Buffer(ref vbuf) => {
                let vlen = vbuf.len();
                1 + varint::space_needed_for(vlen as u64) + vlen
            },
            &ValueLocation::Overflowed(vlen, ref blocks) => {
                1 + varint::space_needed_for(vlen as u64) + blocks.encoded_len()
            },
        }
    }

}

impl KeyLocation {
    fn need(&self, k: &[u8], prefixLen: usize) -> usize {
        let klen = k.len();
        assert!(klen >= prefixLen);
        match *self {
            KeyLocation::Inline => {
                0 // no key flags
                + varint::space_needed_for((klen * 2) as u64) 
                + klen 
                - prefixLen
            },
            KeyLocation::Overflowed(ref blocks) => {
                0 // no key flags
                + varint::space_needed_for((klen * 2 + 1) as u64) 
                + blocks.encoded_len()
            },
        }
    }
}

impl KeyWithLocation {
    pub fn key(&self) -> &[u8] {
        &self.key
    }

    fn len_with_overflow_flag(&self) -> u64 {
        // inline key len is stored * 2, always an even number
        // overflowed key len is stored * 2 + 1, always odd
        match self.location {
            KeyLocation::Inline => {
                (self.key.len() * 2) as u64
            },
            KeyLocation::Overflowed(_) => {
                (self.key.len() * 2 + 1) as u64
            },
        }
    }

    fn need(&self, prefix_len: usize) -> usize {
        self.location.need(&self.key, prefix_len)
    }
}

#[derive(Debug, Clone)]
pub struct KeyWithLocation {
    key: Box<[u8]>,
    location: KeyLocation,
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
    Overflowed(u64, BlockList),
}

struct LeafPair {
    key: KeyWithLocation,
    value: ValueLocation,
}

impl LeafPair {
    fn need(&self, prefix_len: usize) -> usize {
        self.key.need(prefix_len) + self.value.need()
    }
}

struct LeafState {
    sofarLeaf: usize,
    keys_in_this_leaf: Vec<LeafPair>,
    prefixLen: usize,
    // TODO why do we need prev_key here?  can't we just look at the
    // last entry of keys_in_this_leaf ?
    prev_key: Option<Box<[u8]>>,

}

fn write_overflow<R: Read>(
                    ba: &mut R, 
                    pw: &mut PageWriter,
                    limit : usize,
                   ) -> Result<(u64, BlockList)> {

    fn write_page<R: Read>(ba: &mut R, pb: &mut PageBuilder, pgsz: usize, pw: &mut PageWriter, blocks: &mut BlockList, limit: usize) -> Result<(usize, bool)> {
        pb.Reset();
        pb.PutByte(PAGE_TYPE_OVERFLOW);
        let boundary = try!(pw.is_group_on_block_boundary(blocks, limit));
        let room = 
            if boundary.is_some() {
                pb.PutByte(PageFlag::FLAG_BOUNDARY_NODE);
                pgsz - 2 - SIZE_32
            } else {
                pb.PutByte(0u8);
                pgsz - 2
            };
        let put = try!(pb.PutStream2(ba, room));
        if put > 0 {
            if let Some(next_page) = boundary {
                pb.SetLastInt32(next_page);
            }
            try!(pw.write_group_page(pb.buf(), blocks, limit));
        } else {
            // there was nothing to write
        }
        Ok((put, put < room))
    };

    let pgsz = pw.page_size();
    let mut pb = PageBuilder::new(pgsz);

    let mut blocks = BlockList::new();
    let mut sofar = 0;
    loop {
        let (put, finished) = try!(write_page(ba, &mut pb, pgsz, pw, &mut blocks, limit));
        sofar += put as u64;
        if finished {
            break;
        }
    }
    //println!("overflow: len = {}  blocks.len = {}  encoded_len: {}", sofar, blocks.len(), blocks.encoded_len());
    Ok((sofar, blocks))
}

// TODO begin mod leaf

fn calc_leaf_page_len(prefix_len: usize, sofar: usize) -> usize {
    2 // page type and flags
    + 2 // stored count
    + varint::space_needed_for(prefix_len as u64)
    + prefix_len
    + sofar // sum of size of all the actual items
}

// TODO return tuple is too big
fn build_leaf(st: &mut LeafState, pb: &mut PageBuilder) -> (KeyWithLocation, BlockList, usize, usize, u64) {
    pb.Reset();
    pb.PutByte(PageType::LEAF_NODE.to_u8());
    pb.PutByte(0u8); // flags
    pb.PutVarint(st.prefixLen as u64);
    if st.prefixLen > 0 {
        pb.PutArray(&st.keys_in_this_leaf[0].key.key[0 .. st.prefixLen]);
    }
    let count_keys_in_this_leaf = st.keys_in_this_leaf.len();
    // TODO should we support more than 64k keys in a leaf?
    // either way, overflow-check this cast.
    pb.PutInt16(count_keys_in_this_leaf as u16);

    fn f(pb: &mut PageBuilder, prefixLen: usize, lp: &LeafPair, list: &mut BlockList, count_tombstones: &mut u64) {
        match lp.key.location {
            KeyLocation::Inline => {
                pb.PutVarint(lp.key.len_with_overflow_flag());
                pb.PutArray(&lp.key.key[prefixLen .. ]);
            },
            KeyLocation::Overflowed(ref blocks) => {
                pb.PutVarint(lp.key.len_with_overflow_flag());
                blocks.encode(pb);
                list.add_blocklist_no_reorder(blocks);
            },
        }
        match lp.value {
            ValueLocation::Tombstone => {
                *count_tombstones += 1;
                pb.PutByte(ValueFlag::FLAG_TOMBSTONE);
            },
            ValueLocation::Buffer(ref vbuf) => {
                pb.PutByte(0u8);
                pb.PutVarint(vbuf.len() as u64);
                pb.PutArray(&vbuf);
            },
            ValueLocation::Overflowed(vlen, ref blocks) => {
                pb.PutByte(ValueFlag::FLAG_OVERFLOW);
                pb.PutVarint(vlen as u64);
                blocks.encode(pb);
                list.add_blocklist_no_reorder(blocks);
            },
        }
    }

    let mut blocks = BlockList::new();
    let mut count_tombstones = 0;

    // deal with all the keys except the last one
    for lp in st.keys_in_this_leaf.drain(0 .. count_keys_in_this_leaf - 1) {
        f(pb, st.prefixLen, &lp, &mut blocks, &mut count_tombstones);
    }

    // now the last key
    assert!(st.keys_in_this_leaf.len() == 1);
    let last_key = {
        let lp = st.keys_in_this_leaf.remove(0); 
        assert!(st.keys_in_this_leaf.is_empty());
        f(pb, st.prefixLen, &lp, &mut blocks, &mut count_tombstones);
        lp.key
    };
    blocks.sort_and_consolidate();
    (last_key, blocks, pb.sofar(), count_keys_in_this_leaf, count_tombstones)
}

fn write_leaf(st: &mut LeafState, 
                pb: &mut PageBuilder, 
                pw: &mut PageWriter,
               ) -> Result<(usize, pgitem)> {
    let (last_key, blocks, len_page, count_pairs, count_tombstones) = build_leaf(st, pb);
    //println!("leaf blocklist: {:?}", blocks);
    //println!("leaf blocklist, len: {}   encoded_len: {:?}", blocks.len(), blocks.encoded_len());
    assert!(st.keys_in_this_leaf.is_empty());
    try!(pb.write_page(pw));
    assert!(!blocks.contains_page(pb.last_page_written));
    // TODO pgitem::new
    let pg = pgitem {
        page: pb.last_page_written, 
        info: ChildInfo::Leaf{
            blocks_overflows: blocks, 
            count_tombstones: count_tombstones,
        },
        last_key: last_key
    };
    st.sofarLeaf = 0;
    st.prefixLen = 0;
    Ok((len_page, pg))
}

fn process_pair_into_leaf(st: &mut LeafState, 
                pb: &mut PageBuilder, 
                pw: &mut PageWriter,
                vbuf: &mut [u8],
                mut pair: kvp,
               ) -> Result<Option<pgitem>> {
    let pgsz = pw.page_size();
    let k = pair.Key;

    if cfg!(expensive_check) 
    {
       // this code can be used to verify that we are being given kvps in order
        match st.prev_key {
            None => {
            },
            Some(ref prev_key) => {
                let c = k.cmp(&prev_key);
                if c != Ordering::Greater {
                    println!("prev_key: {:?}", prev_key);
                    println!("k: {:?}", k);
                    panic!("unsorted keys");
                }
            },
        }
        st.prev_key = Some(k.clone());
    }

    let kloc = {
        // the max limit of an inline key is when that key is the only
        // one in the leaf, and its value is overflowed.  well actually,
        // the reference to an overflowed value can take up a few dozen bytes 
        // in pathological cases, whereas a really short value could be smaller.
        // nevermind that.

        // TODO maybe the max value inline should be configured low enough to
        // ensure that two keys with no prefix can fit in a parent page.  but
        // this is tricky, as the extra child info stuff per item in a parent
        // page can be hard to predict.

        // alternatively, we could set the max value inline to ensure that
        // enough room is left in a parent page to store an overflowed item,
        // but that has some of the same issues, and it also introduces the
        // possibility that a key might be inline in the leaf but overflowed
        // in the parent.

        // also, we could look at the previous key.  the only screw case is
        // when we get 2 or more keys in a row which can't fit in a parent
        // page, so we end up with one parent per leaf, which means the
        // depth of the btree grows forever.  so we could look for this case
        // specifically, and when we see two long keys in a row, overflow the
        // second one.

        // TODO the following code still needs tuning

        // TODO the following code is even more pessimistic now that we do
        // offsets in encoded blocklists
        const PESSIMISTIC_OVERFLOW_INFO_SIZE: usize = 
            1 // number of blocks
            +
            (
            5 // varint, block start page num, worst case
            + 4 // varint, num pages in block, pathological
            )
            * 8 // crazy case
            ;

        let maxKeyInline = 
            pgsz 
            - 2 // page type and flags
            - 2 // count keys
            - 1 // prefixLen of 0
            - varint::space_needed_for((pgsz * 2) as u64) // approx worst case inline key len
            - 1 // value flags
            - 9 // worst case varint value len
            - PESSIMISTIC_OVERFLOW_INFO_SIZE; // overflowed value page

        if k.len() <= maxKeyInline {
            KeyLocation::Inline
        } else {
            // for an overflowed key, there is probably no practical hard limit on the size
            // of the encoded block list.  we want things to be as contiguous as
            // possible, but if the block list won't fit on the usable part of a
            // fresh page, something is seriously wrong.
            // rather than calculate the actual hard limit, we provide an arbitrary
            // fraction of the page which would still be pathological.
            let hard_limit = pgsz / 4;
            let mut r = misc::ByteSliceRead::new(&k);
            let (len, blocks) = try!(write_overflow(&mut r, pw, hard_limit));
            assert!((len as usize) == k.len());
            KeyLocation::Overflowed(blocks)
        }
    };

    // we have decided whether the key is going to be inlined or overflowed.  but
    // we have NOT yet decided which page the key is going on.  will it fit on the
    // current page or does it have to bump to the next one?  we don't know yet.

    // 2 for the page type and flags
    // 2 for the stored count
    const LEAF_PAGE_OVERHEAD: usize = 2 + 2;

    let vloc = {
        let maxValueInline = {
            // TODO use calc_leaf_page_len
            let fixed_costs_on_new_page =
                LEAF_PAGE_OVERHEAD
                + 2 // worst case prefixlen varint
                + kloc.need(&k, 0)
                + 1 // value flags
                + varint::space_needed_for(pgsz as u64) // vlen can't be larger than this for inline
                ;
            assert!(fixed_costs_on_new_page < pgsz);
            let available_for_inline_value_on_new_page = pgsz - fixed_costs_on_new_page;
            available_for_inline_value_on_new_page
        };

        // for the write_overflow calls below, we already know how much 
        // we spent on the key, so we know what our actual limit is for the encoded
        // block list for the value.  the hard limit, basically, is:  we cannot get
        // into a state where the key and value cannot fit on the same page.

        // TODO use calc_leaf_page_len
        let hard_limit_for_value_overflow =
            pgsz
            - LEAF_PAGE_OVERHEAD
            - 2 // worst case prefixlen varint
            - kloc.need(&k, 0)
            - 1 // value flags
            - 9 // worst case varint for value len
            ;

        match pair.Value {
            Blob::Tombstone => {
                ValueLocation::Tombstone
            },
            Blob::Stream(ref mut strm) => {
                // TODO
                // not sure reusing vbuf is worth it.  maybe we should just
                // alloc here.  ownership will get passed into the
                // ValueLocation when it fits.
                let vread = try!(misc::io::read_fully(&mut *strm, &mut vbuf[0 .. maxValueInline + 1]));
                let vbuf = &vbuf[0 .. vread];
                // TODO should be <= ?
                if vread < maxValueInline {
                    // TODO this alloc+copy is unfortunate
                    let mut va = Vec::with_capacity(vbuf.len());
                    for i in 0 .. vbuf.len() {
                        va.push(vbuf[i]);
                    }
                    ValueLocation::Buffer(va.into_boxed_slice())
                } else {
                    let (len, blocks) = try!(write_overflow(&mut (vbuf.chain(strm)), pw, hard_limit_for_value_overflow));
                    ValueLocation::Overflowed(len, blocks)
                }
            },
            Blob::SameFileOverflow(len, blocks) => {
                ValueLocation::Overflowed(len, blocks)
            },
            Blob::Boxed(a) => {
                // TODO should be <= ?
                if a.len() < maxValueInline {
                    ValueLocation::Buffer(a)
                } else {
                    let mut r = misc::ByteSliceRead::new(&a);
                    let (len, blocks) = try!(write_overflow(&mut r, pw, hard_limit_for_value_overflow));
                    assert!(len as usize == a.len());
                    ValueLocation::Overflowed(len, blocks)
                }
            },
        }
    };

    // whether/not the key/value are to be overflowed is now already decided.
    // now all we have to do is decide if this key/value are going into this leaf
    // or not.  note that it is possible to overflow these and then have them not
    // fit into the current leaf and end up landing in the next leaf.

    fn calc_prefix_len(st: &LeafState, k: &[u8], kloc: &KeyLocation) -> usize {
        if st.keys_in_this_leaf.is_empty() {
            0
        } else {
            match kloc {
                &KeyLocation::Inline => {
                    let max_prefix =
                        if st.prefixLen > 0 {
                            st.prefixLen
                        } else {
                            k.len()
                        };
                    bcmp::PrefixMatch(&*st.keys_in_this_leaf[0].key.key, &k, max_prefix)
                },
                &KeyLocation::Overflowed(_) => {
                    // an overflowed key does not change the prefix
                    st.prefixLen
                },
            }
        }
    }

    // note that the LeafPair struct gets ownership of the key provided
    // from above.
    let kwloc = KeyWithLocation {
        key: k,
        location: kloc,
    };
    let lp = LeafPair {
                key: kwloc,
                value: vloc,
                };

    let would_be_prefix_len = calc_prefix_len(&st, &lp.key.key, &lp.key.location);
    assert!(would_be_prefix_len <= lp.key.key.len());
    let would_be_sofar_before_this_pair = 
        if would_be_prefix_len != st.prefixLen {
            assert!(st.prefixLen == 0 || would_be_prefix_len < st.prefixLen);
            // the prefixLen would change with the addition of this key,
            // so we need to recalc sofar
            let sum = st.keys_in_this_leaf.iter().map(|lp| lp.need(would_be_prefix_len) ).sum();;
            sum
        } else {
            st.sofarLeaf
        };
    let fits = {
        let would_be_len_page_before_this_pair = calc_leaf_page_len(would_be_prefix_len, would_be_sofar_before_this_pair);
        if pgsz > would_be_len_page_before_this_pair {
            let available_for_this_pair = pgsz - would_be_len_page_before_this_pair;
            let needed_for_this_pair = lp.need(would_be_prefix_len);
            available_for_this_pair >= needed_for_this_pair
        } else {
            false
        }
    };
    let wrote =
        if !fits {
            assert!(st.keys_in_this_leaf.len() > 0);
            let should_be = calc_leaf_page_len(st.prefixLen, st.sofarLeaf);
            let (len_page, pg) = try!(write_leaf(st, pb, pw));
            //println!("should_be = {}   len_page = {}", should_be, len_page);
            assert!(should_be == len_page);
            assert!(st.sofarLeaf == 0);
            assert!(st.prefixLen == 0);
            assert!(st.keys_in_this_leaf.is_empty());
            st.sofarLeaf = lp.need(st.prefixLen);
            Some(pg)
        } else {
            st.prefixLen = would_be_prefix_len;
            st.sofarLeaf = would_be_sofar_before_this_pair + lp.need(st.prefixLen);
            None
        };

    st.keys_in_this_leaf.push(lp);

    Ok(wrote)
}

fn flush_leaf(st: &mut LeafState, 
                pb: &mut PageBuilder, 
                pw: &mut PageWriter,
               ) -> Result<Option<pgitem>> {
    if !st.keys_in_this_leaf.is_empty() {
        assert!(st.keys_in_this_leaf.len() > 0);
        let should_be = calc_leaf_page_len(st.prefixLen, st.sofarLeaf);
        let (len_page, pg) = try!(write_leaf(st, pb, pw));
        //println!("should_be = {}   len_page = {}", should_be, len_page);
        assert!(should_be == len_page);
        Ok(Some(pg))
    } else {
        Ok(None)
    }
}

fn write_leaves<I: Iterator<Item=Result<kvp>>, >(
                    pw: &mut PageWriter,
                    mut pairs: I,
                    f: std::sync::Arc<PageCache>,
                    ) -> Result<Option<SegmentHeaderInfo>> {

    let mut pb = PageBuilder::new(pw.page_size());

    // TODO this is a buffer just for the purpose of being reused
    // in cases where the blob is provided as a stream, and we need
    // read a bit of it to figure out if it might fit inline rather
    // than overflow.
    let mut vbuf = vec![0; pw.page_size()].into_boxed_slice(); 

    let mut st = LeafState {
        sofarLeaf: 0,
        keys_in_this_leaf: Vec::new(),
        prefixLen: 0,
        prev_key: None,
    };

    let mut chain = ParentNodeWriter::new(pw.page_size(), 1);

    for result_pair in pairs {
        let pair = try!(result_pair);
        if let Some(pg) = try!(process_pair_into_leaf(&mut st, &mut pb, pw, &mut vbuf, pair)) {
            try!(chain.add_child(pw, pg, 0));
        }
    }
    if let Some(pg) = try!(flush_leaf(&mut st, &mut pb, pw)) {
        try!(chain.add_child(pw, pg, 0));
    }

    let (count_parent_nodes, seg) = try!(chain.done(pw));

    let seg =
        match seg {
            Some(seg) => {
                let buf = 
                    match seg.buf {
                        Some(buf) => {
                            buf
                        },
                        None => {
                            let (pb_seg, buf) = pb.into_buf();
                            assert!(pb_seg == seg.root_page);
                            buf
                        },
                    };

                let buf = std::sync::Arc::new(buf);
                try!(f.put(seg.root_page, &buf));
                let seg = SegmentHeaderInfo::new(seg.root_page, buf);
                Some(seg)
            },
            None => {
                None
            },
        };

    Ok(seg)
}

struct WroteMerge {
    segment: Option<SegmentHeaderInfo>,
    nodes_rewritten: Box<[Vec<PageNum>]>,
    nodes_recycled: Box<[usize]>,
    overflows_freed: Vec<BlockList>, // TODO in rewritten leaves
    keys_promoted: usize,
    keys_rewritten: usize,
    keys_shadowed: usize,
    tombstones_removed: usize,
    elapsed_ms: i64,
}

struct WroteSurvivors {
    // TODO segment None can never happen, because a merge from
    // level N to N+1 is not allowed to deplete N, because that
    // would mean that N did not need to be merged.
    segment: Option<SegmentHeaderInfo>,
    nodes_rewritten: Box<[Vec<PageNum>]>,
    nodes_recycled: Box<[usize]>,
    elapsed_ms: i64,
}

fn merge_process_pair(
    pair: kvp,
    st: &mut LeafState,
    pb: &mut PageBuilder,
    pw: &mut PageWriter,
    vbuf: &mut [u8],
    behind: &mut Option<Vec<PageCursor>>,
    chain: &mut ParentNodeWriter,
    dest_level: DestLevel,
    ) -> Result<bool>
{
    fn necessary_tombstone(k: &[u8], 
                    behind: &mut Vec<PageCursor>,
               ) -> Result<bool> {

        // TODO
        // in leveldb, this is simpler.  they don't do a full seek.  rather,
        // they keep a tombstone if any upstream segments have any "files"
        // that overlap the key.  it's a shallower search.
        if behind.is_empty() {
            return Ok(false);
        }

        // TODO would it be faster to just keep behind moving Next() along with chain?
        // then we could optimize cases where we already know that the key is not present
        // in behind because, for example, we hit the max key in behind already.

        let k = KeyRef::Slice(k);

        for mut cursor in behind.iter_mut() {
            if SeekResult::Equal == try!(cursor.SeekRef(&k, SeekOp::SEEK_EQ)) {
                // TODO if the value was found but it is another tombstone...
                return Ok(true);
            }
        }
        Ok(false)
    }

    let keep =
        match behind {
            &mut Some(ref mut behind) => {
                if pair.Value.is_tombstone() {
                    if try!(necessary_tombstone(&pair.Key, behind)) {
                        true
                    } else {
                        //println!("dest,{:?},skip_tombstone_promoted", dest_level, );
                        false
                    }
                } else {
                    true
                }
            },
            &mut None => {
                true
            },
        };

    if keep {
        if let Some(pg) = try!(process_pair_into_leaf(st, pb, pw, vbuf, pair)) {
            try!(chain.add_child(pw, pg, 0));
        }
    }

    Ok(keep)
}

// TODO return tuple too large
fn merge_rewrite_leaf(
                    st: &mut LeafState,
                    pb: &mut PageBuilder,
                    pw: &mut PageWriter,
                    vbuf: &mut [u8],
                    pairs: &mut CursorIterator,
                    leafreader: &LeafPage,
                    behind: &mut Option<Vec<PageCursor>>,
                    chain: &mut ParentNodeWriter,
                    overflows_freed: &mut Vec<BlockList>,
                    dest_level: DestLevel,
                    ) -> Result<(usize, usize, usize, usize)> {

    #[derive(Debug)]
    enum Action {
        Pairs,
        LeafPair,
    }

    let mut i = 0;
    let mut keys_promoted = 0;
    let mut keys_rewritten = 0;
    let mut keys_shadowed = 0;
    let mut tombstones_removed = 0;

    let len = leafreader.count_keys();
    while i < len {
        let action = 
            match pairs.peek() {
                Some(&Err(ref e)) => {
                    // TODO have the action return this error
                    return Err(Error::Misc(format!("inside error pairs: {}", e)));
                },
                Some(&Ok(ref peek_pair)) => {
                    // we are in the middle of a leaf being rewritten

                    // TODO if there is an otherleaf, we know that it
                    // is greater than pair or kvp/i.  assert that.
                    let c = {
                        let k = try!(leafreader.key(i));
                        k.compare_with(&peek_pair.Key)
                    };
                    match c {
                        Ordering::Greater => {
                            Action::Pairs
                        },
                        Ordering::Equal => {
                            // whatever value is coming from the rewritten leaf, it is shadowed
// TODO if the key was overflowed, we need that too.
                            let pair = try!(leafreader.kvp_for_merge(i));
                            match &pair.Value {
                                &Blob::SameFileOverflow(_, ref blocks) => {
                                    overflows_freed.push(blocks.clone());
                                },
                                _ => {
                                },
                            }
                            keys_shadowed += 1;
                            i += 1;
                            Action::Pairs
                        },
                        Ordering::Less => {
                            Action::LeafPair
                        },
                    }
                },
                None => {
                    Action::LeafPair
                },
            };
        //println!("dest,{:?},action,{:?}", dest_level, action);
        match action {
            Action::Pairs => {
                let pair = try!(misc::inside_out(pairs.next())).unwrap();
                if try!(merge_process_pair(pair, st, pb, pw, vbuf, behind, chain, dest_level)) {
                    keys_promoted += 1;
                } else {
                    tombstones_removed += 1;
                }
            },
            Action::LeafPair => {
                let pair = try!(leafreader.kvp_for_merge(i));
                // TODO it is interesting to note that (in not-very-thorough testing), if we
                // put a tombstone check here, it never skips a tombstone.
                if let Some(pg) = try!(process_pair_into_leaf(st, pb, pw, vbuf, pair)) {
                    try!(chain.add_child(pw, pg, 0));
                }
                keys_rewritten += 1;
                i += 1;
            },
        }
    }

    Ok((keys_promoted, keys_rewritten, keys_shadowed, tombstones_removed))
}

// TODO return tuple too large
fn merge_rewrite_parent(
                    st: &mut LeafState,
                    pb: &mut PageBuilder,
                    pw: &mut PageWriter,
                    vbuf: &mut [u8],
                    pairs: &mut CursorIterator,
                    leaf: &mut LeafPage,
                    parent: &ParentPage,
                    behind: &mut Option<Vec<PageCursor>>,
                    chain: &mut ParentNodeWriter,
                    overflows_freed: &mut Vec<BlockList>,
                    nodes_rewritten: &mut Box<[Vec<PageNum>]>,
                    nodes_recycled: &mut Box<[usize]>,
                    dest_level: DestLevel,
                    ) -> Result<(usize, usize, usize, usize)> {

    #[derive(Debug)]
    enum Action {
        RewriteNode,
        RecycleNodes(usize),
    }

    let mut keys_promoted = 0;
    let mut keys_rewritten = 0;
    let mut keys_shadowed = 0;
    let mut tombstones_removed = 0;

    let len = parent.count_items();
// TODO doesn't i increment every time through the loop now?
// since Action::Pairs is gone.
// switch to for loop?
    let mut i = 0;
    while i < len {
        let action = 
            match pairs.peek() {
                Some(&Err(ref e)) => {
                    // TODO have the action return this error
                    return Err(Error::Misc(format!("inside error pairs: {}", e)));
                },
                None => {
                    Action::RecycleNodes(1)
                },
                Some(&Ok(ref peek_pair)) => {
                    let k = &KeyRef::Slice(&peek_pair.Key);
                    match try!(parent.cmp_with_child_last_key(i, k)) {
                        Ordering::Less | Ordering::Equal => {
                            Action::RewriteNode
                        },
                        Ordering::Greater => {
                            // this node can be recycled.
                            // but we can decide to rewrite it anyway.

                            let consecutive_child_nodes_recycleable = {
                                let mut j = i + 1;
                                let mut count = 1;
                                while j < len {
                                    match try!(parent.cmp_with_child_last_key(j, k)) {
                                        Ordering::Greater => {
                                            count += 1;
                                        },
                                        _ => {
                                            break;
                                        },
                                    }
                                    j += 1;
                                }
                                count
                            };

                            // TODO this should be a config setting
                            let min_recycle =
                                match parent.depth() {
                                    1 => 2,
                                    2 => 2,
                                    _ => 1,
                                };
                            if consecutive_child_nodes_recycleable >= min_recycle {
                                Action::RecycleNodes(consecutive_child_nodes_recycleable)
                            } else {
                                Action::RewriteNode
                            }
                        },
                    }
                },
            };
        //println!("dest,{:?},action,{:?}", dest_level, action);
        match action {
            Action::RecycleNodes(n) => {
                //println!("recycling node of depth {}", parent.depth() - 1);
                if let Some(pg) = try!(flush_leaf(st, pb, pw)) {
                    try!(chain.add_child(pw, pg, 0));
                }
                for _ in 0 .. n {
                    let pg = try!(parent.child_pgitem(i));
                    try!(chain.add_child(pw, pg, parent.depth() - 1));
                    nodes_recycled[parent.depth() as usize - 1] += 1;
                    i += 1;
                }
            },
            Action::RewriteNode => {
                //println!("rewriting node of depth {}", parent.depth() - 1);
                nodes_rewritten[parent.depth() as usize - 1].push(parent.child_pagenum(i));
                if parent.depth() == 1 {
                    let pg = try!(parent.child_pgitem(i));
                    try!(leaf.move_to_page(pg.page));
                    let (sub_keys_promoted, sub_keys_rewritten, sub_keys_shadowed, sub_tombstones_removed) = try!(merge_rewrite_leaf(st, pb, pw, vbuf, pairs, leaf, behind, chain, overflows_freed, dest_level));

                    // in the case where we rewrote a page that didn't really NEED to be,
                    // the following assert is not true
                    //assert!(sub_keys_promoted > 0 || sub_tombstones_removed > 0);

                    assert!(sub_keys_rewritten > 0 || sub_keys_shadowed > 0);

                    keys_promoted += sub_keys_promoted;
                    keys_rewritten += sub_keys_rewritten;
                    keys_shadowed += sub_keys_shadowed;
                    tombstones_removed += sub_tombstones_removed;
                } else {
                    let sub = try!(parent.fetch_item_parent(i));
                    let (sub_keys_promoted, sub_keys_rewritten, sub_keys_shadowed, sub_tombstones_removed) = try!(merge_rewrite_parent(st, pb, pw, vbuf, pairs, leaf, &sub, behind, chain, overflows_freed, nodes_rewritten, nodes_recycled, dest_level));
                    keys_promoted += sub_keys_promoted;
                    keys_rewritten += sub_keys_rewritten;
                    keys_shadowed += sub_keys_shadowed;
                    tombstones_removed += sub_tombstones_removed;
                }
                i += 1;
            },
        }
    }

    Ok((keys_promoted, keys_rewritten, keys_shadowed, tombstones_removed))
}

fn write_merge(
                pw: &mut PageWriter,
                pairs: &mut CursorIterator,
                into: &MergingInto,
                mut behind: Option<Vec<PageCursor>>,
                path: &str,
                f: std::sync::Arc<PageCache>,
                dest_level: DestLevel,
                ) -> Result<WroteMerge> {

    let t1 = time::PreciseTime::now();

    // TODO could/should pb and vbuf move into LeafState?

    // TODO this is a buffer just for the purpose of being reused
    // in cases where the blob is provided as a stream, and we need
    // read a bit of it to figure out if it might fit inline rather
    // than overflow.
    let mut vbuf = vec![0; pw.page_size()].into_boxed_slice(); 
    let mut pb = PageBuilder::new(pw.page_size());
    let mut st = LeafState {
        sofarLeaf: 0,
        keys_in_this_leaf: Vec::new(),
        prefixLen: 0,
        prev_key: None,
    };
    let mut chain = ParentNodeWriter::new(pw.page_size(), 1);
    let depths = 
        match *into {
            MergingInto::None => {
                0
            },
            MergingInto::Leaf(ref leaf) => {
                1
            },
            MergingInto::Parent(ref parent) => {
                parent.depth() as usize + 1
            },
        };
    let mut nodes_rewritten = vec![vec![]; depths].into_boxed_slice();
    let mut nodes_recycled = vec![0; depths].into_boxed_slice();

    let mut overflows_freed = vec![];
    let mut keys_promoted = 0;
    let mut keys_rewritten = 0;
    let mut keys_shadowed = 0;
    let mut tombstones_removed = 0;

    match *into {
        MergingInto::None => {
            // nothing to do here
        },
        MergingInto::Leaf(ref leaf) => {
            let (sub_keys_promoted, sub_keys_rewritten, sub_keys_shadowed, sub_tombstones_removed) = try!(merge_rewrite_leaf(&mut st, &mut pb, pw, &mut vbuf, pairs, leaf, &mut behind, &mut chain, &mut overflows_freed, dest_level));
            keys_promoted = sub_keys_promoted;
            keys_rewritten = sub_keys_rewritten;
            keys_shadowed = sub_keys_shadowed;
            tombstones_removed = sub_tombstones_removed;
            nodes_rewritten[0].push(leaf.pagenum);
        },
        MergingInto::Parent(ref parent) => {
            // TODO tune this.  maybe they should mostly be depth - 1 ?
            let rewrite_level = 
                match parent.depth() {
                    1 => 1,
                    2 => 1,
                    3 => 2,
                    4 => 2,
                    5 => 3,
                    6 => 3,
                    _ => 3,
                };
            let it = try!(ParentPage::new(f.clone(), parent.pagenum)).into_node_iter(rewrite_level);
            let mut leaf = LeafPage::new_empty(f.clone(), );
            let mut sub = ParentPage::new_empty(f.clone());
            for r in it {
                let nd = try!(r);
                if nd.depth == rewrite_level {
                    try!(sub.move_to_page(nd.page));
                    let (sub_keys_promoted, sub_keys_rewritten, sub_keys_shadowed, sub_tombstones_removed) = try!(merge_rewrite_parent(&mut st, &mut pb, pw, &mut vbuf, pairs, &mut leaf, &sub, &mut behind, &mut chain, &mut overflows_freed, &mut nodes_rewritten, &mut nodes_recycled, dest_level));
                    keys_promoted += sub_keys_promoted;
                    keys_rewritten += sub_keys_rewritten;
                    keys_shadowed += sub_keys_shadowed;
                    tombstones_removed += sub_tombstones_removed;
                }
                nodes_rewritten[nd.depth as usize].push(nd.page);
            }
        },
    }

    // any pairs left need to get processed
    for pair in pairs {
        let pair = try!(pair);
        if try!(merge_process_pair(pair, &mut st, &mut pb, pw, &mut vbuf, &mut behind, &mut chain, dest_level)) {
            keys_promoted += 1;
        } else {
            tombstones_removed += 1;
        }
    }

    if let Some(pg) = try!(flush_leaf(&mut st, &mut pb, pw)) {
        //println!("dest,{:?},child,{:?}", dest_level, pg);
        try!(chain.add_child(pw, pg, 0));
    }

    let (count_parent_nodes, seg) = try!(chain.done(pw));
    let starting_depth =
        match *into {
            MergingInto::None => {
                None
            },
            MergingInto::Leaf(_) => {
                Some(0)
            },
            MergingInto::Parent(ref p) => {
                Some(p.depth())
            },
        };

    let ending_depth =
        match seg {
            Some(ref seg) => {
                Some(seg.depth)
            },
            None => {
                None
            },
        };

    let seg =
        match seg {
            Some(seg) => {
                let buf = 
                    match seg.buf {
                        Some(buf) => {
                            buf
                        },
                        None => {
                            let (pb_seg, buf) = pb.into_buf();
                            assert!(pb_seg == seg.root_page);
                            buf
                        },
                    };

                let buf = std::sync::Arc::new(buf);
                try!(f.put(seg.root_page, &buf));
                let seg = SegmentHeaderInfo::new(seg.root_page, buf);
                Some(seg)
            },
            None => {
                None
            },
        };

    let t2 = time::PreciseTime::now();
    let elapsed = t1.to(t2);

    let wrote = WroteMerge {
        segment: seg,
        nodes_rewritten: nodes_rewritten,
        nodes_recycled: nodes_recycled,
        overflows_freed: overflows_freed,
        keys_promoted: keys_promoted,
        keys_rewritten: keys_rewritten,
        keys_shadowed: keys_shadowed,
        tombstones_removed: tombstones_removed,
        elapsed_ms: elapsed.num_milliseconds(),
    };
    Ok(wrote)
}

fn survivors_rewrite_immediate_parent_of_skip(
                    pw: &mut PageWriter,
                    skip_pages: &Vec<PageNum>,
                    skip_depth: u8,
                    parent: &ParentPage,
                    chain: &mut ParentNodeWriter,
                    ) -> Result<usize> {

    assert!(parent.depth() == skip_depth + 1);

    let mut nodes_recycled = 0;

// TODO it would be better to do this with only one loop

    fn find_page(parent: &ParentPage, page: PageNum) -> usize {
        for i in 0 .. parent.count_items() {
            if parent.child_pagenum(i) == page {
                return i;
            }
        }
        unreachable!();
    }

    let first_skip = find_page(parent, skip_pages[0]);
    for i in 0 .. skip_pages.len() {
        assert!(parent.child_pagenum(first_skip + i) == skip_pages[i]);
    }
    let last_skip = first_skip + skip_pages.len() - 1;

    for i in 0 .. parent.count_items() {
        if i >= first_skip && i <= last_skip {
            // skip
        } else {
            let pg = try!(parent.child_pgitem(i));
            try!(chain.add_child(pw, pg, parent.depth() - 1));
            nodes_recycled += 1;
        }
    }

    assert!(nodes_recycled == parent.count_items() - skip_pages.len());

    Ok(nodes_recycled)
}

fn survivors_rewrite_ancestor(
                    pw: &mut PageWriter,
                    skip_pages: &Vec<PageNum>,
                    skip_depth: u8,
                    skip_lineage: &Vec<PageNum>,
                    parent: &ParentPage,
                    chain: &mut ParentNodeWriter,
                    nodes_rewritten: &mut Box<[Vec<PageNum>]>,
                    nodes_recycled: &mut Box<[usize]>,
                    ) -> Result<()> {

    assert!(parent.depth() > skip_depth + 1);

    let len = parent.count_items();
    let this_skip = skip_lineage[parent.depth() as usize - 1];
    assert!(this_skip != 0);
    for i in 0 .. len {
        let this_pagenum = parent.child_pagenum(i);
        if this_pagenum == this_skip {
            nodes_rewritten[parent.depth() as usize - 1].push(this_pagenum);
            let sub = try!(parent.fetch_item_parent(i));
            try!(survivors_rewrite_node(pw, skip_pages, skip_depth, skip_lineage, &sub, chain, nodes_rewritten, nodes_recycled,));
        } else {
            let pg = try!(parent.child_pgitem(i));
            try!(chain.add_child(pw, pg, parent.depth() - 1));
            nodes_recycled[parent.depth() as usize - 1] += 1;
        }
    }

    Ok(())
}

fn survivors_rewrite_node(
                    pw: &mut PageWriter,
                    skip_pages: &Vec<PageNum>,
                    skip_depth: u8,
                    skip_lineage: &Vec<PageNum>,
                    parent: &ParentPage,
                    chain: &mut ParentNodeWriter,
                    nodes_rewritten: &mut Box<[Vec<PageNum>]>,
                    nodes_recycled: &mut Box<[usize]>,
                    ) -> Result<()> {
    if parent.depth() - 1 == skip_depth {
        let num_recycled = try!(survivors_rewrite_immediate_parent_of_skip(pw, skip_pages, skip_depth, parent, chain));
        nodes_recycled[skip_depth as usize] += num_recycled;
    } else if parent.depth() - 1 > skip_depth {
        try!(survivors_rewrite_ancestor(pw, skip_pages, skip_depth, skip_lineage, parent, chain, nodes_rewritten, nodes_recycled, ));
    } else {
        panic!();
    }
    Ok(())
}

fn write_survivors(
                pw: &mut PageWriter,
                skip_pages: &Vec<PageNum>,
                skip_depth: u8,
                skip_lineage: &Vec<PageNum>,
                parent: &ParentPage,
                path: &str,
                f: &PageCache,
                dest_level: DestLevel,
                ) -> Result<WroteSurvivors> {

    let t1 = time::PreciseTime::now();

    assert!(!skip_pages.is_empty());
    assert!(skip_lineage[skip_depth as usize] == 0);

    let mut chain = ParentNodeWriter::new(pw.page_size(), 1);
    let mut nodes_rewritten = vec![vec![]; parent.depth() as usize + 1].into_boxed_slice();
    let mut nodes_recycled = vec![0; parent.depth() as usize + 1].into_boxed_slice();

    try!(survivors_rewrite_node(pw, skip_pages, skip_depth, skip_lineage, parent, &mut chain, &mut nodes_rewritten, &mut nodes_recycled, ));
    nodes_rewritten[parent.depth() as usize].push(parent.pagenum);

    let (count_parent_nodes, seg) = try!(chain.done(pw));

    let seg = 
        match seg {
            Some(seg) => {
                match seg.buf {
                    Some(buf) => {
                        let buf = std::sync::Arc::new(buf);
                        try!(f.put(seg.root_page, &buf));
                        Some(SegmentHeaderInfo::new(seg.root_page, buf))
                    },
                    None => {
                        let buf = try!(f.get(seg.root_page));
                        Some(SegmentHeaderInfo::new(seg.root_page, buf))
                    },
                }
            },
            None => {
                None
            },
        };

    let t2 = time::PreciseTime::now();
    let elapsed = t1.to(t2);

    let wrote = WroteSurvivors {
        segment: seg,
        nodes_rewritten: nodes_rewritten,
        nodes_recycled: nodes_recycled,
        elapsed_ms: elapsed.num_milliseconds(),
    };
    Ok(wrote)
}

struct ParentNodeWriter {
    pb: PageBuilder,
    st: ParentState,
    prev_child: Option<pgitem>,
    my_depth: u8,

    result_one: Option<pgitem>,
    results_chain: Option<Box<ParentNodeWriter>>,

    count_emit: usize,
}

impl ParentNodeWriter {
    fn new(
        pgsz: usize, 
        my_depth: u8,
        ) -> Self {
        let st = ParentState {
            prefixLen: 0,
            sofar: 0,
            items: vec![],
        };

        ParentNodeWriter {
            pb: PageBuilder::new(pgsz),
            st: st,
            prev_child: None,
            my_depth: my_depth,
            result_one: None,
            results_chain: None,
            count_emit: 0,
        }
    }

    fn calc_page_len(prefix_len: usize, sofar: usize) -> usize {
        2 // page type and flags
        + 1 // stored depth
        + 2 // stored count
        + varint::space_needed_for(prefix_len as u64) 
        + prefix_len 
        + sofar // sum of size of all the actual items
    }

    fn put_key(&mut self, k: &KeyWithLocation, prefix_len: usize) {
        match k.location {
            KeyLocation::Inline => {
                self.pb.PutArray(&k.key[prefix_len .. ]);
            },
            KeyLocation::Overflowed(ref blocks) => {
                blocks.encode(&mut self.pb);
            },
        }
    }

    fn put_item(&mut self, total_count_leaves: &mut PageCount, total_count_tombstones: &mut u64, item: &pgitem, prefix_len: usize) {
        self.pb.PutVarint(item.page as u64);
        match &item.info {
            &ChildInfo::Leaf{
                ref blocks_overflows,
                count_tombstones,
            } => {
                assert!(self.my_depth == 1);
                blocks_overflows.encode(&mut self.pb);
                self.pb.PutVarint(count_tombstones as u64);
                *total_count_leaves += 1;
                *total_count_tombstones += count_tombstones;
            },
            &ChildInfo::Parent{
                count_leaves, 
                count_tombstones,
                //count_items, 
                //count_bytes,
            } => {
                assert!(self.my_depth > 1);
                self.pb.PutVarint(count_leaves as u64);
                self.pb.PutVarint(count_tombstones as u64);
                //self.pb.PutVarint(count_items as u64);
                //self.pb.PutVarint(count_bytes as u64);
                *total_count_leaves += count_leaves;
                *total_count_tombstones += count_tombstones;
            },
        }

        self.pb.PutVarint(item.last_key.len_with_overflow_flag());
        self.put_key(&item.last_key, prefix_len);
    }

    fn build_parent_page(&mut self,
                      ) -> (KeyWithLocation, PageCount, u64, usize, usize) {
        // TODO? assert!(st.items.len() > 1);
        //println!("build_parent_page, prefixLen: {:?}", st.prefixLen);
        //println!("build_parent_page, items: {:?}", st.items);
        self.pb.Reset();
        self.pb.PutByte(PageType::PARENT_NODE.to_u8());
        self.pb.PutByte(0u8);
        self.pb.PutByte(self.my_depth);
        self.pb.PutVarint(self.st.prefixLen as u64);
        if self.st.prefixLen > 0 {
            self.pb.PutArray(&self.st.items[0].last_key.key[0 .. self.st.prefixLen]);
        }
        let count_items = self.st.items.len();
        self.pb.PutInt16(count_items as u16);
        //println!("self.st.items.len(): {}", self.st.items.len());

        let mut count_leaves = 0;
        let mut count_tombstones = 0;

        // deal with all the items except the last one
        let tmp_count = self.st.items.len() - 1;
        let tmp_vec = self.st.items.drain(0 .. tmp_count).collect::<Vec<_>>();
        let prefix_len = self.st.prefixLen;
        for item in tmp_vec {
            self.put_item(&mut count_leaves, &mut count_tombstones, &item, prefix_len);
        }

        assert!(self.st.items.len() == 1);

        // now the last item
        let last_key = {
            let item = self.st.items.remove(0); 
            let prefix_len = self.st.prefixLen;
            self.put_item(&mut count_leaves, &mut count_tombstones, &item, prefix_len);
            item.last_key
        };
        assert!(self.st.items.is_empty());

        (last_key, count_leaves, count_tombstones, count_items, self.pb.sofar())
    }

    fn write_parent_page(&mut self,
                          pw: &mut PageWriter,
                         ) -> Result<(usize, pgitem)> {
        // assert st.sofar > 0
        let (last_key, count_leaves, count_tombstones, count_items, count_bytes) = self.build_parent_page();
        assert!(self.st.items.is_empty());
        //println!("parent blocklist: {:?}", blocks);
        //println!("parent blocklist, len: {}   encoded_len: {:?}", blocks.len(), blocks.encoded_len());
        try!(self.pb.write_page(pw));
        // TODO pgitem::new
        let pg = pgitem {
            page: self.pb.last_page_written, 
            info: ChildInfo::Parent{
                count_leaves: count_leaves, 
                count_tombstones: count_tombstones,
                //count_items: count_items, 
                //count_bytes: count_bytes,
            },
            last_key: last_key,
        };
        self.st.sofar = 0;
        self.st.prefixLen = 0;
        Ok((count_bytes, pg))
    }

    fn calc_prefix_len(&self, item: &pgitem) -> usize {
        if self.st.items.is_empty() {
            item.last_key.key.len()
        } else {
            if self.st.prefixLen > 0 {
                let a =
                    match &item.last_key.location {
                        &KeyLocation::Inline => {
                            bcmp::PrefixMatch(&*self.st.items[0].last_key.key, &item.last_key.key, self.st.prefixLen)
                        },
                        &KeyLocation::Overflowed(_) => {
                            // an overflowed key does not change the prefix
                            self.st.prefixLen
                        },
                    };
                a
            } else {
                0
            }
        }
    }

    fn add_child_to_current(&mut self, pw: &mut PageWriter, child: pgitem) -> Result<()> {
        let pgsz = pw.page_size();

        if cfg!(expensive_check) 
        {
            // TODO FYI this code is the only reason we need to derive Clone on
            // pgitem and its parts
            match self.prev_child {
                None => {
                },
                Some(ref prev_child) => {
                    let c = child.last_key.key.cmp(&prev_child.last_key.key);
                    if c != Ordering::Greater {
                        println!("prev_child last_key: {:?}", prev_child.last_key);
                        println!("cur child last_key: {:?}", child.last_key);
                        panic!("unsorted child pages");
                    }
                },
            }
            self.prev_child = Some(child.clone());
        }

        // to fit this child into this parent page, we need room for
        // the root page
        // the block list (if child is a leaf) or the page count
        // key len, varint, shifted for overflow flags
        // key
        //     if inline, the key, minus prefix
        //     if overflow, the blocklist (borrowed from child, or not)

        // the key is stored just as it was in the child, inline or overflow.
        // if it is overflowed, we just store the same blocklist reference.

        // claim:  if the key fit inlined in the child, it will
        // fit inlined here in the parent page.

        // TODO we probably need to do this differently.  a parent page
        // that can only fit one item is not useful.  so the maximum size of
        // an inline key in a parent page needs to be configured to ensure
        // that at least two will fit.  so if we are adding the first key
        // to this parent, we can only use about half the available space,
        // because the next one might be the same size.  alternatively, we
        // could say that the first one gets to use as much as it wants
        // as long as it leaves enough for an overflow, and then, when
        // calculating whether the second one will fit, we have to overflow
        // it to make sure that the parent has two items.

        let would_be_prefix_len = self.calc_prefix_len(&child);
        let would_be_sofar_before_this_key = 
            if would_be_prefix_len != self.st.prefixLen {
                assert!(self.st.prefixLen == 0 || would_be_prefix_len < self.st.prefixLen);
                // the prefixLen would change with the addition of this key,
                // so we need to recalc sofar
                let sum = self.st.items.iter().map(|lp| lp.need(would_be_prefix_len, self.my_depth) ).sum();;
                sum
            } else {
                self.st.sofar
            };
        let fits = {
            let would_be_len_page_before_this_key = Self::calc_page_len(would_be_prefix_len, would_be_sofar_before_this_key);
            if pgsz > would_be_len_page_before_this_key {
                let avalable_for_this_key = pgsz - would_be_len_page_before_this_key;
                let fits = avalable_for_this_key >= child.need(would_be_prefix_len, self.my_depth);
                fits
            } else {
                false
            }
        };

        if !fits {
            // if it was not possible to put a second item into this page,
            // then one of them should have been overflowed.
            assert!(self.st.items.len() > 1);
            
            let should_be = Self::calc_page_len(self.st.prefixLen, self.st.sofar);
            let (count_bytes, pg) = try!(self.write_parent_page(pw));
            self.count_emit += 1;
            assert!(should_be == count_bytes);
            try!(self.emit(pw, pg));
            assert!(self.st.sofar == 0);
            assert!(self.st.prefixLen == 0);
            assert!(self.st.items.is_empty());
            self.st.prefixLen = child.last_key.key.len();
            self.st.sofar = child.need(self.st.prefixLen, self.my_depth);
        } else {
            self.st.prefixLen = would_be_prefix_len;
            self.st.sofar = would_be_sofar_before_this_key + child.need(self.st.prefixLen, self.my_depth);
        }

        self.st.items.push(child);

        Ok(())
    }

    fn add_child(&mut self, pw: &mut PageWriter, child: pgitem, depth: u8) -> Result<()> {
        //println!("add_child: my_depth: {}, child_depth: {}, child_page: {} {}", self.my_depth, depth, child.page, if child.blocks.underfull() { "UNDERFULL" } else { "" } );
        if depth == self.my_depth - 1 {
            try!(self.add_child_to_current(pw, child));
        } else if depth == self.my_depth {
            try!(self.flush_page(pw));
            try!(self.emit(pw, child));
        } else {
            try!(self.flush_page(pw));
            try!(self.require_chain(pw));
            let mut chain = self.results_chain.as_mut().unwrap();
            try!(chain.add_child(pw, child, depth));
        }
        Ok(())
    }

    fn require_chain(&mut self, pw: &mut PageWriter) -> Result<()> {
        if self.results_chain.is_some() {
            assert!(self.result_one.is_none());
        } else if self.result_one.is_some() {
            let first = self.result_one.take().unwrap();
            //println!("adding a depth level: {}", self.depth);
            let mut chain = ParentNodeWriter::new(self.pb.buf.len(), self.my_depth + 1);
            try!(chain.add_child(pw, first, self.my_depth));
            self.results_chain = Some(box chain);
        } else {
            let mut chain = ParentNodeWriter::new(self.pb.buf.len(), self.my_depth + 1);
            self.results_chain = Some(box chain);
        }
        Ok(())
    }

    fn emit(&mut self, pw: &mut PageWriter, pg: pgitem) -> Result<()> {
        if self.results_chain.is_some() {
            assert!(self.result_one.is_none());
            let mut chain = self.results_chain.as_mut().unwrap();
            try!(chain.add_child(pw, pg, self.my_depth));
        } else if self.result_one.is_some() {
            try!(self.require_chain(pw));
            assert!(self.results_chain.is_some());
            try!(self.emit(pw, pg));
        } else {
            self.result_one = Some(pg);
        }
        Ok(())
    }

    fn flush_page(&mut self, pw: &mut PageWriter) -> Result<()> {
        if !self.st.items.is_empty() {
            let should_be = Self::calc_page_len(self.st.prefixLen, self.st.sofar);
            let (count_bytes, pg) = try!(self.write_parent_page(pw));
            // TODO try!(pg.verify(pw.page_size(), path, f.clone()));
            self.count_emit += 1;
            assert!(should_be == count_bytes);
            try!(self.emit(pw, pg));
            assert!(self.st.items.is_empty());
        }
        Ok(())
    }

    fn done(mut self, pw: &mut PageWriter, ) -> Result<(usize, Option<ParentNodeSegment>)> {
        if self.result_one.is_none() && self.results_chain.is_none() && self.st.items.len() == 1 {
            // we were given only one child.  instead of writing a parent node,
            // we just return it.  since we didn't write it, we don't have a buffer
            // for it.
            let pg = self.st.items.remove(0);
            let seg = ParentNodeSegment::new(pg.page, None, self.my_depth - 1);
            assert!(self.count_emit == 0);
            Ok((self.count_emit, Some(seg)))
        } else {
            //println!("my_depth: {}, calling flush_page from done", self.my_depth);
            try!(self.flush_page(pw));
            assert!(self.st.items.is_empty());
            if let Some(chain) = self.results_chain {
                assert!(self.result_one.is_none());
                let (count_chain, seg) = try!(chain.done(pw));
                let (pb_page, buf) = self.pb.into_buf();
                let seg = seg.map(
                    |seg| {
                        match seg.buf {
                            Some(buf) => {
                                ParentNodeSegment::new(seg.root_page, Some(buf), seg.depth)
                            },
                            None => {
                                let buf =
                                    if pb_page == seg.root_page {
                                        Some(buf)
                                    } else {
                                        None
                                    };
                                ParentNodeSegment::new(seg.root_page, buf, seg.depth)
                            },
                        }
                    }
                 );
                Ok((self.count_emit + count_chain, seg))
            } else if let Some(pg) = self.result_one {
                let (pgnum_of_buf, buf) = self.pb.into_buf();
                let buf =
                    if pgnum_of_buf == pg.page {
                        Some(buf)
                    } else {
                        None
                    };
                let seg = ParentNodeSegment::new(pg.page, buf, self.my_depth);
                Ok((self.count_emit, Some(seg)))
            } else {
                assert!(self.count_emit == 0);
                Ok((self.count_emit, None))
            }
        }
    }

}

#[derive(Debug, Clone)]
pub struct ParentNodeSegment {
    root_page: PageNum,
    // this is kinda like SegmentHeaderInfo, but the buffer is optional,
    // since ParentNodeWriter sometimes doesn't have the buffer already, 
    // and when that happens, it just returns None and forces the caller
    // to fill it in.
    buf: Option<Box<[u8]>>,
    depth: u8,
}

impl ParentNodeSegment {
    pub fn new(root_page: PageNum, buf: Option<Box<[u8]>>, depth: u8) -> Self {
        ParentNodeSegment {
            root_page: root_page,
            buf: buf,
            depth: depth,
        }
    }

}

fn create_segment<I>(mut pw: PageWriter, 
                        source: I,
                        f: std::sync::Arc<PageCache>,
                       ) -> Result<Option<SegmentHeaderInfo>> where I: Iterator<Item=Result<kvp>> {

    let seg = try!(write_leaves(&mut pw, source, f));

    try!(pw.end());

    Ok(seg)
}

pub struct OverflowReader {
    fs: std::sync::Arc<PageCache>,
    len: u64,
    firstPage: PageNum, // TODO this will be needed later for Seek trait
    buf: Box<[u8]>,
    currentPage: PageNum,
    sofarOverall: u64,
    sofarThisPage: usize,
    bytesOnThisPage: usize,
    offsetOnThisPage: usize,
}
    
impl OverflowReader {
    pub fn new(fs: std::sync::Arc<PageCache>, firstPage: PageNum, len: u64) -> Result<OverflowReader> {
        // TODO the vec new below is really slow.  use a pool?
        let buf = vec![0; fs.page_size()].into_boxed_slice();
        let mut res = 
            OverflowReader {
                fs: fs,
                len: len,
                firstPage: firstPage,
                buf: buf,
                currentPage: firstPage,
                sofarOverall: 0,
                sofarThisPage: 0,
                bytesOnThisPage: 0,
                offsetOnThisPage: 0,
            };
        try!(res.ReadPage());
        Ok(res)
    }

    // TODO consider supporting Seek trait

    fn ReadPage(&mut self) -> Result<()> {
        try!(self.fs.read_page(self.currentPage, &mut *self.buf));
        if self.buf[0] != PAGE_TYPE_OVERFLOW {
            return Err(Error::CorruptFile("first overflow page has invalid page type"));
        }
        self.sofarThisPage = 0;
        self.offsetOnThisPage = 2;
        if self.CheckPageFlag(PageFlag::FLAG_BOUNDARY_NODE) {
            self.bytesOnThisPage = self.buf.len() - 2 - SIZE_32;
        } else {
            self.bytesOnThisPage = self.buf.len() - 2;
        }
        Ok(())
    }

    fn GetLastInt32(&self) -> u32 {
        let at = self.buf.len() - SIZE_32;
        // TODO just self.buf?  instead of making 4-byte slice.
        let a = misc::bytes::extract_4(&self.buf[at .. at + 4]);
        endian::u32_from_bytes_be(a)
    }

    fn CheckPageFlag(&self, f: u8) -> bool {
        0 != (self.buf[1] & f)
    }

    fn Read(&mut self, ba: &mut [u8], offset: usize, wanted: usize) -> Result<usize> {
        if self.sofarOverall >= self.len {
            Ok(0)
        } else {
            if self.sofarThisPage >= self.bytesOnThisPage {
                if self.CheckPageFlag(PageFlag::FLAG_BOUNDARY_NODE) {
                    self.currentPage = self.GetLastInt32();
                } else {
                    self.currentPage += 1;
                }
                try!(self.ReadPage());
            }

            let available = std::cmp::min(self.bytesOnThisPage - self.sofarThisPage, (self.len - self.sofarOverall) as usize);
            let num = std::cmp::min(available, wanted);
            for i in 0 .. num {
                ba[offset + i] = self.buf[self.offsetOnThisPage + self.sofarThisPage + i];
            }
            self.sofarOverall = self.sofarOverall + (num as u64);
            self.sofarThisPage = self.sofarThisPage + num;
            Ok(num)
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

pub struct LeafPage {
    f: std::sync::Arc<PageCache>,
    pr: std::sync::Arc<Box<[u8]>>,
    pagenum: PageNum,

    prefix: Option<Box<[u8]>>,

    pairs: Vec<PairInLeaf>,
    bytes_used_on_page: usize,
}

impl LeafPage {
    fn new(
           f: std::sync::Arc<PageCache>,
           pagenum: PageNum,
          ) -> Result<LeafPage> {

        let buf = try!(f.get(pagenum));
        let mut pairs = vec![];
        let (prefix, bytes_used_on_page) = try!(Self::parse_page(pagenum, &buf, &mut pairs));

        let mut res = LeafPage {
            f: f,
            pagenum: pagenum,
            pr: buf,
            pairs: pairs,
            prefix: prefix,
            bytes_used_on_page: bytes_used_on_page,
        };

        Ok(res)
    }

    fn new_empty(
           f: std::sync::Arc<PageCache>,
          ) -> LeafPage {

        // TODO this is dumb
        let buf = std::sync::Arc::new(vec![0; 1].into_boxed_slice());
        let res = LeafPage {
            f: f,
            pagenum: 0,
            pr: buf,
            pairs: Vec::new(),
            prefix: None,
            bytes_used_on_page: 0, // temporary
        };

        res
    }

    pub fn count_keys(&self) -> usize {
        self.pairs.len()
    }

    // TODO not sure if we need to provide funcs: key_overflows() and value_overflows()

    pub fn overflows(&self) -> Vec<&BlockList> {
        let mut list = vec![];
        for i in 0 .. self.pairs.len() {
            match &self.pairs[i].key {
                &KeyInPage::Inline(_, _) => {
                },
                &KeyInPage::Overflowed(_, ref blocks) => {
                    list.push(blocks);
                },
            }
            match &self.pairs[i].value {
                &ValueInLeaf::Tombstone => {
                },
                &ValueInLeaf::Inline(_, _) => {
                },
                &ValueInLeaf::Overflowed(_, ref blocks) => {
                    list.push(blocks);
                },
            }
        }
        list
    }

    pub fn blocklist_unsorted(&self) -> BlockList {
        let mut list = BlockList::new();
        for blist in self.overflows() {
            list.add_blocklist_no_reorder(blist);
        }
        list
    }

    fn parse_page(pgnum: PageNum, pr: &[u8], pairs: &mut Vec<PairInLeaf>) -> Result<(Option<Box<[u8]>>, usize)> {
        let mut prefix = None;

        let mut cur = 0;
        let pt = try!(PageType::from_u8(misc::buf_advance::get_byte(pr, &mut cur)));
        if pt != PageType::LEAF_NODE {
            panic!(format!("bad leaf page num: {}", pgnum));
            return Err(Error::CorruptFile("leaf has invalid page type"));
        }
        cur = cur + 1; // skip flags

        // TODO fn read_prefix_from_page()
        let prefix_len = varint::read(pr, &mut cur) as usize;
        if prefix_len > 0 {
            // TODO should we just remember prefix as a reference instead of box/copy?
            let mut a = vec![0; prefix_len].into_boxed_slice();
            a.clone_from_slice(&pr[cur .. cur + prefix_len]);
            cur = cur + prefix_len;
            prefix = Some(a);
        } else {
            prefix = None;
        }
        let count_keys = misc::buf_advance::get_u16(pr, &mut cur) as usize;
        // assert count_keys>0

        match pairs.len().cmp(&count_keys) {
            Ordering::Equal => {
            },
            Ordering::Less => {
                pairs.reserve(count_keys);
            },
            Ordering::Greater => {
                pairs.truncate(count_keys);
            },
        }

        for i in 0 .. count_keys {
            let k = try!(KeyInPage::read(pr, &mut cur, prefix_len));
            let v = try!(ValueInLeaf::read(pr, &mut cur));
            let pair = PairInLeaf {
                key: k,
                value: v,
            };

            if i < pairs.len() {
                pairs[i] = pair;
            } else {
                pairs.push(pair);
            }
        }

        Ok((prefix, cur))
    }

    fn count_tombstones(pagenum: PageNum, buf: &[u8]) -> Result<u64> {
        let mut pairs = vec![];
        let (prefix, bytes_used_on_page) = try!(Self::parse_page(pagenum, &buf, &mut pairs));
        let mut total_count_tombstones = 0;
        for p in pairs {
            if p.value.is_tombstone() {
                total_count_tombstones += 1;
            }
        }
        Ok(total_count_tombstones)
    }

    pub fn len_on_page(&self) -> usize {
        self.bytes_used_on_page
    }

    pub fn move_to_page(&mut self, pgnum: PageNum) -> Result<()> {
        //println!("leaf read page: {}", pgnum);
        self.pr = try!(self.f.get(pgnum));
        self.pagenum = pgnum;
        let (prefix, bytes_used_on_page) = try!(Self::parse_page(pgnum, &self.pr, &mut self.pairs));
        self.prefix = prefix;
        self.bytes_used_on_page = bytes_used_on_page;
        Ok(())
    }

    // TODO shouldn't we have a method that returns the KeyInLeaf?
    #[inline]
    fn key<'a>(&'a self, n: usize) -> Result<KeyRef<'a>> { 
        let prefix: Option<&[u8]> = 
            match self.prefix {
                Some(ref b) => Some(b),
                None => None,
            };
        let k = try!(self.pairs[n].key.keyref(&self.pr, prefix, &self.f));
        Ok(k)
    }

    fn kvp_for_merge(&self, n: usize) -> Result<kvp> {
        let k = try!(self.key(n)).into_boxed_slice();
        let v = try!(self.value(n)).into_blob_for_merge();
        let p = kvp {
            Key: k,
            Value: v,
        };
        Ok(p)
    }

    // TODO shouldn't we have a method that returns the ValueInLeaf?
    fn value<'a>(&'a self, n: usize) -> Result<ValueRef<'a>> {
        match &self.pairs[n].value {
            &ValueInLeaf::Tombstone => {
                Ok(ValueRef::Tombstone)
            },
            &ValueInLeaf::Inline(vlen, pos) => {
                Ok(ValueRef::Slice(&self.pr[pos .. pos + vlen]))
            },
            &ValueInLeaf::Overflowed(vlen, ref blocks) => {
                Ok(ValueRef::Overflowed(self.f.clone(), vlen, blocks.clone()))
            },
        }
    }

    // TODO shouldn't we have a method that returns the ValueInLeaf?
    fn value_len<'a>(&'a self, n: usize) -> Result<Option<u64>> {
        match &self.pairs[n].value {
            &ValueInLeaf::Tombstone => {
                Ok(None)
            },
            &ValueInLeaf::Inline(vlen, _) => {
                Ok(Some(vlen as u64))
            },
            &ValueInLeaf::Overflowed(vlen, _) => {
                Ok(Some(vlen))
            },
        }
    }

    fn search(&self, k: &KeyRef, min: usize, max: usize, sop: SeekOp, le: Option<usize>, ge: Option<usize>) -> Result<(Option<usize>, bool)> {
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
                let q = try!(self.key(mid));
                KeyRef::cmp(&q, k)
            };
            match cmp {
                Ordering::Equal => Ok((Some(mid), true)),
                Ordering::Less => self.search(k, (mid+1), max, sop, Some(mid), ge),
                Ordering::Greater => 
                    // we could just recurse with mid-1, but that would overflow if
                    // mod is 0, so we catch that case here.
                    if mid == 0 { 
                        match sop {
                            SeekOp::SEEK_EQ => Ok((None, false)),
                            SeekOp::SEEK_LE => Ok((le, false)),
                            SeekOp::SEEK_GE => Ok((Some(mid), false)),
                        }
                    } else { 
                        self.search(k, min, (mid-1), sop, le, Some(mid))
                    },
            }
        }
    }

}

pub struct LeafCursor {
    page: LeafPage,
    cur: Option<usize>,
}

impl LeafCursor {
    fn new(page: LeafPage) -> LeafCursor {
        LeafCursor {
            page: page,
            cur: None,
        }
    }

    fn seek(&mut self, k: &KeyRef, sop: SeekOp) -> Result<SeekResult> {
        //println!("leaf cursor page: {}  search: kq = {:?},  sop = {:?}", self.page.pagenum, k, sop);
        let tmp_countLeafKeys = self.page.count_keys();
        let (newCur, equal) = try!(self.page.search(k, 0, (tmp_countLeafKeys - 1), sop, None, None));
        self.cur = newCur;
        if self.cur.is_none() {
            //println!("    Invalid");
            Ok(SeekResult::Invalid)
        } else if equal {
            //println!("    Equal");
            Ok(SeekResult::Equal)
        } else {
            //println!("    Unequal");
            Ok(SeekResult::Unequal)
        }
    }

    fn move_to_page(&mut self, pgnum: PageNum) -> Result<()> {
        self.page.move_to_page(pgnum)
    }

    pub fn blocklist_unsorted(&self) -> BlockList {
        self.page.blocklist_unsorted()
    }

}

impl IForwardCursor for LeafCursor {
    fn IsValid(&self) -> bool {
        if let Some(i) = self.cur {
            assert!(i < self.page.count_keys());
            true
        } else {
            false
        }
    }

    fn KeyRef<'a>(&'a self) -> Result<KeyRef<'a>> {
        match self.cur {
            None => {
                Err(Error::CursorNotValid)
            },
            Some(cur) => {
                self.page.key(cur)
            },
        }
    }

    fn ValueRef<'a>(&'a self) -> Result<ValueRef<'a>> {
        match self.cur {
            None => {
                Err(Error::CursorNotValid)
            },
            Some(cur) => {
                self.page.value(cur)
            }
        }
    }

    fn ValueLength(&self) -> Result<Option<u64>> {
        match self.cur {
            None => {
                Err(Error::CursorNotValid)
            },
            Some(cur) => {
                self.page.value_len(cur)
            }
        }
    }

    fn First(&mut self) -> Result<()> {
        self.cur = Some(0);
        Ok(())
    }

    fn Next(&mut self) -> Result<()> {
        match self.cur {
            Some(cur) => {
                if (cur + 1) < self.page.count_keys() {
                    self.cur = Some(cur + 1);
                } else {
                    self.cur = None;
                }
            },
            None => {
            },
        }
        Ok(())
    }

}

impl ICursor for LeafCursor {
    fn Last(&mut self) -> Result<()> {
        self.cur = Some(self.page.count_keys() - 1);
        Ok(())
    }

    fn Prev(&mut self) -> Result<()> {
        match self.cur {
            Some(cur) => {
                if cur > 0 {
                    self.cur = Some(cur - 1);
                } else {
                    self.cur = None;
                }
            },
            None => {
            },
        }
        Ok(())
    }

    fn SeekRef(&mut self, k: &KeyRef, sop: SeekOp) -> Result<SeekResult> {
        //println!("Leaf SeekRef {}  k={:?}  sop={:?}", self.pagenum, k, sop);
        let sr = try!(self.seek(k, sop));
        if cfg!(expensive_check) 
        {
            try!(sr.verify(k, sop, self));
        }
        Ok(sr)
    }

}

pub enum PageCursor {
    Leaf(LeafCursor),
    Parent(ParentCursor),
}

impl PageCursor {
    fn new(
           f: std::sync::Arc<PageCache>,
           pagenum: PageNum,
          ) -> Result<PageCursor> {

        let buf = try!(f.get(pagenum));
        let pt = try!(PageType::from_u8(buf[0]));
        let sub = 
            match pt {
                PageType::LEAF_NODE => {
                    let page = try!(LeafPage::new(f, pagenum));
                    let sub = LeafCursor::new(page);
                    PageCursor::Leaf(sub)
                },
                PageType::PARENT_NODE => {
                    let page = try!(ParentPage::new(f, pagenum));
                    let sub = try!(ParentCursor::new(page));
                    PageCursor::Parent(sub)
                },
            };

        Ok(sub)
    }

    fn pagenum(&self) -> PageNum {
        match self {
            &PageCursor::Leaf(ref c) => {
                c.page.pagenum
            },
            &PageCursor::Parent(ref c) => {
                c.page.pagenum
            },
        }
    }

    pub fn page_type(&self) -> PageType {
        match self {
            &PageCursor::Leaf(_) => {
                PageType::LEAF_NODE
            },
            &PageCursor::Parent(_) => {
                PageType::PARENT_NODE
            },
        }
    }

    pub fn blocklist_unsorted(&self) -> Result<BlockList> {
        match self {
            &PageCursor::Leaf(ref c) => {
                Ok(c.blocklist_unsorted())
            },
            &PageCursor::Parent(ref c) => {
                c.blocklist_unsorted()
            },
        }
    }

    fn move_to_page(&mut self, pg: PageNum) -> Result<()> {
        match self {
            &mut PageCursor::Leaf(ref mut c) => {
                try!(c.move_to_page(pg));
            },
            &mut PageCursor::Parent(ref mut c) => {
                try!(c.move_to_page(pg));
            },
        }
        Ok(())
    }
}

impl IForwardCursor for PageCursor {
    fn IsValid(&self) -> bool {
        match self {
            &PageCursor::Leaf(ref c) => c.IsValid(),
            &PageCursor::Parent(ref c) => c.IsValid(),
        }
    }

    fn KeyRef<'a>(&'a self) -> Result<KeyRef<'a>> {
        match self {
            &PageCursor::Leaf(ref c) => c.KeyRef(),
            &PageCursor::Parent(ref c) => c.KeyRef(),
        }
    }

    fn ValueRef<'a>(&'a self) -> Result<ValueRef<'a>> {
        match self {
            &PageCursor::Leaf(ref c) => c.ValueRef(),
            &PageCursor::Parent(ref c) => c.ValueRef(),
        }
    }

    fn ValueLength(&self) -> Result<Option<u64>> {
        match self {
            &PageCursor::Leaf(ref c) => c.ValueLength(),
            &PageCursor::Parent(ref c) => c.ValueLength(),
        }
    }

    fn First(&mut self) -> Result<()> {
        match self {
            &mut PageCursor::Leaf(ref mut c) => c.First(),
            &mut PageCursor::Parent(ref mut c) => c.First(),
        }
    }

    fn Next(&mut self) -> Result<()> {
        match self {
            &mut PageCursor::Leaf(ref mut c) => c.Next(),
            &mut PageCursor::Parent(ref mut c) => c.Next(),
        }
    }

}

impl ICursor for PageCursor {
    fn Last(&mut self) -> Result<()> {
        match self {
            &mut PageCursor::Leaf(ref mut c) => c.Last(),
            &mut PageCursor::Parent(ref mut c) => c.Last(),
        }
    }

    fn Prev(&mut self) -> Result<()> {
        match self {
            &mut PageCursor::Leaf(ref mut c) => c.Prev(),
            &mut PageCursor::Parent(ref mut c) => c.Prev(),
        }
    }

    fn SeekRef(&mut self, k: &KeyRef, sop: SeekOp) -> Result<SeekResult> {
        //println!("PageCursor SeekRef  k={:?}  sop={:?}", k, sop);
        let sr = 
            match self {
                &mut PageCursor::Leaf(ref mut c) => c.SeekRef(k, sop),
                &mut PageCursor::Parent(ref mut c) => c.SeekRef(k, sop),
            };
        let sr = try!(sr);
        if cfg!(expensive_check) 
        {
            try!(sr.verify(k, sop, self));
        }
        Ok(sr)
    }

}

#[derive(PartialEq,Copy,Clone,Debug)]
pub enum Overlap {
    Less,
    Yes,
    Greater,
}

#[derive(Debug)]
pub enum KeyInPage {
    Inline(usize, usize),
    Overflowed(usize, BlockList),
}

impl KeyInPage {
    #[inline]
    fn read(pr: &[u8], cur: &mut usize, prefix_len: usize) -> Result<Self> {
        let klen = varint::read(pr, cur) as usize;
        if klen == 0 {
            return Err(Error::CorruptFile("key cannot be zero length"));
        }
        let inline = 0 == klen % 2;
        let klen = klen / 2;
        let k = 
            if inline {
                let k = KeyInPage::Inline(klen, *cur);
                *cur += klen - prefix_len;
                k
            } else {
                let blocks = BlockList::read(&pr, cur);
                let k = KeyInPage::Overflowed(klen, blocks);
                k
            };
        Ok(k)
    }

    #[inline]
    fn keyref<'a>(&self, pr: &'a [u8], prefix: Option<&'a [u8]>, f: &std::sync::Arc<PageCache>) -> Result<KeyRef<'a>> { 
        match self {
            &KeyInPage::Inline(klen, at) => {
                match prefix {
                    Some(a) => {
                        Ok(KeyRef::Prefixed(&a, &pr[at .. at + klen - a.len()]))
                    },
                    None => {
                        Ok(KeyRef::Slice(&pr[at .. at + klen]))
                    },
                }
            },
            &KeyInPage::Overflowed(klen, ref blocks) => {
                // TODO KeyRef::Overflow...
                let mut ostrm = try!(OverflowReader::new(f.clone(), blocks.blocks[0].firstPage, klen as u64));
                let mut x_k = Vec::with_capacity(klen);
                try!(ostrm.read_to_end(&mut x_k));
                let x_k = x_k.into_boxed_slice();
                Ok(KeyRef::Boxed(x_k))
            },
        }
    }

    #[inline]
    fn key_with_location(&self, pr: &[u8], prefix: Option<&[u8]>, f: &std::sync::Arc<PageCache>) -> Result<KeyWithLocation> { 
        match self {
            &KeyInPage::Inline(klen, at) => {
                let k = 
                    match prefix {
                        Some(a) => {
                            let k = {
                                let mut k = Vec::with_capacity(klen);
                                k.extend_from_slice(a);
                                k.extend_from_slice(&pr[at .. at + klen - a.len()]);
                                k.into_boxed_slice()
                            };
                            k
                        },
                        None => {
                            let k = {
                                let mut k = Vec::with_capacity(klen);
                                k.extend_from_slice(&pr[at .. at + klen]);
                                k.into_boxed_slice()
                            };
                            k
                        },
                    };
                let kw = KeyWithLocation {
                    key: k,
                    location: KeyLocation::Inline,
                };
                Ok(kw)
            },
            &KeyInPage::Overflowed(klen, ref blocks) => {
                let k = {
                    let mut ostrm = try!(OverflowReader::new(f.clone(), blocks.blocks[0].firstPage, klen as u64));
                    let mut x_k = Vec::with_capacity(klen);
                    try!(ostrm.read_to_end(&mut x_k));
                    let x_k = x_k.into_boxed_slice();
                    x_k
                };
                let kw = KeyWithLocation {
                    key: k,
                    location: KeyLocation::Overflowed(blocks.clone()),
                };
                Ok(kw)
            },
        }
    }

}

#[derive(Debug)]
enum ValueInLeaf {
    Tombstone,
    Inline(usize, usize),
    Overflowed(u64, BlockList),
}

impl ValueInLeaf {
    fn read(pr: &[u8], cur: &mut usize) -> Result<Self> {
        let vflag = misc::buf_advance::get_byte(pr, cur);
        let v = 
            if 0 != (vflag & ValueFlag::FLAG_TOMBSTONE) { 
                ValueInLeaf::Tombstone
            } else {
                let vlen = varint::read(pr, cur);
                if 0 != (vflag & ValueFlag::FLAG_OVERFLOW) {
                    let blocks = BlockList::read(&pr, cur);
                    ValueInLeaf::Overflowed(vlen as u64, blocks)
                } else {
                    let v = ValueInLeaf::Inline(vlen as usize, *cur);
                    *cur = *cur + (vlen as usize);
                    v
                }
            };
        Ok(v)
    }

    fn is_tombstone(&self) -> bool {
        match self {
            &ValueInLeaf::Tombstone => true,
            &ValueInLeaf::Inline(_,_) => false,
            &ValueInLeaf::Overflowed(_,_) => false,
        }
    }

}

#[derive(Debug)]
struct PairInLeaf {
    key: KeyInPage,
    value: ValueInLeaf,
}

#[derive(Debug)]
pub struct ParentPageItem {
    page: PageNum,

    info: ChildInfo,

    // the ChildInfo does NOT contain page, whether it is a block list or a page count

    last_key: KeyInPage,
}

impl ParentPageItem {
    pub fn page(&self) -> PageNum {
        self.page
    }

    pub fn last_key(&self) -> &KeyInPage {
        &self.last_key
    }

    fn count_tombstones(&self) -> u64 {
        self.info.count_tombstones()
    }
}

pub struct Node {
    pub depth: u8,
    pub page: PageNum,
    pub parent: Option<PageNum>,
}

struct NodeIterator {
    stack: Vec<(ParentPage, Option<PageNum>, Option<usize>)>,
    min_depth: u8,
}

impl NodeIterator {
    fn new(top: ParentPage, min_depth: u8) -> Self {
        assert!(top.depth() >= min_depth);
        NodeIterator {
            stack: vec![(top, None, None)],
            min_depth: min_depth,
        }
    }

    fn get_next(&mut self) -> Result<Option<Node>> {
        loop {
            match self.stack.pop() {
                None => {
                    return Ok(None);
                },
                Some((parent, above, None)) => {
                    let depth = parent.depth();
                    let page = parent.pagenum;
                    if depth > self.min_depth {
                        self.stack.push((parent, above, Some(0)));
                    }
                    let nd = Node {
                        depth: depth,
                        page: page,
                        parent: above,
                    };
                    return Ok(Some(nd));
                },
                Some((parent, above, Some(cur))) => {
                    let cur_pagenum = parent.pagenum;
                    if parent.depth() == self.min_depth + 1 {
                        let pg = parent.child_pagenum(cur);
                        let nd = Node {
                            depth: self.min_depth,
                            page: pg,
                            parent: Some(cur_pagenum),
                        };
                        if cur + 1 < parent.children.len() {
                            self.stack.push((parent, above, Some(cur + 1)));
                        }
                        return Ok(Some(nd));
                    } else {
                        let child = try!(parent.fetch_item_parent(cur));
                        if cur + 1 < parent.children.len() {
                            self.stack.push((parent, above, Some(cur + 1)));
                        }
                        self.stack.push((child, Some(cur_pagenum), None));
                    }
                },
            }
        }
    }
}

impl Iterator for NodeIterator {
    type Item = Result<Node>;
    fn next(&mut self) -> Option<Result<Node>> {
        match self.get_next() {
            Ok(None) => {
                None
            },
            Ok(Some(nd)) => {
                Some(Ok(nd))
            },
            Err(e) => {
                Some(Err(e))
            },
        }
    }
}

pub struct ParentPage {
    f: std::sync::Arc<PageCache>,
    pr: std::sync::Arc<Box<[u8]>>,
    pagenum: PageNum,

    prefix: Option<Box<[u8]>>,
    children: Vec<ParentPageItem>,

    bytes_used_on_page: usize,
}

impl ParentPage {
    fn new(
           f: std::sync::Arc<PageCache>,
           pagenum: PageNum,
          ) -> Result<ParentPage> {

        let buf = try!(f.get(pagenum));
        let (prefix, children, bytes_used_on_page) = try!(Self::parse_page(pagenum, &buf));
        assert!(children.len() > 0);

        let res = ParentPage {
            f: f,
            pr: buf,
            pagenum: pagenum,

            prefix: prefix,
            children: children,

            bytes_used_on_page: bytes_used_on_page,
        };

        Ok(res)
    }

    fn new_empty(
           f: std::sync::Arc<PageCache>,
          ) -> ParentPage {

        // TODO this is dumb
        let buf = std::sync::Arc::new(vec![0; 1].into_boxed_slice());

        let res = ParentPage {
            f: f,
            pr: buf,
            pagenum: 0,

            prefix: None,
            children: vec![],

            bytes_used_on_page: 0,
        };

        res
    }

    pub fn len_on_page(&self) -> usize {
        self.bytes_used_on_page
    }

    fn child_blocklist(&self, i: usize) -> Result<BlockList> {
        match self.children[i].info {
            ChildInfo::Leaf{
                ref blocks_overflows,
                ..
            } => {
                assert!(self.depth() == 1);
                Ok(blocks_overflows.clone())
            },
            ChildInfo::Parent{..} => {
                assert!(self.depth() > 1);
                let pagenum = self.children[i].page;

                let page = try!(ParentPage::new(self.f.clone(), pagenum));
                page.blocklist_unsorted()
                // TODO assert that count matches the blocklist?
            },
        }
    }

    pub fn child_key<'a>(&'a self, i: usize) -> Result<KeyRef<'a>> {
        let last_key = try!(self.key(&self.children[i].last_key));
        Ok(last_key)
    }

    fn child_pgitem(&self, i: usize) -> Result<pgitem> {
        // TODO this func shows up as a common offender of malloc calls
        let last_key = try!(self.key_with_location(&self.children[i].last_key));
        // TODO pgitem::new
        let pg = pgitem {
            page: self.children[i].page,
            info: self.children[i].info.clone(), // TODO sad clone
            last_key: last_key,
        };
        Ok(pg)
    }

    pub fn depth(&self) -> u8 {
        self.pr[2]
    }

    pub fn is_grandparent(&self) -> bool {
        // depth is never 0
        // when children are leaves, depth is 1
        self.depth() > 1
    }

    // TODO name
    pub fn make_leaf_page(&self) -> LeafPage {
        LeafPage::new_empty(self.f.clone())
    }

    // TODO name
    pub fn make_parent_page(&self) -> ParentPage {
        ParentPage::new_empty(self.f.clone())
    }

    pub fn into_node_iter(self, min_depth: u8) -> Box<Iterator<Item=Result<Node>>> {
        box NodeIterator::new(self, min_depth)
    }

    fn count_leaves(&self) -> PageCount {
        // TODO if depth is 1, just return children.len()
        self
            .children
            .iter()
            .map(|x| x.info.count_leaves())
            .sum()
    }

    fn blocklist_unsorted(&self) -> Result<BlockList> {
        let mut list = BlockList::new();
        for i in 0 .. self.children.len() {
            // we do not add the blocklist for any overflow keys,
            // because we don't own that blocklist.  it is simply a reference
            // to the blocklist for an overflow key when it was written into
            // its leaf.
            list.add_page_no_reorder(self.children[i].page);
            let blocks = try!(self.child_blocklist(i));
            list.add_blocklist_no_reorder(&blocks);
        }
        Ok(list)
    }

    pub fn count_items(&self) -> usize {
        self.children.len()
    }

    #[inline]
    fn key<'a>(&'a self, k: &KeyInPage) -> Result<KeyRef<'a>> { 
        let prefix: Option<&[u8]> = 
            match self.prefix {
                Some(ref b) => Some(b),
                None => None,
            };
        let k = try!(k.keyref(&self.pr, prefix, &self.f));
        Ok(k)
    }

    fn key_with_location(&self, k: &KeyInPage) -> Result<KeyWithLocation> { 
        let prefix: Option<&[u8]> = 
            match self.prefix {
                Some(ref b) => Some(b),
                None => None,
            };
        let k = try!(k.key_with_location(&self.pr, prefix, &self.f));
        Ok(k)
    }

    fn parse_page(pgnum: PageNum, pr: &[u8]) -> Result<(Option<Box<[u8]>>, Vec<ParentPageItem>, usize)> {
        // TODO it would be nice if this could accept a vec and reuse
        // it, like the leaf version does.
        let mut cur = 0;
        let pt = try!(PageType::from_u8(misc::buf_advance::get_byte(pr, &mut cur)));
        if  pt != PageType::PARENT_NODE {
            panic!(format!("bad parent pagenum is {}", pgnum));
            return Err(Error::CorruptFile("parent page has invalid page type"));
        }
        let flags = misc::buf_advance::get_byte(pr, &mut cur);
        let depth = misc::buf_advance::get_byte(pr, &mut cur);
        assert!(depth > 0);
        let prefix_len = varint::read(pr, &mut cur) as usize;
        let prefix = {
            if prefix_len > 0 {
                // TODO should we just remember prefix as a reference instead of box/copy?
                let mut a = vec![0; prefix_len].into_boxed_slice();
                a.clone_from_slice(&pr[cur .. cur + prefix_len]);
                cur = cur + prefix_len;
                Some(a)
            } else {
                None
            }
        };
        let count_items = misc::buf_advance::get_u16(pr, &mut cur) as usize;
        // TODO count_items has gotta be > 1, right?  or does it?
        //println!("count_items: {}", count_items);
        let mut children = Vec::with_capacity(count_items);

        for i in 0 .. count_items {
            let page = varint::read(pr, &mut cur) as PageNum;
            //println!("page: {}", page);

            let info = 
                if depth == 1 {
                    let blocks_overflows = BlockList::read(pr, &mut cur);
                    let count_tombstones = varint::read(pr, &mut cur) as u64;
                    ChildInfo::Leaf{
                        blocks_overflows: blocks_overflows,
                        count_tombstones: count_tombstones,
                    }
                } else {
                    let count_leaves = varint::read(pr, &mut cur) as PageCount;
                    let count_tombstones = varint::read(pr, &mut cur) as u64;
                    ChildInfo::Parent{
                        count_leaves: count_leaves, 
                        count_tombstones: count_tombstones,
                    }
                };
            //println!("childinfo: {:?}", blocks);

            let last_key = try!(KeyInPage::read(pr, &mut cur, prefix_len));

            let pg = ParentPageItem {
                page: page, 
                info: info,
                last_key: last_key,
            };
            children.push(pg);
        }

        //println!("children parsed: {:?}", children);

        Ok((prefix, children, cur))
    }

    fn count_stuff_for_needs_merge(pgnum: PageNum, buf: &[u8]) -> Result<(PageCount, u64)> {
        let (_, children, _) = try!(Self::parse_page(pgnum, buf));
        let mut total_count_leaves = 0;
        let mut total_count_tombstones = 0;
        for item in children {
            match item.info {
                ChildInfo::Leaf{count_tombstones, ..} => {
                    total_count_leaves += 1;
                    total_count_tombstones += count_tombstones;
                },
                ChildInfo::Parent{count_leaves, count_tombstones, ..} => {
                    total_count_leaves += count_leaves;
                    total_count_tombstones += count_tombstones;
                },
            }
        }
        Ok((total_count_leaves, total_count_tombstones))
    }

    fn choose_one(&self) -> usize {

        // if tombstones are present, prioritize promoting them

        let mut result = 0;
        let mut max = self.children[0].count_tombstones();
        for i in 1 .. self.children.len() {
            if self.children[i].count_tombstones() > max {
                max = self.children[i].count_tombstones();
                result = i;
            }
        }

        if max == 0 {
            // there are no tombstones

            // we need to pick a child, and it kinda doesn't matter which
            // one, but we don't need the number to be really random, and we
            // don't want to take a dependency on time or rand just for this,
            // so we use the page number as a lame source of randomness.

            // TODO later, we probably want to be more clever.  leveldb 
            // remembers the key range of the last compaction and picks up
            // where it left off.  we also will eventually want the ability
            // to have two merges going on in the same level in different
            // threads, which should be fine if the key ranges do not overlap
            // the same stuff, and if we can fix up the parent node at the end.

            let i = ((self.pagenum as u32) % (self.children.len() as u32)) as usize;
            i
        } else {
            result
        }
    }

    fn choose_range(&self, want: usize) -> usize {

        // if tombstones are present, prioritize promoting them

        let mut cur_sum = 0;
        let mut winning_sum = 0;
        let mut winning_i = 0;
        for i in 0 .. self.children.len() {
            if i >= want {
                cur_sum -= self.children[i - want].count_tombstones();
            }
            cur_sum += self.children[i].count_tombstones();
            if i + 1 >= want {
                if cur_sum > winning_sum {
                    winning_sum = cur_sum;
                    winning_i = i + 1 - want;
                }
            }
        }

        if winning_sum == 0 {
            // there are no tombstones

            // we need to pick a child, and it kinda doesn't matter which
            // one, but we don't need the number to be really random, and we
            // don't want to take a dependency on time or rand just for this,
            // so we use the page number as a lame source of randomness.

            // TODO later, we probably want to be more clever.  leveldb 
            // remembers the key range of the last compaction and picks up
            // where it left off.  we also will eventually want the ability
            // to have two merges going on in the same level in different
            // threads, which should be fine if the key ranges do not overlap
            // the same stuff, and if we can fix up the parent node at the end.

            let count = self.children.len() - want + 1;
            let i = ((self.pagenum as u32) % (count as u32)) as usize;
            assert!(i + want - 1 < self.children.len());
            i
        } else {
            assert!(winning_i + want - 1 < self.children.len());
            winning_i
        }
    }

    fn choose_nodes_to_promote(&self, depth: u8, lineage: &mut Vec<PageNum>, want: usize) -> Result<(Vec<PageNum>, u64)> {
        lineage[self.depth() as usize] = self.pagenum;

        if self.depth() - 1 == depth {
            let i =
                if self.children.len() <= want {
                    0
                } else {
                    let i = self.choose_range(want);
                    assert!(i + want - 1 < self.children.len());
                    i
                };
            let avail = self.children.len() - i;
            let take = std::cmp::min(avail, want);
            //println!("any_node,{},{},{}", self.children.len(), i, take);
            let v = 
                self.children[i .. i + take]
                .iter()
                .map(|x| x.page)
                .collect::<Vec<_>>();
            let count_tombstones = 
                self.children[i .. i + take]
                .iter()
                .map(|x| x.count_tombstones())
                .sum();
            Ok((v, count_tombstones))
        } else {
            assert!(self.depth() - 1 > depth);
            assert!(self.depth() > 1);

            let i = self.choose_one();
            let pagenum = self.child_pagenum(i);

            let page = try!(ParentPage::new(self.f.clone(), pagenum));
            page.choose_nodes_to_promote(depth, lineage, want)
        }
    }

    pub fn move_to_page(&mut self, pgnum: PageNum) -> Result<()> {
        self.pr = try!(self.f.get(pgnum));
        self.pagenum = pgnum;
        let (prefix, children, bytes_used_on_page) = try!(Self::parse_page(pgnum, &self.pr));
        self.prefix = prefix;
        self.children = children;
        self.bytes_used_on_page = bytes_used_on_page;

        Ok(())
    }

    fn cmp_with_child_last_key(&self, i: usize, kq: &KeyRef) -> Result<Ordering> {
        let child_key = try!(self.key(&self.children[i].last_key));
        Ok(KeyRef::cmp(kq, &child_key))
    }

    fn get_child_cursor(&self, i: usize) -> Result<PageCursor> {
        let sub = try!(PageCursor::new(self.f.clone(), self.children[i].page));
        Ok(sub)
    }

    pub fn child_pagenum(&self, i: usize) -> PageNum {
        self.children[i].page
    }

    fn fetch_item_parent(&self, i: usize) -> Result<ParentPage> {
        let child = try!(ParentPage::new(self.f.clone(), self.children[i].page));
        Ok(child)
    }

}

pub struct ParentCursor {
    page: ParentPage,
    cur: Option<usize>,
    sub: Box<PageCursor>,
}

impl ParentCursor {
    fn new(page: ParentPage,) -> Result<ParentCursor> {

        // TODO so, er, ParentPage actually does know its depth/child_type
        let sub = try!(page.get_child_cursor(0));

        let res = ParentCursor {
            page: page,
            cur: Some(0),
            sub: box sub,
        };

        Ok(res)
    }

    fn set_child(&mut self, i: usize) -> Result<()> {
        //println!("set_child i={}  child_pagenum={}   self_pagenum={}", i, self.page.child_pagenum(i), self.page.pagenum);
        match self.cur {
            Some(n) => {
                // TODO any chance this is a problem?
                if n == i {
                    //println!("ParentCursor already on page index {}, which is pagenum {}", i, self.page.children[i].page);
                    // already there
                    return Ok(());
                }
            },
            None => {
            },
        }
        let pagenum = self.page.child_pagenum(i);
        // TODO or should we just get a new sub PageCursor?
        try!(self.sub.move_to_page(pagenum));
        self.cur = Some(i);
        Ok(())
    }

    fn move_to_page(&mut self, pgnum: PageNum) -> Result<()> {
        try!(self.page.move_to_page(pgnum));
        let pagenum = self.page.child_pagenum(0);
        try!(self.sub.move_to_page(pagenum));
        self.cur = Some(0);
        Ok(())
    }

    pub fn blocklist_unsorted(&self) -> Result<BlockList> {
        self.page.blocklist_unsorted()
    }

    fn seek(&mut self, k: &KeyRef, sop: SeekOp) -> Result<SeekResult> {
        //println!("parent page: {}  search: kq = {:?},  sop = {:?}", self.page.pagenum, k, sop);

        for i in 0 .. self.page.count_items() {
            match try!(self.page.cmp_with_child_last_key(i, k)) {
                Ordering::Less | Ordering::Equal => {
                    try!(self.set_child(i));
                    let sr = try!(self.sub.SeekRef(k, sop));
                    if i > 0 && sop == SeekOp::SEEK_LE && sr == SeekResult::Invalid {
                        try!(self.set_child(i - 1));
                        try!(self.sub.Last());
                        return Ok(SeekResult::Unequal);
                    } else {
                        return Ok(sr)
                    }
                },
                Ordering::Greater => {
                    // keep looking
                },
            }
        }
        //println!("parent page seek after loop");
        // the only way to exit the loop to here is for the key to be
        // greater than the last item.
        match sop {
            SeekOp::SEEK_LE => {
                let last_child = self.page.count_items() - 1;
                try!(self.set_child(last_child));
                try!(self.sub.Last());
                return Ok(SeekResult::Unequal);
            },
            SeekOp::SEEK_GE => {
                self.cur = None;
                return Ok(SeekResult::Invalid);
            },
            SeekOp::SEEK_EQ => {
                self.cur = None;
                return Ok(SeekResult::Invalid);
            },
        }
    }

}

impl IForwardCursor for ParentCursor {
    fn IsValid(&self) -> bool {
        match self.cur {
            None => false,
            Some(_) => {
                self.sub.IsValid()
            },
        }
    }

    fn KeyRef<'a>(&'a self) -> Result<KeyRef<'a>> {
        match self.cur {
            None => {
                Err(Error::CursorNotValid)
            },
            Some(_) => {
                self.sub.KeyRef()
            },
        }
    }

    fn ValueRef<'a>(&'a self) -> Result<ValueRef<'a>> {
        match self.cur {
            None => {
                Err(Error::CursorNotValid)
            },
            Some(_) => {
                self.sub.ValueRef()
            },
        }
    }

    fn ValueLength(&self) -> Result<Option<u64>> {
        match self.cur {
            None => {
                Err(Error::CursorNotValid)
            },
            Some(_) => {
                self.sub.ValueLength()
            },
        }
    }

    fn First(&mut self) -> Result<()> {
        try!(self.set_child(0));
        self.sub.First()
    }

    fn Next(&mut self) -> Result<()> {
        match self.cur {
            None => {
                Err(Error::CursorNotValid)
            },
            Some(i) => {
                try!(self.sub.Next());
                if !self.sub.IsValid() && i + 1 < self.page.count_items() {
                    try!(self.set_child(i + 1));
                    self.sub.First()
                } else {
                    Ok(())
                }
            },
        }
    }

}

impl ICursor for ParentCursor {
    fn Last(&mut self) -> Result<()> {
        let last_child = self.page.count_items() - 1;
        try!(self.set_child(last_child));
        self.sub.Last()
    }

    fn Prev(&mut self) -> Result<()> {
        match self.cur {
            None => {
                Err(Error::CursorNotValid)
            },
            Some(i) => {
                try!(self.sub.Prev());
                if !self.sub.IsValid() && i > 0 {
                    try!(self.set_child(i - 1));
                    self.sub.Last()
                } else {
                    Ok(())
                }
            },
        }
    }

    fn SeekRef(&mut self, k: &KeyRef, sop: SeekOp) -> Result<SeekResult> {
        let sr = try!(self.seek(k, sop));
        if cfg!(expensive_check) 
        {
            try!(sr.verify(k, sop, self));
        }
        Ok(sr)
    }

}

pub struct MultiPageCursor {
    children: Vec<PageNum>,
    cur: Option<usize>,
    sub: Box<PageCursor>,
}

impl MultiPageCursor {
    fn new(
           f: std::sync::Arc<PageCache>,
           children: Vec<PageNum>,
          ) -> Result<MultiPageCursor> {

        assert!(children.len() > 0);

        let sub = try!(PageCursor::new(f, children[0]));

        let res = MultiPageCursor {
            children: children,
            cur: Some(0),
            sub: box sub,

        };

        Ok(res)
    }

    fn current_pagenum(&self) -> Result<PageNum> {
        match self.cur {
            Some(i) => {
                Ok(self.children[i])
            },
            None => {
                Err(Error::CursorNotValid)
            },
        }
    }

    fn set_child(&mut self, i: usize) -> Result<()> {
        match self.cur {
            Some(n) => {
                if n == i {
                    // already there
                    return Ok(());
                }
            },
            None => {
            },
        }
        let pagenum = self.children[i];
        try!(self.sub.move_to_page(pagenum));
        self.cur = Some(i);
        Ok(())
    }

}

impl IForwardCursor for MultiPageCursor {
    fn IsValid(&self) -> bool {
        match self.cur {
            None => false,
            Some(_) => {
                self.sub.IsValid()
            },
        }
    }

    fn KeyRef<'a>(&'a self) -> Result<KeyRef<'a>> {
        match self.cur {
            None => {
                Err(Error::CursorNotValid)
            },
            Some(_) => {
                self.sub.KeyRef()
            },
        }
    }

    fn ValueRef<'a>(&'a self) -> Result<ValueRef<'a>> {
        match self.cur {
            None => {
                Err(Error::CursorNotValid)
            },
            Some(_) => {
                self.sub.ValueRef()
            },
        }
    }

    fn ValueLength(&self) -> Result<Option<u64>> {
        match self.cur {
            None => {
                Err(Error::CursorNotValid)
            },
            Some(_) => {
                self.sub.ValueLength()
            },
        }
    }

    fn First(&mut self) -> Result<()> {
        try!(self.set_child(0));
        self.sub.First()
    }

    fn Next(&mut self) -> Result<()> {
        match self.cur {
            None => {
                Err(Error::CursorNotValid)
            },
            Some(i) => {
                try!(self.sub.Next());
                if !self.sub.IsValid() && i + 1 < self.children.len() {
                    try!(self.set_child(i + 1));
                    self.sub.First()
                } else {
                    Ok(())
                }
            },
        }
    }

}

#[derive(Clone)]
struct HeaderData {
    fresh: Vec<SegmentHeaderInfo>,
    young: Vec<SegmentHeaderInfo>,
    levels: Vec<Option<SegmentHeaderInfo>>,

    changeCounter: u64,
    mergeCounter: u64,
}

struct HeaderStuff {
    data: HeaderData,
    f: File,
}

// TODO how big should the header be?  this defines the minimum size of a
// database file.
const HEADER_SIZE_IN_BYTES: usize = 4096;

fn read_header(path: &str) -> Result<(HeaderData, PageCache, PageNum)> {
    fn read<R>(fs: &mut R) -> Result<Box<[u8]>> where R : Read {
        let mut pr = vec![0; HEADER_SIZE_IN_BYTES].into_boxed_slice();
        let got = try!(misc::io::read_fully(fs, &mut pr));
        if got < HEADER_SIZE_IN_BYTES {
            Err(Error::CorruptFile("invalid header"))
        } else {
            Ok(pr)
        }
    }

    fn parse(pr: &Box<[u8]>, f: File) -> Result<(HeaderData, PageCache)> {
        fn read_segment_list(pr: &Box<[u8]>, cur: &mut usize) -> Result<Vec<PageNum>> {
            let count = varint::read(&pr, cur) as usize;
            let mut a = Vec::with_capacity(count);
            for _ in 0 .. count {
                let root_page = varint::read(&pr, cur) as PageNum;
                a.push(root_page);
            }
            Ok(a)
        }

        fn fix_segment_list(segments: Vec<PageNum>, f: &PageCache) -> Result<Vec<SegmentHeaderInfo>> {
            let mut v = Vec::with_capacity(segments.len());
            for page in segments.iter() {
                let pagenum = *page;
                let buf = try!(f.get(pagenum));
                let seg = SegmentHeaderInfo::new(pagenum, buf);
                v.push(seg);
            }
            Ok(v)
        }

        fn fix_main_segment_list(segments: Vec<PageNum>, f: &PageCache) -> Result<Vec<Option<SegmentHeaderInfo>>> {
            let mut v = Vec::with_capacity(segments.len());
            for page in segments.iter() {
                let pagenum = *page;

                if pagenum == 0 {
                    v.push(None)
                } else {
                    let buf = try!(f.get(pagenum));
                    let seg = SegmentHeaderInfo::new(pagenum, buf);
                    v.push(Some(seg));
                }
            }
            Ok(v)
        }

        let mut cur = 0;

        let pgsz = misc::buf_advance::get_u32(&pr, &mut cur) as usize;
        let changeCounter = varint::read(&pr, &mut cur);
        let mergeCounter = varint::read(&pr, &mut cur);

        let f = PageCache::new(f, pgsz);

        let fresh = try!(read_segment_list(pr, &mut cur));
        let young = try!(read_segment_list(pr, &mut cur));
        let levels = try!(read_segment_list(pr, &mut cur));

        let fresh = try!(fix_segment_list(fresh, &f));
        let young = try!(fix_segment_list(young, &f));
        let levels = try!(fix_main_segment_list(levels, &f));

        let hd = 
            HeaderData {
                fresh: fresh,
                young: young,
                levels: levels,
                changeCounter: changeCounter,
                mergeCounter: mergeCounter,
            };

        Ok((hd, f))
    }

    fn calcNextPage(pgsz: usize, len: usize) -> PageNum {
        let numPagesSoFar = (if pgsz > len { 1 } else { len / pgsz }) as PageNum;
        numPagesSoFar + 1
    }

    // --------

    let mut f = try!(OpenOptions::new()
            .read(true)
            .create(true)
            .open(&path));

    let len = try!(f.metadata()).len();
    if len > 0 {
        let pr = try!(read(&mut f));
        let (h, f) = try!(parse(&pr, f));
        let nextAvailablePage = calcNextPage(f.page_size(), len as usize);
        Ok((h, f, nextAvailablePage))
    } else {
        // TODO shouldn't this use settings passed in?
        let defaultPageSize = DEFAULT_SETTINGS.default_page_size;
        let h = {
            HeaderData {
                fresh: vec![],
                young: vec![],
                levels: vec![],
                changeCounter: 0,
                mergeCounter: 0,
            }
        };
        let nextAvailablePage = calcNextPage(defaultPageSize, HEADER_SIZE_IN_BYTES);
        let f = PageCache::new(f, defaultPageSize);
        Ok((h, f, nextAvailablePage))
    }

}

fn list_all_blocks(
    f: &std::sync::Arc<PageCache>,
    h: &HeaderData, 
    ) -> Result<BlockList> {
    let mut blocks = BlockList::new();

    let headerBlock = PageBlock::new(1, (HEADER_SIZE_IN_BYTES / f.page_size()) as PageNum);
    blocks.add_block_no_reorder(headerBlock);

    fn do_seglist<'a, I: Iterator<Item=&'a SegmentHeaderInfo>>(f: &std::sync::Arc<PageCache>, segments: I, blocks: &mut BlockList) -> Result<()> {
        for seg in segments {
            let b = try!(seg.blocklist_unsorted(f));
            blocks.add_blocklist_no_reorder(&b);
            blocks.add_page_no_reorder(seg.root_page);
        }
        Ok(())
    }

    try!(do_seglist(f, h.fresh.iter(), &mut blocks));
    try!(do_seglist(f, h.young.iter(), &mut blocks));
    try!(do_seglist(f, h.levels.iter().filter_map(|s| s.as_ref()), &mut blocks));

    blocks.sort_and_consolidate();

    Ok(blocks)
}

use std::sync::Mutex;
use std::sync::RwLock;

#[derive(Debug)]
struct Space {
    path: String,
    page_size: usize,
    pages_per_block: PageCount,
    nextPage: PageNum,

    fresh_free: Vec<BlockList>,
    free_blocks: BlockList,

    next_rlock: u64,
    rlocks: HashMap<u64, HashSet<PageNum>>,

    // when a merge makes some blocks inactive, but those blocks
    // cannot yet be freed because there is an rlock on them,
    // those blocks go into zombies.
    zombies: HashMap<PageNum, BlockList>,

    dependencies: HashMap<PageNum, HashSet<PageNum>>,
}

impl Space {
    fn add_rlock(&mut self, segments: HashSet<PageNum>) -> u64 {
        //println!("add_rlock: {:?}", segments);
        let rlock = self.next_rlock;
        self.next_rlock += 1;
        assert!(!self.rlocks.contains_key(&rlock));
        let was = self.rlocks.insert(rlock, segments);
        assert!(was.is_none());
        rlock
    }

    fn has_rlock(&self, pgnum: PageNum) -> bool {
        // TODO we might want a reverse index on this to make it faster
        for h in self.rlocks.values() {
            if h.contains(&pgnum) {
                return true;
            }
        }
        false
    }

    fn maybe_release_segment(&mut self, seg: PageNum) {
        //println!("maybe_release_segment: {}", seg);
        if self.dependencies.contains_key(&seg) || self.has_rlock(seg) {
            // anything that still has an rlock (directly or
            // indirectly through a dependency) has gotta be
            // left alone.
            //println!("seg {} has deps, so no release", seg);
            return;
        }

        // OK, this segment
        // finally no longer exists.  It is no longer in the
        // header (or it wouldn't be here), and there are no
        // longer any direct or indirect rlocks on it.

        // Any zombies waiting directly on this segment can now
        // be freed.

        // Also, any dependencies waiting on this segment can
        // be removed and released as well.

        match self.zombies.remove(&seg) {
            Some(blocks) => {
                //println!("release zombies, so add_free_blocks: {:?}", blocks);
                self.add_free_blocks(blocks);
            },
            None => {
            },
        }

        let mut recurse = vec![];
        for (other, ref mut deps) in self.dependencies.iter_mut() {
            if deps.remove(&seg) {
                if deps.is_empty() {
                    recurse.push(*other);
                }
            }
        }

        for seg in recurse {
            self.dependencies.remove(&seg);
            self.maybe_release_segment(seg);
        }
    }

    fn release_rlock(&mut self, rlock: u64) {
        let segments = 
            match self.rlocks.remove(&rlock) {
                None => {
                    panic!("attempt to release non-existent rlock");
                },
                Some(segments) => {
                    segments
                },
            };
        //println!("release rlock on {:?}", segments);
        if self.zombies.is_empty() && self.dependencies.is_empty() {
            // if there are no zombies or deps, there is nothing more to do here
            return;
        }

        for seg in segments {
            self.maybe_release_segment(seg);
        }
    }

    fn add_inactive(&mut self, mut blocks: HashMap<PageNum, BlockList>) {
        // everything in blocks should go in either free or zombie

        //println!("add_inactive: {:?}", blocks);
        //println!("dependencies: {:?}", self.dependencies);
        if !blocks.is_empty() {
            let segments = blocks.keys().map(|p| *p).collect::<HashSet<PageNum>>();
            let new_zombie_segments = 
                segments
                .into_iter()
                .filter(|seg| self.dependencies.contains_key(seg) || self.has_rlock(*seg) )
                .collect::<HashSet<_>>();
            for pg in new_zombie_segments {
                let b = blocks.remove(&pg).unwrap();
                //println!("seg {} has rlock so zombie: {:?}", pg, b);
                assert!(!self.zombies.contains_key(&pg));
                self.zombies.insert(pg, b);
            }
            if !blocks.is_empty() {
                for (pg, b) in blocks {
                    //println!("no rlock on {}, so add_free_blocks: {:?}", pg, b);
                    self.add_free_blocks(b);
                }
            }
        }
    }

    fn add_dependencies(&mut self, seg: PageNum, depends_on: Vec<PageNum>) {
        //println!("add_dependencies: {} depends on {:?}", seg, depends_on);
        let depends_on = 
            depends_on
            .into_iter()
            .filter(|seg| self.dependencies.contains_key(seg) || self.has_rlock(*seg))
            .collect::<HashSet<_>>();
        if depends_on.is_empty() {
            return;
        }
        assert!(!self.dependencies.contains_key(&seg));
        self.dependencies.insert(seg, depends_on);
    }

    fn add_free_blocks(&mut self, blocks: BlockList) {
        // organizing the free block list can be expensive
        // if the list is large, so we only do it every so
        // often.
        self.fresh_free.push(blocks);
        // TODO tunable parameter, not constant
        if self.fresh_free.len() >= 8 {
            self.organize_free_blocks();
        }
    }

    fn step1_sort_and_consolidate(&mut self) {
        for list in self.fresh_free.iter() {
            self.free_blocks.add_blocklist_no_reorder(list);
        }
        self.fresh_free.clear();

        self.free_blocks.sort_and_consolidate();
        if self.free_blocks.count_blocks() > 0 && self.free_blocks.last_page() == self.nextPage - 1 {
            let i_last_block = self.free_blocks.count_blocks() - 1;
            let blk = self.free_blocks.remove_block(i_last_block);
            //println!("    killing free_at_end: {:?}", blk);
            self.nextPage = blk.firstPage;
        }

    }

    fn step2_sort_for_usage(&mut self) {
        // we want the largest blocks at the front of the list
        // two blocks of the same size?  sort earlier block first.
        self.free_blocks.sort_by_size_desc_page_asc();
    }

    fn organize_free_blocks(&mut self) {
        // the list is kept consolidated and sorted by size descending.
        // unfortunately this requires two sorts, and they happen here
        // inside a critical section.  but the benefit is considered
        // worth the trouble.

        self.step1_sort_and_consolidate();
        self.step2_sort_for_usage();
    }

    fn truncate_file_if_possible(&mut self) -> Result<()> {
        self.step1_sort_and_consolidate();

        let file_length = try!(std::fs::metadata(&self.path)).len();
        let page_size = self.page_size as u64;
        let first_page_beyond = (file_length / page_size + 1) as u32;
        if first_page_beyond > self.nextPage {
            let fs = try!(OpenOptions::new()
                    .read(true)
                    .write(true)
                    .open(&self.path)
                    );
            try!(fs.set_len(((self.nextPage - 1) as u64) * page_size));
        }

        self.step2_sort_for_usage();

        Ok(())
    }

    fn getBlock(&mut self, req: BlockRequest) -> PageBlock {
        fn find_block_starting_at(space: &mut Space, start: Vec<PageNum>) -> Option<usize> {
            // TODO which way should we nest these two loops?
            for i in 0 .. space.free_blocks.count_blocks() {
                for j in 0 .. start.len() {
                    if space.free_blocks[i].firstPage == start[j] {
                        return Some(i);
                    }
                }
            }
            None
        }

        fn find_block_minimum_size(space: &mut Space, size: PageCount) -> Option<usize> {
            // space.free_blocks is sorted by size desc, so we only
            // need to check the first block.
            if space.free_blocks[0].count_pages() >= size {
                return Some(0);
            } else {
                // if this block isn't big enough, none of the ones after it will be
                return None;
            }
        }

        fn find_block_after_minimum_size(space: &mut Space, after: PageNum, size: PageCount) -> Option<usize> {
            for i in 0 .. space.free_blocks.count_blocks() {
                if space.free_blocks[i].count_pages() >= size {
                    if space.free_blocks[i].firstPage > after {
                        return Some(i);
                    } else {
                        // big enough, but not "after".  keep looking.
                    }
                } else {
                    // if this block isn't big enough, none of the ones after it will be
                    return None;
                }
            }
            None
        }

        enum FromWhere {
            End(PageCount),
            FirstFree,
            SpecificFree(usize),
        }

        if let Some(after) = req.get_after() {
            assert!(self.nextPage > after);
        }

        if self.free_blocks.is_empty() && !self.fresh_free.is_empty() {
            self.organize_free_blocks();
        }

        let from =
            if self.free_blocks.is_empty() {
                FromWhere::End(self.pages_per_block)
            } else if req.start_is(self.nextPage) {
                FromWhere::End(self.pages_per_block)
            } else {
                match req {
                    BlockRequest::Any => {
                        FromWhere::FirstFree
                    },
                    BlockRequest::StartOrAfterMinimumSize(start, after, size) => {
                        assert!(start.iter().all(|start| *start > after));
                        if let Some(i) = find_block_starting_at(self, start) {
                            FromWhere::SpecificFree(i)
                        } else if let Some(i) = find_block_after_minimum_size(self, after, size) {
                            FromWhere::SpecificFree(i)
                        } else {
                            FromWhere::End(std::cmp::max(size, self.pages_per_block))
                        }
                    },
                    BlockRequest::MinimumSize(size) => {
                        if let Some(i) = find_block_minimum_size(self, size) {
                            FromWhere::SpecificFree(i)
                        } else {
                            FromWhere::End(std::cmp::max(size, self.pages_per_block))
                        }
                    },
                    BlockRequest::StartOrAny(start) => {
                        if let Some(i) = find_block_starting_at(self, start) {
                            FromWhere::SpecificFree(i)
                        } else {
                            FromWhere::FirstFree
                        }
                    },

                }
            };

        match from {
            FromWhere::FirstFree => {
                self.free_blocks.remove_block(0)
            },
            FromWhere::SpecificFree(i) => {
                self.free_blocks.remove_block(i)
            },
            FromWhere::End(size) => {
                let newBlk = PageBlock::new(self.nextPage, self.nextPage + size - 1) ;
                self.nextPage = self.nextPage + size;
                newBlk
            },
        }
    }

}

enum MergingInto {
    None,
    Leaf(LeafPage),
    Parent(ParentPage),
}

impl MergingInto {
    fn old_segment(&self) -> Option<PageNum> {
        match *self {
            MergingInto::None => None,
            MergingInto::Leaf(ref page) => Some(page.pagenum),
            MergingInto::Parent(ref page) => Some(page.pagenum),
        }
    }
}

#[derive(Debug)]
enum MergeFrom {
    Fresh{segments: Vec<PageNum>},
    FreshNoRewrite{segments: Vec<PageNum>},
    Young{old_segment: PageNum, new_segment: Option<SegmentHeaderInfo>},
    Other{level: usize, old_segment: PageNum, new_segment: Option<SegmentHeaderInfo>},
}

impl MergeFrom {
    fn get_dest_level(&self) -> DestLevel {
        match self {
            &MergeFrom::Fresh{..} => DestLevel::Young,
            &MergeFrom::FreshNoRewrite{..} => DestLevel::Young,
            &MergeFrom::Young{..} => DestLevel::Other(0),
            &MergeFrom::Other{level, ..} => DestLevel::Other(level + 1),
        }
    }
}

#[derive(Debug, PartialEq)]
enum NeedsMerge {
    No,
    Yes,
    Desperate,
}

#[derive(Debug)]
pub struct PendingMerge {
    from: MergeFrom,
    old_dest_segment: Option<PageNum>,
    new_dest_segment: Option<SegmentHeaderInfo>,
    now_inactive: HashMap<PageNum, BlockList>,
}

struct SafePagePool {
    // we keep a pool of page buffers so we can lend them to
    // SegmentCursors.
    pages: Vec<Box<[u8]>>,
}

struct Senders {
    notify_fresh: mpsc::Sender<MergeMessage>,
    notify_young: mpsc::Sender<MergeMessage>,
    notify_levels: Vec<mpsc::Sender<MergeMessage>>,
}

struct InnerPageCache {
    f: File,
    pages: HashMap<PageNum, std::sync::Weak<Box<[u8]>>>,
}

pub struct PageCache {
    pgsz: usize,
    stuff: Mutex<InnerPageCache>,
    // TODO pool of empty pages to be reused?
}

impl PageCache {
    fn new(f: File, pgsz: usize) -> Self {
        let stuff = InnerPageCache {
            f: f,
            pages: HashMap::new(),
        };
        PageCache {
            pgsz: pgsz,
            stuff: Mutex::new(stuff),
        }
    }

    fn page_size(&self) -> usize {
        self.pgsz
    }

    fn inner_read(stuff: &mut InnerPageCache, page: PageNum, buf: &mut [u8]) -> Result<()> {
        try!(utils::SeekPage(&mut stuff.f, buf.len(), page));
        try!(misc::io::read_fully(&mut stuff.f, buf));
        Ok(())
    }

    fn read_page(&self, page: PageNum, buf: &mut [u8]) -> Result<()> {
        let mut stuff = try!(self.stuff.lock());
        // TODO assert pgsz?
        try!(Self::inner_read(&mut stuff, page, buf));
        Ok(())
    }

    fn inner_put(stuff: &mut InnerPageCache, pgnum: PageNum, strong: &std::sync::Arc<Box<[u8]>>) {
        let weak = std::sync::Arc::downgrade(strong);
        match stuff.pages.entry(pgnum) {
            std::collections::hash_map::Entry::Vacant(e) => {
                e.insert(weak);
            },
            std::collections::hash_map::Entry::Occupied(mut e) => {
                assert!(e.get().upgrade().is_none());
                e.insert(weak);
            },
        }
    }

    fn put(&self, pgnum: PageNum, strong: &std::sync::Arc<Box<[u8]>>) -> Result<()> {
        let mut stuff = try!(self.stuff.lock());
        Self::inner_put(&mut stuff, pgnum, strong);
        Ok(())
    }

    fn get(&self, pgnum: PageNum) -> Result<std::sync::Arc<Box<[u8]>>> {
        let mut stuff = try!(self.stuff.lock());
        match stuff.pages.entry(pgnum) {
            std::collections::hash_map::Entry::Vacant(e) => {
            },
            std::collections::hash_map::Entry::Occupied(e) => {
                match e.get().upgrade() {
                    Some(strong) => {
                        return Ok(strong)
                    },
                    None => {
                        e.remove();
                    },
                }
            },
        }

        let mut buf = vec![0; self.pgsz].into_boxed_slice();
        try!(Self::inner_read(&mut stuff, pgnum, &mut buf));
        let strong = std::sync::Arc::new(buf);
        Self::inner_put(&mut stuff, pgnum, &strong);
        Ok(strong)
    }
}

// there can be only one InnerPart instance per path
struct InnerPart {
    path: String,
    settings: DbSettings,

    // TODO are we concerned here about readers starving the
    // writers?  In other words, so many cursors that a merge
    // cannot get committed?
    header: RwLock<HeaderStuff>,

    space: Mutex<Space>,
    senders: Mutex<Senders>,
    page_cache: std::sync::Arc<PageCache>,

    // TODO the contents of these mutexes should be something useful
    mergelock_fresh: Mutex<u32>,
    mergelock_young: Mutex<u32>,
    // TODO vec, or boxed slice?
    mergelock_levels: Vec<Mutex<u32>>,

}

#[derive(Debug, Copy, Clone)]
pub enum FromLevel {
    Fresh,
    Young,
    Other(usize),
}

impl FromLevel {
    fn get_dest_level(&self) -> DestLevel {
        match self {
            &FromLevel::Fresh => DestLevel::Young,
            &FromLevel::Young => DestLevel::Other(0),
            &FromLevel::Other(level) => DestLevel::Other(level + 1),
        }
    }
}

#[derive(Debug, Copy, Clone)]
enum DestLevel {
    Young,
    Other(usize),
}

impl DestLevel {
    fn as_from_level(&self) -> FromLevel {
        match self {
            &DestLevel::Young => FromLevel::Young,
            &DestLevel::Other(n) => FromLevel::Other(n),
        }
    }
}

enum MergeMessage {
    Work,
    Terminate,
}

pub struct WriteLock {
    inner: std::sync::Arc<InnerPart>,
}

impl WriteLock {
    pub fn commit_segment(&self, seg: SegmentHeaderInfo) -> Result<()> {
        try!(self.inner.commit_segment(seg));
        Ok(())
    }

// TODO this doesn't need to be public at all now, does it?
    pub fn commit_merge(&self, pm: PendingMerge) -> Result<()> {
        try!(self.inner.commit_merge(pm));
        Ok(())
    }
}

pub struct DatabaseFile {
    // there can be only one of this stuff per path
    inner: std::sync::Arc<InnerPart>,
    write_lock: std::sync::Arc<Mutex<WriteLock>>,

    thread_fresh: thread::JoinHandle<()>,
    thread_young: thread::JoinHandle<()>,
    // TODO vec, or boxed slice?
    thread_levels: Vec<thread::JoinHandle<()>>,
}

impl DatabaseFile {
    pub fn new(path: String, settings: DbSettings) -> Result<std::sync::Arc<DatabaseFile>> {

        // TODO we should pass in settings to read_header, right?
        let (header, f, first_available_page) = try!(read_header(&path));

        // when we first open the file, we find all the blocks that are in use by
        // an active segment.  all OTHER blocks are considered free.

        let f = std::sync::Arc::new(f);

        let mut blocks = try!(list_all_blocks(&f, &header));

        if cfg!(expensive_check) 
        {
            blocks.sort_and_consolidate();
            println!("initial blocks in use: {:?}", blocks);
        }

        let last_page_used = blocks.last_page();
        blocks.invert();
        if first_available_page > (last_page_used + 1) {
            let blk = PageBlock::new(last_page_used + 1, first_available_page - 1);
            blocks.add_block_no_reorder(blk);
            // TODO it is tempting to truncate the file here.  but this might not
            // be the right place.  we should preserve the ability to open a file
            // read-only.
        }

        if cfg!(expensive_check) 
        {
            blocks.sort_and_consolidate();
            println!("initial free blocks: {:?}", blocks);
        }

        // we want the largest blocks at the front of the list
        // two blocks of the same size?  sort earlier block first.
        blocks.sort_by_size_desc_page_asc();

        // TODO Space::new()
        let space = Space {
            // TODO maybe we should just ignore the actual end of the file
            // and set nextPage to last_page_used + 1, and not add the block above
            path: path.clone(),
            page_size: f.page_size(),
            nextPage: first_available_page, 
            pages_per_block: settings.pages_per_block,
            fresh_free: vec![],
            free_blocks: blocks,
            next_rlock: 1,
            rlocks: HashMap::new(),
            zombies: HashMap::new(),
            dependencies: HashMap::new(),
        };

        // each merge level is handled by its own thread.  a Rust channel is used to
        // notify that thread that there may be merge work to be done, or that it needs
        // to terminate.

        let (tx_fresh, rx_fresh): (mpsc::Sender<MergeMessage>, mpsc::Receiver<MergeMessage>) = mpsc::channel();
        let (tx_young, rx_young): (mpsc::Sender<MergeMessage>, mpsc::Receiver<MergeMessage>) = mpsc::channel();

        let mut senders = vec![];
        let mut receivers = vec![];
        for level in 0 .. NUM_LEVELS {
            let (tx, rx): (mpsc::Sender<MergeMessage>, mpsc::Receiver<MergeMessage>) = mpsc::channel();
            senders.push(tx);
            receivers.push(rx);
        }

        let senders = Senders {
            notify_fresh: tx_fresh,
            notify_young: tx_young,
            notify_levels: senders,
        };

        let mut mergelock_levels = vec![];
        for level in 0 .. NUM_LEVELS {
            mergelock_levels.push(Mutex::new(0));
        }

        let file_header_write = 
            try!(OpenOptions::new()
                    .read(true)
                    .write(true)
                    .open(&path));

        let header = HeaderStuff {
            data: header,
            f: file_header_write,
        };

        let inner = InnerPart {
            path: path,
            page_cache: f,
            settings: settings, 
            header: RwLock::new(header),
            space: Mutex::new(space),
            mergelock_fresh: Mutex::new(0),
            mergelock_young: Mutex::new(0),
            mergelock_levels: mergelock_levels,
            senders: Mutex::new(senders),
        };

        let inner = std::sync::Arc::new(inner);

        let lck = 
            WriteLock { 
                inner: inner.clone(),
            };

        let lck = std::sync::Arc::new(Mutex::new(lck));

        fn merge_loop(inner: std::sync::Arc<InnerPart>, write_lock: std::sync::Arc<Mutex<WriteLock>>, rx: mpsc::Receiver<MergeMessage>, from: FromLevel) {
            loop {
                match rx.recv() {
                    Ok(msg) => {
                        match msg {
                            MergeMessage::Work => {
                                match DatabaseFile::merge(&inner, &write_lock, from) {
                                    Ok(()) => {
                                    },
                                    Err(e) => {
                                        // TODO what now?
                                        println!("{:?}", e);
                                        panic!();
                                    },
                                }
                            },
                            MergeMessage::Terminate => {
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
        }

        let thread_fresh = {
            let inner = inner.clone();
            let lck = lck.clone();
            try!(thread::Builder::new().name("fresh".to_string()).spawn(move || merge_loop(inner, lck, rx_fresh, FromLevel::Fresh)))
        };

        let thread_young = {
            let inner = inner.clone();
            let lck = lck.clone();
            try!(thread::Builder::new().name("young".to_string()).spawn(move || merge_loop(inner, lck, rx_young, FromLevel::Young)))
        };

        let mut thread_levels = vec![];
        for (level, rx) in receivers.into_iter().enumerate() {
            let thread = {
                let inner = inner.clone();
                let lck = lck.clone();
                try!(thread::Builder::new().name(format!("level_{}", level)).spawn(move || merge_loop(inner, lck, rx, FromLevel::Other(level))))
            };
            thread_levels.push(thread);
        }

        let db = DatabaseFile {
            inner: inner,
            write_lock: lck,
            thread_fresh: thread_fresh,
            thread_young: thread_young,
            thread_levels: thread_levels,
        };
        let db = std::sync::Arc::new(db);

        Ok(db)
    }

    pub fn stop(mut self) -> Result<()> {
        // these need to be stopped in ascending order.  we can't
        // have one of them stop while another one is still sending notifications
        // to it.

        println!("---------------- Stopping fresh");
        {
            let senders = try!(self.inner.senders.lock());
            try!(senders.notify_fresh.send(MergeMessage::Terminate).map_err(wrap_err));
        }

        match self.thread_fresh.join() {
            Ok(()) => {
            },
            Err(e) => {
                return Err(Error::Misc(format!("thread join failed: {:?}", e)));
            },
        }

        println!("---------------- Stopping young");
        {
            let senders = try!(self.inner.senders.lock());
            try!(senders.notify_young.send(MergeMessage::Terminate).map_err(wrap_err));
        }

        match self.thread_young.join() {
            Ok(()) => {
            },
            Err(e) => {
                return Err(Error::Misc(format!("thread join failed: {:?}", e)));
            },
        }

        for i in 0 .. NUM_LEVELS {
            println!("---------------- Stopping level {}", i);
            {
                let mut senders = try!(self.inner.senders.lock());
                let tx = &senders.notify_levels[i];
                try!(tx.send(MergeMessage::Terminate).map_err(wrap_err));
            }
            let j = self.thread_levels.remove(0);
            match j.join() {
                Ok(()) => {
                },
                Err(e) => {
                    return Err(Error::Misc(format!("thread join failed: {:?}", e)));
                },
            }
        }

        Ok(())
    }

    fn merge(inner: &std::sync::Arc<InnerPart>, write_lock: &std::sync::Arc<Mutex<WriteLock>>, level: FromLevel) -> Result<()> {
        // no merge should prevent writes of new segments
        // into fresh.  merges do not need the main write lock
        // until commit_merge() is called.

        // but we do need to make sure merges are not stepping
        // on other merges.

        fn guts(inner: &std::sync::Arc<InnerPart>, write_lock: &std::sync::Arc<Mutex<WriteLock>>, level: FromLevel) -> Result<Option<u64>> {
            match try!(InnerPart::needs_merge(&inner, level)) {
                NeedsMerge::No => {
                    Ok(None)
                },
                _ => {
                    match try!(InnerPart::needs_merge(&inner, level.get_dest_level().as_from_level())) {
                        NeedsMerge::Desperate => {
                            try!(inner.notify_work(level.get_dest_level().as_from_level()));
                            Ok(Some(inner.settings.sleep_desperate_level))
                        },
                        _ => {
                            let pm = try!(InnerPart::prepare_merge(&inner, level));
                            {
                                let lck = try!(write_lock.lock());
                                try!(lck.commit_merge(pm));
                                Ok(Some(0))
                            }
                        },
                    }
                },
            }
        }

        match level {
            FromLevel::Fresh => {
                loop {
                    let delay = {
                        let foo = try!(inner.mergelock_fresh.lock());
                        // no mergelock_young needed here
                        let delay = 
                            match try!(guts(&inner, &write_lock, level)) {
                                Some(delay) => {
                                    delay
                                },
                                None => {
                                    break;
                                },
                            };
                        delay
                    };
                    if delay > 0 {
                        println!("desperate,{:?},sleeping,{}", level, inner.settings.sleep_desperate_fresh);
                        std::thread::sleep(std::time::Duration::from_millis(delay));
                    }
                }
            },
            FromLevel::Young => {
                loop {
                    let delay = {
                        let foo = try!(inner.mergelock_young.lock());
                        let bar = try!(inner.mergelock_levels[0].lock());
                        let delay = 
                            match try!(guts(&inner, &write_lock, level)) {
                                Some(delay) => {
                                    delay
                                },
                                None => {
                                    break;
                                },
                            };
                        delay
                    };
                    if delay > 0 {
                        println!("desperate,{:?},sleeping,{}", level, inner.settings.sleep_desperate_fresh);
                        std::thread::sleep(std::time::Duration::from_millis(delay));
                    }
                }
            },
            FromLevel::Other(n) => {
                loop {
                    let delay = {
                        let foo = try!(inner.mergelock_levels[n].lock());
                        let bar = try!(inner.mergelock_levels[n + 1].lock());
                        let delay = 
                            match try!(guts(&inner, &write_lock, level)) {
                                Some(delay) => {
                                    delay
                                },
                                None => {
                                    break;
                                },
                            };
                        delay
                    };
                    if delay > 0 {
                        println!("desperate,{:?},sleeping,{}", level, inner.settings.sleep_desperate_fresh);
                        std::thread::sleep(std::time::Duration::from_millis(delay));
                    }
                }
            },
        }
        Ok(())
    }

    // TODO func to ask for the write lock without blocking?

    pub fn get_write_lock(&self) -> Result<std::sync::MutexGuard<WriteLock>> {
        while NeedsMerge::Desperate == try!(InnerPart::needs_merge(&self.inner, FromLevel::Fresh)) {
            // TODO if we need to sleep more than once, do we really need to notify_work
            // every time?
            try!(self.inner.notify_work(FromLevel::Fresh));
            println!("desperate,main,sleeping,{}", self.inner.settings.sleep_desperate_fresh);
            std::thread::sleep(std::time::Duration::from_millis(self.inner.settings.sleep_desperate_fresh));
        }

        let lck = try!(self.write_lock.lock());
        Ok(lck)
    }

    // the following methods are passthrus, exposing inner
    // stuff publicly.

    pub fn open_cursor(&self) -> Result<LivingCursor> {
        InnerPart::open_cursor(&self.inner)
    }

    pub fn open_cursor_on_page(&self, pg: PageNum) -> Result<PageCursor> {
        InnerPart::open_cursor_on_page(&self.inner, pg)
    }

    // TODO this might want to be just LeafPage
    pub fn open_cursor_on_leaf_page(&self, pg: PageNum) -> Result<LeafCursor> {
        InnerPart::open_cursor_on_leaf_page(&self.inner, pg)
    }

    pub fn open_cursor_on_parent_page(&self, pg: PageNum) -> Result<ParentCursor> {
        InnerPart::open_cursor_on_parent_page(&self.inner, pg)
    }

    pub fn read_parent_page(&self, pg: PageNum) -> Result<ParentPage> {
        InnerPart::read_parent_page(&self.inner, pg)
    }

    pub fn write_segment(&self, pairs: BTreeMap<Box<[u8]>, Blob>) -> Result<Option<SegmentHeaderInfo>> {
        InnerPart::write_segment(&self.inner, pairs)
    }

    // tests use this
    pub fn write_segment_from_sorted_sequence<I>(&self, source: I) -> Result<Option<SegmentHeaderInfo>>
        where I: Iterator<Item=Result<kvp>>  {
        InnerPart::write_segment_from_sorted_sequence(&self.inner, source)
    }

    pub fn list_segments(&self) -> Result<(Vec<(PageNum, PageCount)>, Vec<(PageNum, PageCount)>, Vec<(PageNum, PageCount)>)> {
        InnerPart::list_segments(&self.inner)
    }

    pub fn release_pending_segment(&self, location: PageNum) -> Result<()> {
        InnerPart::release_pending_segment(&self.inner, location)
    }

    pub fn list_free_blocks(&self) -> Result<BlockList> {
        InnerPart::list_free_blocks(&self.inner)
    }

    pub fn get_page(&self, pgnum: PageNum) -> Result<std::sync::Arc<Box<[u8]>>> {
        InnerPart::get_page(&self.inner, pgnum)
    }
}

impl HeaderStuff {
    fn write_header(&mut self, hdr: HeaderData, pgsz: usize) -> Result<()> {

        fn build_segment_list(h: &HeaderData) -> Vec<u8> {
            let mut pb = vec![];

            fn add_list(pb: &mut Vec<u8>, v: &Vec<SegmentHeaderInfo>) {
                misc::push_varint(pb, v.len() as u64);
                for seg in v.iter() {
                    misc::push_varint(pb, seg.root_page as u64);
                }
            }

            fn add_main_list(pb: &mut Vec<u8>, v: &Vec<Option<SegmentHeaderInfo>>) {
                misc::push_varint(pb, v.len() as u64);
                for seg in v.iter() {
                    match seg {
                        &Some(ref seg) => {
                            misc::push_varint(pb, seg.root_page as u64);
                        },
                        &None => {
                            misc::push_varint(pb, 0);
                        },
                    }
                }
            }

            add_list(&mut pb, &h.fresh);
            add_list(&mut pb, &h.young);
            add_main_list(&mut pb, &h.levels);

            pb
        }

        //println!("header, fresh,{}, young,{}, levels,{}", hdr.fresh.len(), hdr.young.len(), hdr.levels.len());

        let mut pb = PageBuilder::new(HEADER_SIZE_IN_BYTES);
        // TODO format version number
        // TODO aren't there some settings that should go in here?
        pb.PutInt32(pgsz as u32);

        pb.PutVarint(hdr.changeCounter);
        pb.PutVarint(hdr.mergeCounter);

        let pbSegList = build_segment_list(&hdr);

        // TODO the + 1 in the following line is probably no longer needed.
        // I think it used to be the flag indicating header overflow.
        if pb.Available() >= (pbSegList.len() + 1) {
            pb.PutArray(&pbSegList);
        } else {
            return Err(Error::Misc(String::from("header too big")));
        }

        try!(self.f.seek(SeekFrom::Start(0)));
        try!(pb.Write(&mut self.f));
        try!(self.f.flush());
        self.data = hdr;
        Ok(())
    }
}

impl InnerPart {

    #[cfg(remove_me)]
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

    fn cursor_dropped(&self, rlock: u64) {
        // TODO dislike doing stuff which requires error handling here in impl Drop
        //println!("cursor_dropped");
        let mut space = self.space.lock().unwrap(); // TODO gotta succeed
        space.release_rlock(rlock);
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

    // a stored segmentinfo for a segment is a single blob of bytes.
    // root page
    // number of pairs
    // each pair is startBlock,countBlocks
    // level
    // all in varints

    #[cfg(remove_me)]
    fn get_loaner_page(inner: &std::sync::Arc<InnerPart>) -> Result<Lend<Box<[u8]>>> {
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
        let page = Lend::new(page, box done_page);
        Ok(page)
    }

    fn open_cursor_on_page(inner: &std::sync::Arc<InnerPart>, pg: PageNum) -> Result<PageCursor> {
        let cursor = try!(PageCursor::new(inner.page_cache.clone(), pg));
        Ok(cursor)
    }

    fn open_cursor_on_leaf_page(inner: &std::sync::Arc<InnerPart>, pg: PageNum) -> Result<LeafCursor> {
        let page = try!(LeafPage::new(inner.page_cache.clone(), pg));
        let cursor = LeafCursor::new(page);
        Ok(cursor)
    }

    fn open_cursor_on_parent_page(inner: &std::sync::Arc<InnerPart>, pg: PageNum) -> Result<ParentCursor> {
        let page = try!(ParentPage::new(inner.page_cache.clone(), pg));
        let cursor = try!(ParentCursor::new(page));
        Ok(cursor)
    }

    fn read_parent_page(inner: &std::sync::Arc<InnerPart>, pg: PageNum) -> Result<ParentPage> {
        let page = try!(ParentPage::new(inner.page_cache.clone(), pg));
        Ok(page)
    }

    fn open_cursor(inner: &std::sync::Arc<InnerPart>) -> Result<LivingCursor> {
        let headerstuff = try!(inner.header.read());
        let header = &headerstuff.data;
        let f = inner.page_cache.clone(); // TODO one extra clone?

        let cursors = 
            header.fresh.iter()
            .chain(header.young.iter())
            .chain(header.levels.iter().filter_map(|s| s.as_ref()))
            .map(|seg| {
                let csr = try!(PageCursor::new(f.clone(), seg.root_page));
                Ok(csr)
            })
            .collect::<Result<Vec<_>>>();
        let cursors = try!(cursors);

        let segments = 
            header.fresh.iter()
            .chain(header.young.iter())
            .chain(header.levels.iter().filter_map(|s| s.as_ref()))
            .map(|seg| {
                seg.root_page
            })
            .collect::<HashSet<_>>();

        let rlock = {
            let mut space = try!(inner.space.lock());
            let rlock = space.add_rlock(segments);
            rlock
        };

        println!("open_cursor,{}, fresh,{}, young,{}, levels,{}", rlock, header.fresh.len(), header.young.len(), header.levels.len());

        if cfg!(expensive_check) 
        {
            let segnums = 
                header.fresh.iter()
                .chain(header.young.iter())
                .chain(header.levels.iter().filter_map(|s| s.as_ref()))
                .map(|seg| seg.root_page)
                .collect::<Vec<_>>();
            println!("open_cursor,{},{:?}", rlock, segnums);
        }

        let foo = inner.clone();
        let done = move |_| -> () {
            // TODO this wants to propagate errors
            foo.cursor_dropped(rlock);
        };

        let mc = MultiCursor::new(cursors);
        let mc = Lend::new(mc, box done);
        let lc = LivingCursor::new(rlock, mc);

        Ok(lc)
    }

    fn get_page(inner: &std::sync::Arc<InnerPart>, pgnum: PageNum) -> Result<std::sync::Arc<Box<[u8]>>> {
        let buf = try!(inner.page_cache.get(pgnum));
        Ok(buf)
    }

    fn list_free_blocks(inner: &std::sync::Arc<InnerPart>) -> Result<BlockList> {
        let mut space = try!(inner.space.lock());
        space.organize_free_blocks();
		let blocks = space.free_blocks.clone();
        Ok(blocks)
    }

    fn release_pending_segment(inner: &std::sync::Arc<InnerPart>, location: PageNum) -> Result<()> {
        //let mut space = try!(inner.space.lock());
        // TODO have to read the page to get the block list
        //try!(Self::addFreeBlocks(&mut space, &inner.path, inner.pgsz, location.blocks.blocks));
        Ok(())
    }

    fn list_segments(inner: &std::sync::Arc<InnerPart>) -> Result<(Vec<(PageNum, PageCount)>, Vec<(PageNum, PageCount)>, Vec<(PageNum, PageCount)>)> {
        let headerstuff = try!(inner.header.read());
        let header = &headerstuff.data;

        fn do_group(segments: &[SegmentHeaderInfo]) -> Result<Vec<(PageNum, PageCount)>> {
            let mut v = vec![];
            for seg in segments.iter() {
                let count = try!(seg.count_leaves_for_list_segments());
                v.push((seg.root_page, count));
            }
            Ok(v)
        }

        fn do_main_group(segments: &[Option<SegmentHeaderInfo>]) -> Result<Vec<(PageNum, PageCount)>> {
            let mut v = vec![];
            for seg in segments.iter() {
                match seg {
                    &Some(ref seg) => {
                        let count = try!(seg.count_leaves_for_list_segments());
                        v.push((seg.root_page, count));
                    },
                    &None => {
                        // TODO using 0,0 here is not ideal
                        v.push((0, 0));
                    },
                }
            }
            Ok(v)
        }

        let fresh = try!(do_group(&header.fresh));
        let young = try!(do_group(&header.young));
        let levels = try!(do_main_group(&header.levels));

        Ok((fresh, young, levels))
    }

    fn commit_segment(&self, seg: SegmentHeaderInfo) -> Result<()> {
        {
            let mut headerstuff = try!(self.header.write());

            // TODO assert new seg shares no pages with any seg in current state

            let mut newHeader = headerstuff.data.clone();

            newHeader.fresh.insert(0, seg);

            newHeader.changeCounter = newHeader.changeCounter + 1;

            try!(headerstuff.write_header(newHeader, self.page_cache.page_size()));
        }

        // note that we intentionally do not release the writeLock here.
        // you can change the segment list more than once while holding
        // the writeLock.  the writeLock gets released when you Dispose() it.

        try!(self.notify_work(FromLevel::Fresh));

        Ok(())
    }

    fn write_segment(inner: &std::sync::Arc<InnerPart>, pairs: BTreeMap<Box<[u8]>, Blob>) -> Result<Option<SegmentHeaderInfo>> {
        //println!("writing segment with {} pairs", pairs.len());
        let source = pairs.into_iter().map(|t| {
            let (k, v) = t;
            Ok(kvp {Key:k, Value:v})
        });
        let pw = try!(PageWriter::new(inner.clone()));
        let seg = try!(create_segment(pw, source, inner.page_cache.clone()));
        /*
        if cfg!(expensive_check) 
        {
            match seg {
                Some(ref seg) => {
                    let mut blocks = try!(seg.blocklist_unsorted(&inner.path, f.clone()));
                    blocks.sort_and_consolidate();
                    println!("write_segment,{:?}", blocks);
                },
                None => {
                },
            }
        }
        */
        Ok(seg)
    }

    // tests use this
    fn write_segment_from_sorted_sequence<I>(inner: &std::sync::Arc<InnerPart>, source: I) -> Result<Option<SegmentHeaderInfo>> 
        where I: Iterator<Item=Result<kvp>>  {
        let pw = try!(PageWriter::new(inner.clone()));
        let seg = try!(create_segment(pw, source, inner.page_cache.clone()));
        Ok(seg)
    }

    fn notify_work(&self, from_level: FromLevel) -> Result<()> {
        let senders = try!(self.senders.lock());
        match from_level {
            FromLevel::Fresh => {
                try!(senders.notify_fresh.send(MergeMessage::Work).map_err(wrap_err));
            },
            FromLevel::Young => {
                try!(senders.notify_young.send(MergeMessage::Work).map_err(wrap_err));
            },
            FromLevel::Other(i) => {
                try!(senders.notify_levels[i].send(MergeMessage::Work).map_err(wrap_err));
            },
        }
        Ok(())
    }

    fn needs_merge(inner: &std::sync::Arc<InnerPart>, from_level: FromLevel) -> Result<NeedsMerge> {
        match from_level {
            FromLevel::Other(i) => {
                if i == NUM_LEVELS - 1 {
                    // this level doesn't need a merge because it has nowhere to promote to
                    return Ok(NeedsMerge::No);
                }
            },
            _ => {
            },
        }
        let headerstuff = try!(inner.header.read());
        let header = &headerstuff.data;
        match from_level {
            FromLevel::Fresh => {
                if header.fresh.is_empty() {
                    return Ok(NeedsMerge::No);
                }

                if header.fresh.len() > inner.settings.desperate_fresh {
                    return Ok(NeedsMerge::Desperate);
                }

                // TODO consider always returning Yes here.  but
                // doing that seems to cause a big perf hit.  why?
                // the idea was to just keep Fresh empty.
                let i = header.fresh.len() - 1;
                let pt = try!(PageType::from_u8(header.fresh[i].buf[0]));
                match pt {
                    PageType::PARENT_NODE => {
                        // a parent node is promoted from Fresh without a rewrite
                        return Ok(NeedsMerge::Yes);
                    },
                    PageType::LEAF_NODE => {
                        if header.fresh.len() > 1 {
                            return Ok(NeedsMerge::Yes);
                        } else {
                            return Ok(NeedsMerge::No);
                        }
                    },
                }

                return Ok(NeedsMerge::Yes);
            },
            FromLevel::Young => {
                if header.young.is_empty() {
                    return Ok(NeedsMerge::No);
                }

                if header.young.len() > inner.settings.desperate_young {
                    return Ok(NeedsMerge::Desperate);
                }

                return Ok(NeedsMerge::Yes);
            },
            FromLevel::Other(i) => {
                if header.levels.len() <= i {
                    // this level doesn't need a merge because it doesn't exist
                    return Ok(NeedsMerge::No);
                }
                match &header.levels[i] {
                    &Some(ref seg) => {
                        match try!(PageType::from_u8(seg.buf[0])) {
                            PageType::LEAF_NODE => {
                                // TODO this is a fairly expensive way to count the stuff.
                                // it parses the page out of the buffer.
                                let count_tombstones = try!(LeafPage::count_tombstones(seg.root_page, &seg.buf));
                                if count_tombstones > 0 {
                                    return Ok(NeedsMerge::Yes);
                                }
                                /*
                                // TODO this causes a mysterious perf loss
                                if i + 1 < header.levels.len() {
                                    return Ok(NeedsMerge::Yes);
                                }
                                */
                                return Ok(NeedsMerge::No);
                            },
                            PageType::PARENT_NODE => {
                                // TODO this is a fairly expensive way to count the stuff.
                                // it parses the page out of the buffer.
                                // store the count in SegmentHeaderInfo ?

                                let (count_leaves, count_tombstones) = try!(ParentPage::count_stuff_for_needs_merge(seg.root_page, &seg.buf));
                                if count_tombstones > 0 {
                                    return Ok(NeedsMerge::Yes);
                                }
                                let size = (count_leaves as u64) * (inner.page_cache.page_size() as u64);
                                if size < get_level_size(i) {
                                    // this level doesn't need a merge because it is doesn't have enough data in it
                                    return Ok(NeedsMerge::No);
                                }
                                if size > inner.settings.desperate_level_factor * get_level_size(i) {
                                    // TODO not sure we need this.  but without it,
                                    // Other(0) gets out of control on 5M urls.
                                    // maybe a locking and starvation issue.
                                    return Ok(NeedsMerge::Desperate);
                                }
                                return Ok(NeedsMerge::Yes);
                            },
                        }
                    },
                    &None => {
                        return Ok(NeedsMerge::No);
                    },
                }
            },
        }
    }

    fn prepare_merge(inner: &std::sync::Arc<InnerPart>, from_level: FromLevel) -> Result<PendingMerge> {
        let t1 = time::PreciseTime::now();

        enum MergingFrom {
            FreshLeaves{
                segments: Vec<PageNum>,
            },
            YoungLeaf{
                segment: PageNum,
                count_tombstones: u64,
            },
            YoungPartial{
                old_segment: ParentPage,
                promote_pages: Vec<PageNum>, // must be contig within same parent
                promote_depth: u8,
                promote_blocks: BlockList, 
                promote_lineage: Vec<PageNum>, 
                count_tombstones: u64,
            },
            OtherLeaf{
                level: usize,  // TODO why is this here?
                segment: PageNum,
                count_tombstones: u64,
            },
            OtherPartial{
                level: usize,  // TODO why is this here?
                old_segment: ParentPage, 
                promote_pages: Vec<PageNum>, // must be contig within same parent
                promote_depth: u8,
                promote_blocks: BlockList, 
                promote_lineage: Vec<PageNum>, 
                count_tombstones: u64,
            },
        }

        let f = &inner.page_cache;

        let (cursor, from, into, behind_cursors, behind_rlock) = {
            let headerstuff = try!(inner.header.read());
            let header = &headerstuff.data;

            let (cursors, from) = {
                // find all the stuff that is getting promoted.  
                // we need a cursor on this so we can rewrite it into the next level.
                // we also need to remember where it came from, so we can remove it from the header segments lists.

                // we actually do not need read locks on this stuff, because
                // a read lock is simply to prevent commit_merge() from freeing
                // something that is still being read by something else.
                // two merges promoting the same stuff are not allowed.

                fn get_cursors(inner: &std::sync::Arc<InnerPart>, f: &std::sync::Arc<PageCache>, merge_segments: &[SegmentHeaderInfo]) -> Result<Vec<MultiPageCursor>> {
                    let mut cursors = Vec::with_capacity(merge_segments.len());
                    for i in 0 .. merge_segments.len() {
                        let pagenum = merge_segments[i].root_page;
                        let cursor = try!(MultiPageCursor::new(f.clone(), vec![pagenum]));
                        cursors.push(cursor);
                    }

                    Ok(cursors)
                }

                fn slice_from_end(v: &[SegmentHeaderInfo], count: usize) -> &[SegmentHeaderInfo] {
                    let count = std::cmp::min(count, v.len());
                    let i = v.len() - count;
                    let v = &v[i ..];
                    v
                }

                match from_level {
                    FromLevel::Fresh => {
                        let i = header.fresh.len() - 1;
                        match try!(PageType::from_u8(header.fresh[i].buf[0])) {
                            PageType::LEAF_NODE => {
                                let mut i = i;
                                // TODO should there be a limit to how many leaves we will take at one time?

                                // note that must accept just one if that's all we have.
                                // otherwise, we could get stuck with the last segment being a leaf
                                // and the second-to-last segment being a parent.
                                while i > 0 {
                                    if PageType::LEAF_NODE == try!(PageType::from_u8(header.fresh[i - 1].buf[0])) {
                                        i -= 1;
                                    } else {
                                        break;
                                    }
                                }

                                let merge_segments = slice_from_end(&header.fresh, header.fresh.len() - i);

                                let cursors = try!(get_cursors(inner, f, &merge_segments));

                                let merge_segments = 
                                    merge_segments
                                    .iter()
                                    .map( |seg| seg.root_page)
                                    .collect::<Vec<_>>();;

                                (cursors, MergingFrom::FreshLeaves{segments: merge_segments})
                            },
                            PageType::PARENT_NODE => {
                                let mut i = i;
                                while i > 0 {
                                    if PageType::PARENT_NODE == try!(PageType::from_u8(header.fresh[i - 1].buf[0])) {
                                        i -= 1;
                                    } else {
                                        break;
                                    }
                                }

                                let merge_segments = slice_from_end(&header.fresh, header.fresh.len() - i);

                                let merge_segments = 
                                    merge_segments
                                    .iter()
                                    .map(|seg| seg.root_page)
                                    .collect::<Vec<_>>();;

                                // TODO dislike early return
                                let pm = 
                                    PendingMerge {
                                        from: MergeFrom::FreshNoRewrite{segments: merge_segments},
                                        old_dest_segment: None,
                                        new_dest_segment: None,
                                        now_inactive: HashMap::new(),
                                    };
                                let t2 = time::PreciseTime::now();
                                let elapsed = t1.to(t2);
                                //println!("prepare,from,{:?}, ms,{}", from_level, elapsed.num_milliseconds());
                                return Ok(pm);
                            },
                        }

                    },
                    FromLevel::Young => {
                        let i = header.young.len() - 1;
                        let segment = &header.young[i];
                        match try!(PageType::from_u8(header.young[i].buf[0])) {
                            PageType::LEAF_NODE => {
                                let count_tombstones = try!(LeafPage::count_tombstones(segment.root_page, &segment.buf));

                                // TODO sad that this will re-read the leaf page
                                let cursor = try!(MultiPageCursor::new(f.clone(), vec![segment.root_page]));

                                let from = MergingFrom::YoungLeaf{
                                    segment: segment.root_page,
                                    count_tombstones: count_tombstones,
                                };

                                (vec![cursor], from)
                            },
                            PageType::PARENT_NODE => {
                                let promote_depth = 0;

                                let parent = try!(ParentPage::new(f.clone(), segment.root_page));

                                let mut lineage = vec![0; parent.depth() as usize + 1];
                                let (chosen_pages, count_tombstones) = try!(parent.choose_nodes_to_promote(promote_depth, &mut lineage, inner.settings.num_leaves_promote));
                                //println!("{:?},promoting_pages,{:?}", from_level, chosen_pages);
                                //println!("lineage: {}", lineage);

                                let cursor = try!(MultiPageCursor::new(f.clone(), chosen_pages.clone()));

                                let from = MergingFrom::YoungPartial{
                                    old_segment: parent, 
                                    promote_lineage: lineage, 
                                    promote_pages: chosen_pages, 
                                    promote_depth: promote_depth,
                                    promote_blocks: BlockList::new(), 
                                    count_tombstones: count_tombstones,
                                };
                                (vec![cursor], from)
                            }
                        }
                    },
                    FromLevel::Other(level) => {
                        assert!(header.levels.len() > level);
                        // TODO unwrap here is ugly.  but needs_merge happpened first
                        let old_from_segment = header.levels[level].as_ref().unwrap();
                        match try!(PageType::from_u8(old_from_segment.buf[0])) {
                            PageType::LEAF_NODE => {
                                let count_tombstones = try!(LeafPage::count_tombstones(old_from_segment.root_page, &old_from_segment.buf));

                                // TODO sad that this will re-read the leaf page
                                let cursor = try!(MultiPageCursor::new(f.clone(), vec![old_from_segment.root_page]));

                                let from = MergingFrom::OtherLeaf{
                                    level: level,
                                    segment: old_from_segment.root_page,
                                    count_tombstones: count_tombstones,
                                };

                                (vec![cursor], from)
                            },
                            PageType::PARENT_NODE => {
                                let depth_root = old_from_segment.buf[2];
                                //println!("old_from_segment: {}, depth: {}", old_from_segment.root_page, depth_root);
                                assert!(depth_root >= 1);
                                // TODO do we really ever want to promote from a depth other than leaves?
                                let promote_depth = 0;

                                let parent = try!(ParentPage::new(f.clone(), old_from_segment.root_page));

                                let mut lineage = vec![0; parent.depth() as usize + 1];
                                let (chosen_pages, count_tombstones) = try!(parent.choose_nodes_to_promote(promote_depth, &mut lineage, inner.settings.num_leaves_promote));
                                //println!("{:?},promoting_pages,{:?}", from_level, chosen_pages);
                                let cursor = try!(MultiPageCursor::new(f.clone(), chosen_pages.clone()));
                                //println!("lineage: {}", lineage);

                                let promote_blocks =
                                    // TODO if promote_depth is always 0, this is silly
                                    if promote_depth == 0 {
                                        BlockList::new()
                                    } else {
                                        // TODO don't include the overflows here
                                        unreachable!();
                                    };

                                let from = MergingFrom::OtherPartial{
                                    level: level, 
                                    old_segment: parent, 
                                    promote_lineage: lineage, 
                                    promote_pages: chosen_pages, 
                                    promote_depth: promote_depth,
                                    promote_blocks: promote_blocks, 
                                    count_tombstones: count_tombstones,
                                };
                                (vec![cursor], from)
                            },
                        }
                    },
                }
            };

            let cursor = {
                let mc = MergeCursor::new(cursors);
                mc
            };

            let into = 
                match from_level.get_dest_level() {
                    DestLevel::Young => {
                        // for merges from Fresh into Young, there is no dest segment.
                        MergingInto::None
                    },
                    DestLevel::Other(dest_level) => {
                        if header.levels.len() > dest_level {
                            match &header.levels[dest_level] {
                                &Some(ref dest_segment) => {
                                    let pt = try!(PageType::from_u8(dest_segment.buf[0]));

                                    match pt {
                                        PageType::LEAF_NODE => {
                                            //println!("root of the dest segment is a leaf");
                                            let leaf = try!(LeafPage::new(f.clone(), dest_segment.root_page));
                                            MergingInto::Leaf(leaf)
                                        },
                                        PageType::PARENT_NODE => {
                                            let parent = try!(ParentPage::new(f.clone(), dest_segment.root_page));
                                            MergingInto::Parent(parent)
                                        },
                                    }
                                },
                                &None => {
                                    // the dest segment currently does not exist
                                    MergingInto::None
                                },
                            }
                        } else {
                            // the dest segment does not exist yet.
                            MergingInto::None
                        }
                    },
                };

            let (behind_cursors, behind_rlock) = {

                // during merge, a tombstone can be removed iff there is nothing
                // for that key left in the segments behind the dest segment.
                // so we need cursors on all those segments so that we can check
                // while writing the merge segment.

                // TODO is it really true that we can skip tombstone checks if
                // there are no tombstones being promoted?  what about tombstones
                // in the overlapping stuff that needs to get rewritten?  is that
                // possible?

                let behind_segments = {
                    match from {
                        MergingFrom::FreshLeaves{..} => {
                            None
                        },
                        MergingFrom::YoungLeaf{count_tombstones, ..} => {
                            if count_tombstones == 0 {
                                None
                            } else {
                                let dest_level = 0;
                                let mut behind_segments = Vec::with_capacity(header.levels.len());
                                for i in dest_level + 1 .. header.levels.len() {
                                    let seg = &header.levels[i];

                                    behind_segments.push(seg);
                                }
                                Some(behind_segments)
                            }
                        },
                        MergingFrom::YoungPartial{count_tombstones, ..} => {
                            if count_tombstones == 0 {
                                None
                            } else {
                                let dest_level = 0;
                                let mut behind_segments = Vec::with_capacity(header.levels.len());
                                for i in dest_level + 1 .. header.levels.len() {
                                    let seg = &header.levels[i];

                                    behind_segments.push(seg);
                                }
                                Some(behind_segments)
                            }
                        },
                        MergingFrom::OtherLeaf{level, count_tombstones, ..} => {
                            if count_tombstones == 0 {
                                None
                            } else {
                                let dest_level = level + 1;
                                let mut behind_segments = Vec::with_capacity(header.levels.len());
                                for i in dest_level + 1 .. header.levels.len() {
                                    let seg = &header.levels[i];

                                    behind_segments.push(seg);
                                }
                                Some(behind_segments)
                            }
                        },
                        MergingFrom::OtherPartial{level, count_tombstones, ..} => {
                            if count_tombstones == 0 {
                                None
                            } else {
                                let dest_level = level + 1;
                                let mut behind_segments = Vec::with_capacity(header.levels.len());
                                for i in dest_level + 1 .. header.levels.len() {
                                    let seg = &header.levels[i];

                                    behind_segments.push(seg);
                                }
                                Some(behind_segments)
                            }
                        },
                    }
                };

                match behind_segments {
                    Some(behind_segments) => {
                        let behind_segments =
                            behind_segments
                            .iter()
                            .filter_map(|s| s.as_ref())
                            .collect::<Vec<_>>();

                        let behind_cursors = {
                            fn get_cursor(
                                f: std::sync::Arc<PageCache>,
                                seg: &SegmentHeaderInfo,
                                ) -> Result<PageCursor> {
                                let cursor = try!(PageCursor::new(f, seg.root_page));
                                Ok(cursor)
                            }

                            let behind_cursors = 
                                behind_segments
                                .iter()
                                .map(|seg| get_cursor(f.clone(), seg))
                                .collect::<Result<Vec<_>>>();
                            let behind_cursors = try!(behind_cursors);
                            Some(behind_cursors)
                        };
                        let behind_segments =
                            behind_segments
                            .iter()
                            .map(|seg| seg.root_page)
                            .collect::<HashSet<_>>();
                        let behind_rlock = {
                                // we do need read locks for all these cursors to protect them from going
                                // away while we are writing the merge.
                                let rlock = {
                                    let mut space = try!(inner.space.lock());
                                    let rlock = space.add_rlock(behind_segments);
                                    rlock
                                };
                                Some(rlock)
                            };
                        (behind_cursors, behind_rlock)
                    },
                    None => {
                        (None, None)
                    },
                }
            };

            (cursor, from, into, behind_cursors, behind_rlock)
        };

        let mut pw = try!(PageWriter::new(inner.clone()));

        let (new_dest_segment, dest_nodes_rewritten, overflows_freed, overflows_eaten) = {
            // note that cursor.First() should NOT have already been called
            let mut cursor = cursor;
            try!(cursor.First());
            if cursor.IsValid() {
                let mut source = CursorIterator::new(cursor);
                let wrote = try!(write_merge(&mut pw, &mut source, &into, behind_cursors, &inner.path, f.clone(), from_level.get_dest_level()));

                let count_keys_yielded_by_merge_cursor = source.count_keys_yielded();
                //println!("count_keys_yielded_by_merge_cursor: {}", count_keys_yielded_by_merge_cursor);

                println!("merge,from,{:?}, leaves_rewritten,{}, leaves_recycled,{}, parent1_rewritten,{}, parent1_recycled,{}, keys_promoted,{}, keys_rewritten,{}, keys_shadowed,{}, tombstones_removed,{}, ms,{}", 
                         from_level, 
                         if wrote.nodes_rewritten.len() > 0 { wrote.nodes_rewritten[0].len() } else { 0 },
                         if wrote.nodes_recycled.len() > 0 { wrote.nodes_recycled[0] } else { 0 },
                         if wrote.nodes_rewritten.len() > 1 { wrote.nodes_rewritten[1].len() } else { 0 },
                         if wrote.nodes_recycled.len() > 1 { wrote.nodes_recycled[1] } else { 0 },
                         wrote.keys_promoted, 
                         wrote.keys_rewritten, 
                         wrote.keys_shadowed, 
                         wrote.tombstones_removed, 
                         wrote.elapsed_ms,
                        );

                if cfg!(expensive_check) 
                {
                    let count_dest_keys_before =
                        match &into {
                            &MergingInto::None => {
                                0
                            },
                            &MergingInto::Leaf(ref leaf) => {
                                leaf.count_keys()
                            },
                            &MergingInto::Parent(ref parent) => {
                                let mine = try!(ParentPage::new(f.clone(), parent.pagenum));
                                let mut cursor = try!(ParentCursor::new(mine));
                                let mut count = 0;
                                try!(cursor.First());
                                while cursor.IsValid() {
                                    count += 1;
                                    try!(cursor.Next());
                                }
                                count
                            },
                        };

                    let count_dest_keys_after =
                        match wrote.segment {
                            Some(ref seg) => {
                                try!(seg.count_keys(&inner.path, f))
                            },
                            None => {
                                0
                            },
                        };

                    let count_keys_shadowed_in_merge_cursor = source.count_keys_shadowed();
                    let count_keys_yielded_by_merge_cursor = source.count_keys_yielded();

                    println!("count_dest_keys_before: {}", count_dest_keys_before);
                    println!("count_dest_keys_after: {}", count_dest_keys_after);
                    println!("count_keys_yielded_by_merge_cursor: {}", count_keys_yielded_by_merge_cursor);
                    println!("count_keys_shadowed_in_merge_cursor: {}", count_keys_shadowed_in_merge_cursor);
                    println!("keys promoted in merge: {}", wrote.keys_promoted);
                    println!("keys rewritten in merge: {}", wrote.keys_rewritten);
                    println!("keys shadowed in merge: {}", wrote.keys_shadowed);
                    println!("tombstones removed in merge: {}", wrote.tombstones_removed);

                    assert!(count_dest_keys_after == count_dest_keys_before + count_keys_yielded_by_merge_cursor - wrote.keys_shadowed - wrote.tombstones_removed);
                }

                let overflows_eaten = source.overflows_eaten();

                (wrote.segment, wrote.nodes_rewritten, wrote.overflows_freed, overflows_eaten)
            } else {
                // TODO returning None and empty vecs is silly
                (None, vec![].into_boxed_slice(), vec![], vec![])
            }
        };

        // the read locks on behind can be released now
        match behind_rlock {
            Some(behind_rlock) => {
                let mut space = try!(inner.space.lock());
                space.release_rlock(behind_rlock);
            },
            None => {
            },
        }

        let old_dest_segment = 
            match &into {
                &MergingInto::None => {
                    None
                },
                &MergingInto::Leaf(ref leaf) => {
                    Some(leaf.pagenum)
                },
                &MergingInto::Parent(ref parent) => {
                    Some(parent.pagenum)
                },
            };

        // there are four sources of pages in this operation:
        //     the fresh segments being promoted
        //     the young segments being promoted
        //     the level segment being promoted
        //     the dest segment
        //
        // all those pages must end up in one of three places:
        //     the new dest segment
        //     the new from segment
        //     inactive

        let mut now_inactive: HashMap<PageNum, BlockList> = {
            let mut now_inactive = HashMap::new();
            match from {
                MergingFrom::FreshLeaves{ref segments} => {
                    for &seg in segments.iter() {
                        let mut blocks = BlockList::new();
                        blocks.add_page_no_reorder(seg);
                        // TODO overflows_eaten should be a hashmap
                        for &(s,ref b) in overflows_eaten.iter() {
                            if s == seg {
                                blocks.add_blocklist_no_reorder(b);
                            }
                        }
                        assert!(!now_inactive.contains_key(&seg));
                        now_inactive.insert(seg, blocks);
                    }
                },
                MergingFrom::YoungLeaf{segment, ..} => {
                    let mut blocks = BlockList::new();
                    blocks.add_page_no_reorder(segment);
                    assert!(overflows_eaten.is_empty());
                    assert!(!now_inactive.contains_key(&segment));
                    now_inactive.insert(segment, blocks);
                },
                MergingFrom::OtherLeaf{segment, ..} => {
                    let mut blocks = BlockList::new();
                    blocks.add_page_no_reorder(segment);
                    assert!(overflows_eaten.is_empty());
                    assert!(!now_inactive.contains_key(&segment));
                    now_inactive.insert(segment, blocks);
                },
                MergingFrom::YoungPartial{..} => {
                    // this is done below
                },
                MergingFrom::OtherPartial{..} => {
                    // this is done below
                },
            }
            match into.old_segment() {
                Some(old_segment) => {
                    let mut blocks = BlockList::new();
                    for depth in 0 .. dest_nodes_rewritten.len() {
                        for pgnum in dest_nodes_rewritten[depth].iter() {
                            blocks.add_page_no_reorder(*pgnum);
                        }
                    }
                    for b in overflows_freed {
                        blocks.add_blocklist_no_reorder(&b);
                    }
                    assert!(!now_inactive.contains_key(&old_segment));
                    now_inactive.insert(old_segment, blocks);
                },
                None => {
                },
            }
            now_inactive
        };

        let from = 
            match from {
                MergingFrom::FreshLeaves{segments} => {
                    MergeFrom::Fresh{
                        segments: segments,
                    }
                },
                MergingFrom::YoungLeaf{segment, ..} => {
                    MergeFrom::Young{
                        old_segment: segment,
                        new_segment: None,
                    }
                },
                MergingFrom::YoungPartial{old_segment, promote_pages, promote_depth, promote_lineage, promote_blocks, ..} => {
                    // TODO this code is very similar to the MergingFrom::OtherPartial case below
                    //println!("promote_lineage: {:?}", promote_lineage);
                    //println!("promote_blocks: {:?}", promote_blocks);
                    let wrote = try!(write_survivors(&mut pw, &promote_pages, promote_depth, &promote_lineage, &old_segment, &inner.path, &f, from_level.get_dest_level()));

                    println!("survivors,from,{:?}, leaves_rewritten,{}, leaves_recycled,{}, parent1_rewritten,{}, parent1_recycled,{}, ms,{}", 
                             from_level, 
                             if wrote.nodes_rewritten.len() > 0 { wrote.nodes_rewritten[0].len() } else { 0 },
                             if wrote.nodes_recycled.len() > 0 { wrote.nodes_recycled[0] } else { 0 },
                             if wrote.nodes_rewritten.len() > 1 { wrote.nodes_rewritten[1].len() } else { 0 },
                             if wrote.nodes_recycled.len() > 1 { wrote.nodes_recycled[1] } else { 0 },
                             wrote.elapsed_ms,
                            );

                    let from = 
                        MergeFrom::Young{
                            old_segment: old_segment.pagenum,
                            new_segment: wrote.segment,
                        };
                    let mut blocks = promote_blocks;
                    for page in promote_pages {
                        blocks.add_page_no_reorder(page);
                    }
                    // TODO isn't promote_lineage the same as nodes rewritten, basically?
                    for depth in 0 .. wrote.nodes_rewritten.len() {
                        for pgnum in wrote.nodes_rewritten[depth].iter() {
                            blocks.add_page_no_reorder(*pgnum);
                        }
                    }
                    //println!("blocks becoming inactive on survivors: {:?}", blocks);
                    assert!(!now_inactive.contains_key(&old_segment.pagenum));
                    now_inactive.insert(old_segment.pagenum, blocks);
                    from
                },
                MergingFrom::OtherLeaf{level, segment, ..} => {
                    MergeFrom::Other{
                        level: level,
                        old_segment: segment,
                        new_segment: None,
                    }
                },
                MergingFrom::OtherPartial{level, old_segment, promote_pages, promote_depth, promote_lineage, promote_blocks, ..} => {
                    //println!("promote_lineage: {:?}", promote_lineage);
                    //println!("promote_blocks: {:?}", promote_blocks);
                    let wrote = try!(write_survivors(&mut pw, &promote_pages, promote_depth, &promote_lineage, &old_segment, &inner.path, &f, from_level.get_dest_level()));
                    println!("survivors,from,{:?}, leaves_rewritten,{}, leaves_recycled,{}, parent1_rewritten,{}, parent1_recycled,{}, ms,{}", 
                             from_level, 
                             if wrote.nodes_rewritten.len() > 0 { wrote.nodes_rewritten[0].len() } else { 0 },
                             if wrote.nodes_recycled.len() > 0 { wrote.nodes_recycled[0] } else { 0 },
                             if wrote.nodes_rewritten.len() > 1 { wrote.nodes_rewritten[1].len() } else { 0 },
                             if wrote.nodes_recycled.len() > 1 { wrote.nodes_recycled[1] } else { 0 },
                             wrote.elapsed_ms,
                            );

                    let from = 
                        MergeFrom::Other {
                            level: level,
                            old_segment: old_segment.pagenum,
                            new_segment: wrote.segment,
                        };
                    let mut blocks = promote_blocks;
                    for page in promote_pages {
                        blocks.add_page_no_reorder(page);
                    }
                    // TODO isn't promote_lineage the same as nodes rewritten, basically?
                    for depth in 0 .. wrote.nodes_rewritten.len() {
                        for pgnum in wrote.nodes_rewritten[depth].iter() {
                            blocks.add_page_no_reorder(*pgnum);
                        }
                    }
                    //println!("blocks becoming inactive on survivors: {:?}", blocks);
                    assert!(!now_inactive.contains_key(&old_segment.pagenum));
                    now_inactive.insert(old_segment.pagenum, blocks);
                    from
                },
            };

        try!(pw.end());

        // TODO bizarre.  with the following expensive_check turned on,
        // the multiple runs of the test suite are faster.
        if cfg!(expensive_check) 
        {
            // TODO function is inherently inefficient when called on a segment that
            // is in the header, because it loads and allocs the root page, a copy
            // of which is already in the header.
            fn get_blocklist_for_segment_including_root(
                page: PageNum,
                f: &std::sync::Arc<PageCache>,
                ) -> Result<BlockList> {
                let buf = try!(f.get(page));

                let pt = try!(PageType::from_u8(buf[0]));
                let mut blocks =
                    match pt {
                        PageType::LEAF_NODE => {
                            let page = try!(LeafPage::new(f.clone(), page));
                            page.blocklist_unsorted()
                        },
                        PageType::PARENT_NODE => {
                            let parent = try!(ParentPage::new(f.clone(), page));
                            try!(parent.blocklist_unsorted())
                        },
                    };
                blocks.add_page_no_reorder(page);
                Ok(blocks)
            }

            let old_now_inactive = {
                let mut now_inactive = HashMap::new();
                match from {
                    MergeFrom::Fresh{ref segments} => {
                        for &seg in segments.iter() {
                            let blocks = try!(get_blocklist_for_segment_including_root(seg, f));
                            assert!(!now_inactive.contains_key(&seg));
                            now_inactive.insert(seg, blocks);
                        }
                    },
                    MergeFrom::FreshNoRewrite{..} => {
                    },
                    MergeFrom::Young{old_segment, ..} => {
                        let blocks = try!(get_blocklist_for_segment_including_root(old_segment, f));
                        assert!(!now_inactive.contains_key(&old_segment));
                        now_inactive.insert(old_segment, blocks);
                    },
                    MergeFrom::Other{old_segment, ..} => {
                        let blocks = try!(get_blocklist_for_segment_including_root(old_segment, f));
                        assert!(!now_inactive.contains_key(&old_segment));
                        now_inactive.insert(old_segment, blocks);
                    },
                }
                match old_dest_segment {
                    Some(seg) => {
                        let blocks = try!(get_blocklist_for_segment_including_root(seg, f));
                        assert!(!now_inactive.contains_key(&seg));
                        now_inactive.insert(seg, blocks);
                    },
                    None => {
                    },
                }
                now_inactive
            };

            let old_now_inactive = {
                let mut old_now_inactive = old_now_inactive;
                match new_dest_segment {
                    Some(ref seg) => {
                        let mut blocks = try!(seg.blocklist_unsorted(f));
                        blocks.add_page_no_reorder(seg.root_page);
                        for (k,b) in old_now_inactive.iter_mut() {
                            b.remove_anything_in(&blocks);
                        }
                    },
                    None => {
                    },
                }
                match from {
                    MergeFrom::Young{ref new_segment, ..} => {
                        if let &Some(ref new_segment) = new_segment {
                            let mut blocks = try!(new_segment.blocklist_unsorted(f));
                            blocks.add_page_no_reorder(new_segment.root_page);
                            for (k, b) in old_now_inactive.iter_mut() {
                                b.remove_anything_in(&blocks);
                            }
                        }
                    },
                    MergeFrom::Other{ref new_segment, ..} => {
                        if let &Some(ref new_segment) = new_segment {
                            let mut blocks = try!(new_segment.blocklist_unsorted(f));
                            blocks.add_page_no_reorder(new_segment.root_page);
                            for (k, b) in old_now_inactive.iter_mut() {
                                b.remove_anything_in(&blocks);
                            }
                        }
                    },
                    _ => {
                    },
                }
                old_now_inactive
            };

            // TODO okay now the two should match

            //println!("now_inactive: {:?}", now_inactive);
            //println!("old_now_inactive: {:?}", old_now_inactive);

            {
                let mut new = now_inactive.keys().map(|p| *p).collect::<Vec<PageNum>>();
                new.sort();

                let mut old = old_now_inactive.keys().map(|p| *p).collect::<Vec<PageNum>>();
                old.sort();

                assert!(old == new);

                for seg in old {
                    let mut old_blocks = old_now_inactive.get(&seg).unwrap().clone();
                    let mut new_blocks = now_inactive.get(&seg).unwrap().clone();

                    old_blocks.sort_and_consolidate();
                    new_blocks.sort_and_consolidate();

                    //if cfg!(expensive_check) 
                    {
                        match new_dest_segment {
                            Some(ref new_dest_segment) => {
                                let mut blocks = try!(new_dest_segment.blocklist_unsorted(f));
                                blocks.add_page_no_reorder(new_dest_segment.root_page);

                                let both = blocks.remove_anything_in(&new_blocks);
                                if !both.is_empty() {
                                    println!("{:?}: inactive problem: segment {}", from_level, seg);
                                    println!("new: {:?}", new_blocks);
                                    println!("new inactive but in new dest ({}): {:?}", new_dest_segment.root_page, both);
                                    panic!();
                                }

                            },
                            None => {
                                //println!("new_dest_segment: None");
                            },
                        }
                    }

                    //if cfg!(expensive_check) 
                    {
                        match from {
                            MergeFrom::Young{ref new_segment, ..} => {
                                if let &Some(ref new_segment) = new_segment {
                                    let mut blocks = try!(new_segment.blocklist_unsorted(f));
                                    blocks.add_page_no_reorder(new_segment.root_page);

                                    let both = blocks.remove_anything_in(&new_blocks);
                                    if !both.is_empty() {
                                        println!("{:?}: inactive problem: segment {}", from_level, seg);
                                        println!("new: {:?}", new_blocks);
                                        println!("new inactive but in new from ({}): {:?}", new_segment.root_page, both);
                                        panic!();
                                    }
                                }

                            },
                            MergeFrom::Other{ref new_segment, ..} => {
                                if let &Some(ref new_segment) = new_segment {
                                    let mut blocks = try!(new_segment.blocklist_unsorted(f));
                                    blocks.add_page_no_reorder(new_segment.root_page);

                                    let both = blocks.remove_anything_in(&new_blocks);
                                    if !both.is_empty() {
                                        println!("{:?}: inactive problem: segment {}", from_level, seg);
                                        println!("new: {:?}", new_blocks);
                                        println!("new inactive but in new from ({}): {:?}", new_segment.root_page, both);
                                        panic!();
                                    }
                                }

                            },
                            _ => {
                                //println!("new_from_segment: None");
                            },
                        }
                    }

                    if old_blocks.count_pages() != new_blocks.count_pages() {
                        println!("{:?}: inactive mismatch: segment {}", from_level, seg);
                        println!("old count: {:?}", old_blocks.count_pages());
                        println!("new count: {:?}", new_blocks.count_pages());
                        println!("old: {:?}", old_blocks);
                        println!("new: {:?}", new_blocks);

                        let mut only_in_old = old_blocks.clone();
                        only_in_old.remove_anything_in(&new_blocks);
                        println!("only_in_old: {:?}", only_in_old);

                        let mut only_in_new = new_blocks.clone();
                        only_in_new.remove_anything_in(&old_blocks);
                        println!("only_in_new: {:?}", only_in_new);

                        panic!("inactive mismatch");
                    }
                }
            }
        }

        //println!("now_inactive: {:?}", now_inactive);

        let pm = 
            PendingMerge {
                from: from,
                old_dest_segment: old_dest_segment,
                new_dest_segment: new_dest_segment,
                now_inactive: now_inactive,
            };
        //println!("PendingMerge: {:?}", pm);

        let t2 = time::PreciseTime::now();
        let elapsed = t1.to(t2);
        //println!("prepare,from,{:?}, ms,{}", from_level, elapsed.num_milliseconds());

        Ok(pm)
    }

    fn commit_merge(&self, pm: PendingMerge) -> Result<()> {
        let dest_level = pm.from.get_dest_level();
        //println!("commit_merge: {:?}", pm);
        {
            let mut headerstuff = try!(self.header.write());

            // TODO assert new seg shares no pages with any seg in current state?

            let mut newHeader = headerstuff.data.clone();

            fn update_header(newHeader: &mut HeaderData, old_dest_segment: Option<PageNum>, new_dest_segment: Option<SegmentHeaderInfo>, dest_level: usize) {
                match (old_dest_segment, new_dest_segment) {
                    (None, None) => {
                        // a merge resulted in what would have been an empty segment.
                        // multiple promoted segments cancelled each other out.
                        // but there wasn't anything in this level anyway, either
                        // because it didn't exist or had been depleted.
                        if newHeader.levels.len() == dest_level {
                            // fine
                        } else {
                            assert!(newHeader.levels[dest_level].is_none());
                        }
                    },
                    (None, Some(new_seg)) => {
                        if newHeader.levels.len() == dest_level {
                            // first merge into this new level
                            newHeader.levels.push(Some(new_seg));
                        } else {
                            // merge into a previously depleted level
                            assert!(dest_level < newHeader.levels.len());
                            assert!(newHeader.levels[dest_level].is_none());
                            newHeader.levels[dest_level] = Some(new_seg);
                            println!("level {} resurrected", dest_level);
                        }
                    },
                    (Some(old), None) => {
                        // a merge resulted in what would have been an empty segment.
                        // promoted segments cancelled out everything that was in
                        // the dest level.
                        assert!(dest_level < newHeader.levels.len());
                        assert!(newHeader.levels[dest_level].as_ref().unwrap().root_page == old);
                        // TODO if this is the last level, just remove it?
                        newHeader.levels[dest_level] = None;
                        println!("level {} depleted", dest_level);
                    },
                    (Some(old), Some(new_seg)) => {
                        // level already exists
                        assert!(dest_level < newHeader.levels.len());
                        assert!(newHeader.levels[dest_level].as_ref().unwrap().root_page == old);
                        newHeader.levels[dest_level] = Some(new_seg);
                    },
                }
            }

            fn find_segments_in_list(merge: &[PageNum], hdr: &[SegmentHeaderInfo]) -> usize {
                fn slice_within(sub: &[PageNum], within: &[PageNum]) -> usize {
                    match within.iter().position(|&g| g == sub[0]) {
                        Some(ndx_first) => {
                            let count = sub.len();
                            if sub == &within[ndx_first .. ndx_first + count] {
                                ndx_first
                            } else {
                                panic!("not contiguous")
                            }
                        },
                        None => {
                            panic!("not contiguous")
                        },
                    }
                }

                // verify that segemnts are contiguous and at the end
                let hdr = hdr.iter().map(|seg| seg.root_page).collect::<Vec<_>>();
                let ndx = slice_within(merge, hdr.as_slice());
                assert!(ndx == hdr.len() - merge.len());
                ndx
            }

            let mut deps = HashMap::new();

            // TODO this code assumes that the new dest segment might have
            // recycled something from ANY of the promoted segments OR from
            // the old dest segment.  this is a little bit pessimistic.
            // a node page can only be recycled from the old dest, but overflows
            // could have been recycled from anywhere.  the write merge segment code
            // could keep track of things more closely, but that would probably
            // be low bang for the buck.
            match pm.new_dest_segment {
                None => {
                },
                Some(ref new_seg) => {
                    let mut deps_dest = vec![];
                    match pm.from {
                        MergeFrom::Fresh{ref segments} => {
                            for seg in segments {
                                deps_dest.push(*seg);
                            }
                        },
                        MergeFrom::FreshNoRewrite{..} => {
                            assert!(pm.now_inactive.is_empty());
                        },
                        MergeFrom::Young{old_segment, ..} => {
                            deps_dest.push(old_segment);
                        },
                        MergeFrom::Other{old_segment, ..} => {
                            deps_dest.push(old_segment);
                        },
                    }
                    match pm.old_dest_segment {
                        Some(seg) => {
                            deps_dest.push(seg);
                        },
                        None => {
                        },
                    }
                    assert!(!deps.contains_key(&new_seg.root_page));
                    deps.insert(new_seg.root_page, deps_dest);
                },
            }

            // also, the survivors must depend on the old segment

            match pm.from {
                MergeFrom::Fresh{..} => {
                },
                MergeFrom::FreshNoRewrite{..} => {
                },
                MergeFrom::Young{old_segment, ref new_segment} => {
                    match new_segment {
                        &Some(ref new_segment) => {
                            assert!(!deps.contains_key(&new_segment.root_page));
                            deps.insert(new_segment.root_page, vec![old_segment]);
                        },
                        &None => {
                        },
                    }
                },
                MergeFrom::Other{level, old_segment, ref new_segment} => {
                    match new_segment {
                        &Some(ref new_segment) => {
                            assert!(!deps.contains_key(&new_segment.root_page));
                            deps.insert(new_segment.root_page, vec![old_segment]);
                        },
                        &None => {
                        },
                    }
                },
            }

            match pm.from {
                MergeFrom::Fresh{ref segments} => {
                    let ndx = find_segments_in_list(segments, &headerstuff.data.fresh);
                    for _ in segments {
                        newHeader.fresh.remove(ndx);
                    }

                    assert!(pm.old_dest_segment.is_none());
                    match pm.new_dest_segment {
                        None => {
                            // a merge resulted in what would have been an empty segment.
                            // this happens because tombstones.
                            // multiple segments from the fresh level cancelled each other out.
                            // nothing needs to be inserted in the young level.
                        },
                        Some(new_seg) => {
                            newHeader.young.insert(0, new_seg);
                        },
                    }
                },
                MergeFrom::FreshNoRewrite{ref segments} => {
                    let ndx = find_segments_in_list(segments, &headerstuff.data.fresh);
                    for _ in segments {
                        let s = newHeader.fresh.remove(ndx);
                        newHeader.young.insert(0, s);
                    }

                    assert!(pm.old_dest_segment.is_none());
                    assert!(pm.new_dest_segment.is_none());
                },
                MergeFrom::Young{old_segment, new_segment} => {
                    let i = newHeader.young.len() - 1;
                    assert!(old_segment == newHeader.young[i].root_page);
                    match new_segment {
                        Some(new_segment) => {
                            newHeader.young[i] = new_segment;
                        },
                        None => {
                            newHeader.young.remove(i);
                        },
                    }

                    let dest_level = 0;
                    update_header(&mut newHeader, pm.old_dest_segment, pm.new_dest_segment, dest_level);
                },
                MergeFrom::Other{level, old_segment, new_segment} => {
                    assert!(old_segment == newHeader.levels[level].as_ref().unwrap().root_page);
                    newHeader.levels[level] = new_segment;

                    let dest_level = level + 1;
                    update_header(&mut newHeader, pm.old_dest_segment, pm.new_dest_segment, dest_level);
                },
            }

            newHeader.mergeCounter = newHeader.mergeCounter + 1;

            try!(headerstuff.write_header(newHeader, self.page_cache.page_size()));
            //println!("merge committed");

            let mut space = try!(self.space.lock());
            for (seg, depends_on) in deps {
                space.add_dependencies(seg, depends_on);
            }
            space.add_inactive(pm.now_inactive);
        }

        // note that we intentionally do not release the writeLock here.
        // you can change the segment list more than once while holding
        // the writeLock.  the writeLock gets released when you Dispose() it.

        try!(self.notify_work(dest_level.as_from_level()));

        Ok(())
    }

}

struct PageWriter {
    inner: std::sync::Arc<InnerPart>,
    f: File,

    // TODO the following two could be BlockLists if we didn't have to worry about it reordering the list
    blocks: Vec<PageBlock>,
    group_blocks: Vec<PageBlock>,

    last_page: PageNum,
}

impl PageWriter {
    fn new(inner: std::sync::Arc<InnerPart>) -> Result<Self> {
        let f = try!(inner.OpenForWriting());
        let pw = PageWriter {
            inner: inner,
            f: f,
            blocks: vec![],
            group_blocks: vec![],
            last_page: 0,
        };
        Ok(pw)
    }

    fn request_block(&self, req: BlockRequest) -> Result<PageBlock> {
        let mut space = try!(self.inner.space.lock());
        let blk = space.getBlock(req);
        Ok(blk)
    }

    fn ensure_inventory(&mut self) -> Result<()> {
        assert!(self.blocks.len() <= 2);
        if self.blocks.is_empty() {
            let blk = try!(self.request_block(BlockRequest::MinimumSize(2)));
            self.blocks.push(blk);
            Ok(())
        } else if self.blocks.len() == 1 {
            if self.blocks[0].count_pages() == 1 {
                let want = self.blocks[0].lastPage + 1;
                let blk2 = try!(self.request_block(BlockRequest::StartOrAny(vec![want])));
                if blk2.firstPage == want {
                    self.blocks[0].lastPage = blk2.lastPage;
                } else {
                    self.blocks.push(blk2);
                }
            }
            Ok(())
        } else if self.blocks.len() == 2 {
            Ok(())
        } else {
            unreachable!();
        }
    }

    fn get_page_from(blocks: &mut Vec<PageBlock>) -> Result<PageNum> {
        assert!(!blocks.is_empty());
        if blocks[0].count_pages() == 1 {
            assert!(blocks.len() > 1);
            let blk = blocks.remove(0);
            assert!(blk.firstPage == blk.lastPage);
            Ok(blk.firstPage)
        } else {
            let pg = blocks[0].firstPage;
            blocks[0].firstPage += 1;
            Ok(pg)
        }
    }

    fn get_page(&mut self) -> Result<PageNum> {
        try!(self.ensure_inventory());
        let pg = try!(Self::get_page_from(&mut self.blocks));
        Ok(pg)
    }

    fn ensure_group_inventory(&mut self, group: &BlockList, limit: usize) -> Result<()> {
        // TODO the limit parameter is the hard limit on the size of the
        // encoded blocklist for the group.  We can use this information,
        // in cases where we are getting close to the limit, to get more
        // desperate and request a large block at the end of the file.

        // TODO not sure what minimum size we should request.
        // we want overflows to be contiguous, but we also want to
        // avoid putting them at the end of the file.
        // TODO config constant?
        const MINIMUM_SIZE_FIRST_BLOCK_IN_GROUP: PageCount = 16;

        assert!(self.group_blocks.len() <= 2);
        if self.group_blocks.is_empty() {
            // if there is no inventory, then the group has gotta be empty,
            // because we don't allow the inventory to be completely depleted
            // during the processing of a group.
            assert!(group.is_empty());

            // TODO we might want to prefer a very early block, since all the other blocks
            // in this group are going to have to be after it.  

            // note that the free block list 
            // is secondary sorted by firstPage ASC.

            // suppose the min size is 10.  
            
            // Would we prefer a 500 page block late in the file?  making it less likely
            // that we will need another block at all?  but if we do need another block,
            // we will have ruled out all the free blocks before it.

            // or would we prefer a 10 page block early in the file?  this makes it more
            // likely we will need another block, but more of the free block list is
            // available for choosing.

            let blk = try!(self.request_block(BlockRequest::MinimumSize(MINIMUM_SIZE_FIRST_BLOCK_IN_GROUP)));
            self.group_blocks.push(blk);
            Ok(())
        } else if self.group_blocks.len() == 1 {
            if !group.is_empty() {
                assert!(self.group_blocks[0].firstPage > group.blocks[0].firstPage);
            }
            if self.group_blocks[0].count_pages() == 1 {
                // we always prefer a block which extends the one we've got in inventory
                let want = self.group_blocks[0].lastPage + 1;

                let req =
                    match group.count_blocks() {
                        0 => {
                            // group hasn't started yet.  so it doesn't care where the block is,
                            // but it soon will, because it will be given the currently available
                            // page, so we need to make sure we get something after that one.
                            let after = self.group_blocks[0].firstPage;

                            BlockRequest::StartOrAfterMinimumSize(vec![want], after, MINIMUM_SIZE_FIRST_BLOCK_IN_GROUP)
                        },
                        _ => {
                            // the one available page must fit on one of the blocks already
                            // in the group
                            assert!(group.would_extend_an_existing_block(self.group_blocks[0].firstPage));

                            // we would also prefer any block which would extend any of the
                            // blocks already in the group

                            let mut wants = Vec::with_capacity(4);
                            for i in 0 .. group.count_blocks() {
                                let pg = group.blocks[i].lastPage + 1;
                                if want != pg {
                                    wants.push(pg);
                                }
                            }
                            wants.insert(0, want);

                            // the group is running, so we cannnot accept any block before the
                            // first page of the group.
                            let after = group.blocks[0].firstPage;

                            // TODO use the limit provided for close cases
                            // TODO tune the numbers below
                            // TODO maybe the request size should be a formula instead of match cases

                            match group.count_blocks() {
                                0 => {
                                    // already handled above
                                    unreachable!();
                                },
                                1 => {
                                    BlockRequest::StartOrAfterMinimumSize(wants, after, 8)
                                },
                                2 => {
                                    BlockRequest::StartOrAfterMinimumSize(wants, after, 32)
                                },
                                3 => {
                                    BlockRequest::StartOrAfterMinimumSize(wants, after, 128)
                                },
                                4 => {
                                    BlockRequest::StartOrAfterMinimumSize(wants, after, 256)
                                },
                                5 => {
                                    BlockRequest::StartOrAfterMinimumSize(wants, after, 256)
                                },
                                _ => {
                                    BlockRequest::StartOrAfterMinimumSize(wants, after, 1024)
                                },
                            }
                        },
                    };
                let blk2 = try!(self.request_block(req));
                if !group.is_empty() {
                    assert!(blk2.firstPage > group.blocks[0].firstPage);
                }
                if blk2.firstPage == self.group_blocks[0].lastPage + 1 {
                    self.group_blocks[0].lastPage = blk2.lastPage;
                } else {
                    self.group_blocks.push(blk2);
                }
            }
            Ok(())
        } else if self.group_blocks.len() == 2 {
            if !group.is_empty() {
                assert!(self.group_blocks[0].firstPage > group.blocks[0].firstPage);
            }
            Ok(())
        } else {
            unreachable!();
        }
    }

    fn get_group_page(&mut self, group: &mut BlockList, limit: usize) -> Result<PageNum> {
        try!(self.ensure_group_inventory(group, limit));
        let pg = try!(Self::get_page_from(&mut self.group_blocks));
        if group.blocks.len() > 0 {
            let first = group.blocks[0].firstPage;
            assert!(pg > first);
        }
        let extended = group.add_page_no_reorder(pg);
        // TODO only consol if above false?
        group.sort_and_consolidate();
        assert!(group.encoded_len() < limit);
        Ok(pg)
    }

    fn page_size(&self) -> usize {
        self.inner.page_cache.page_size()
    }

    fn is_group_on_block_boundary(&mut self, group: &BlockList, limit: usize) -> Result<Option<PageNum>> {
        try!(self.ensure_group_inventory(group, limit));
        // at this point, the caller must be able to request 
        // two pages without change in the group inventory
        // don't reorder the inventory.
        // make sure we always take from the first block in inventory.

        if self.group_blocks[0].count_pages() > 1 {
            Ok(None)
        } else {
            assert!(self.group_blocks[0].count_pages() == 1);
            assert!(self.group_blocks.len() > 1);
            assert!(self.group_blocks[0].lastPage + 1 != self.group_blocks[1].firstPage);
            Ok(Some(self.group_blocks[1].firstPage))
        }
    }

    fn do_write(&mut self, buf: &[u8], pg: PageNum) -> Result<()> {
        if pg != self.last_page + 1 {
            try!(utils::SeekPage(&mut self.f, self.inner.page_cache.page_size(), pg));
        }
        try!(self.f.write_all(buf));
        self.last_page = pg;
        Ok(())
    }

    fn write_group_page(&mut self, buf: &[u8], group: &mut BlockList, limit: usize) -> Result<()> {
        let pg = try!(self.get_group_page(group, limit));
        try!(self.do_write(buf, pg));
        Ok(())
    }

    fn write_page(&mut self, buf: &[u8]) -> Result<PageNum> {
        let pg = try!(self.get_page());
        try!(self.do_write(buf, pg));
        //println!("wrote page {}", pg);
        Ok(pg)
    }

    // TODO this could happen on Drop.
    // but it needs error handling.
    // so maybe Drop should panic if it didn't happen.
    fn end(self) -> Result<()> {
        if !self.blocks.is_empty() || !self.group_blocks.is_empty() {
            let mut space = try!(self.inner.space.lock());
            if !self.blocks.is_empty() {
                space.add_free_blocks(BlockList {blocks: self.blocks});
            }
            if !self.group_blocks.is_empty() {
                space.add_free_blocks(BlockList {blocks: self.group_blocks});
            }
            // TODO consider calling space.truncate_if_possible() here
        }
        Ok(())
    }

}

// ----------------------------------------------------------------
// TODO the stuff below does not belong here

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
            let r = kvp{Key:k, Value:Blob::Boxed(v)};
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

            let r = kvp{Key:k, Value:Blob::Boxed(v)};
            self.cur = self.cur + 1;
            Some(Ok(r))
        }
    }
}

