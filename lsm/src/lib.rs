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

extern crate misc;
extern crate time;

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

const MIN_OVERFLOW_HEADER_LEN: usize = 32;

// TODO does this need to be a constant?  maybe we should just allow it
// to grow as needed?  but then we would need to start up new threads
// and channels.
const NUM_REGULAR_LEVELS: usize = 8;

pub type PageNum = u64;
pub type PageCount = u64;

#[derive(Debug)]
pub enum KeyForStorage {
// TODO maybe just a struct, with the box, and optional/private blocklist?
    Boxed(Box<[u8]>),
    SameFileOverflow(Box<[u8]>, PageNum),
}

impl KeyForStorage {
    fn as_ref(&self) -> &[u8] {
        match *self {
            KeyForStorage::Boxed(ref b) => b,
            KeyForStorage::SameFileOverflow(ref b, _) => b,
        }
    }

}

pub enum ValueForStorage {
    UnknownLen(Box<Read>),
    Read(Box<Read>, u64),
    Boxed(Box<[u8]>),
    Tombstone,
    SameFileOverflow(PageNum),
}

impl std::fmt::Debug for ValueForStorage {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            &ValueForStorage::Tombstone => {
                write!(f, "Tombstone")
            },
            &ValueForStorage::UnknownLen(_) => {
                write!(f, "UnknownLen")
            },
            &ValueForStorage::Read(_, len) => {
                write!(f, "Read ({})", len)
            },
            &ValueForStorage::Boxed(ref a) => {
                write!(f, "{:?}", a)
            },
            &ValueForStorage::SameFileOverflow(_) => {
                write!(f, "SameFileOverflow")
            },
        }
    }
}

impl ValueForStorage {
    fn is_tombstone(&self) -> bool {
        match self {
            &ValueForStorage::Tombstone => true,
            &ValueForStorage::UnknownLen(_) => false,
            &ValueForStorage::Read(_,_) => false,
            &ValueForStorage::Boxed(_) => false,
            &ValueForStorage::SameFileOverflow(_) => false,
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
    EarlyExactSize(PageCount),
    StartOrAfterMinimumSize(Vec<PageNum>, PageNum, PageCount),
    StartOrAny(Vec<PageNum>),
}

impl BlockRequest {
    fn start_is(&self, pg: PageNum) -> bool {
        match self {
            &BlockRequest::Any => false,
            &BlockRequest::MinimumSize(_) => false,
            &BlockRequest::EarlyExactSize(_) => false,

            &BlockRequest::StartOrAny(ref v) => v.iter().any(|n| *n == pg),
            &BlockRequest::StartOrAfterMinimumSize(ref v, _, _) => v.iter().any(|n| *n == pg),
        }
    }

    fn get_after(&self) -> Option<PageNum> {
        match self {
            &BlockRequest::Any => None,
            &BlockRequest::MinimumSize(_) => None,
            &BlockRequest::EarlyExactSize(_) => None,

            &BlockRequest::StartOrAny(_) => None,
            &BlockRequest::StartOrAfterMinimumSize(_, after, _) => Some(after),
        }
    }
}

pub struct PairForStorage {
    key: KeyForStorage,
    value: ValueForStorage,
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

    fn page_after(&self, cur: PageNum) -> PageNum {
        for i in 0 .. self.blocks.len() {
            let blk = &self.blocks[i];
            if blk.lastPage == cur {
                return self.blocks[i + 1].firstPage;
            } else if cur >= blk.firstPage && cur < blk.lastPage {
                return cur + 1;
            }
        }
        unreachable!();
    }

    fn last_page(&self) -> PageNum {
        // TODO assume it is sorted
        // TODO assuming self.blocks is not empty
        self.blocks[self.blocks.len() - 1].lastPage
    }

    pub fn first_page(&self) -> PageNum {
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

    fn encode_base(&self, a: &mut Vec<u64>) {
        // we store each PageBlock as first/offset instead of first/last, since the
        // offset will always compress better as a varint.
        
        // if there are multiple blocks, we store the firstPage field
        // of all blocks after the first one as offsets from the first one.
        // this requires that the first block has a firstPage field which is
        // lower than all the others.

        a.push( self.blocks.len() as u64);
        if self.blocks.len() > 0 {
            let first_page = self.blocks[0].firstPage;
            a.push( self.blocks[0].firstPage as u64);
            a.push( (self.blocks[0].lastPage - self.blocks[0].firstPage) as u64);
            if self.blocks.len() > 1 {
                for i in 1 .. self.blocks.len() {
                    assert!(self.blocks[i].firstPage > first_page);
                    a.push( (self.blocks[i].firstPage - first_page) as u64);
                    a.push( (self.blocks[i].lastPage - self.blocks[i].firstPage) as u64);
                }
            }
        }
    }

    fn encode(&self, pb: &mut PageBuilder) {
        let mut a = Vec::with_capacity(1 + self.blocks.len() * 2);
        self.encode_base(&mut a);
        for n in a {
            pb.put_varint(n);
        }
    }

    fn encode_into_vec(&self, v: &mut Vec<u8>) {
        let mut a = Vec::with_capacity(1 + self.blocks.len() * 2);
        self.encode_base(&mut a);
        for n in a {
            misc::push_varint(v, n);
        }
    }

    fn encoded_len(&self) -> usize {
        let mut len = 0;
        let mut a = Vec::with_capacity(1 + self.blocks.len() * 2);
        self.encode_base(&mut a);
        for v in a {
            len += varint::space_needed_for(v);
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
    Overflowed(Box<[u8]>, std::sync::Arc<PageCache>, PageNum),

    // the other two are references into the page
    Prefixed(&'a [u8],&'a [u8]),
    Slice(&'a [u8]),
}

impl<'a> std::fmt::Debug for KeyRef<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::result::Result<(), std::fmt::Error> {
        match *self {
            KeyRef::Overflowed(ref a, _, page) => write!(f, "Overflowed, page={}, a={:?}", page, a),
            KeyRef::Prefixed(front,back) => write!(f, "Prefixed, front={:?}, back={:?}", front, back),
            KeyRef::Slice(a) => write!(f, "Array, val={:?}", a),
        }
    }
}

impl<'a> KeyRef<'a> {
    fn into_key_for_merge(self) -> KeyForStorage {
        match self {
            KeyRef::Overflowed(a, _, page) => {
                KeyForStorage::SameFileOverflow(a, page)
            },
            KeyRef::Slice(a) => {
                let mut k = Vec::with_capacity(a.len());
                k.extend_from_slice(a);
                KeyForStorage::Boxed(k.into_boxed_slice())
            },
            KeyRef::Prefixed(front,back) => {
                let mut k = Vec::with_capacity(front.len() + back.len());
                k.extend_from_slice(front);
                k.extend_from_slice(back);
                KeyForStorage::Boxed(k.into_boxed_slice())
            },
        }
    }

    pub fn len(&self) -> usize {
        match *self {
            KeyRef::Overflowed(ref a, _, _) => a.len(),
            KeyRef::Slice(a) => a.len(),
            KeyRef::Prefixed(front, back) => front.len() + back.len(),
        }
    }

    pub fn u8_at(&self, i: usize) -> Result<u8> {
        match self {
            &KeyRef::Overflowed(ref a, _, _) => {
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
            &KeyRef::Overflowed(ref a, _, _) => {
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
                &KeyRef::Overflowed(ref a, _, _) => {
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
            &KeyRef::Overflowed(ref a, _, _) => {
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

    pub fn for_slice(k: &[u8]) -> KeyRef {
        KeyRef::Slice(k)
    }

    pub fn into_boxed_slice(self) -> Box<[u8]> {
        match self {
            KeyRef::Overflowed(a, _, _) => {
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
            (&KeyRef::Overflowed(ref x_k, _, _), &KeyRef::Overflowed(ref y_k, _, _)) => {
                bcmp::Compare(&x_k, &y_k)
            },
            (&KeyRef::Overflowed(ref x_k, _, _), &KeyRef::Prefixed(ref y_p, ref y_k)) => {
                Self::compare_x_py(&x_k, y_p, y_k)
            },
            (&KeyRef::Overflowed(ref x_k, _, _), &KeyRef::Slice(ref y_k)) => {
                bcmp::Compare(&x_k, &y_k)
            },
            (&KeyRef::Prefixed(ref x_p, ref x_k), &KeyRef::Overflowed(ref y_k, _, _)) => {
                Self::compare_px_y(x_p, x_k, &y_k)
            },
            (&KeyRef::Slice(ref x_k), &KeyRef::Overflowed(ref y_k, _, _)) => {
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
    Overflowed(std::sync::Arc<PageCache>, PageNum),
    Tombstone,
}

/// Like a ValueRef, but cannot represent a tombstone.  Available
/// only from a LivingCursor.
pub enum LiveValueRef<'a> {
    Slice(&'a [u8]),
    Overflowed(std::sync::Arc<PageCache>, PageNum),
}

impl<'a> ValueRef<'a> {
    fn into_value_for_merge(self) -> ValueForStorage {
        match self {
            ValueRef::Slice(a) => {
                let mut k = Vec::with_capacity(a.len());
                k.extend_from_slice(a);
                ValueForStorage::Boxed(k.into_boxed_slice())
            },
            ValueRef::Overflowed(_, page) => ValueForStorage::SameFileOverflow(page),
            ValueRef::Tombstone => ValueForStorage::Tombstone,
        }
    }

}

impl<'a> std::fmt::Debug for ValueRef<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::result::Result<(), std::fmt::Error> {
        match *self {
            ValueRef::Slice(a) => write!(f, "Array, len={:?}", a),
            ValueRef::Overflowed(_, page) => write!(f, "Overflowed, page={}", page),
            ValueRef::Tombstone => write!(f, "Tombstone"),
        }
    }
}

impl<'a> LiveValueRef<'a> {
    pub fn read(&'a self) -> Result<(u64, Box<Read + 'a>)> {
        match self {
            &LiveValueRef::Slice(a) => {
                let r = misc::ByteSliceRead::new(a);
                Ok((a.len() as u64, box r))
            },
            &LiveValueRef::Overflowed(ref f, page) => {
                let strm = try!(OverflowReader::new(f.clone(), page));
                Ok((strm.len, box strm))
            },
        }
    }

    pub fn _into_value_for_merge(self) -> ValueForStorage {
        match self {
            LiveValueRef::Slice(a) => {
                let mut k = Vec::with_capacity(a.len());
                k.extend_from_slice(a);
                ValueForStorage::Boxed(k.into_boxed_slice())
            },
            LiveValueRef::Overflowed(_, page) => ValueForStorage::SameFileOverflow(page),
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
            LiveValueRef::Overflowed(ref f, page) => {
                let mut a = vec![];
                let mut strm = try!(OverflowReader::new(f.clone(), page));
                try!(strm.read_to_end(&mut a));
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
            LiveValueRef::Overflowed(_, page) => write!(f, "Overflowed, page={}", page),
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
// since it uses SameFileOverflow.
struct CursorIterator {
    csr: MergeCursor,
    peeked: Option<Result<PairForStorage>>,
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

    fn overflows_eaten(self) -> Vec<(PageNum, PageNum)> {
        self.csr.overflows_eaten()
    }

    fn peek(&mut self) -> Option<&Result<PairForStorage>> {
        if self.peeked.is_none() {
            self.peeked = self.get_next();
        }
        match self.peeked {
            Some(ref value) => Some(value),
            None => None,
        }
    }

    fn get_next(&mut self) -> Option<Result<PairForStorage>> {
        if self.csr.is_valid() {
            let k = {
                let k = self.csr.key();
                if k.is_err() {
                    return Some(Err(k.err().unwrap()));
                }
                let k = k.unwrap().into_key_for_merge();
                k
            };
            let v = {
                let v = self.csr.value();
                if v.is_err() {
                    return Some(Err(v.err().unwrap()));
                }
                let v = v.unwrap().into_value_for_merge();
                v
            };
            let r = self.csr.next();
            if r.is_err() {
                return Some(Err(r.err().unwrap()));
            }
            Some(Ok(PairForStorage {key: k, value: v}))
        } else {
            return None;
        }
    }

}

impl Iterator for CursorIterator {
    type Item = Result<PairForStorage>;
    fn next(&mut self) -> Option<Result<PairForStorage>> {
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
    fn verify(&self, k: &KeyRef, sop: SeekOp, csr: &IForwardCursor) -> Result<()> {
        match self {
            &SeekResult::Invalid => {
                assert!(!csr.is_valid());
            },
            _ => {
                let q = try!(csr.key());
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

    fn from_cursor(csr: &IForwardCursor, k: &KeyRef) -> Result<SeekResult> {
        if csr.is_valid() {
            let kc = try!(csr.key());
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
    fn first(&mut self) -> Result<()>;
    fn next(&mut self) -> Result<()>;
    fn is_valid(&self) -> bool;
    fn key<'a>(&'a self) -> Result<KeyRef<'a>>;
}

pub trait IValue {
    fn value<'a>(&'a self) -> Result<ValueRef<'a>>;
    fn value_is_tombstone(&self) -> Result<bool>;
}

pub trait ILiveValue {
    fn value<'a>(&'a self) -> Result<LiveValueRef<'a>>;
}

pub trait ISeekableCursor {
    fn seek(&mut self, k: &KeyRef, sop: SeekOp) -> Result<SeekResult>;
    fn last(&mut self) -> Result<()>;
    fn prev(&mut self) -> Result<()>;

}

#[derive(Copy, Clone)]
pub struct DbSettings {
    pub default_page_size: usize,
    pub pages_per_block: PageCount,
    pub sleep_desperate_incoming: u64,
    pub sleep_desperate_waiting: u64,
    pub sleep_desperate_regular: u64,
    pub desperate_incoming: usize,
    pub desperate_waiting: usize,
    pub desperate_level_factor: u64,
    pub num_leaves_promote: usize,
    // TODO min consecutive recycle
    // TODO recent_free
    // TODO level factor
    // TODO what to promote from level N to N+1
}

pub const DEFAULT_SETTINGS: DbSettings = 
    DbSettings {
        default_page_size: 4096,
        pages_per_block: 256,
        sleep_desperate_incoming: 20,
        sleep_desperate_waiting: 20,
        sleep_desperate_regular: 50,
        desperate_incoming: 128,
        desperate_waiting: 128,
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
                    try!(page.blocklist_unsorted())
                },
                PageType::PARENT_NODE => {
                    let parent = try!(ParentPage::new(f.clone(), self.root_page));
                    try!(parent.blocklist_unsorted())
                },
            };
        Ok(blocks)
    }

    fn iter_nodes(&self, 
                          f: &std::sync::Arc<PageCache>,
                          ) -> Result<Box<Iterator<Item=Result<Node>>>> {
        let pt = try!(PageType::from_u8(self.buf[0]));
        let it: Box<Iterator<Item=Result<Node>>> =
            match pt {
                PageType::LEAF_NODE => {
                    let page = try!(LeafPage::new(f.clone(), self.root_page));
                    let node = Node {
                        depth: 0,
                        page: self.root_page,
                        parent: None,
                    };
                    let it = std::iter::once(Ok(node));
                    box it
                },
                PageType::PARENT_NODE => {
                    let parent = try!(ParentPage::new(f.clone(), self.root_page));
                    let it = parent.into_node_iter(0);
                    box it
                },
            };
        Ok(it)
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
                    try!(cursor.first());
                    while cursor.is_valid() {
                        count += 1;
                        try!(cursor.next());
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

    pub fn page_offset(pgsz: usize, pageNumber: PageNum) -> Result<u64> {
        if 0 == pageNumber { 
            // TODO should this panic?
            return Err(Error::InvalidPageNumber);
        }
        let pos = ((pageNumber as u64) - 1) * (pgsz as u64);
        Ok(pos)
    }

    pub fn seek_page<S: Seek>(strm: &mut S, pgsz: usize, pageNumber: PageNum) -> Result<u64> {
        let pos = try!(page_offset(pgsz, pageNumber));
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

    fn reset(&mut self) {
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

    fn available(&self) -> usize {
        self.buf.len() - self.cur
    }

    fn put_u8_at(&mut self, x: u8, at: usize) {
        self.buf[at] = x;
    }

    fn put_u8(&mut self, x: u8) {
        self.buf[self.cur] = x;
        self.cur = self.cur + 1;
    }

    fn put_from_stream<R: Read>(&mut self, s: &mut R, len: usize) -> io::Result<usize> {
        let n = try!(misc::io::read_fully(s, &mut self.buf[self.cur .. self.cur + len]));
        self.cur = self.cur + n;
        let res : io::Result<usize> = Ok(n);
        res
    }

    fn put_from_slice(&mut self, ba: &[u8]) {
        self.buf[self.cur .. self.cur + ba.len()].clone_from_slice(ba);
        self.cur = self.cur + ba.len();
    }

    fn put_varint(&mut self, ov: u64) {
        varint::write(&mut *self.buf, &mut self.cur, ov);
    }

    fn put_varint_at(&mut self, ov: u64, at: usize) {
        let mut cur = at;
        varint::write(&mut *self.buf, &mut cur, ov);
    }

    fn put_array_at(&mut self, ba: &[u8], at: usize) {
        self.buf[at .. at + ba.len()].clone_from_slice(ba);
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
            if c.is_valid() {
                let k = try!(c.key());
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

    fn find_min(&mut self) -> Result<Option<usize>> {
        self.dir = Direction::Forward;
        if self.subcursors.is_empty() {
            Ok(None)
        } else {
            try!(self.sort(false));
            Ok(self.sorted_first())
        }
    }

    fn find_max(&mut self) -> Result<Option<usize>> {
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
            let sr = try!(self.subcursors[j].seek(k, sop));
            if sr.is_valid_and_equal() { 
                self.cur = Some(j);
                return Ok(sr);
            }
        }
        match sop {
            SeekOp::SEEK_GE => {
                self.cur = try!(self.find_min());
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
                self.cur = try!(self.find_max());
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

impl IValue for MultiCursor {
    fn value<'a>(&'a self) -> Result<ValueRef<'a>> {
        match self.cur {
            None => {
                Err(Error::CursorNotValid)
            },
            Some(icur) => {
                self.subcursors[icur].value()
            },
        }
    }

    fn value_is_tombstone(&self) -> Result<bool> {
        match self.cur {
            None => {
                Err(Error::CursorNotValid)
            },
            Some(icur) => {
                self.subcursors[icur].value_is_tombstone()
            },
        }
    }

}

impl IForwardCursor for MultiCursor {
    fn is_valid(&self) -> bool {
        match self.cur {
            Some(i) => self.subcursors[i].is_valid(),
            None => false
        }
    }

    fn first(&mut self) -> Result<()> {
        for i in 0 .. self.subcursors.len() {
            try!(self.subcursors[i].first());
        }
        self.cur = try!(self.find_min());
        Ok(())
    }

    fn key<'a>(&'a self) -> Result<KeyRef<'a>> {
        match self.cur {
            None => {
                Err(Error::CursorNotValid)
            },
            Some(icur) => {
                self.subcursors[icur].key()
            },
        }
    }

    fn next(&mut self) -> Result<()> {
        //println!("MC next");
        match self.cur {
            None => {
                Err(Error::CursorNotValid)
            },
            Some(icur) => {
                // we need to fix every cursor to point to its min
                // value > icur.

                // if perf didn't matter, this would be simple.
                // call next on icur.  and call Seek(GE) (and maybe next)
                // on every other cursor.

                // but there are several cases where we can do a lot
                // less work than a Seek.  And we have the information
                // to identify those cases.  So, this function is
                // pretty complicated, but it's fast.

                // --------

                // the current cursor (icur) is easy.  it just needs next().
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
                    // entries which were Ordering:Equal to cur.  call next on
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
                                    try!(self.subcursors[n].next());
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
                                    if csr.is_valid() {
                                        let cmp = {
                                            let k = try!(csr.key());
                                            let cmp = KeyRef::cmp(&k, ki);
                                            cmp
                                        };
                                        match cmp {
                                            Ordering::Less => {
                                                try!(csr.next());
                                                // we moved one step.  let's see if we need to move one more.
                                                if csr.is_valid() {
                                                    let cmp = {
                                                        let k = try!(csr.key());
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
                                                            try!(csr.next());
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
                                                try!(csr.next());
                                            },
                                        }
                                    } else {
                                        let sr = try!(csr.seek(&ki, SeekOp::SEEK_GE));
                                        if sr.is_valid_and_equal() {
                                            try!(csr.next());
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
                                    let sr = try!(csr.seek(&ki, SeekOp::SEEK_GE));
                                    if sr.is_valid_and_equal() {
                                        try!(csr.next());
                                    }
                                }
                                Ok(())
                            },
                        }
                    }

                    {
                        let (before, middle, after) = split3(&mut *self.subcursors, icur);
                        let icsr = &middle[0];
                        let ki = try!(icsr.key());
                        try!(half(self.dir, &ki, before));
                        try!(half(self.dir, &ki, after));
                    }
                }

                // now the current cursor
                try!(self.subcursors[icur].next());

                // now re-sort
                self.cur = try!(self.find_min());
                Ok(())
            },
        }
    }

}

impl ISeekableCursor for MultiCursor {
    fn last(&mut self) -> Result<()> {
        for i in 0 .. self.subcursors.len() {
            try!(self.subcursors[i].last());
        }
        self.cur = try!(self.find_max());
        Ok(())
    }

    // TODO fix prev like next
    fn prev(&mut self) -> Result<()> {
        match self.cur {
            None => {
                Err(Error::CursorNotValid)
            },
            Some(icur) => {
                let kboxed = {
                    let k = try!(self.subcursors[icur].key());
                    let k = k.into_boxed_slice();
                    k
                };
                let k = KeyRef::Slice(&kboxed);
                for j in 0 .. self.subcursors.len() {
                    let csr = &mut self.subcursors[j];
                    if (self.dir != Direction::Backward) && (icur != j) { 
                        try!(csr.seek(&k, SeekOp::SEEK_LE));
                    }
                    if csr.is_valid() {
                        let eq = {
                            let kc = try!(csr.key());
                            Ordering::Equal == KeyRef::cmp(&kc, &k)
                        };
                        if eq {
                            try!(csr.prev());
                        }
                    }
                }
                self.cur = try!(self.find_max());
                Ok(())
            },
        }
    }

    fn seek(&mut self, k: &KeyRef, sop: SeekOp) -> Result<SeekResult> {
        //println!("MC seek  k={:?}  sop={:?}", k, sop);
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

    // fst of the following tuple is segment num
    overflows_eaten: Vec<(PageNum, PageNum)>,
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

    // overflows owned by leaves but shadowed by something earlier
    fn overflows_eaten(self) -> Vec<(PageNum, PageNum)> {
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
            if c.is_valid() {
                ka.push(Some(try!(c.key())));
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

    fn find_min(&mut self) -> Result<Option<usize>> {
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

impl IValue for MergeCursor {
    fn value<'a>(&'a self) -> Result<ValueRef<'a>> {
        match self.cur {
            None => {
                Err(Error::CursorNotValid)
            },
            Some(icur) => {
                self.subcursors[icur].value()
            },
        }
    }

    fn value_is_tombstone(&self) -> Result<bool> {
        match self.cur {
            None => {
                Err(Error::CursorNotValid)
            },
            Some(icur) => {
                self.subcursors[icur].value_is_tombstone()
            },
        }
    }

}

impl IForwardCursor for MergeCursor {
    fn is_valid(&self) -> bool {
        match self.cur {
            Some(i) => self.subcursors[i].is_valid(),
            None => false
        }
    }

    fn first(&mut self) -> Result<()> {
        for i in 0 .. self.subcursors.len() {
            try!(self.subcursors[i].first());
        }
        if self.subcursors.len() > 1 {
            self.cur = try!(self.find_min());
        } else {
            self.cur = Some(0);
        }
        Ok(())
    }

    fn key<'a>(&'a self) -> Result<KeyRef<'a>> {
        match self.cur {
            None => {
                Err(Error::CursorNotValid)
            },
            Some(icur) => {
                self.subcursors[icur].key()
            },
        }
    }

    fn next(&mut self) -> Result<()> {
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
                    // call next on icur.  and call Seek(GE) (and maybe next)
                    // on every other cursor.

                    // because we keep the list sorted,
                    // each cursor is at most
                    // one step away.

                    // we know that every valid cursor
                    // is pointing at a key which is either == to icur, or
                    // it is already the min key > icur.

                    assert!(icur == self.sorted[0].0);
                    // immediately after that, there may (or may not be) some
                    // entries which were Ordering:Equal to cur.  call next on
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
                                        match try!(self.subcursors[n].key()) {
                                            KeyRef::Prefixed(_, _) => {
                                            },
                                            KeyRef::Slice(_) => {
                                            },
                                            KeyRef::Overflowed(_, _, page) => {
                                                self.overflows_eaten.push((try!(self.subcursors[n].current_pagenum()), page));
                                            },
                                        }

                                        match try!(self.subcursors[n].value()) {
                                            ValueRef::Slice(_) => {
                                            },
                                            ValueRef::Tombstone => {
                                            },
                                            ValueRef::Overflowed(_, page) => {
                                                self.overflows_eaten.push((try!(self.subcursors[n].current_pagenum()), page));
                                            },
                                        }
                                    }
                                    try!(self.subcursors[n].next());
                                } else {
                                    break;
                                }
                            },
                        }
                    }

                    // now the current cursor
                    try!(self.subcursors[icur].next());

                    // now re-sort
                    self.cur = try!(self.find_min());
                    Ok(())
                } else {
                    assert!(icur == 0);
                    try!(self.subcursors[icur].next());
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
    fn skip_tombstones_forward(&mut self) -> Result<()> {
        while self.chain.is_valid() && try!(self.chain.value_is_tombstone()) {
            self.skipped += 1;
            try!(self.chain.next());
        }
        Ok(())
    }

    fn skip_tombstones_backward(&mut self) -> Result<()> {
        while self.chain.is_valid() && try!(self.chain.value_is_tombstone()) {
            self.skipped += 1;
            try!(self.chain.prev());
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

impl ILiveValue for LivingCursor {
    fn value<'a>(&'a self) -> Result<LiveValueRef<'a>> {
        match try!(self.chain.value()) {
            ValueRef::Slice(a) => Ok(LiveValueRef::Slice(a)),
            ValueRef::Overflowed(f, blocks) => Ok(LiveValueRef::Overflowed(f, blocks)),
            ValueRef::Tombstone => Err(Error::Misc(String::from("LiveValueRef tombstone TODO unreachable"))),
        }
    }

}

impl IForwardCursor for LivingCursor {
    fn first(&mut self) -> Result<()> {
        try!(self.chain.first());
        try!(self.skip_tombstones_forward());
        Ok(())
    }

    fn key<'a>(&'a self) -> Result<KeyRef<'a>> {
        self.chain.key()
    }

    fn is_valid(&self) -> bool {
        self.chain.is_valid() 
            && {
                let r = self.chain.value_is_tombstone();
                if r.is_ok() {
                    !r.unwrap()
                } else {
                    false
                }
            }
    }

    fn next(&mut self) -> Result<()> {
        //println!("LC next");
        try!(self.chain.next());
        try!(self.skip_tombstones_forward());
        Ok(())
    }

}

impl ISeekableCursor for LivingCursor {
    fn last(&mut self) -> Result<()> {
        try!(self.chain.last());
        try!(self.skip_tombstones_backward());
        Ok(())
    }

    fn prev(&mut self) -> Result<()> {
        try!(self.chain.prev());
        try!(self.skip_tombstones_backward());
        Ok(())
    }

    fn seek(&mut self, k: &KeyRef, sop:SeekOp) -> Result<SeekResult> {
        //println!("Living seek  k={:?}  sop={:?}", k, sop);
        let sr = try!(self.chain.seek(k, sop));
        if cfg!(expensive_check) 
        {
            try!(sr.verify(k, sop, self));
        }
        match sop {
            SeekOp::SEEK_GE => {
                if sr.is_valid() && self.chain.value_is_tombstone().unwrap() {
                    try!(self.skip_tombstones_forward());
                    SeekResult::from_cursor(&*self.chain, k)
                } else {
                    Ok(sr)
                }
            },
            SeekOp::SEEK_LE => {
                if sr.is_valid() && self.chain.value_is_tombstone().unwrap() {
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

}

impl IForwardCursor for RangeCursor {
    fn key<'a>(&'a self) -> Result<KeyRef<'a>> {
        if self.is_valid() {
            self.chain.key()
        } else {
            Err(Error::CursorNotValid)
        }
    }

    fn is_valid(&self) -> bool {
        self.chain.is_valid() 
            && {
                let k = self.chain.key().unwrap();
                //println!("RC bounds checking: {:?}", k);
                self.min.is_in_bounds(&k) && self.max.is_in_bounds(&k)
            }
    }

    fn first(&mut self) -> Result<()> {
        let sr = try!(self.chain.seek(&KeyRef::for_slice(&self.min.k), SeekOp::SEEK_GE));
        match (sr, self.min.cmp) {
            (SeekResult::Equal, OpGt::GT) => {
                try!(self.chain.next());
            },
            _ => {
            },
        }
        Ok(())
    }

    fn next(&mut self) -> Result<()> {
        if self.is_valid() {
            self.chain.next()
        } else {
            Err(Error::CursorNotValid)
        }
    }

}

impl ILiveValue for RangeCursor {
    fn value<'a>(&'a self) -> Result<LiveValueRef<'a>> {
        if self.is_valid() {
            self.chain.value()
        } else {
            Err(Error::CursorNotValid)
        }
    }

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

}

impl<'c> IForwardCursor for PrefixCursor<'c> {
    // TODO lifetimes below should be 'c ?
    fn key<'a>(&'a self) -> Result<KeyRef<'a>> {
        if self.is_valid() {
            let k = try!(self.chain.key());
            //println!("PrefixCursor yielding: {:?}", k);
            //assert!(k.starts_with(&self.prefix));
            Ok(k)
        } else {
            Err(Error::CursorNotValid)
        }
    }

    fn is_valid(&self) -> bool {
        self.chain.is_valid() 
            && 
            {
                let k = self.chain.key().unwrap();
                //println!("PrefixCursor chain is valid, its k={:?}", k);
                k.starts_with(&self.prefix)
            }
    }

    fn first(&mut self) -> Result<()> {
        let sr = try!(self.chain.seek(&KeyRef::for_slice(&self.prefix), SeekOp::SEEK_GE));
        Ok(())
    }

    fn next(&mut self) -> Result<()> {
        if self.is_valid() {
            try!(self.chain.next());
            Ok(())
        } else {
            Err(Error::CursorNotValid)
        }
    }

}

impl<'c> ILiveValue for PrefixCursor<'c> {
    // TODO lifetimes below should be 'c ?
    fn value<'a>(&'a self) -> Result<LiveValueRef<'a>> {
        if self.is_valid() {
            self.chain.value()
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

#[derive(Debug, Clone)]
enum ChildInfo {
    Leaf{
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
                count_tombstones,
            } => {
                varint::space_needed_for(count_tombstones as u64)
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

// this type is used during construction of a page
#[derive(Debug, Clone)]
pub struct ItemForParent {
    pub page: PageNum,
    info: ChildInfo,

    last_key: KeyWithLocationForParent,
}

impl ItemForParent {
    #[cfg(remove_me)]
    fn new(page: PageNum, blocks: BlockList, last_key: KeyWithLocation) -> ItemForParent {
        assert!(!blocks.contains_page(page));
        ItemForParent {
            page: page,
            blocks: blocks,
            last_key: last_key,
        }
    }

    fn need(&self, prefix_len: usize) -> usize {
        let needed = 
            varint::space_needed_for(self.page as u64) 
            + self.info.need()
            + self.last_key.need(prefix_len)
            ;
        needed
    }

    fn is_inline(&self) -> bool {
        self.last_key.is_inline()
    }

    fn to_owned_overflow(&mut self, pw: &mut PageWriter) -> Result<()> {
        let k = &self.last_key.key;
        let mut r = misc::ByteSliceRead::new(&k);
        let (len, blocks) = try!(write_overflow_known_len(&mut r, k.len() as u64, pw));
        assert!((len as usize) == k.len());
        //println!("OwnedOverflow: {:?}", blocks);
        self.last_key.location = KeyLocationForParent::OwnedOverflow(blocks.first_page());
        Ok(())
    }

}

struct ParentUnderConstruction {
    prefix_len: usize,
    sofar: usize,
    items: Vec<ItemForParent>,
}

// this type is used during construction of a page
#[derive(Debug, Clone)]
enum KeyLocationForLeaf {
    Inline,
    Overflow(PageNum),
}

// this type is used during construction of a page
#[derive(Debug, Clone)]
enum KeyLocationForParent {
    Inline,
    BorrowedOverflow(PageNum),
    OwnedOverflow(PageNum),
}

impl ValueLocation {
    #[inline]
    fn val_with_flag_for_len_inline(vlen: usize) -> u64 {
        (vlen as u64) << 1
    }

    fn need(&self) -> usize {
        match self {
            &ValueLocation::Tombstone => {
                varint::space_needed_for(1 as u64) 
            },
            &ValueLocation::Buffer(ref vbuf) => {
                let val = Self::val_with_flag_for_len_inline(vbuf.len());
                varint::space_needed_for(val) 
                + vbuf.len()
            },
            &ValueLocation::Overflowed(page) => {
                let val_with_flag = ((page as u64) << 1) | 1;
                varint::space_needed_for(val_with_flag as u64)
            },
        }
    }

}

impl KeyLocationForLeaf {
    fn val_with_overflow_flag(&self, k: &[u8]) -> u64 {
        assert!(k.len() > 0);
        match *self {
            KeyLocationForLeaf::Inline => {
                (k.len() as u64) << 1
            },
            KeyLocationForLeaf::Overflow(page) => {
                ((page as u64) << 1) | 1
            },
        }
    }

    fn need(&self, k: &[u8], prefix_len: usize) -> usize {
        match *self {
            KeyLocationForLeaf::Inline => {
                assert!(k.len() >= prefix_len);
                varint::space_needed_for(self.val_with_overflow_flag(k)) 
                + k.len() 
                - prefix_len
            },
            KeyLocationForLeaf::Overflow(page) => {
                varint::space_needed_for(self.val_with_overflow_flag(k)) 
            },
        }
    }

    fn for_parent(self) -> KeyLocationForParent {
        match self {
            KeyLocationForLeaf::Inline => KeyLocationForParent::Inline,
            KeyLocationForLeaf::Overflow(blocks) => KeyLocationForParent::BorrowedOverflow(blocks),
        }
    }

    fn is_inline(&self) -> bool {
        match *self {
            KeyLocationForLeaf::Inline => true,
            KeyLocationForLeaf::Overflow(_) => false,
        }
    }

}

impl KeyLocationForParent {
    fn val_with_overflow_flag(&self, k: &[u8]) -> u64 {
        assert!(k.len() > 0);
        match *self {
            KeyLocationForParent::Inline => {
                let klen = (k.len() as u64) << 2;
                klen
            },
            KeyLocationForParent::BorrowedOverflow(page) => {
                let page = (page as u64) << 2;
                page | 1
            },
            KeyLocationForParent::OwnedOverflow(page) => {
                let page = (page as u64) << 2;
                page | 1 | 2
            },
        }
    }

    fn need(&self, k: &[u8], prefix_len: usize) -> usize {
        match *self {
            KeyLocationForParent::Inline => {
                assert!(k.len() >= prefix_len);
                varint::space_needed_for(self.val_with_overflow_flag(k)) 
                + k.len() 
                - prefix_len
            },
            KeyLocationForParent::BorrowedOverflow(page) 
            | KeyLocationForParent::OwnedOverflow(page) => 
            {
                varint::space_needed_for(self.val_with_overflow_flag(k)) 
            },
        }
    }

    fn is_inline(&self) -> bool {
        match *self {
            KeyLocationForParent::Inline => true,
            KeyLocationForParent::BorrowedOverflow(_) => false,
            KeyLocationForParent::OwnedOverflow(_) => false,
        }
    }

    fn is_owned_overflow(&self) -> bool {
        match *self {
            KeyLocationForParent::Inline => false,
            KeyLocationForParent::BorrowedOverflow(_) => false,
            KeyLocationForParent::OwnedOverflow(_) => true,
        }
    }

}

impl KeyWithLocationForLeaf {
    pub fn key(&self) -> &[u8] {
        &self.key
    }

    fn for_parent(self) -> KeyWithLocationForParent {
        KeyWithLocationForParent {
            key: self.key,
            location: self.location.for_parent(),
        }
    }

    fn val_with_overflow_flag(&self) -> u64 {
        self.location.val_with_overflow_flag(&self.key)
    }

    fn need(&self, prefix_len: usize) -> usize {
        self.location.need(&self.key, prefix_len)
    }

    fn is_inline(&self) -> bool {
        self.location.is_inline()
    }
}

impl KeyWithLocationForParent {
    pub fn key(&self) -> &[u8] {
        &self.key
    }

    fn val_with_overflow_flag(&self) -> u64 {
        self.location.val_with_overflow_flag(&self.key)
    }

    fn need(&self, prefix_len: usize) -> usize {
        self.location.need(&self.key, prefix_len)
    }

    fn is_inline(&self) -> bool {
        self.location.is_inline()
    }

    // back to Inline
    fn fix_owned_overflow(&mut self) {
        assert!(self.key.len() > 0);
        if self.location.is_owned_overflow() {
            //println!("fixing owned overflow: {:?}", self.location);
            self.location = KeyLocationForParent::Inline;
        }
    }
}

#[derive(Debug, Clone)]
pub struct KeyWithLocationForLeaf {
    key: Box<[u8]>,
    location: KeyLocationForLeaf,
}

#[derive(Debug, Clone)]
pub struct KeyWithLocationForParent {
    key: Box<[u8]>,
    location: KeyLocationForParent,
}

// this enum keeps track of what happened to a value as we
// processed it.  it might have already been overflowed.  if
// it's going to fit in the page, we still have the data
// buffer.
#[derive(Debug)]
enum ValueLocation {
    Tombstone,
    // when this is a Buffer, this gets ownership of PairForStorage.value
    Buffer(Box<[u8]>),
    Overflowed(PageNum),
}

// this type is used during construction of a page
struct ItemForLeaf {
    key: KeyWithLocationForLeaf,
    value: ValueLocation,
}

impl ItemForLeaf {
    fn need(&self, prefix_len: usize) -> usize {
        self.key.need(prefix_len) + self.value.need()
    }

    fn is_key_inline(&self) -> bool {
        self.key.is_inline()
    }
}

struct LeafUnderConstruction {
    sofar: usize,
    items: Vec<ItemForLeaf>,
    prefix_len: usize,
    // TODO why do we need prev_key here?  can't we just look at the
    // last entry of items ?
    prev_key: Option<Box<[u8]>>,

}

fn calc_overflow_pages(len: u64, header_len: u64, pgsz: u64) -> PageCount {
    let total_len = header_len + len;
    let pages = total_len / pgsz + if 0 == (total_len % pgsz) {0} else {1};
    pages as PageCount
}

fn write_overflow_known_len<R: Read>(
                    ba: &mut R, 
                    len: u64,
                    pw: &mut PageWriter,
                   ) -> Result<(u64, BlockList)> {

    let pgsz = pw.page_size();
    let mut pb = PageBuilder::new(pgsz);

    let pages = calc_overflow_pages(len, MIN_OVERFLOW_HEADER_LEN as u64, pgsz as u64);

    let mut group = try!(pw.begin_group(Some(pages)));
    let mut sofar = 0;
    while sofar < len {
        pb.reset();
        let want =
            if sofar == 0 {
                // first page
                assert!(1 + varint::space_needed_for(len) <= MIN_OVERFLOW_HEADER_LEN);
                let mut hdr = [0; MIN_OVERFLOW_HEADER_LEN];
                hdr[0] = 1; // defines the format of the header
                let mut cur = 1;
                varint::write(&mut hdr, &mut cur, len);
                pb.put_from_slice(&hdr);
                pgsz - MIN_OVERFLOW_HEADER_LEN
            } else {
                pgsz
            };
        let put = try!(pb.put_from_stream(ba, want));
        if put > 0 {
            try!(pw.write_group_page(pb.buf(), &mut group));
        } else {
            // there was nothing to write
            assert!(sofar > 0);
        }
        sofar += put as u64;
    }
    assert!(sofar == len);
    //println!("overflow: len = {}  blocks.len = {}  encoded_len: {}", sofar, blocks.len(), blocks.encoded_len());
    let blocks = try!(pw.end_group(group));
    Ok((sofar, blocks))
}

fn write_overflow_unknown_len<R: Read>(
                    ba: &mut R, 
                    pw: &mut PageWriter,
                   ) -> Result<(u64, BlockList)> {

    let pgsz = pw.page_size();
    let mut pb_first = PageBuilder::new(pgsz);
    let mut pb = PageBuilder::new(pgsz);

    let mut group = try!(pw.begin_group(None));

    pb_first.reset();
    let mut hdr = [0; MIN_OVERFLOW_HEADER_LEN];
    // the header will need to get filled in later
    pb_first.put_from_slice(&hdr);
    let put = try!(pb_first.put_from_stream(ba, pgsz - MIN_OVERFLOW_HEADER_LEN));
    assert!(put > 0);
    try!(pw.write_group_page(pb_first.buf(), &mut group));
    let mut sofar = put as u64;

    loop {
        pb.reset();
        let put = try!(pb.put_from_stream(ba, pgsz));
        if put > 0 {
            try!(pw.write_group_page(pb.buf(), &mut group));
        } else {
            // there was nothing to write
            assert!(sofar > 0);
        }
        sofar += put as u64;
        if put < pgsz {
            break;
        }
    }

    //println!("overflow: len = {}  blocks.len = {}  encoded_len: {}", sofar, blocks.len(), blocks.encoded_len());
    let blocks = try!(pw.end_group(group));
    let len = sofar;
    println!("overflow unknown size: {:?}", blocks);

    // go back and fix the header on the first page
    let first_page = blocks.first_page();
    if blocks.count_blocks() == 1 {
        // the overflow ended up contiguous.
        // this can be format 1, no block list needed.
        let pages_should_be = calc_overflow_pages(len, MIN_OVERFLOW_HEADER_LEN as u64, pgsz as u64);
        assert!(pages_should_be == blocks.count_pages());
        pb_first.put_u8_at(1, 0);
        pb_first.put_varint_at(len, 1);
        try!(pw.write_page_at(pb_first.buf(), first_page));
    } else {
        let mut hdr = vec![];
        hdr.push(2u8);
        misc::push_varint(&mut hdr, len);
        blocks.encode_into_vec(&mut hdr);
        if hdr.len() <= MIN_OVERFLOW_HEADER_LEN {
            pb_first.put_array_at(&hdr, 0);
            try!(pw.write_page_at(pb_first.buf(), first_page));
        } else {
            // TODO format 3
            unimplemented!();
        }
    }

    Ok((len, blocks))
}

// TODO begin mod leaf

fn calc_leaf_page_len(prefix_len: usize, sofar: usize, count_items: usize) -> usize {
    2 // page type and flags
    + varint::space_needed_for(prefix_len as u64)
    + prefix_len
    + varint::space_needed_for(count_items as u64)
    + sofar // sum of size of all the actual items
}

struct BuildLeafReturnValue {
    last_key: KeyWithLocationForLeaf,
    overflows: Vec<PageNum>,
    len_page: usize,
    count_pairs: usize,
    count_tombstones: u64,
}

fn build_leaf(st: &mut LeafUnderConstruction, pb: &mut PageBuilder) -> BuildLeafReturnValue {
    pb.reset();
    pb.put_u8(PageType::LEAF_NODE.to_u8());
    pb.put_u8(0u8); // flags
    pb.put_varint(st.prefix_len as u64);
    if st.prefix_len > 0 {
        let mut other = None;
        for i in 0..st.items.len() {
            if st.items[i].is_key_inline() {
                other = Some(i);
                break;
            }
        }
        match other {
            Some(i) => {
                pb.put_from_slice(&st.items[i].key.key[0 .. st.prefix_len]);
            },
            None => {
                unreachable!();
            },
        }
    }
    let count_keys_in_this_leaf = st.items.len();
    pb.put_varint(count_keys_in_this_leaf as u64);

    fn put_item(pb: &mut PageBuilder, prefix_len: usize, lp: &ItemForLeaf, list: &mut Vec<PageNum>, count_tombstones: &mut u64) {
        pb.put_varint(lp.key.val_with_overflow_flag());
        match lp.key.location {
            KeyLocationForLeaf::Inline => {
                pb.put_from_slice(&lp.key.key[prefix_len .. ]);
            },
            KeyLocationForLeaf::Overflow(page) => {
                list.push(page);
            },
        }
        match lp.value {
            ValueLocation::Tombstone => {
                *count_tombstones += 1;
                pb.put_u8(1);
            },
            ValueLocation::Buffer(ref vbuf) => {
                let val_with_flag = (vbuf.len() as u64) << 1;
                pb.put_varint(val_with_flag);
                pb.put_from_slice(&vbuf);
            },
            ValueLocation::Overflowed(page) => {
                let val_with_flag = ((page as u64) << 1) | 1;
                pb.put_varint(val_with_flag);
                // and add to overflows list.
                list.push(page);
            },
        }
    }

    let mut overflows = vec![];
    let mut count_tombstones = 0;

    // deal with all the keys except the last one
    for lp in st.items.drain(0 .. count_keys_in_this_leaf - 1) {
        put_item(pb, st.prefix_len, &lp, &mut overflows, &mut count_tombstones);
    }

    // now the last key
    assert!(st.items.len() == 1);
    let last_key = {
        let lp = st.items.remove(0); 
        assert!(st.items.is_empty());
        put_item(pb, st.prefix_len, &lp, &mut overflows, &mut count_tombstones);
        lp.key
    };
    BuildLeafReturnValue {
        last_key: last_key,
        overflows: overflows,
        len_page: pb.sofar(),
        count_pairs: count_keys_in_this_leaf,
        count_tombstones: count_tombstones,
    }
}

fn write_leaf(st: &mut LeafUnderConstruction, 
                pb: &mut PageBuilder, 
                pw: &mut PageWriter,
               ) -> Result<(usize, ItemForParent)> {
    let BuildLeafReturnValue {last_key, overflows, len_page, count_pairs, count_tombstones} = build_leaf(st, pb);
    // TODO we should do something with the overflows. it used to go into ChildInfo::Leaf
    let last_key = last_key.for_parent();
    //println!("leaf blocklist: {:?}", blocks);
    //println!("leaf blocklist, len: {}   encoded_len: {:?}", blocks.len(), blocks.encoded_len());
    assert!(st.items.is_empty());
    try!(pb.write_page(pw));
    // TODO ItemForParent::new
    let pg = ItemForParent {
        page: pb.last_page_written, 
        info: ChildInfo::Leaf{
            count_tombstones: count_tombstones,
        },
        last_key: last_key
    };
    st.sofar = 0;
    st.prefix_len = 0;
    Ok((len_page, pg))
}

fn process_pair_into_leaf(st: &mut LeafUnderConstruction, 
                pb: &mut PageBuilder, 
                pw: &mut PageWriter,
                mut pair: PairForStorage,
               ) -> Result<Option<ItemForParent>> {
    let pgsz = pw.page_size();
    let k = pair.key;

    if cfg!(expensive_check) 
    {
       // this code can be used to verify that we are being given keys in order
        match st.prev_key {
            None => {
            },
            Some(ref prev_key) => {
                let c = k.as_ref().cmp(&prev_key);
                if c != Ordering::Greater {
                    println!("prev_key: {:?}", prev_key);
                    println!("k: {:?}", k);
                    panic!("unsorted keys");
                }
            },
        }
        st.prev_key = {
            let mut a = Vec::with_capacity(k.as_ref().len());
            a.extend_from_slice(k.as_ref());
            Some(a.into_boxed_slice())
        };
    }

    let (k, kloc) =
        match k {
            KeyForStorage::Boxed(k) => {
                // the max limit of an inline key is when that key is the only
                // one in the leaf, and its value is overflowed.  well actually,
                // the reference to an overflowed value can take up a few dozen bytes 
                // in pathological cases, whereas a really short value could be smaller.
                // nevermind that.

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
                    - 1 // prefix_len of 0
                    - varint::space_needed_for((pgsz * 2) as u64) // approx worst case inline key len
                    - 1 // value flags
                    - 9 // worst case varint value len
                    - PESSIMISTIC_OVERFLOW_INFO_SIZE; // overflowed value page

                if k.len() <= maxKeyInline {
                    (k, KeyLocationForLeaf::Inline)
                } else {
                    let (len, blocks) = {
                        let mut r = misc::ByteSliceRead::new(&k.as_ref());
                        try!(write_overflow_known_len(&mut r, k.len() as u64, pw))
                    };
                    assert!((len as usize) == k.len());
                    (k, KeyLocationForLeaf::Overflow(blocks.first_page()))
                }
            },
            KeyForStorage::SameFileOverflow(k, page) => {
                (k, KeyLocationForLeaf::Overflow(page))
            },
        };

    // we have decided whether the key is going to be inlined or overflowed.  but
    // we have NOT yet decided which page the key is going on.  will it fit on the
    // current page or does it have to bump to the next one?  we don't know yet.

    let vloc = {
        let maxValueInline = {
            let fixed_costs_on_new_page = calc_leaf_page_len(0, 0, 1)
                + kloc.need(&k, 0)
                + varint::space_needed_for(ValueLocation::val_with_flag_for_len_inline(pgsz)) 
                ;
            assert!(fixed_costs_on_new_page < pgsz); // TODO lte?
            let available_for_inline_value_on_new_page = pgsz - fixed_costs_on_new_page;
            available_for_inline_value_on_new_page
        };

        // for the write_overflow calls below, we already know how much 
        // we spent on the key, so we know what our actual limit is for the encoded
        // block list for the value.  the hard limit, basically, is:  we cannot get
        // into a state where the key and value cannot fit on the same page.

        match pair.value {
            ValueForStorage::Tombstone => {
                ValueLocation::Tombstone
            },
            ValueForStorage::UnknownLen(ref mut strm) => {
                // TODO config constant?
                let mut vbuf = vec![0; 32768].into_boxed_slice();
                let vread = try!(misc::io::read_fully(&mut *strm, &mut vbuf));
                if vread < vbuf.len() {
                    // known len
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
                        let (len, blocks) = try!(write_overflow_known_len(&mut (vbuf.chain(strm)), vread as u64, pw));
                        ValueLocation::Overflowed(blocks.first_page())
                    }
                } else {
                    let (len, blocks) = try!(write_overflow_unknown_len(&mut (vbuf.chain(strm)), pw));
                    ValueLocation::Overflowed(blocks.first_page())
                }
            },
            ValueForStorage::Read(ref mut strm, len) => {
                // TODO should be <= ?
                if (len as usize) < maxValueInline {
                    let mut va = Vec::with_capacity(len as usize);
                    let vread = try!(misc::io::read_fully(&mut *strm, &mut va));
                    assert!(len as usize == vread);
                    ValueLocation::Buffer(va.into_boxed_slice())
                } else {
                    let (len, blocks) = try!(write_overflow_known_len(strm, len, pw));
                    ValueLocation::Overflowed(blocks.first_page())
                }
            },
            ValueForStorage::SameFileOverflow(page) => {
                ValueLocation::Overflowed(page)
            },
            ValueForStorage::Boxed(a) => {
                // TODO should be <= ?
                if a.len() < maxValueInline {
                    ValueLocation::Buffer(a)
                } else {
                    let mut r = misc::ByteSliceRead::new(&a);
                    let (len, blocks) = try!(write_overflow_known_len(&mut r, a.len() as u64, pw));
                    assert!(len as usize == a.len());
                    ValueLocation::Overflowed(blocks.first_page())
                }
            },
        }
    };

    // whether/not the key/value are to be overflowed is now already decided.
    // now all we have to do is decide if this key/value are going into this leaf
    // or not.  note that it is possible to overflow these and then have them not
    // fit into the current leaf and end up landing in the next leaf.

    fn calc_prefix_len(st: &LeafUnderConstruction, k: &[u8], kloc: &KeyLocationForLeaf) -> usize {
        if st.items.is_empty() {
            0
        } else {
            match kloc {
                &KeyLocationForLeaf::Inline => {
                    let max_prefix =
                        if st.prefix_len > 0 {
                            st.prefix_len
                        } else {
                            k.len()
                        };
                    let mut other = None;
                    for i in 0..st.items.len() {
                        if st.items[i].is_key_inline() {
                            other = Some(i);
                            break;
                        }
                    }
                    match other {
                        Some(i) => {
                            bcmp::PrefixMatch(&*st.items[i].key.key, &k, max_prefix)
                        },
                        None => {
                            // in a leaf, with only one inline item, the prefix_len is 0
                            0
                        },
                    }
                },
                &KeyLocationForLeaf::Overflow(_) => {
                    // an overflowed key does not change the prefix
                    st.prefix_len
                },
            }
        }
    }

    // note that the ItemForLeaf struct gets ownership of the key provided
    // from above.
    let kwloc = KeyWithLocationForLeaf {
        key: k,
        location: kloc,
    };
    let lp = ItemForLeaf {
                key: kwloc,
                value: vloc,
                };

    let would_be_prefix_len = calc_prefix_len(&st, &lp.key.key, &lp.key.location);
    assert!(would_be_prefix_len <= lp.key.key.len());
    let would_be_sofar_before_this_pair = 
        if would_be_prefix_len != st.prefix_len {
            assert!(st.prefix_len == 0 || would_be_prefix_len < st.prefix_len);
            // the prefix_len would change with the addition of this key,
            // so we need to recalc sofar
            let sum = st.items.iter().map(|lp| lp.need(would_be_prefix_len) ).sum();;
            sum
        } else {
            st.sofar
        };
    let fits = {
        let would_be_len_page_before_this_pair = calc_leaf_page_len(would_be_prefix_len, would_be_sofar_before_this_pair, st.items.len() + 1);
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
            assert!(st.items.len() > 0);
            let should_be = calc_leaf_page_len(st.prefix_len, st.sofar, st.items.len());
            let (len_page, pg) = try!(write_leaf(st, pb, pw));
            //println!("should_be = {}   len_page = {}", should_be, len_page);
            assert!(should_be == len_page);
            assert!(st.sofar == 0);
            assert!(st.prefix_len == 0);
            assert!(st.items.is_empty());
            st.sofar = lp.need(st.prefix_len);
            Some(pg)
        } else {
            st.prefix_len = would_be_prefix_len;
            st.sofar = would_be_sofar_before_this_pair + lp.need(st.prefix_len);
            None
        };

    st.items.push(lp);

    Ok(wrote)
}

fn flush_leaf(st: &mut LeafUnderConstruction, 
                pb: &mut PageBuilder, 
                pw: &mut PageWriter,
               ) -> Result<Option<ItemForParent>> {
    if !st.items.is_empty() {
        assert!(st.items.len() > 0);
        let should_be = calc_leaf_page_len(st.prefix_len, st.sofar, st.items.len());
        let (len_page, pg) = try!(write_leaf(st, pb, pw));
        //println!("should_be = {}   len_page = {}", should_be, len_page);
        assert!(should_be == len_page);
        Ok(Some(pg))
    } else {
        Ok(None)
    }
}

fn write_leaves<I: Iterator<Item=Result<PairForStorage>>, >(
                    pw: &mut PageWriter,
                    pairs: I,
                    f: std::sync::Arc<PageCache>,
                    ) -> Result<Option<SegmentHeaderInfo>> {

    let mut pb = PageBuilder::new(pw.page_size());

    let mut st = LeafUnderConstruction {
        sofar: 0,
        items: Vec::new(),
        prefix_len: 0,
        prev_key: None,
    };

    let mut chain = ParentNodeWriter::new(pw.page_size(), 1);

    for result_pair in pairs {
        let pair = try!(result_pair);
        if let Some(pg) = try!(process_pair_into_leaf(&mut st, &mut pb, pw, pair)) {
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
    overflows_freed: Vec<PageNum>, // TODO in rewritten leaves
    keys_promoted: usize,
    keys_rewritten: usize,
    keys_shadowed: usize,
    tombstones_removed: usize,
    elapsed_ms: i64,
}

struct WroteSurvivors {
    segment: Option<SegmentHeaderInfo>,
    nodes_rewritten: Box<[Vec<PageNum>]>, // TODO why is this in a box?
    nodes_recycled: Box<[usize]>,
    owned_overflows: Vec<PageNum>,
    elapsed_ms: i64,
}

fn merge_process_pair(
    pair: PairForStorage,
    st: &mut LeafUnderConstruction,
    pb: &mut PageBuilder,
    pw: &mut PageWriter,
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

        // TODO would it be faster to just keep behind moving next() along with chain?
        // then we could optimize cases where we already know that the key is not present
        // in behind because, for example, we hit the max key in behind already.

        let k = KeyRef::Slice(k);

        for mut cursor in behind.iter_mut() {
            if SeekResult::Equal == try!(cursor.seek(&k, SeekOp::SEEK_EQ)) {
                // TODO if the value was found but it is another tombstone...
                return Ok(true);
            }
        }
        Ok(false)
    }

    let keep =
        match behind {
            &mut Some(ref mut behind) => {
                if pair.value.is_tombstone() {
                    if try!(necessary_tombstone(&pair.key.as_ref(), behind)) {
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
        if let Some(pg) = try!(process_pair_into_leaf(st, pb, pw, pair)) {
            try!(chain.add_child(pw, pg, 0));
        }
    }

    Ok(keep)
}

struct MergeRewriteReturnValue {
    keys_promoted: usize,
    keys_rewritten: usize,
    keys_shadowed: usize,
    tombstones_removed: usize,
}

fn merge_rewrite_leaf(
                    st: &mut LeafUnderConstruction,
                    pb: &mut PageBuilder,
                    pw: &mut PageWriter,
                    pairs: &mut CursorIterator,
                    leafreader: &LeafPage,
                    behind: &mut Option<Vec<PageCursor>>,
                    chain: &mut ParentNodeWriter,
                    overflows_freed: &mut Vec<PageNum>,
                    dest_level: DestLevel,
                    ) -> Result<MergeRewriteReturnValue> {

    #[derive(Debug)]
    enum Action {
        Pairs,
        ItemForLeaf,
    }

    let mut i = 0;
    let mut ret =
        MergeRewriteReturnValue {
            keys_promoted: 0,
            keys_rewritten: 0,
            keys_shadowed: 0,
            tombstones_removed: 0,
        };

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
                    // is greater than pair or PairForStorage/i.  assert that.
                    let c = {
                        let k = try!(leafreader.key(i));
                        k.compare_with(&peek_pair.key.as_ref())
                    };
                    match c {
                        Ordering::Greater => {
                            Action::Pairs
                        },
                        Ordering::Equal => {
                            // whatever value is coming from the rewritten leaf, it is shadowed
// TODO explain how we know that this overflow is not
// borrowed by a parent.
                            let pair = try!(leafreader.pair_for_merge(i));
                            match &pair.key {
                                &KeyForStorage::SameFileOverflow(_, page) => {
                                    overflows_freed.push(page);
                                },
                                _ => {
                                },
                            }
                            match &pair.value {
                                &ValueForStorage::SameFileOverflow(page) => {
                                    overflows_freed.push(page);
                                },
                                _ => {
                                },
                            }
                            ret.keys_shadowed += 1;
                            i += 1;
                            Action::Pairs
                        },
                        Ordering::Less => {
                            Action::ItemForLeaf
                        },
                    }
                },
                None => {
                    Action::ItemForLeaf
                },
            };
        //println!("dest,{:?},action,{:?}", dest_level, action);
        match action {
            Action::Pairs => {
                let pair = try!(misc::inside_out(pairs.next())).unwrap();
                if try!(merge_process_pair(pair, st, pb, pw, behind, chain, dest_level)) {
                    ret.keys_promoted += 1;
                } else {
                    ret.tombstones_removed += 1;
                }
            },
            Action::ItemForLeaf => {
                let pair = try!(leafreader.pair_for_merge(i));
                // TODO it is interesting to note that (in not-very-thorough testing), if we
                // put a tombstone check here, it never skips a tombstone.
                if let Some(pg) = try!(process_pair_into_leaf(st, pb, pw, pair)) {
                    try!(chain.add_child(pw, pg, 0));
                }
                ret.keys_rewritten += 1;
                i += 1;
            },
        }
    }

    Ok(ret)
}

fn merge_rewrite_parent(
                    st: &mut LeafUnderConstruction,
                    pb: &mut PageBuilder,
                    pw: &mut PageWriter,
                    pairs: &mut CursorIterator,
                    leaf: &mut LeafPage,
                    parent: &ParentPage,
                    behind: &mut Option<Vec<PageCursor>>,
                    chain: &mut ParentNodeWriter,
                    overflows_freed: &mut Vec<PageNum>,
                    nodes_rewritten: &mut Box<[Vec<PageNum>]>,
                    nodes_recycled: &mut Box<[usize]>,
                    dest_level: DestLevel,
                    ) -> Result<MergeRewriteReturnValue> {

    #[derive(Debug)]
    enum Action {
        RewriteNode,
        RecycleNodes(usize),
    }

    let mut ret =
        MergeRewriteReturnValue {
            keys_promoted: 0,
            keys_rewritten: 0,
            keys_shadowed: 0,
            tombstones_removed: 0,
        };

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
                    let k = &KeyRef::Slice(&peek_pair.key.as_ref());
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
                    let pg = try!(parent.child_as_item_for_parent(i));
                    try!(chain.add_child(pw, pg, parent.depth() - 1));
                    nodes_recycled[parent.depth() as usize - 1] += 1;
                    i += 1;
                }
            },
            Action::RewriteNode => {
                //println!("rewriting node of depth {}", parent.depth() - 1);
                nodes_rewritten[parent.depth() as usize - 1].push(parent.child_pagenum(i));
                if parent.depth() == 1 {
                    let pg = try!(parent.child_as_item_for_parent(i));
                    try!(leaf.move_to_page(pg.page));
                    let sub = try!(merge_rewrite_leaf(st, pb, pw, pairs, leaf, behind, chain, overflows_freed, dest_level));

                    // in the case where we rewrote a page that didn't really NEED to be,
                    // the following assert is not true
                    //assert!(sub_keys_promoted > 0 || sub_tombstones_removed > 0);

                    assert!(sub.keys_rewritten > 0 || sub.keys_shadowed > 0);

                    ret.keys_promoted += sub.keys_promoted;
                    ret.keys_rewritten += sub.keys_rewritten;
                    ret.keys_shadowed += sub.keys_shadowed;
                    ret.tombstones_removed += sub.tombstones_removed;
                } else {
                    let sub = try!(parent.fetch_item_parent(i));
                    let sub = try!(merge_rewrite_parent(st, pb, pw, pairs, leaf, &sub, behind, chain, overflows_freed, nodes_rewritten, nodes_recycled, dest_level));
                    ret.keys_promoted += sub.keys_promoted;
                    ret.keys_rewritten += sub.keys_rewritten;
                    ret.keys_shadowed += sub.keys_shadowed;
                    ret.tombstones_removed += sub.tombstones_removed;
                }
                i += 1;
            },
        }
    }

    parent.get_owned_overflows(overflows_freed);

    Ok(ret)
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

    // TODO could/should pb move into LeafUnderConstruction?

    let mut pb = PageBuilder::new(pw.page_size());
    let mut st = LeafUnderConstruction {
        sofar: 0,
        items: Vec::new(),
        prefix_len: 0,
        prev_key: None,
    };
    let mut chain = ParentNodeWriter::new(pw.page_size(), 1);
    let depths = 
        match *into {
            MergingInto::None => {
                0
            },
            MergingInto::Leaf(_) => {
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
            let sub = try!(merge_rewrite_leaf(&mut st, &mut pb, pw, pairs, leaf, &mut behind, &mut chain, &mut overflows_freed, dest_level));
            keys_promoted = sub.keys_promoted;
            keys_rewritten = sub.keys_rewritten;
            keys_shadowed = sub.keys_shadowed;
            tombstones_removed = sub.tombstones_removed;
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
                try!(sub.move_to_page(nd.page));
                if nd.depth == rewrite_level {
                    let res = try!(merge_rewrite_parent(&mut st, &mut pb, pw, pairs, &mut leaf, &sub, &mut behind, &mut chain, &mut overflows_freed, &mut nodes_rewritten, &mut nodes_recycled, dest_level));
                    keys_promoted += res.keys_promoted;
                    keys_rewritten += res.keys_rewritten;
                    keys_shadowed += res.keys_shadowed;
                    tombstones_removed += res.tombstones_removed;
                } else {
                    sub.get_owned_overflows(&mut overflows_freed);
                }
                nodes_rewritten[nd.depth as usize].push(nd.page);
            }
        },
    }

    // any pairs left need to get processed
    for pair in pairs {
        let pair = try!(pair);
        if try!(merge_process_pair(pair, &mut st, &mut pb, pw, &mut behind, &mut chain, dest_level)) {
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
            let pg = try!(parent.child_as_item_for_parent(i));
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
                    owned_overflows: &mut Vec<PageNum>,
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
            try!(survivors_rewrite_node(pw, skip_pages, skip_depth, skip_lineage, &sub, chain, nodes_rewritten, nodes_recycled, owned_overflows, ));
        } else {
            let pg = try!(parent.child_as_item_for_parent(i));
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
                    nodes_rewritten: &mut Box<[Vec<PageNum>]>, // TODO why is this in a box?
                    nodes_recycled: &mut Box<[usize]>,
                    owned_overflows: &mut Vec<PageNum>,
                    ) -> Result<()> {
    if parent.depth() - 1 == skip_depth {
        let num_recycled = try!(survivors_rewrite_immediate_parent_of_skip(pw, skip_pages, skip_depth, parent, chain));
        nodes_recycled[skip_depth as usize] += num_recycled;
    } else if parent.depth() - 1 > skip_depth {
        try!(survivors_rewrite_ancestor(pw, skip_pages, skip_depth, skip_lineage, parent, chain, nodes_rewritten, nodes_recycled, owned_overflows, ));
    } else {
        panic!();
    }
    let len = parent.count_items();
    for i in 0 .. len {
        match &parent.children[i].last_key {
            &KeyInParentPage::Inline{..} => {
            },
            &KeyInParentPage::BorrowedOverflow{..} => {
            },
            &KeyInParentPage::OwnedOverflow{page, ..} => {
                owned_overflows.push(page);
            },
        }
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
    let mut owned_overflows = vec![];

    try!(survivors_rewrite_node(pw, skip_pages, skip_depth, skip_lineage, parent, &mut chain, &mut nodes_rewritten, &mut nodes_recycled, &mut owned_overflows));
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
        owned_overflows: owned_overflows,
        elapsed_ms: elapsed.num_milliseconds(),
    };
    Ok(wrote)
}

struct ParentNodeWriter {
    pb: PageBuilder,
    st: ParentUnderConstruction,
    prev_child: Option<ItemForParent>,
    my_depth: u8,

    result_one: Option<ItemForParent>,
    results_chain: Option<Box<ParentNodeWriter>>,

    count_emit: usize,

    // TODO need a way to keep track of newly-created overflows
    // and new overflow references
}

impl ParentNodeWriter {
    fn new(
        pgsz: usize, 
        my_depth: u8,
        ) -> Self {
        let st = ParentUnderConstruction {
            prefix_len: 0,
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

    fn calc_page_len(prefix_len: usize, sofar: usize, count_items: usize) -> usize {
        2 // page type and flags
        + 1 // stored depth
        + varint::space_needed_for(prefix_len as u64) 
        + prefix_len 
        + varint::space_needed_for(count_items as u64)
        + sofar // sum of size of all the actual items
    }

    fn put_key(&mut self, k: &KeyWithLocationForParent, prefix_len: usize) {
        self.pb.put_varint(k.val_with_overflow_flag());
        match k.location {
            KeyLocationForParent::Inline => {
                self.pb.put_from_slice(&k.key[prefix_len .. ]);
            },
            KeyLocationForParent::BorrowedOverflow(page)
            | KeyLocationForParent::OwnedOverflow(page) => 
            {
            },
        }
    }

    fn put_item(&mut self, total_count_leaves: &mut PageCount, total_count_tombstones: &mut u64, item: &ItemForParent, prefix_len: usize) {
        self.pb.put_varint(item.page as u64);
        match &item.info {
            &ChildInfo::Leaf{
                count_tombstones,
            } => {
                assert!(self.my_depth == 1);
                self.pb.put_varint(count_tombstones as u64);
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
                self.pb.put_varint(count_leaves as u64);
                self.pb.put_varint(count_tombstones as u64);
                //self.pb.put_varint(count_items as u64);
                //self.pb.put_varint(count_bytes as u64);
                *total_count_leaves += count_leaves;
                *total_count_tombstones += count_tombstones;
            },
        }

        self.put_key(&item.last_key, prefix_len);
    }

    // TODO return tuple is too large
    fn build_parent_page(&mut self,
                      ) -> (KeyWithLocationForParent, PageCount, u64, usize, usize) {
        // TODO? assert!(st.items.len() > 1);
        //println!("build_parent_page, prefix_len: {:?}", st.prefix_len);
        //println!("build_parent_page, items: {:?}", st.items);
        self.pb.reset();
        self.pb.put_u8(PageType::PARENT_NODE.to_u8());
        self.pb.put_u8(0u8);
        self.pb.put_u8(self.my_depth);
        self.pb.put_varint(self.st.prefix_len as u64);
        if self.st.prefix_len > 0 {
            let mut inlined = None;
            for i in 0..self.st.items.len() {
                if self.st.items[i].is_inline() {
                    inlined = Some(i);
                    break;
                }
            }
            match inlined {
                Some(i) => {
                    self.pb.put_from_slice(&self.st.items[i].last_key.key[0 .. self.st.prefix_len]);
                },
                None => {
                    unreachable!();
                },
            }
        }
        let count_items = self.st.items.len();
        self.pb.put_varint(count_items as u64);
        //println!("self.st.items.len(): {}", self.st.items.len());

        let mut count_leaves = 0;
        let mut count_tombstones = 0;

        // deal with all the items except the last one
        let tmp_count = self.st.items.len() - 1;
        let tmp_vec = self.st.items.drain(0 .. tmp_count).collect::<Vec<_>>();
        let prefix_len = self.st.prefix_len;
        for item in tmp_vec {
            self.put_item(&mut count_leaves, &mut count_tombstones, &item, prefix_len);
        }

        assert!(self.st.items.len() == 1);

        // now the last item
        let last_key = {
            let item = self.st.items.remove(0); 
            let prefix_len = self.st.prefix_len;
            self.put_item(&mut count_leaves, &mut count_tombstones, &item, prefix_len);
            item.last_key
        };
        assert!(self.st.items.is_empty());

        // TODO need to return list of overflows referenced
        (last_key, count_leaves, count_tombstones, count_items, self.pb.sofar())
    }

    fn write_parent_page(&mut self,
                          pw: &mut PageWriter,
                         ) -> Result<(usize, ItemForParent)> {
        // assert st.sofar > 0
        let (mut last_key, count_leaves, count_tombstones, count_items, count_bytes) = self.build_parent_page();
        assert!(self.st.items.is_empty());
        //println!("parent blocklist: {:?}", blocks);
        //println!("parent blocklist, len: {}   encoded_len: {:?}", blocks.len(), blocks.encoded_len());
        try!(self.pb.write_page(pw));
        //println!("wrote parent page: {}", self.pb.last_page_written);
        last_key.fix_owned_overflow();
        // TODO ItemForParent::new
        let pg = ItemForParent {
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
        self.st.prefix_len = 0;
        Ok((count_bytes, pg))
    }

    fn calc_prefix_len(&self, item: &ItemForParent) -> usize {
        match &item.last_key.location {
            &KeyLocationForParent::Inline => {
                let mut other = None;
                for i in 0..self.st.items.len() {
                    if self.st.items[i].is_inline() {
                        other = Some(i);
                        break;
                    }
                }
                match other {
                    Some(i) => {
                        bcmp::PrefixMatch(&*self.st.items[i].last_key.key, &item.last_key.key, self.st.prefix_len)
                    },
                    None => {
                        item.last_key.key.len()
                    },
                }
            },
            &KeyLocationForParent::BorrowedOverflow(_)
            | &KeyLocationForParent::OwnedOverflow(_) => 
            {
                // an overflowed key does not change the prefix
                self.st.prefix_len
            },
        }
    }

    fn add_child_to_current(&mut self, pw: &mut PageWriter, child: ItemForParent) -> Result<()> {
        let pgsz = pw.page_size();

        if cfg!(expensive_check) 
        {
            // TODO FYI this code is the only reason we need to derive Clone on
            // ItemForParent and its parts
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
        assert!(would_be_prefix_len < pgsz);
        let would_be_sofar_before_this_key = 
            if would_be_prefix_len != self.st.prefix_len {
                assert!(self.st.prefix_len == 0 || would_be_prefix_len < self.st.prefix_len);
                // the prefix_len would change with the addition of this key,
                // so we need to recalc sofar
                let sum = self.st.items.iter().map(|lp| lp.need(would_be_prefix_len) ).sum();;
                sum
            } else {
                self.st.sofar
            };
        let fits = if self.st.items.len() < 2 {
            // a parent page is required to accept at least 2 items
            true
        } else {
            let would_be_len_page_before_this_key = Self::calc_page_len(would_be_prefix_len, would_be_sofar_before_this_key, self.st.items.len() + 1);
            if pgsz > would_be_len_page_before_this_key {
                let avalable_for_this_key = pgsz - would_be_len_page_before_this_key;
                let fits = avalable_for_this_key >= child.need(would_be_prefix_len);
                fits
            } else {
                false
            }
        };

        if !fits {
            // if it was not possible to put a second item into this page,
            // then one of them should have been overflowed.
            assert!(self.st.items.len() > 1);
            
            let should_be = Self::calc_page_len(self.st.prefix_len, self.st.sofar, self.st.items.len());
            let (count_bytes, pg) = try!(self.write_parent_page(pw));
            self.count_emit += 1;
            assert!(should_be == count_bytes);
            try!(self.emit(pw, pg));
            assert!(self.st.sofar == 0);
            assert!(self.st.prefix_len == 0);
            assert!(self.st.items.is_empty());
            self.st.prefix_len = 
                if child.is_inline() {
                    // in a parent page, with only one inline item, prefix_len is that item's len
                    child.last_key.key.len()
                } else {
                    0
                };
            self.st.sofar = child.need(self.st.prefix_len);
        } else {
            self.st.prefix_len = would_be_prefix_len;
            self.st.sofar = would_be_sofar_before_this_key + child.need(self.st.prefix_len);
        }

        self.st.items.push(child);

        if self.st.items.len() == 2 && Self::calc_page_len(self.st.prefix_len, self.st.sofar, self.st.items.len()) > pgsz {
            if self.st.items[0].is_inline() {
                if self.st.items[1].is_inline() {
                    let remaining_inline =
                        if self.st.items[0].last_key.key.len() > self.st.items[1].last_key.key.len() {
                            try!(self.st.items[0].to_owned_overflow(pw));
                            1
                        } else {
                            try!(self.st.items[1].to_owned_overflow(pw));
                            0
                        };
                    self.st.prefix_len = self.st.items[remaining_inline].last_key.key.len();
                    let sofar = self.st.items[0].need(self.st.prefix_len) + self.st.items[1].need(self.st.prefix_len);
                    if Self::calc_page_len(self.st.prefix_len, sofar, self.st.items.len()) > pgsz {
                        //println!("TWOFER");
                        try!(self.st.items[remaining_inline].to_owned_overflow(pw));
                        self.st.prefix_len = 0;
                    }
                } else {
                    try!(self.st.items[0].to_owned_overflow(pw));
                    self.st.prefix_len = 0;
                }
            } else {
                if self.st.items[1].is_inline() {
                    try!(self.st.items[1].to_owned_overflow(pw));
                    self.st.prefix_len = 0;
                } else {
                    unreachable!();
                }
            }
            //println!("sofar before: {}", self.st.sofar);
            self.st.sofar = self.st.items[0].need(self.st.prefix_len) + self.st.items[1].need(self.st.prefix_len);
            //println!("sofar after: {}", self.st.sofar);
        }
        //println!("items: {}", self.st.items.len());
        //println!("prefix_len: {}", self.st.prefix_len);
        //println!("sofar: {}", self.st.sofar);
        assert!(Self::calc_page_len(self.st.prefix_len, self.st.sofar, self.st.items.len()) <= pgsz);

        Ok(())
    }

    fn add_child(&mut self, pw: &mut PageWriter, child: ItemForParent, depth: u8) -> Result<()> {
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
            let chain = ParentNodeWriter::new(self.pb.buf.len(), self.my_depth + 1);
            self.results_chain = Some(box chain);
        }
        Ok(())
    }

    fn emit(&mut self, pw: &mut PageWriter, pg: ItemForParent) -> Result<()> {
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
            let should_be = Self::calc_page_len(self.st.prefix_len, self.st.sofar, self.st.items.len());
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
                       ) -> Result<Option<SegmentHeaderInfo>> where I: Iterator<Item=Result<PairForStorage>> {

    let seg = try!(write_leaves(&mut pw, source, f));

    try!(pw.end());

    Ok(seg)
}

pub struct OverflowReader {
    fs: std::sync::Arc<PageCache>,
    len: u64,
    header_len: usize,
    blocks: BlockList,
    current_block: usize,
    sofar_overall: u64,
    sofar_this_block: u64,
    bytes_in_this_block: u64,
}
    
impl OverflowReader {
    pub fn get_len_and_blocklist(fs: std::sync::Arc<PageCache>, first_page: PageNum) -> Result<(u64, BlockList)> {
        let rdr = try!(Self::new(fs, first_page));
        Ok((rdr.len, rdr.blocks))
    }

    pub fn new(fs: std::sync::Arc<PageCache>, first_page: PageNum) -> Result<OverflowReader> {
        //println!("reading overflow: {}", first_page);
        let mut hdr = [0; MIN_OVERFLOW_HEADER_LEN];
        let pos = try!(utils::page_offset(fs.page_size(), first_page));
        let got = try!(fs.seek_and_read_fully(&mut hdr, pos));
        assert!(got == MIN_OVERFLOW_HEADER_LEN);
        let (len, blocks, actual_header_len) =
            match hdr[0] {
                1 => {
                    let actual_header_len = MIN_OVERFLOW_HEADER_LEN;
                    let mut cur = 1;
                    let len = varint::read(&hdr, &mut cur);
                    let pages = calc_overflow_pages(len, actual_header_len as u64, fs.page_size() as u64);
                    let blk = PageBlock::new(first_page, first_page + pages - 1);
                    let mut blocks = BlockList::new();
                    blocks.add_block_no_reorder(blk);
                    (len, blocks, actual_header_len)
                },
                2 => {
                    let actual_header_len = MIN_OVERFLOW_HEADER_LEN;
                    let mut cur = 1;
                    let len = varint::read(&hdr, &mut cur);
                    let pages = calc_overflow_pages(len, actual_header_len as u64, fs.page_size() as u64);
                    let blocks = BlockList::read(&hdr, &mut cur);
                    assert!(blocks.first_page() == first_page);
                    (len, blocks, actual_header_len)
                },
                _ => {
                    panic!(); // TODO
                },
            };
        let bytes_in_this_block = (blocks.blocks[0].count_pages() as u64) * (fs.page_size() as u64) - (actual_header_len as u64);
        let mut res = 
            OverflowReader {
                fs: fs,
                len: len,
                header_len: actual_header_len,
                blocks: blocks,
                current_block: 0,
                sofar_overall: 0,
                sofar_this_block: 0,
                bytes_in_this_block: bytes_in_this_block,
            };
        Ok(res)
    }

    // TODO consider supporting Seek trait

    fn set_block(&mut self, i: usize) -> Result<()> {
        // TODO for seek, we would need to support set_block(0)
        assert!(i != 0);

        self.current_block = i;
        self.sofar_this_block = 0;
        // TODO adjust for sofar_overfall on the last block?
        self.bytes_in_this_block = (self.blocks.blocks[i].count_pages() as u64) * (self.fs.page_size() as u64);
        Ok(())
    }

    fn Read(&mut self, ba: &mut [u8], offset: usize, wanted: usize) -> Result<usize> {
        if self.sofar_overall >= self.len {
            Ok(0)
        } else {
            if self.sofar_this_block >= self.bytes_in_this_block {
                // TODO what if there are no more blocks?
                let next_block = self.current_block + 1;
                try!(self.set_block(next_block));
            }

            let available = std::cmp::min(self.bytes_in_this_block - self.sofar_this_block, self.len - self.sofar_overall);
            let num = std::cmp::min(available, wanted as u64) as usize;
            let first_page = self.blocks.blocks[self.current_block].firstPage;
            let offset_this_block = if self.current_block == 0 {
                self.header_len as u64
            } else {
                0
            };
            let pos = try!(utils::page_offset(self.fs.page_size(), first_page)) + self.sofar_this_block + offset_this_block;
            let got = try!(self.fs.seek_and_read_fully(&mut ba[offset .. offset + num], pos));
            self.sofar_overall += got as u64;
            self.sofar_this_block += got as u64;
            Ok(got)
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

    pairs: Vec<ItemInLeafPage>,
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

        let res = LeafPage {
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

    pub fn overflows(&self) -> Vec<PageNum> {
        let mut list = vec![];
        for i in 0 .. self.pairs.len() {
            match &self.pairs[i].key {
                &KeyInLeafPage::Inline{..} => {
                },
                &KeyInLeafPage::Overflow{page, ..} => {
                    list.push(page);
                },
            }
            match &self.pairs[i].value {
                &ValueInLeaf::Tombstone => {
                },
                &ValueInLeaf::Inline(_,_) => {
                },
                &ValueInLeaf::Overflowed(page) => {
                    list.push(page);
                },
            }
        }
        list
    }

    pub fn blocklist_unsorted(&self) -> Result<BlockList> {
        let mut list = BlockList::new();
        for page in self.overflows() {
            let (_, blist) = try!(OverflowReader::get_len_and_blocklist(self.f.clone(), page));
            list.add_blocklist_no_reorder(&blist);
        }
        Ok(list)
    }

    fn parse_page(pgnum: PageNum, pr: &[u8], pairs: &mut Vec<ItemInLeafPage>) -> Result<(Option<Box<[u8]>>, usize)> {
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
        let count_keys = varint::read(pr, &mut cur) as usize;
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
            let k = try!(KeyInLeafPage::read(pr, &mut cur, prefix_len));
            let v = try!(ValueInLeaf::read(pr, &mut cur));
            let pair = ItemInLeafPage {
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

    fn pair_for_merge(&self, n: usize) -> Result<PairForStorage> {
        let k = try!(self.key(n)).into_key_for_merge();
        let v = try!(self.value(n)).into_value_for_merge();
        let p = PairForStorage {
            key: k,
            value: v,
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
            &ValueInLeaf::Overflowed(page) => {
                Ok(ValueRef::Overflowed(self.f.clone(), page))
            },
        }
    }

    fn value_is_tombstone(&self, n: usize) -> Result<bool> {
        match &self.pairs[n].value {
            &ValueInLeaf::Tombstone => {
                Ok(true)
            },
            &ValueInLeaf::Inline(vlen, _) => {
                Ok(false)
            },
            &ValueInLeaf::Overflowed(_) => {
                Ok(false)
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

}

impl IValue for LeafCursor {
    fn value<'a>(&'a self) -> Result<ValueRef<'a>> {
        match self.cur {
            None => {
                Err(Error::CursorNotValid)
            },
            Some(cur) => {
                self.page.value(cur)
            }
        }
    }

    fn value_is_tombstone(&self) -> Result<bool> {
        match self.cur {
            None => {
                Err(Error::CursorNotValid)
            },
            Some(cur) => {
                self.page.value_is_tombstone(cur)
            }
        }
    }

}

impl IForwardCursor for LeafCursor {
    fn is_valid(&self) -> bool {
        if let Some(i) = self.cur {
            assert!(i < self.page.count_keys());
            true
        } else {
            false
        }
    }

    fn key<'a>(&'a self) -> Result<KeyRef<'a>> {
        match self.cur {
            None => {
                Err(Error::CursorNotValid)
            },
            Some(cur) => {
                self.page.key(cur)
            },
        }
    }

    fn first(&mut self) -> Result<()> {
        self.cur = Some(0);
        Ok(())
    }

    fn next(&mut self) -> Result<()> {
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

impl ISeekableCursor for LeafCursor {
    fn last(&mut self) -> Result<()> {
        self.cur = Some(self.page.count_keys() - 1);
        Ok(())
    }

    fn prev(&mut self) -> Result<()> {
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

    fn seek(&mut self, k: &KeyRef, sop: SeekOp) -> Result<SeekResult> {
        //println!("Leaf seek {}  k={:?}  sop={:?}", self.pagenum, k, sop);
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

impl IValue for PageCursor {
    fn value<'a>(&'a self) -> Result<ValueRef<'a>> {
        match self {
            &PageCursor::Leaf(ref c) => c.value(),
            &PageCursor::Parent(ref c) => c.value(),
        }
    }

    fn value_is_tombstone(&self) -> Result<bool> {
        match self {
            &PageCursor::Leaf(ref c) => c.value_is_tombstone(),
            &PageCursor::Parent(ref c) => c.value_is_tombstone(),
        }
    }

}

impl IForwardCursor for PageCursor {
    fn is_valid(&self) -> bool {
        match self {
            &PageCursor::Leaf(ref c) => c.is_valid(),
            &PageCursor::Parent(ref c) => c.is_valid(),
        }
    }

    fn key<'a>(&'a self) -> Result<KeyRef<'a>> {
        match self {
            &PageCursor::Leaf(ref c) => c.key(),
            &PageCursor::Parent(ref c) => c.key(),
        }
    }

    fn first(&mut self) -> Result<()> {
        match self {
            &mut PageCursor::Leaf(ref mut c) => c.first(),
            &mut PageCursor::Parent(ref mut c) => c.first(),
        }
    }

    fn next(&mut self) -> Result<()> {
        match self {
            &mut PageCursor::Leaf(ref mut c) => c.next(),
            &mut PageCursor::Parent(ref mut c) => c.next(),
        }
    }

}

impl ISeekableCursor for PageCursor {
    fn last(&mut self) -> Result<()> {
        match self {
            &mut PageCursor::Leaf(ref mut c) => c.last(),
            &mut PageCursor::Parent(ref mut c) => c.last(),
        }
    }

    fn prev(&mut self) -> Result<()> {
        match self {
            &mut PageCursor::Leaf(ref mut c) => c.prev(),
            &mut PageCursor::Parent(ref mut c) => c.prev(),
        }
    }

    fn seek(&mut self, k: &KeyRef, sop: SeekOp) -> Result<SeekResult> {
        //println!("PageCursor seek  k={:?}  sop={:?}", k, sop);
        let sr = 
            match self {
                &mut PageCursor::Leaf(ref mut c) => c.seek(k, sop),
                &mut PageCursor::Parent(ref mut c) => c.seek(k, sop),
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
pub enum KeyInLeafPage {
    Inline{len: usize, offset: usize},
    Overflow{page: PageNum},
}

#[derive(Debug)]
pub enum KeyInParentPage {
    Inline{len: usize, offset: usize},
    BorrowedOverflow{page: PageNum},
    OwnedOverflow{page: PageNum},
}

impl KeyInLeafPage {
    #[inline]
    fn read(pr: &[u8], cur: &mut usize, prefix_len: usize) -> Result<Self> {
        let val_with_flag = varint::read(pr, cur) as usize;
        let overflow = 0 != (val_with_flag & 1);
        let val = val_with_flag >> 1;
        let k = 
            if !overflow {
                let klen = val;
                if klen == 0 {
                    return Err(Error::CorruptFile("leaf: key cannot be zero length"));
                }
                let k = KeyInLeafPage::Inline{len: klen, offset: *cur};
                *cur += klen - prefix_len;
                k
            } else {
                let page = val as PageNum;
                let k = KeyInLeafPage::Overflow{page: page};
                k
            };
        Ok(k)
    }

    #[inline]
    fn keyref<'a>(&self, pr: &'a [u8], prefix: Option<&'a [u8]>, f: &std::sync::Arc<PageCache>) -> Result<KeyRef<'a>> { 
        match self {
            &KeyInLeafPage::Inline{len: klen, offset} => {
                match prefix {
                    Some(a) => {
                        Ok(KeyRef::Prefixed(&a, &pr[offset .. offset + klen - a.len()]))
                    },
                    None => {
                        Ok(KeyRef::Slice(&pr[offset .. offset + klen]))
                    },
                }
            },
            &KeyInLeafPage::Overflow{page} => {
                let mut ostrm = try!(OverflowReader::new(f.clone(), page));
                let mut x_k = vec![];;
                try!(ostrm.read_to_end(&mut x_k));
                let x_k = x_k.into_boxed_slice();
                Ok(KeyRef::Overflowed(x_k, f.clone(), page))
            },
        }
    }

}

impl KeyInParentPage {
    #[inline]
    fn read(pr: &[u8], cur: &mut usize, prefix_len: usize) -> Result<Self> {
        let val_with_flags = varint::read(pr, cur) as usize;
        let overflow = 0 != (val_with_flags & 1);
        let owned = 0 != (val_with_flags & 2);
        let val = val_with_flags >> 2;
        let k = 
            if !overflow {
                let klen = val as usize;
                if klen == 0 {
                    return Err(Error::CorruptFile("parent: key cannot be zero length"));
                }
                let k = KeyInParentPage::Inline{len: klen, offset: *cur};
                *cur += klen - prefix_len;
                k
            } else {
                let page = val as PageNum;
                if !owned {
                    let k = KeyInParentPage::BorrowedOverflow{page: page};
                    k
                } else {
                    let k = KeyInParentPage::OwnedOverflow{page: page};
                    k
                }
            };
        Ok(k)
    }

    #[inline]
    fn keyref<'a>(&self, pr: &'a [u8], prefix: Option<&'a [u8]>, f: &std::sync::Arc<PageCache>) -> Result<KeyRef<'a>> { 
        match self {
            &KeyInParentPage::Inline{len: klen, offset} => {
                match prefix {
                    Some(a) => {
                        Ok(KeyRef::Prefixed(&a, &pr[offset .. offset + klen - a.len()]))
                    },
                    None => {
                        Ok(KeyRef::Slice(&pr[offset .. offset + klen]))
                    },
                }
            },
            &KeyInParentPage::BorrowedOverflow{page}
            | &KeyInParentPage::OwnedOverflow{page} => 
            {
                let mut ostrm = try!(OverflowReader::new(f.clone(), page));
                let mut x_k = vec![];
                try!(ostrm.read_to_end(&mut x_k));
                let x_k = x_k.into_boxed_slice();
                Ok(KeyRef::Overflowed(x_k, f.clone(), page))
            },
        }
    }

    #[inline]
    fn to_boxed_slice(&self, pr: &[u8], prefix: Option<&[u8]>, f: &std::sync::Arc<PageCache>) -> Result<Box<[u8]>> { 
        match self {
            &KeyInParentPage::Inline{len: klen, offset} => {
                let k = 
                    match prefix {
                        Some(a) => {
                            let k = {
                                let mut k = Vec::with_capacity(klen);
                                k.extend_from_slice(a);
                                k.extend_from_slice(&pr[offset .. offset + klen - a.len()]);
                                k.into_boxed_slice()
                            };
                            k
                        },
                        None => {
                            let k = {
                                let mut k = Vec::with_capacity(klen);
                                k.extend_from_slice(&pr[offset .. offset + klen]);
                                k.into_boxed_slice()
                            };
                            k
                        },
                    };
                Ok(k)
            },
            &KeyInParentPage::BorrowedOverflow{page} |
            &KeyInParentPage::OwnedOverflow{page} => {
                let k = {
                    let mut ostrm = try!(OverflowReader::new(f.clone(), page));
                    let mut x_k = vec![];
                    try!(ostrm.read_to_end(&mut x_k));
                    let x_k = x_k.into_boxed_slice();
                    x_k
                };
                Ok(k)
            },
        }
    }

    #[inline]
    fn key_with_location_for_parent(&self, pr: &[u8], prefix: Option<&[u8]>, f: &std::sync::Arc<PageCache>) -> Result<KeyWithLocationForParent> { 
        let k = try!(self.to_boxed_slice(pr, prefix, f));
        match self {
            &KeyInParentPage::Inline{len: klen, offset} => {
                let kw = KeyWithLocationForParent {
                    key: k,
                    location: KeyLocationForParent::Inline,
                };
                Ok(kw)
            },
            &KeyInParentPage::BorrowedOverflow{page} => {
                let kw = KeyWithLocationForParent {
                    key: k,
                    location: KeyLocationForParent::BorrowedOverflow(page),
                };
                Ok(kw)
            },
            &KeyInParentPage::OwnedOverflow{page} => {
                let kw = KeyWithLocationForParent {
                    key: k,
                    location: KeyLocationForParent::Inline,
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
    Overflowed(PageNum),
}

impl ValueInLeaf {
    fn read(pr: &[u8], cur: &mut usize) -> Result<Self> {
        let val_with_flag = varint::read(&pr, cur) as PageNum;
        let flag = 0 != (val_with_flag & 1);
        let val = val_with_flag >> 1;
        let v = 
            if flag {
                if val == 0 {
                    ValueInLeaf::Tombstone
                } else {
                    let page = val;
                    ValueInLeaf::Overflowed(page)
                }
            } else {
                let vlen = val;
                let v = ValueInLeaf::Inline(vlen as usize, *cur);
                *cur = *cur + (vlen as usize);
                v
            };
        Ok(v)
    }

    fn is_tombstone(&self) -> bool {
        match self {
            &ValueInLeaf::Tombstone => true,
            &ValueInLeaf::Inline(_,_) => false,
            &ValueInLeaf::Overflowed(_) => false,
        }
    }

}

#[derive(Debug)]
struct ItemInLeafPage {
    key: KeyInLeafPage,
    value: ValueInLeaf,
}

#[derive(Debug)]
pub struct ItemInParentPage {
    page: PageNum,

    info: ChildInfo,

    // the ChildInfo does NOT contain page, whether it is a block list or a page count

    last_key: KeyInParentPage,
}

impl ItemInParentPage {
    pub fn page(&self) -> PageNum {
        self.page
    }

    pub fn last_key(&self) -> &KeyInParentPage {
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
    children: Vec<ItemInParentPage>,

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
                ..
            } => {
                assert!(self.depth() == 1);
                let pagenum = self.children[i].page;
                let page = try!(LeafPage::new(self.f.clone(), pagenum));
                page.blocklist_unsorted()
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

    fn child_as_item_for_parent(&self, i: usize) -> Result<ItemForParent> {
        // TODO this func shows up as a common offender of malloc calls
        let last_key = try!(self.key_with_location_for_parent(&self.children[i].last_key));
        assert!( ! last_key.location.is_owned_overflow() );
        // TODO ItemForParent::new
        let pg = ItemForParent {
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

    fn get_owned_overflows(&self, list: &mut Vec<PageNum>) {
        for i in 0 .. self.children.len() {
            match &self.children[i].last_key {
                &KeyInParentPage::Inline{..} => {
                },
                &KeyInParentPage::BorrowedOverflow{..} => {
                },
                &KeyInParentPage::OwnedOverflow{page} => {
                    list.push(page);
                },
            }
        }
    }

    fn blocklist_unsorted(&self) -> Result<BlockList> {
        let mut list = BlockList::new();
        for i in 0 .. self.children.len() {
            list.add_page_no_reorder(self.children[i].page);
            let blocks = try!(self.child_blocklist(i));
            list.add_blocklist_no_reorder(&blocks);
        }
        let mut a = vec![];
        self.get_owned_overflows(&mut a);
        for page in a {
            let (_, blocks) = try!(OverflowReader::get_len_and_blocklist(self.f.clone(), page));
            list.add_blocklist_no_reorder(&blocks);
        }
        Ok(list)
    }

    pub fn count_items(&self) -> usize {
        self.children.len()
    }

    #[inline]
    fn key<'a>(&'a self, k: &KeyInParentPage) -> Result<KeyRef<'a>> { 
        let prefix: Option<&[u8]> = 
            match self.prefix {
                Some(ref b) => Some(b),
                None => None,
            };
        let k = try!(k.keyref(&self.pr, prefix, &self.f));
        Ok(k)
    }

    fn key_with_location_for_parent(&self, k: &KeyInParentPage) -> Result<KeyWithLocationForParent> { 
        let prefix: Option<&[u8]> = 
            match self.prefix {
                Some(ref b) => Some(b),
                None => None,
            };
        let k = try!(k.key_with_location_for_parent(&self.pr, prefix, &self.f));
        Ok(k)
    }

    fn parse_page(pgnum: PageNum, pr: &[u8]) -> Result<(Option<Box<[u8]>>, Vec<ItemInParentPage>, usize)> {
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
        let count_items = varint::read(pr, &mut cur) as usize;
        //println!("count_items: {}", count_items);
        let mut children = Vec::with_capacity(count_items);

        for i in 0 .. count_items {
            let page = varint::read(pr, &mut cur) as PageNum;
            //println!("page: {}", page);

            let info = 
                if depth == 1 {
                    let count_tombstones = varint::read(pr, &mut cur) as u64;
                    ChildInfo::Leaf{
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

            let last_key = try!(KeyInParentPage::read(pr, &mut cur, prefix_len));

            let pg = ItemInParentPage {
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

            let i = ((self.pagenum as PageNum) % (self.children.len() as PageNum)) as usize;
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
            let i = ((self.pagenum as PageNum) % (count as PageNum)) as usize;
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

    fn seek(&mut self, k: &KeyRef, sop: SeekOp) -> Result<SeekResult> {
        //println!("parent page: {}  search: kq = {:?},  sop = {:?}", self.page.pagenum, k, sop);

        for i in 0 .. self.page.count_items() {
            match try!(self.page.cmp_with_child_last_key(i, k)) {
                Ordering::Less | Ordering::Equal => {
                    try!(self.set_child(i));
                    let sr = try!(self.sub.seek(k, sop));
                    if i > 0 && sop == SeekOp::SEEK_LE && sr == SeekResult::Invalid {
                        try!(self.set_child(i - 1));
                        try!(self.sub.last());
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
                try!(self.sub.last());
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

impl IValue for ParentCursor {
    fn value<'a>(&'a self) -> Result<ValueRef<'a>> {
        match self.cur {
            None => {
                Err(Error::CursorNotValid)
            },
            Some(_) => {
                self.sub.value()
            },
        }
    }

    fn value_is_tombstone(&self) -> Result<bool> {
        match self.cur {
            None => {
                Err(Error::CursorNotValid)
            },
            Some(_) => {
                self.sub.value_is_tombstone()
            },
        }
    }

}

impl IForwardCursor for ParentCursor {
    fn is_valid(&self) -> bool {
        match self.cur {
            None => false,
            Some(_) => {
                self.sub.is_valid()
            },
        }
    }

    fn key<'a>(&'a self) -> Result<KeyRef<'a>> {
        match self.cur {
            None => {
                Err(Error::CursorNotValid)
            },
            Some(_) => {
                self.sub.key()
            },
        }
    }

    fn first(&mut self) -> Result<()> {
        try!(self.set_child(0));
        self.sub.first()
    }

    fn next(&mut self) -> Result<()> {
        match self.cur {
            None => {
                Err(Error::CursorNotValid)
            },
            Some(i) => {
                try!(self.sub.next());
                if !self.sub.is_valid() && i + 1 < self.page.count_items() {
                    try!(self.set_child(i + 1));
                    self.sub.first()
                } else {
                    Ok(())
                }
            },
        }
    }

}

impl ISeekableCursor for ParentCursor {
    fn last(&mut self) -> Result<()> {
        let last_child = self.page.count_items() - 1;
        try!(self.set_child(last_child));
        self.sub.last()
    }

    fn prev(&mut self) -> Result<()> {
        match self.cur {
            None => {
                Err(Error::CursorNotValid)
            },
            Some(i) => {
                try!(self.sub.prev());
                if !self.sub.is_valid() && i > 0 {
                    try!(self.set_child(i - 1));
                    self.sub.last()
                } else {
                    Ok(())
                }
            },
        }
    }

    fn seek(&mut self, k: &KeyRef, sop: SeekOp) -> Result<SeekResult> {
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

impl IValue for MultiPageCursor {
    fn value<'a>(&'a self) -> Result<ValueRef<'a>> {
        match self.cur {
            None => {
                Err(Error::CursorNotValid)
            },
            Some(_) => {
                self.sub.value()
            },
        }
    }

    fn value_is_tombstone(&self) -> Result<bool> {
        match self.cur {
            None => {
                Err(Error::CursorNotValid)
            },
            Some(_) => {
                self.sub.value_is_tombstone()
            },
        }
    }

}

impl IForwardCursor for MultiPageCursor {
    fn is_valid(&self) -> bool {
        match self.cur {
            None => false,
            Some(_) => {
                self.sub.is_valid()
            },
        }
    }

    fn key<'a>(&'a self) -> Result<KeyRef<'a>> {
        match self.cur {
            None => {
                Err(Error::CursorNotValid)
            },
            Some(_) => {
                self.sub.key()
            },
        }
    }

    fn first(&mut self) -> Result<()> {
        try!(self.set_child(0));
        self.sub.first()
    }

    fn next(&mut self) -> Result<()> {
        match self.cur {
            None => {
                Err(Error::CursorNotValid)
            },
            Some(i) => {
                try!(self.sub.next());
                if !self.sub.is_valid() && i + 1 < self.children.len() {
                    try!(self.set_child(i + 1));
                    self.sub.first()
                } else {
                    Ok(())
                }
            },
        }
    }

}

#[derive(Clone)]
struct HeaderData {
    incoming: Vec<SegmentHeaderInfo>,
    waiting: Vec<SegmentHeaderInfo>,
    regular: Vec<Option<SegmentHeaderInfo>>,

    change_counter: u64,
    merge_counter: u64,
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

        fn fix_regular_segment_list(segments: Vec<PageNum>, f: &PageCache) -> Result<Vec<Option<SegmentHeaderInfo>>> {
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

        let file_format = pr[0];
        cur += 1;

        let pgsz = varint::read(&pr, &mut cur) as usize;
        let change_counter = varint::read(&pr, &mut cur);
        let merge_counter = varint::read(&pr, &mut cur);

        let f = PageCache::new(f, pgsz);

        let incoming = try!(read_segment_list(pr, &mut cur));
        let waiting = try!(read_segment_list(pr, &mut cur));
        let regular = try!(read_segment_list(pr, &mut cur));

        let incoming = try!(fix_segment_list(incoming, &f));
        let waiting = try!(fix_segment_list(waiting, &f));
        let regular = try!(fix_regular_segment_list(regular, &f));

        let hd = 
            HeaderData {
                incoming: incoming,
                waiting: waiting,
                regular: regular,
                change_counter: change_counter,
                merge_counter: merge_counter,
            };

        Ok((hd, f))
    }

    fn calc_next_page(pgsz: usize, len: usize) -> PageNum {
        let num_pages_sofar = (if pgsz > len { 1 } else { len / pgsz }) as PageNum;
        num_pages_sofar + 1
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
        let next_available_page = calc_next_page(f.page_size(), len as usize);
        Ok((h, f, next_available_page))
    } else {
        // TODO shouldn't this use settings passed in?
        let default_page_size = DEFAULT_SETTINGS.default_page_size;
        let h = {
            HeaderData {
                incoming: vec![],
                waiting: vec![],
                regular: vec![],
                change_counter: 0,
                merge_counter: 0,
            }
        };
        let next_available_page = calc_next_page(default_page_size, HEADER_SIZE_IN_BYTES);
        let f = PageCache::new(f, default_page_size);
        Ok((h, f, next_available_page))
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

    try!(do_seglist(f, h.incoming.iter(), &mut blocks));
    try!(do_seglist(f, h.waiting.iter(), &mut blocks));
    try!(do_seglist(f, h.regular.iter().filter_map(|s| s.as_ref()), &mut blocks));

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
    next_page: PageNum,

    recent_free: Vec<BlockList>,
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
        self.recent_free.push(blocks);
        // TODO tunable parameter, not constant
        if self.recent_free.len() >= 8 {
            self.organize_free_blocks();
        }
    }

    fn step1_sort_and_consolidate(&mut self) {
        for list in self.recent_free.iter() {
            self.free_blocks.add_blocklist_no_reorder(list);
        }
        self.recent_free.clear();

        self.free_blocks.sort_and_consolidate();
        if self.free_blocks.count_blocks() > 0 && self.free_blocks.last_page() == self.next_page - 1 {
            let i_last_block = self.free_blocks.count_blocks() - 1;
            let blk = self.free_blocks.remove_block(i_last_block);
            //println!("    killing free_at_end: {:?}", blk);
            self.next_page = blk.firstPage;
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
        let first_page_beyond = (file_length / page_size + 1) as PageNum;
        if first_page_beyond > self.next_page {
            let fs = try!(OpenOptions::new()
                    .read(true)
                    .write(true)
                    .open(&self.path)
                    );
            try!(fs.set_len(((self.next_page - 1) as u64) * page_size));
        }

        self.step2_sort_for_usage();

        Ok(())
    }

    fn get_block(&mut self, req: BlockRequest) -> PageBlock {
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

        fn find_earliest_block_minimum_size(space: &mut Space, size: PageCount) -> Option<usize> {
            // TODO this will need to look at every block that is
            // big enough.  is that worth it?  if it accepts a block
            // that is larger than we need, that block will need to be
            // split with the remainder added back to the free list.
            // is finding the earliest block worth that?  the rationale
            // is that since an overflow never gets moved, it's worth
            // getting it as early in the file as possible.
            let mut winner = None;
            for i in 0 .. space.free_blocks.count_blocks() {
                if space.free_blocks[i].count_pages() >= size {
                    match winner {
                        None => {
                            winner = Some(i);
                        },
                        Some(j) => {
                            if space.free_blocks[i].firstPage < space.free_blocks[j].firstPage {
                                winner = Some(j);
                            }
                        },
                    }
                } else {
                    // if this block isn't big enough, none of the ones after it will be
                    break;
                }
            }
            return winner;
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

        #[derive(Debug)]
        enum FromWhere {
            End(PageCount),
            FirstFree,
            SpecificFree(usize),
            SpecificFreeExact(usize, PageCount),
        }

        if let Some(after) = req.get_after() {
            assert!(self.next_page > after);
        }

        if self.free_blocks.is_empty() && !self.recent_free.is_empty() {
            self.organize_free_blocks();
        }

        let from =
            if self.free_blocks.is_empty() {
                match req {
                    BlockRequest::EarlyExactSize(size) => {
                        FromWhere::End(size)
                    },
                    _ => {
                        FromWhere::End(self.pages_per_block)
                    },
                }
            } else if req.start_is(self.next_page) {
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
                    BlockRequest::EarlyExactSize(size) => {
                        if let Some(i) = find_earliest_block_minimum_size(self, size) {
                            FromWhere::SpecificFreeExact(i, size)
                        } else {
                            FromWhere::End(size)
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
            FromWhere::SpecificFreeExact(i, size) => {
                let mut blk = self.free_blocks.remove_block(i);
                if blk.count_pages() > size {
                    let mut remainder = BlockList::new();
                    remainder.add_block_no_reorder(PageBlock::new(blk.firstPage + size, blk.lastPage));
                    blk.lastPage = blk.firstPage + size - 1;
                    self.recent_free.push(remainder);
                }
                assert!(blk.count_pages() == size);
                blk
            },
            FromWhere::End(size) => {
                let new_blk = PageBlock::new(self.next_page, self.next_page + size - 1) ;
                self.next_page = self.next_page + size;
                new_blk
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
    Incoming{segments: Vec<PageNum>},
    IncomingNoRewrite{segments: Vec<PageNum>},
    Waiting{old_segment: PageNum, new_segment: Option<SegmentHeaderInfo>},
    Regular{level: usize, old_segment: PageNum, new_segment: Option<SegmentHeaderInfo>},
}

impl MergeFrom {
    fn get_dest_level(&self) -> DestLevel {
        match self {
            &MergeFrom::Incoming{..} => DestLevel::Waiting,
            &MergeFrom::IncomingNoRewrite{..} => DestLevel::Waiting,
            &MergeFrom::Waiting{..} => DestLevel::Regular(0),
            &MergeFrom::Regular{level, ..} => DestLevel::Regular(level + 1),
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

struct Senders {
    notify_incoming: mpsc::Sender<MergeMessage>,
    notify_waiting: mpsc::Sender<MergeMessage>,
    notify_regular: Vec<mpsc::Sender<MergeMessage>>,
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

    fn seek_and_read_fully(&self, buf: &mut [u8], pos: u64) -> Result<usize> {
        let mut stuff = try!(self.stuff.lock());
        let v = try!(stuff.f.seek(SeekFrom::Start(pos)));
        try!(misc::io::read_fully(&mut stuff.f, buf));
        Ok(buf.len())
    }

    fn inner_read(stuff: &mut InnerPageCache, page: PageNum, buf: &mut [u8]) -> Result<()> {
        try!(utils::seek_page(&mut stuff.f, buf.len(), page));
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
                // TODO the following assert failed once.  why?
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
    mergelock_incoming: Mutex<u32>,
    mergelock_waiting: Mutex<u32>,
    // TODO vec, or boxed slice?
    mergelock_regular: Vec<Mutex<u32>>,

}

#[derive(Debug, Copy, Clone)]
pub enum FromLevel {
    Incoming,
    Waiting,
    Regular(usize),
}

impl FromLevel {
    fn get_dest_level(&self) -> DestLevel {
        match self {
            &FromLevel::Incoming => DestLevel::Waiting,
            &FromLevel::Waiting => DestLevel::Regular(0),
            &FromLevel::Regular(level) => DestLevel::Regular(level + 1),
        }
    }
}

#[derive(Debug, Copy, Clone)]
enum DestLevel {
    Waiting,
    Regular(usize),
}

impl DestLevel {
    fn as_from_level(&self) -> FromLevel {
        match self {
            &DestLevel::Waiting => FromLevel::Waiting,
            &DestLevel::Regular(n) => FromLevel::Regular(n),
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

    thread_incoming: thread::JoinHandle<()>,
    thread_waiting: thread::JoinHandle<()>,
    // TODO vec, or boxed slice?
    thread_regular: Vec<thread::JoinHandle<()>>,
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
            // and set next_page to last_page_used + 1, and not add the block above
            path: path.clone(),
            page_size: f.page_size(),
            next_page: first_available_page, 
            pages_per_block: settings.pages_per_block,
            recent_free: vec![],
            free_blocks: blocks,
            next_rlock: 1,
            rlocks: HashMap::new(),
            zombies: HashMap::new(),
            dependencies: HashMap::new(),
        };

        // each merge level is handled by its own thread.  a Rust channel is used to
        // notify that thread that there may be merge work to be done, or that it needs
        // to terminate.

        let (tx_incoming, rx_incoming): (mpsc::Sender<MergeMessage>, mpsc::Receiver<MergeMessage>) = mpsc::channel();
        let (tx_waiting, rx_waiting): (mpsc::Sender<MergeMessage>, mpsc::Receiver<MergeMessage>) = mpsc::channel();

        let mut senders = vec![];
        let mut receivers = vec![];
        for level in 0 .. NUM_REGULAR_LEVELS {
            let (tx, rx): (mpsc::Sender<MergeMessage>, mpsc::Receiver<MergeMessage>) = mpsc::channel();
            senders.push(tx);
            receivers.push(rx);
        }

        let senders = Senders {
            notify_incoming: tx_incoming,
            notify_waiting: tx_waiting,
            notify_regular: senders,
        };

        let mut mergelock_regular = vec![];
        for level in 0 .. NUM_REGULAR_LEVELS {
            mergelock_regular.push(Mutex::new(0));
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
            mergelock_incoming: Mutex::new(0),
            mergelock_waiting: Mutex::new(0),
            mergelock_regular: mergelock_regular,
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

        let thread_incoming = {
            let inner = inner.clone();
            let lck = lck.clone();
            try!(thread::Builder::new().name("incoming".to_string()).spawn(move || merge_loop(inner, lck, rx_incoming, FromLevel::Incoming)))
        };

        let thread_waiting = {
            let inner = inner.clone();
            let lck = lck.clone();
            try!(thread::Builder::new().name("waiting".to_string()).spawn(move || merge_loop(inner, lck, rx_waiting, FromLevel::Waiting)))
        };

        let mut thread_regular = vec![];
        for (level, rx) in receivers.into_iter().enumerate() {
            let thread = {
                let inner = inner.clone();
                let lck = lck.clone();
                try!(thread::Builder::new().name(format!("regular_{}", level)).spawn(move || merge_loop(inner, lck, rx, FromLevel::Regular(level))))
            };
            thread_regular.push(thread);
        }

        let db = DatabaseFile {
            inner: inner,
            write_lock: lck,
            thread_incoming: thread_incoming,
            thread_waiting: thread_waiting,
            thread_regular: thread_regular,
        };
        let db = std::sync::Arc::new(db);

        Ok(db)
    }

    pub fn stop(mut self) -> Result<()> {
        // these need to be stopped in ascending order.  we can't
        // have one of them stop while another one is still sending notifications
        // to it.

        println!("---------------- Stopping incoming");
        {
            let senders = try!(self.inner.senders.lock());
            try!(senders.notify_incoming.send(MergeMessage::Terminate).map_err(wrap_err));
        }

        match self.thread_incoming.join() {
            Ok(()) => {
            },
            Err(e) => {
                return Err(Error::Misc(format!("thread join failed: {:?}", e)));
            },
        }

        println!("---------------- Stopping waiting");
        {
            let senders = try!(self.inner.senders.lock());
            try!(senders.notify_waiting.send(MergeMessage::Terminate).map_err(wrap_err));
        }

        match self.thread_waiting.join() {
            Ok(()) => {
            },
            Err(e) => {
                return Err(Error::Misc(format!("thread join failed: {:?}", e)));
            },
        }

        for i in 0 .. NUM_REGULAR_LEVELS {
            println!("---------------- Stopping regular {}", i);
            {
                let mut senders = try!(self.inner.senders.lock());
                let tx = &senders.notify_regular[i];
                try!(tx.send(MergeMessage::Terminate).map_err(wrap_err));
            }
            let j = self.thread_regular.remove(0);
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
        // into incoming.  merges do not need the big write lock
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
                            Ok(Some(inner.settings.sleep_desperate_regular))
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
            FromLevel::Incoming => {
                loop {
                    let delay = {
                        let foo = try!(inner.mergelock_incoming.lock());
                        // no mergelock_waiting needed here
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
                        println!("desperate,{:?},sleeping,{}", level, inner.settings.sleep_desperate_incoming);
                        std::thread::sleep(std::time::Duration::from_millis(delay));
                    }
                }
            },
            FromLevel::Waiting => {
                loop {
                    let delay = {
                        let foo = try!(inner.mergelock_waiting.lock());
                        let bar = try!(inner.mergelock_regular[0].lock());
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
                        println!("desperate,{:?},sleeping,{}", level, inner.settings.sleep_desperate_incoming);
                        std::thread::sleep(std::time::Duration::from_millis(delay));
                    }
                }
            },
            FromLevel::Regular(n) => {
                loop {
                    let delay = {
                        let foo = try!(inner.mergelock_regular[n].lock());
                        let bar = try!(inner.mergelock_regular[n + 1].lock());
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
                        println!("desperate,{:?},sleeping,{}", level, inner.settings.sleep_desperate_incoming);
                        std::thread::sleep(std::time::Duration::from_millis(delay));
                    }
                }
            },
        }
        Ok(())
    }

    // TODO func to ask for the write lock without blocking?

    pub fn get_write_lock(&self) -> Result<std::sync::MutexGuard<WriteLock>> {
        while NeedsMerge::Desperate == try!(InnerPart::needs_merge(&self.inner, FromLevel::Incoming)) {
            // TODO if we need to sleep more than once, do we really need to notify_work
            // every time?
            try!(self.inner.notify_work(FromLevel::Incoming));
            println!("desperate,regular,sleeping,{}", self.inner.settings.sleep_desperate_incoming);
            std::thread::sleep(std::time::Duration::from_millis(self.inner.settings.sleep_desperate_incoming));
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

    pub fn write_segment(&self, pairs: BTreeMap<Box<[u8]>, ValueForStorage>) -> Result<Option<SegmentHeaderInfo>> {
        InnerPart::write_segment(&self.inner, pairs)
    }

    // tests use this
    pub fn write_segment_from_sorted_sequence<I>(&self, source: I) -> Result<Option<SegmentHeaderInfo>>
        where I: Iterator<Item=Result<PairForStorage>>  {
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

            fn add_regular_list(pb: &mut Vec<u8>, v: &Vec<Option<SegmentHeaderInfo>>) {
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

            add_list(&mut pb, &h.incoming);
            add_list(&mut pb, &h.waiting);
            add_regular_list(&mut pb, &h.regular);

            pb
        }

        //println!("header, incoming,{}, waiting,{}, regular,{}", hdr.incoming.len(), hdr.waiting.len(), hdr.regular.len());

        let mut pb = PageBuilder::new(HEADER_SIZE_IN_BYTES);
        pb.put_u8(0); // file format
        pb.put_varint(pgsz as u64);

        // TODO aren't there some settings that should go in here?

        pb.put_varint(hdr.change_counter);
        pb.put_varint(hdr.merge_counter);

        let seglist = build_segment_list(&hdr);

        // TODO the + 1 in the following line is probably no longer needed.
        // I think it used to be the flag indicating header overflow.
        if pb.available() >= (seglist.len() + 1) {
            pb.put_from_slice(&seglist);
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
                try!(utils::seek_page(&mut fs, self.pgsz, x));
                try!(fs.write(&bad));
            }
        }
        Ok(())
    }

    // a stored segmentinfo for a segment is a single blob of bytes.
    // root page
    // number of pairs
    // each pair is startBlock,countBlocks
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
            header.incoming.iter()
            .chain(header.waiting.iter())
            .chain(header.regular.iter().filter_map(|s| s.as_ref()))
            .map(|seg| {
                let csr = try!(PageCursor::new(f.clone(), seg.root_page));
                Ok(csr)
            })
            .collect::<Result<Vec<_>>>();
        let cursors = try!(cursors);

        let segments = 
            header.incoming.iter()
            .chain(header.waiting.iter())
            .chain(header.regular.iter().filter_map(|s| s.as_ref()))
            .map(|seg| {
                seg.root_page
            })
            .collect::<HashSet<_>>();

        let rlock = {
            let mut space = try!(inner.space.lock());
            let rlock = space.add_rlock(segments);
            rlock
        };

        println!("open_cursor,{}, incoming,{}, waiting,{}, regular,{}", rlock, header.incoming.len(), header.waiting.len(), header.regular.len());

        if cfg!(expensive_check) 
        {
            let segnums = 
                header.incoming.iter()
                .chain(header.waiting.iter())
                .chain(header.regular.iter().filter_map(|s| s.as_ref()))
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

        fn do_regular_group(segments: &[Option<SegmentHeaderInfo>]) -> Result<Vec<(PageNum, PageCount)>> {
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

        let incoming = try!(do_group(&header.incoming));
        let waiting = try!(do_group(&header.waiting));
        let regular = try!(do_regular_group(&header.regular));

        Ok((incoming, waiting, regular))
    }

    fn commit_segment(&self, seg: SegmentHeaderInfo) -> Result<()> {
        {
            let mut headerstuff = try!(self.header.write());

            // TODO assert new seg shares no pages with any seg in current state

            let mut new_header = headerstuff.data.clone();

            new_header.incoming.insert(0, seg);

            new_header.change_counter = new_header.change_counter + 1;

            try!(headerstuff.write_header(new_header, self.page_cache.page_size()));
        }

        // note that we intentionally do not release the writeLock here.
        // you can change the segment list more than once while holding
        // the writeLock.  the writeLock gets released when you Dispose() it.

        try!(self.notify_work(FromLevel::Incoming));

        Ok(())
    }

    fn write_segment(inner: &std::sync::Arc<InnerPart>, pairs: BTreeMap<Box<[u8]>, ValueForStorage>) -> Result<Option<SegmentHeaderInfo>> {
        //println!("writing segment with {} pairs", pairs.len());
        let source = pairs.into_iter().map(|t| {
            let (k, v) = t;
            let k = KeyForStorage::Boxed(k);
            Ok(PairForStorage {key: k, value: v})
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
        where I: Iterator<Item=Result<PairForStorage>>  {
        let pw = try!(PageWriter::new(inner.clone()));
        let seg = try!(create_segment(pw, source, inner.page_cache.clone()));
        Ok(seg)
    }

    fn notify_work(&self, from_level: FromLevel) -> Result<()> {
        let senders = try!(self.senders.lock());
        match from_level {
            FromLevel::Incoming => {
                try!(senders.notify_incoming.send(MergeMessage::Work).map_err(wrap_err));
            },
            FromLevel::Waiting => {
                try!(senders.notify_waiting.send(MergeMessage::Work).map_err(wrap_err));
            },
            FromLevel::Regular(i) => {
                try!(senders.notify_regular[i].send(MergeMessage::Work).map_err(wrap_err));
            },
        }
        Ok(())
    }

    fn needs_merge(inner: &std::sync::Arc<InnerPart>, from_level: FromLevel) -> Result<NeedsMerge> {
        match from_level {
            FromLevel::Regular(i) => {
                if i == NUM_REGULAR_LEVELS - 1 {
                    // this level doesn't need a merge because it has nowhere to promote to
                    // TODO this hard-coded restriction on number of regular levels should go away
                    return Ok(NeedsMerge::No);
                }
            },
            _ => {
            },
        }
        let headerstuff = try!(inner.header.read());
        let header = &headerstuff.data;
        match from_level {
            FromLevel::Incoming => {
                if header.incoming.is_empty() {
                    return Ok(NeedsMerge::No);
                }

                if header.incoming.len() > inner.settings.desperate_incoming {
                    return Ok(NeedsMerge::Desperate);
                }

                // TODO consider always returning Yes here.  but
                // doing that seems to cause a big perf hit.  why?
                // the idea was to just keep Incoming empty.
                let i = header.incoming.len() - 1;
                let pt = try!(PageType::from_u8(header.incoming[i].buf[0]));
                match pt {
                    PageType::PARENT_NODE => {
                        // a parent node is promoted from Incoming without a rewrite
                        return Ok(NeedsMerge::Yes);
                    },
                    PageType::LEAF_NODE => {
                        if header.incoming.len() > 1 {
                            return Ok(NeedsMerge::Yes);
                        } else {
                            return Ok(NeedsMerge::No);
                        }
                    },
                }

                return Ok(NeedsMerge::Yes);
            },
            FromLevel::Waiting => {
                if header.waiting.is_empty() {
                    return Ok(NeedsMerge::No);
                }

                if header.waiting.len() > inner.settings.desperate_waiting {
                    return Ok(NeedsMerge::Desperate);
                }

                return Ok(NeedsMerge::Yes);
            },
            FromLevel::Regular(i) => {
                if header.regular.len() <= i {
                    // this level doesn't need a merge because it currently doesn't exist
                    return Ok(NeedsMerge::No);
                }
                match &header.regular[i] {
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
                                if i + 1 < header.regular.len() {
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
                                    // Regular(0) gets out of control on 5M urls.
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
            IncomingLeaves{
                // Segments of depth > 0 are moved from Incoming to Waiting
                // without rewriting them.
                // Leaf segments are moved from Incoming to Waiting by
                // grouping them together into bigger segments.
                segments: Vec<PageNum>,
            },
            WaitingLeaf{
                segment: PageNum,
                count_tombstones: u64,
            },
            WaitingPartial{
                old_segment: ParentPage,
                promote_pages: Vec<PageNum>, // must be contig within same parent
                promote_depth: u8,
                promote_blocks: BlockList, 
                promote_lineage: Vec<PageNum>, 
                count_tombstones: u64,
            },
            RegularLeaf{
                level: usize,  // TODO why is this here?
                segment: PageNum,
                count_tombstones: u64,
            },
            RegularPartial{
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
                    FromLevel::Incoming => {
                        let i = header.incoming.len() - 1;
                        match try!(PageType::from_u8(header.incoming[i].buf[0])) {
                            PageType::LEAF_NODE => {
                                let mut i = i;
                                // TODO should there be a limit to how many leaves we will take at one time?

                                // note that must accept just one if that's all we have.
                                // otherwise, we could get stuck with the last segment being a leaf
                                // and the second-to-last segment being a parent.
                                while i > 0 {
                                    if PageType::LEAF_NODE == try!(PageType::from_u8(header.incoming[i - 1].buf[0])) {
                                        i -= 1;
                                    } else {
                                        break;
                                    }
                                }

                                let merge_segments = slice_from_end(&header.incoming, header.incoming.len() - i);

                                let cursors = try!(get_cursors(inner, f, &merge_segments));

                                let merge_segments = 
                                    merge_segments
                                    .iter()
                                    .map( |seg| seg.root_page)
                                    .collect::<Vec<_>>();;

                                (cursors, MergingFrom::IncomingLeaves{segments: merge_segments})
                            },
                            PageType::PARENT_NODE => {
                                let mut i = i;
                                while i > 0 {
                                    if PageType::PARENT_NODE == try!(PageType::from_u8(header.incoming[i - 1].buf[0])) {
                                        i -= 1;
                                    } else {
                                        break;
                                    }
                                }

                                let merge_segments = slice_from_end(&header.incoming, header.incoming.len() - i);

                                let merge_segments = 
                                    merge_segments
                                    .iter()
                                    .map(|seg| seg.root_page)
                                    .collect::<Vec<_>>();;

                                // TODO dislike early return
                                let pm = 
                                    PendingMerge {
                                        from: MergeFrom::IncomingNoRewrite{segments: merge_segments},
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
                    FromLevel::Waiting => {
                        let i = header.waiting.len() - 1;
                        let segment = &header.waiting[i];
                        match try!(PageType::from_u8(header.waiting[i].buf[0])) {
                            PageType::LEAF_NODE => {
                                let count_tombstones = try!(LeafPage::count_tombstones(segment.root_page, &segment.buf));

                                // TODO sad that this will re-read the leaf page
                                let cursor = try!(MultiPageCursor::new(f.clone(), vec![segment.root_page]));

                                let from = MergingFrom::WaitingLeaf{
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

                                let from = MergingFrom::WaitingPartial{
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
                    FromLevel::Regular(level) => {
                        assert!(header.regular.len() > level);
                        // TODO unwrap here is ugly.  but needs_merge happpened first
                        let old_from_segment = header.regular[level].as_ref().unwrap();
                        match try!(PageType::from_u8(old_from_segment.buf[0])) {
                            PageType::LEAF_NODE => {
                                let count_tombstones = try!(LeafPage::count_tombstones(old_from_segment.root_page, &old_from_segment.buf));

                                // TODO sad that this will re-read the leaf page
                                let cursor = try!(MultiPageCursor::new(f.clone(), vec![old_from_segment.root_page]));

                                let from = MergingFrom::RegularLeaf{
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

                                let from = MergingFrom::RegularPartial{
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
                    DestLevel::Waiting => {
                        // for merges from Incoming into Waiting, there is no dest segment.
                        MergingInto::None
                    },
                    DestLevel::Regular(dest_level) => {
                        if header.regular.len() > dest_level {
                            match &header.regular[dest_level] {
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
                        MergingFrom::IncomingLeaves{..} => {
                            None
                        },
                        MergingFrom::WaitingLeaf{count_tombstones, ..} => {
                            if count_tombstones == 0 {
                                None
                            } else {
                                let dest_level = 0;
                                let mut behind_segments = Vec::with_capacity(header.regular.len());
                                for i in dest_level + 1 .. header.regular.len() {
                                    let seg = &header.regular[i];

                                    behind_segments.push(seg);
                                }
                                Some(behind_segments)
                            }
                        },
                        MergingFrom::WaitingPartial{count_tombstones, ..} => {
                            if count_tombstones == 0 {
                                None
                            } else {
                                let dest_level = 0;
                                let mut behind_segments = Vec::with_capacity(header.regular.len());
                                for i in dest_level + 1 .. header.regular.len() {
                                    let seg = &header.regular[i];

                                    behind_segments.push(seg);
                                }
                                Some(behind_segments)
                            }
                        },
                        MergingFrom::RegularLeaf{level, count_tombstones, ..} => {
                            if count_tombstones == 0 {
                                None
                            } else {
                                let dest_level = level + 1;
                                let mut behind_segments = Vec::with_capacity(header.regular.len());
                                for i in dest_level + 1 .. header.regular.len() {
                                    let seg = &header.regular[i];

                                    behind_segments.push(seg);
                                }
                                Some(behind_segments)
                            }
                        },
                        MergingFrom::RegularPartial{level, count_tombstones, ..} => {
                            if count_tombstones == 0 {
                                None
                            } else {
                                let dest_level = level + 1;
                                let mut behind_segments = Vec::with_capacity(header.regular.len());
                                for i in dest_level + 1 .. header.regular.len() {
                                    let seg = &header.regular[i];

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
            // note that cursor.first() should NOT have already been called
            let mut cursor = cursor;
            try!(cursor.first());
            if cursor.is_valid() {
                let mut source = CursorIterator::new(cursor);
                let wrote = try!(write_merge(&mut pw, &mut source, &into, behind_cursors, &inner.path, f.clone(), from_level.get_dest_level()));

                //println!("write_merge, nodes_rewritten: {:?}", wrote.nodes_rewritten);

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
                                try!(cursor.first());
                                while cursor.is_valid() {
                                    count += 1;
                                    try!(cursor.next());
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
        //     the incoming segments being promoted
        //     the waiting segments being promoted
        //     the regular segment being promoted
        //     the dest segment
        //
        // all those pages must end up in one of three places:
        //     the new dest segment
        //     the new from segment
        //     inactive

        let mut now_inactive: HashMap<PageNum, BlockList> = {
            let mut now_inactive = HashMap::new();
            match from {
                MergingFrom::IncomingLeaves{ref segments} => {
                    for &seg in segments.iter() {
                        let mut blocks = BlockList::new();
                        blocks.add_page_no_reorder(seg);
                        // TODO overflows_eaten should be a hashmap
                        for &(s, page) in overflows_eaten.iter() {
                            if s == seg {
                                let (_, blist) = try!(OverflowReader::get_len_and_blocklist(f.clone(), page));
                                blocks.add_blocklist_no_reorder(&blist);
                            }
                        }
                        assert!(!now_inactive.contains_key(&seg));
                        now_inactive.insert(seg, blocks);
                    }
                },
                MergingFrom::WaitingLeaf{segment, ..} => {
                    let mut blocks = BlockList::new();
                    blocks.add_page_no_reorder(segment);
                    assert!(overflows_eaten.is_empty());
                    assert!(!now_inactive.contains_key(&segment));
                    now_inactive.insert(segment, blocks);
                },
                MergingFrom::RegularLeaf{segment, ..} => {
                    let mut blocks = BlockList::new();
                    blocks.add_page_no_reorder(segment);
                    assert!(overflows_eaten.is_empty());
                    assert!(!now_inactive.contains_key(&segment));
                    now_inactive.insert(segment, blocks);
                },
                MergingFrom::WaitingPartial{..} => {
                    // this is done below
                },
                MergingFrom::RegularPartial{..} => {
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
                    for page in overflows_freed {
                        let (_, blist) = try!(OverflowReader::get_len_and_blocklist(f.clone(), page));
                        blocks.add_blocklist_no_reorder(&blist);
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
                MergingFrom::IncomingLeaves{segments} => {
                    MergeFrom::Incoming{
                        segments: segments,
                    }
                },
                MergingFrom::WaitingLeaf{segment, ..} => {
                    MergeFrom::Waiting{
                        old_segment: segment,
                        new_segment: None,
                    }
                },
                MergingFrom::WaitingPartial{old_segment, promote_pages, promote_depth, promote_lineage, promote_blocks, ..} => {
                    // TODO this code is very similar to the MergingFrom::RegularPartial case below
                    //println!("promote_lineage: {:?}", promote_lineage);
                    //println!("promote_pages: {:?}", promote_pages);
                    // TODO this seems to be the place where overflowed keys are getting lost
                    // instead of becoming inactive
                    let wrote = try!(write_survivors(&mut pw, &promote_pages, promote_depth, &promote_lineage, &old_segment, &inner.path, &f, from_level.get_dest_level()));

                    println!("survivors,from,{:?}, leaves_rewritten,{}, leaves_recycled,{}, parent1_rewritten,{}, parent1_recycled,{}, ms,{}", 
                             from_level, 
                             if wrote.nodes_rewritten.len() > 0 { wrote.nodes_rewritten[0].len() } else { 0 },
                             if wrote.nodes_recycled.len() > 0 { wrote.nodes_recycled[0] } else { 0 },
                             if wrote.nodes_rewritten.len() > 1 { wrote.nodes_rewritten[1].len() } else { 0 },
                             if wrote.nodes_recycled.len() > 1 { wrote.nodes_recycled[1] } else { 0 },
                             wrote.elapsed_ms,
                            );
                    //println!("node_rewritten: {:?}", wrote.nodes_rewritten);

                    let from = 
                        MergeFrom::Waiting{
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
                    for page in wrote.owned_overflows {
                        let (_, blist) = try!(OverflowReader::get_len_and_blocklist(f.clone(), page));
                        blocks.add_blocklist_no_reorder(&blist);
                    }
                    //println!("blocks becoming inactive on survivors: {:?}", blocks);
                    assert!(!now_inactive.contains_key(&old_segment.pagenum));
                    now_inactive.insert(old_segment.pagenum, blocks);
                    from
                },
                MergingFrom::RegularLeaf{level, segment, ..} => {
                    MergeFrom::Regular{
                        level: level,
                        old_segment: segment,
                        new_segment: None,
                    }
                },
                MergingFrom::RegularPartial{level, old_segment, promote_pages, promote_depth, promote_lineage, promote_blocks, ..} => {
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
                        MergeFrom::Regular {
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
                    for page in wrote.owned_overflows {
                        let (_, blist) = try!(OverflowReader::get_len_and_blocklist(f.clone(), page));
                        blocks.add_blocklist_no_reorder(&blist);
                    }
                    //println!("blocks becoming inactive on survivors: {:?}", blocks);
                    assert!(!now_inactive.contains_key(&old_segment.pagenum));
                    now_inactive.insert(old_segment.pagenum, blocks);
                    from
                },
            };

        try!(pw.end());

        // bizarre
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
                            try!(page.blocklist_unsorted())
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
                    MergeFrom::Incoming{ref segments} => {
                        for &seg in segments.iter() {
                            let blocks = try!(get_blocklist_for_segment_including_root(seg, f));
                            assert!(!now_inactive.contains_key(&seg));
                            now_inactive.insert(seg, blocks);
                        }
                    },
                    MergeFrom::IncomingNoRewrite{..} => {
                    },
                    MergeFrom::Waiting{old_segment, ..} => {
                        let blocks = try!(get_blocklist_for_segment_including_root(old_segment, f));
                        println!("old_segment {} was {:?}", old_segment, blocks);
                        assert!(!now_inactive.contains_key(&old_segment));
                        now_inactive.insert(old_segment, blocks);
                    },
                    MergeFrom::Regular{old_segment, ..} => {
                        let blocks = try!(get_blocklist_for_segment_including_root(old_segment, f));
                        assert!(!now_inactive.contains_key(&old_segment));
                        now_inactive.insert(old_segment, blocks);
                    },
                }
                match old_dest_segment {
                    Some(seg) => {
                        let blocks = try!(get_blocklist_for_segment_including_root(seg, f));
                        println!("old_dest_segment {} is {:?}", seg, blocks);
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
                        println!("new_dest_segment {} is {:?}", seg.root_page, blocks);
                        for (k,b) in old_now_inactive.iter_mut() {
                            b.remove_anything_in(&blocks);
                        }
                    },
                    None => {
                    },
                }
                match from {
                    MergeFrom::Waiting{ref new_segment, ..} => {
                        if let &Some(ref new_segment) = new_segment {
                            let mut blocks = try!(new_segment.blocklist_unsorted(f));
                            blocks.add_page_no_reorder(new_segment.root_page);
                            println!("new_segment {} is {:?}", new_segment.root_page, blocks);
                            for (k, b) in old_now_inactive.iter_mut() {
                                b.remove_anything_in(&blocks);
                            }
                        }
                    },
                    MergeFrom::Regular{ref new_segment, ..} => {
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
                            MergeFrom::Waiting{ref new_segment, ..} => {
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
                            MergeFrom::Regular{ref new_segment, ..} => {
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
                        println!("from: {:?}", from);
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

            let mut new_header = headerstuff.data.clone();

            fn update_header(new_header: &mut HeaderData, old_dest_segment: Option<PageNum>, new_dest_segment: Option<SegmentHeaderInfo>, dest_level: usize) {
                match (old_dest_segment, new_dest_segment) {
                    (None, None) => {
                        // a merge resulted in what would have been an empty segment.
                        // multiple promoted segments cancelled each other out.
                        // but there wasn't anything in this level anyway, either
                        // because it didn't exist or had been depleted.
                        if new_header.regular.len() == dest_level {
                            // fine
                        } else {
                            assert!(new_header.regular[dest_level].is_none());
                        }
                    },
                    (None, Some(new_seg)) => {
                        if new_header.regular.len() == dest_level {
                            // first merge into this new level
                            new_header.regular.push(Some(new_seg));
                        } else {
                            // merge into a previously depleted level
                            assert!(dest_level < new_header.regular.len());
                            assert!(new_header.regular[dest_level].is_none());
                            new_header.regular[dest_level] = Some(new_seg);
                            println!("level {} resurrected", dest_level);
                        }
                    },
                    (Some(old), None) => {
                        // a merge resulted in what would have been an empty segment.
                        // promoted segments cancelled out everything that was in
                        // the dest level.
                        assert!(dest_level < new_header.regular.len());
                        assert!(new_header.regular[dest_level].as_ref().unwrap().root_page == old);
                        // TODO if this is the last level, just remove it?
                        new_header.regular[dest_level] = None;
                        println!("level {} depleted", dest_level);
                    },
                    (Some(old), Some(new_seg)) => {
                        // level already exists
                        assert!(dest_level < new_header.regular.len());
                        assert!(new_header.regular[dest_level].as_ref().unwrap().root_page == old);
                        new_header.regular[dest_level] = Some(new_seg);
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
                        MergeFrom::Incoming{ref segments} => {
                            for seg in segments {
                                deps_dest.push(*seg);
                            }
                        },
                        MergeFrom::IncomingNoRewrite{..} => {
                            assert!(pm.now_inactive.is_empty());
                        },
                        MergeFrom::Waiting{old_segment, ..} => {
                            deps_dest.push(old_segment);
                        },
                        MergeFrom::Regular{old_segment, ..} => {
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
                MergeFrom::Incoming{..} => {
                },
                MergeFrom::IncomingNoRewrite{..} => {
                },
                MergeFrom::Waiting{old_segment, ref new_segment} => {
                    match new_segment {
                        &Some(ref new_segment) => {
                            assert!(!deps.contains_key(&new_segment.root_page));
                            deps.insert(new_segment.root_page, vec![old_segment]);
                        },
                        &None => {
                        },
                    }
                },
                MergeFrom::Regular{level, old_segment, ref new_segment} => {
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
                MergeFrom::Incoming{ref segments} => {
                    let ndx = find_segments_in_list(segments, &headerstuff.data.incoming);
                    for _ in segments {
                        new_header.incoming.remove(ndx);
                    }

                    assert!(pm.old_dest_segment.is_none());
                    match pm.new_dest_segment {
                        None => {
                            // a merge resulted in what would have been an empty segment.
                            // this happens because tombstones.
                            // multiple segments from the incoming level cancelled each other out.
                            // nothing needs to be inserted in the waiting level.
                        },
                        Some(new_seg) => {
                            new_header.waiting.insert(0, new_seg);
                        },
                    }
                },
                MergeFrom::IncomingNoRewrite{ref segments} => {
                    let ndx = find_segments_in_list(segments, &headerstuff.data.incoming);
                    for _ in segments {
                        let s = new_header.incoming.remove(ndx);
                        new_header.waiting.insert(0, s);
                    }

                    assert!(pm.old_dest_segment.is_none());
                    assert!(pm.new_dest_segment.is_none());
                },
                MergeFrom::Waiting{old_segment, new_segment} => {
                    let i = new_header.waiting.len() - 1;
                    assert!(old_segment == new_header.waiting[i].root_page);
                    match new_segment {
                        Some(new_segment) => {
                            new_header.waiting[i] = new_segment;
                        },
                        None => {
                            new_header.waiting.remove(i);
                        },
                    }

                    let dest_level = 0;
                    update_header(&mut new_header, pm.old_dest_segment, pm.new_dest_segment, dest_level);
                },
                MergeFrom::Regular{level, old_segment, new_segment} => {
                    assert!(old_segment == new_header.regular[level].as_ref().unwrap().root_page);
                    new_header.regular[level] = new_segment;

                    let dest_level = level + 1;
                    update_header(&mut new_header, pm.old_dest_segment, pm.new_dest_segment, dest_level);
                },
            }

            new_header.merge_counter = new_header.merge_counter + 1;

            try!(headerstuff.write_header(new_header, self.page_cache.page_size()));
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

    last_page: PageNum,
}

struct PageGroup {
    inventory: Vec<PageBlock>,
    blocks: BlockList,
    known_size: Option<PageCount>,
}

impl PageWriter {
    fn new(inner: std::sync::Arc<InnerPart>) -> Result<Self> {
        let f = try!(OpenOptions::new()
                .read(true)
                .write(true)
                .open(&inner.path));
        let pw = PageWriter {
            inner: inner,
            f: f,
            blocks: vec![],
            last_page: 0,
        };
        Ok(pw)
    }

    fn begin_group(&mut self, known_size: Option<PageCount>) -> Result<PageGroup> {
        let mut group = PageGroup {
            inventory: vec![],
            known_size: known_size,
            blocks: BlockList::new(),
        };

        if let Some(want) = group.known_size {
            // TODO we could see if self.blocks (inventory) has something we could use
            let blk = try!(self.request_block(BlockRequest::EarlyExactSize(want)));
            assert!(blk.count_pages() == want);
            group.inventory.push(blk);
        }

        Ok(group)
    }

    fn end_group(&self, group: PageGroup) -> Result<BlockList> {
        if !group.inventory.is_empty() {
            assert!(group.known_size.is_none());

            // TODO or, consider putting the group inventory back into the main inventory
            let mut space = try!(self.inner.space.lock());
            space.add_free_blocks(BlockList {blocks: group.inventory});
            // TODO consider calling space.truncate_if_possible() here
        }
        Ok(group.blocks)
    }

    fn request_block(&self, req: BlockRequest) -> Result<PageBlock> {
        let mut space = try!(self.inner.space.lock());
        let blk = space.get_block(req);
        Ok(blk)
    }

    fn ensure_inventory(&mut self) -> Result<()> {
        assert!(self.blocks.len() <= 2);
        if self.blocks.is_empty() {
            let blk = try!(self.request_block(BlockRequest::MinimumSize(2)));
            self.blocks.push(blk);
            Ok(())
        } else if self.blocks.len() == 1 {
            // TODO remove this restriction because no more boundary stuff?
            // TODO probably still makes sense to never deplete, so that we
            // can request a block that starts where the current one ends,
            // but...
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
            // TODO remove this restriction because no more boundary stuff?
            //assert!(blocks.len() > 1);
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

    fn ensure_group_inventory(&mut self, group: &mut PageGroup) -> Result<()> {
        // this is only used for groups where the size was not known
        assert!(group.known_size.is_none());

        // TODO not sure what minimum size we should request.
        // we want overflows to be contiguous, but we also want to
        // avoid putting them at the end of the file.
        // TODO config constant?
        const MINIMUM_SIZE_FIRST_BLOCK_IN_GROUP: PageCount = 16;

        // TODO the need to have the first page always be the lowest numbered
        // page in the resulting blocklist is not going to be so important.

        assert!(group.inventory.len() <= 2);
        if group.inventory.is_empty() {
            // if there is no inventory, then the group has gotta be empty,
            // because we don't allow the inventory to be completely depleted
            // during the processing of a group.
            assert!(group.blocks.is_empty());

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

            let want = MINIMUM_SIZE_FIRST_BLOCK_IN_GROUP;
            let blk = try!(self.request_block(BlockRequest::MinimumSize(want)));
            group.inventory.push(blk);
            Ok(())
        } else if group.inventory.len() == 1 {
            if !group.blocks.is_empty() {
                assert!(group.inventory[0].firstPage > group.blocks[0].firstPage);
            }
            if group.inventory[0].count_pages() == 1 {
                // we always prefer a block which extends the one we've got in inventory
                let want = group.inventory[0].lastPage + 1;

                let req =
                    match group.blocks.count_blocks() {
                        0 => {
                            // group hasn't started yet.  so it doesn't care where the block is,
                            // but it soon will, because it will be given the currently available
                            // page, so we need to make sure we get something after that one.
                            let after = group.inventory[0].firstPage;

                            BlockRequest::StartOrAfterMinimumSize(vec![want], after, MINIMUM_SIZE_FIRST_BLOCK_IN_GROUP)
                        },
                        _ => {
                            // the one available page must fit on one of the blocks already
                            // in the group
                            assert!(group.blocks.would_extend_an_existing_block(group.inventory[0].firstPage));

                            // we would also prefer any block which would extend any of the
                            // blocks already in the group

                            let mut wants = Vec::with_capacity(4);
                            for i in 0 .. group.blocks.count_blocks() {
                                let pg = group.blocks[i].lastPage + 1;
                                if want != pg {
                                    wants.push(pg);
                                }
                            }
                            wants.insert(0, want);

                            // the group is running, so we cannnot accept any block before the
                            // first page of the group.
                            let after = group.blocks[0].firstPage;

                            // TODO tune the numbers below
                            // TODO maybe the request size should be a formula instead of match cases

                            match group.blocks.count_blocks() {
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
                if !group.blocks.is_empty() {
                    assert!(blk2.firstPage > group.blocks[0].firstPage);
                }
                if blk2.firstPage == group.inventory[0].lastPage + 1 {
                    group.inventory[0].lastPage = blk2.lastPage;
                } else {
                    group.inventory.push(blk2);
                }
            }
            Ok(())
        } else if group.inventory.len() == 2 {
            if !group.blocks.is_empty() {
                assert!(group.inventory[0].firstPage > group.blocks[0].firstPage);
            }
            Ok(())
        } else {
            unreachable!();
        }
    }

    fn get_group_page(&mut self, group: &mut PageGroup) -> Result<PageNum> {
        if group.known_size.is_none() {
            try!(self.ensure_group_inventory(group));
        }
        let pg = try!(Self::get_page_from(&mut group.inventory));
        if group.blocks.blocks.len() > 0 {
            let first = group.blocks[0].firstPage;
            assert!(pg > first);
        }
        let extended = group.blocks.add_page_no_reorder(pg);
        Ok(pg)
    }

    fn page_size(&self) -> usize {
        self.inner.page_cache.page_size()
    }

    fn write_page_at(&mut self, buf: &[u8], pg: PageNum) -> Result<()> {
        if pg != self.last_page + 1 {
            try!(utils::seek_page(&mut self.f, self.inner.page_cache.page_size(), pg));
        }
        try!(self.f.write_all(buf));
        self.last_page = pg;
        Ok(())
    }

    fn write_group_page(&mut self, buf: &[u8], group: &mut PageGroup) -> Result<()> {
        let pg = try!(self.get_group_page(group));
        try!(self.write_page_at(buf, pg));
        Ok(())
    }

    fn write_page(&mut self, buf: &[u8]) -> Result<PageNum> {
        let pg = try!(self.get_page());
        try!(self.write_page_at(buf, pg));
        //println!("wrote page {}", pg);
        Ok(pg)
    }

    // TODO this could happen on Drop.
    // but it needs error handling.
    // so maybe Drop should panic if it didn't happen.
    fn end(self) -> Result<()> {
        if !self.blocks.is_empty() {
            let mut space = try!(self.inner.space.lock());
            if !self.blocks.is_empty() {
                space.add_free_blocks(BlockList {blocks: self.blocks});
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
    type Item = Result<PairForStorage>;
    // TODO allow the number of digits to be customized?
    fn next(&mut self) -> Option<Result<PairForStorage>> {
        if self.cur > self.end {
            None
        }
        else {
            let k = format!("{:08}", self.cur).into_bytes().into_boxed_slice();
            let v = format!("{}", self.cur * 2).into_bytes().into_boxed_slice();
            let k = KeyForStorage::Boxed(k);
            let r = PairForStorage {key: k, value: ValueForStorage::Boxed(v) };
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
    type Item = Result<PairForStorage>;
    fn next(&mut self) -> Option<Result<PairForStorage>> {
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

            let k = KeyForStorage::Boxed(k);
            let r = PairForStorage {key: k, value: ValueForStorage::Boxed(v) };
            self.cur = self.cur + 1;
            Some(Ok(r))
        }
    }
}

