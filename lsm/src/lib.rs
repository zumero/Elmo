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

const NUM_LEVELS: usize = 8;

pub type PageNum = u32;
pub type PageCount = u32;
// type PageSize = u32;

// TODO also perhaps the type representing size of a value, u32
// size of a value should NOT be usize, right?

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

// TODO maybe KeyRange should just go away, always use the KeyRef form?
#[derive(Debug)]
pub struct KeyRange {
    // TODO consider enum to support case where min=max
    min: Box<[u8]>,
    max: Box<[u8]>,
}

impl KeyRange {
    fn overlaps(&self, other: &KeyRange) -> Overlap {
        match bcmp::Compare(&self.min, &other.max) {
            Ordering::Greater => {
                Overlap::Greater
            },
            Ordering::Equal => {
                Overlap::Yes
            },
            Ordering::Less => {
                match bcmp::Compare(&self.max, &other.min) {
                    Ordering::Less => {
                        Overlap::Less
                    },
                    Ordering::Greater | Ordering::Equal => {
                        Overlap::Yes
                    },
                }
            },
        }
    }

}

#[derive(Debug)]
pub struct KeyRangeRef<'a> {
    // TODO consider enum to support case where min=max
    min: KeyRef<'a>,
    max: KeyRef<'a>,
}

impl<'a> KeyRangeRef<'a> {
    fn into_keyrange(self) -> KeyRange {
        KeyRange {
            min: self.min.into_boxed_slice(),
            max: self.max.into_boxed_slice(),
        }
    }
    
    fn grow(self, cur: KeyRange) -> KeyRange {
        let min = self.min.min_with(cur.min);
        let max = self.max.max_with(cur.max);
        let range = KeyRange {
            min: min,
            max: max,
        };
        range
    }

    fn overlaps(&self, other: &KeyRange) -> Overlap {
        match self.min.compare_with(&other.max) {
            Ordering::Greater => {
                Overlap::Greater
            },
            Ordering::Equal => {
                Overlap::Yes
            },
            Ordering::Less => {
                match self.max.compare_with(&other.min) {
                    Ordering::Less => {
                        Overlap::Less
                    },
                    Ordering::Greater | Ordering::Equal => {
                        Overlap::Yes
                    },
                }
            },
        }
    }
}

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
struct kvp {
    // TODO note that there is no provision here for SameFileOverflow from a merge
    Key: Box<[u8]>,
    Value: Blob,
}

#[derive(Debug, Clone)]
pub struct BlockList {
    // TODO we could keep track of how this is sorted if
    // we put this in a module to make the blocks field private.
    blocks: Vec<PageBlock>,
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

    fn encode(&self, pb: &mut Vec<u8>) {
        // we store each PageBlock as first/offset instead of first/last, since the
        // offset will always compress better as a varint.
        
        // if there are multiple blocks, we store the firstPage field
        // of all blocks after the first one as offsets from th first one.
        // this requires that the list was sorted before this func was called.

        misc::push_varint(pb, self.blocks.len() as u64);
        if self.blocks.len() > 0 {
            let first_page = self.blocks[0].firstPage;
            misc::push_varint(pb, self.blocks[0].firstPage as u64);
            misc::push_varint(pb, (self.blocks[0].lastPage - self.blocks[0].firstPage) as u64);
            if self.blocks.len() > 1 {
                for i in 1 .. self.blocks.len() {
                    assert!(self.blocks[i].firstPage > first_page);
                    misc::push_varint(pb, (self.blocks[i].firstPage - first_page) as u64);
                    misc::push_varint(pb, (self.blocks[i].lastPage - self.blocks[i].firstPage) as u64);
                }
            }
        }
    }

    fn encoded_len(&self) -> usize {
        // TODO do this without mem alloc
        let mut v = vec![];
        self.encode(&mut v);
        v.len()
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

#[inline]
fn read_page_into_buf(f: &std::rc::Rc<std::cell::RefCell<File>>, page: PageNum, buf: &mut [u8]) -> Result<()> {
    {
        let f = &mut *(f.borrow_mut());
        try!(utils::SeekPage(f, buf.len(), page));
        try!(misc::io::read_fully(f, buf));
    }
    Ok(())
}

#[inline]
fn read_and_alloc_page(f: &std::rc::Rc<std::cell::RefCell<File>>, page: PageNum, pgsz: usize) -> Result<Box<[u8]>> {
    let mut buf = vec![0; pgsz].into_boxed_slice();
    try!(read_page_into_buf(f, page, &mut buf));
    Ok(buf)
}

// TODO function is inherently inefficient when called on a segment that
// is in the header, because it loads and allocs the root page, a copy
// of which is already in the header.
fn get_blocklist_for_segment_including_root(
    page: PageNum,
    pgsz: usize,
    path: &str,
    f: std::rc::Rc<std::cell::RefCell<File>>,
    ) -> Result<BlockList> {
    let buf = try!(read_and_alloc_page(&f, page, pgsz));
    let done_page = move |_| -> () {
    };
    let buf = Lend::new(buf, box done_page);

    let pt = try!(PageType::from_u8(buf[0]));
    let mut blocks =
        match pt {
            PageType::LEAF_NODE => {
                let page = try!(LeafPage::new_already_read_page(path, f.clone(), page, buf));
                page.blocklist_unsorted()
            },
            PageType::PARENT_NODE => {
                let parent = try!(ParentPage::new_already_read_page(path, f.clone(), page, buf));
                try!(parent.blocklist_unsorted())
            },
        };
    blocks.add_page_no_reorder(page);
    Ok(blocks)
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
    // TODO should the file and pgsz be in here?
    //Overflowed(String, usize, u64, BlockList),

    Boxed(Box<[u8]>),
    // TODO consider a type representing an overflow reference with len and blocks?

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
    // TODO should the file and pgsz be in here?
    Overflowed(String, usize, u64, BlockList),
    Tombstone,
}

/// Like a ValueRef, but cannot represent a tombstone.  Available
/// only from a LivingCursor.
pub enum LiveValueRef<'a> {
    Slice(&'a [u8]),
    // TODO should the file and pgsz be in here?
    Overflowed(String, usize, u64, BlockList),
}

impl<'a> ValueRef<'a> {
    pub fn len(&self) -> Option<u64> {
        match *self {
            ValueRef::Slice(a) => Some(a.len() as u64),
            ValueRef::Overflowed(_, _, len, _) => Some(len),
            ValueRef::Tombstone => None,
        }
    }

    pub fn into_blob_for_merge(self) -> Blob {
        match self {
            ValueRef::Slice(a) => {
                let mut k = Vec::with_capacity(a.len());
                k.push_all(a);
                Blob::Boxed(k.into_boxed_slice())
            },
            ValueRef::Overflowed(path, pgsz, len, blocks) => Blob::SameFileOverflow(len, blocks),
            ValueRef::Tombstone => Blob::Tombstone,
        }
    }

}

impl<'a> std::fmt::Debug for ValueRef<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::result::Result<(), std::fmt::Error> {
        match *self {
            ValueRef::Slice(a) => write!(f, "Array, len={:?}", a),
            ValueRef::Overflowed(_, _, len, _) => write!(f, "Overflowed, len={}", len),
            ValueRef::Tombstone => write!(f, "Tombstone"),
        }
    }
}

impl<'a> LiveValueRef<'a> {
    pub fn len(&self) -> u64 {
        match *self {
            LiveValueRef::Slice(a) => a.len() as u64,
            LiveValueRef::Overflowed(_, _, len, _) => len,
        }
    }

    pub fn into_blob_for_merge(self) -> Blob {
        match self {
            LiveValueRef::Slice(a) => {
                let mut k = Vec::with_capacity(a.len());
                k.push_all(a);
                Blob::Boxed(k.into_boxed_slice())
            },
            LiveValueRef::Overflowed(path, pgsz, len, blocks) => Blob::SameFileOverflow(len, blocks),
        }
    }

    // TODO dangerous function if len() is big
    // TODO change this to return a stream, and require file/pgsz?
    #[cfg(remove_me)]
    pub fn _into_boxed_slice(self) -> Result<Box<[u8]>> {
        match self {
            LiveValueRef::Slice(a) => {
                let mut v = Vec::with_capacity(a.len());
                v.push_all(a);
                Ok(v.into_boxed_slice())
            },
            LiveValueRef::Overflowed(ref path, pgsz, len, ref blocks) => {
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
            LiveValueRef::Overflowed(ref path, pgsz, len, ref blocks) => {
                let mut a = Vec::with_capacity(len as usize);
                let mut strm = try!(OverflowReader::new(path, pgsz, blocks.blocks[0].firstPage, len));
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
            LiveValueRef::Overflowed(_, _, len, _) => write!(f, "Overflowed, len={}", len),
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

    fn eaten(self) -> Vec<(PageNum, BlockList)> {
        self.csr.eaten()
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

#[derive(Copy,Clone)]
pub struct DbSettings {
    pub DefaultPageSize: usize,
    pub PagesPerBlock: PageCount,
}

pub const DEFAULT_SETTINGS: DbSettings = 
    DbSettings {
        DefaultPageSize: 4096,
        PagesPerBlock: 256,
    };

#[derive(Debug, Clone)]
pub struct SegmentHeaderInfo {
    pub root_page: PageNum,
    buf: Box<[u8]>,
}

impl SegmentHeaderInfo {
    pub fn new(root_page: PageNum, buf: Box<[u8]>) -> Self {
        SegmentHeaderInfo {
            root_page: root_page,
            buf: buf,
        }
    }

    fn count_pages(&self) -> Result<PageCount> {
        let pt = try!(PageType::from_u8(self.buf[0]));
        match pt {
            PageType::LEAF_NODE => {
                // TODO
                Ok(0)
            },
            PageType::PARENT_NODE => {
                let count_pages = try!(ParentPage::count_pages(&self.buf));
                Ok(count_pages)
            },
        }
    }

    // note that the resulting blocklist here does not include the root page
    fn blocklist_unsorted(&self, 
                          path: &str,
                          f: std::rc::Rc<std::cell::RefCell<File>>,
                          ) -> Result<BlockList> {
        let done_page = move |_| -> () {
        };
        let buf = Lend::new(self.buf.clone(), box done_page);

        let pt = try!(PageType::from_u8(self.buf[0]));
        let blocks =
            match pt {
                PageType::LEAF_NODE => {
                    let page = try!(LeafPage::new_already_read_page(path, f.clone(), self.root_page, buf));
                    page.blocklist_unsorted()
                },
                PageType::PARENT_NODE => {
                    let parent = try!(ParentPage::new_already_read_page(path, f.clone(), self.root_page, buf));
                    try!(parent.blocklist_unsorted())
                },
            };
        Ok(blocks)
    }

    // TODO blocklist_unsorted_no_overflows is basically the same as NodeIterator
    fn blocklist_unsorted_no_overflows(&self, 
                          path: &str,
                          f: std::rc::Rc<std::cell::RefCell<File>>,
                          ) -> Result<BlockList> {
        let done_page = move |_| -> () {
        };
        let buf = Lend::new(self.buf.clone(), box done_page);

        let pt = try!(PageType::from_u8(self.buf[0]));
        let blocks =
            match pt {
                PageType::LEAF_NODE => {
                    BlockList::new()
                },
                PageType::PARENT_NODE => {
                    let parent = try!(ParentPage::new_already_read_page(path, f.clone(), self.root_page, buf));
                    try!(parent.blocklist_unsorted_no_overflows())
                },
            };
        Ok(blocks)
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

    pub fn SeekPage(strm: &mut Seek, pgsz: usize, pageNumber: PageNum) -> Result<u64> {
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
        let ba = vec![0; pgsz as usize].into_boxed_slice();
        PageBuilder { cur: 0, buf:ba } 
    }

    fn buf(&self) -> &[u8] {
        &self.buf
    }

    fn into_buf(self) -> Box<[u8]> {
        self.buf
    }

    fn Reset(&mut self) {
        self.cur = 0;
    }

    fn sofar(&self) -> usize {
        self.cur
    }

    fn Write(&self, strm: &mut Write) -> io::Result<()> {
        strm.write_all(&*self.buf)
    }

    fn Available(&self) -> usize {
        self.buf.len() - self.cur
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
    subcursors: Box<[PageCursor]>, 
    sorted: Box<[(usize, Option<Ordering>)]>,
    cur: Option<usize>, 

    overflows_eaten: Vec<(PageNum, BlockList)>,

    // TODO optimize the case where there is only one subcursor
}

impl MergeCursor {
    fn eaten(self) -> Vec<(PageNum, BlockList)> {
        self.overflows_eaten
    }

    fn sort(&mut self) -> Result<()> {
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

    fn sorted_first(&self) -> Option<usize> {
        let n = self.sorted[0].0;
        if self.sorted[0].1.is_some() {
            Some(n)
        } else {
            None
        }
    }

    fn findMin(&mut self) -> Result<Option<usize>> {
        if self.subcursors.is_empty() {
            Ok(None)
        } else {
            try!(self.sort());
            Ok(self.sorted_first())
        }
    }

    fn new(subs: Vec<PageCursor>) -> MergeCursor {
        let s = subs.into_boxed_slice();
        let mut sorted = Vec::with_capacity(s.len());
        for i in 0 .. s.len() {
            sorted.push((i, None));
        }
        MergeCursor { 
            subcursors: s, 
            sorted: sorted.into_boxed_slice(), 
            cur: None, 
            overflows_eaten: vec![],
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
                                {
                                    let v = try!(self.subcursors[n].ValueRef());
                                    match v {
                                        ValueRef::Overflowed(path, pgsz, len, blocks) => {
                                            let k = try!(self.subcursors[n].KeyRef());
                                            //println!("eaten: {:?} -- {:?}", k, blocks);
                                            self.overflows_eaten.push((self.subcursors[n].pagenum(), blocks));
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
            },
        }
    }

}

pub struct LivingCursor { 
    chain: Lend<MultiCursor>,
}

impl LivingCursor {
    pub fn LiveValueRef<'a>(&'a self) -> Result<LiveValueRef<'a>> {
        match try!(self.chain.ValueRef()) {
            ValueRef::Slice(a) => Ok(LiveValueRef::Slice(a)),
            ValueRef::Overflowed(path, pgsz, len, blocks) => Ok(LiveValueRef::Overflowed(path, pgsz, len, blocks)),
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

    fn new(ch: Lend<MultiCursor>) -> LivingCursor {
        LivingCursor { chain: ch }
    }
}

impl IForwardCursor for LivingCursor {
    fn First(&mut self) -> Result<()> {
        try!(self.chain.First());
        try!(self.skipTombstonesForward());
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
        try!(self.chain.Next());
        try!(self.skipTombstonesForward());
        Ok(())
    }

}

impl ICursor for LivingCursor {
    fn Last(&mut self) -> Result<()> {
        try!(self.chain.Last());
        try!(self.skipTombstonesBackward());
        Ok(())
    }

    fn Prev(&mut self) -> Result<()> {
        try!(self.chain.Prev());
        try!(self.skipTombstonesBackward());
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
                    try!(self.skipTombstonesForward());
                    SeekResult::from_cursor(&*self.chain, k)
                } else {
                    Ok(sr)
                }
            },
            SeekOp::SEEK_LE => {
                if sr.is_valid() && self.chain.ValueLength().unwrap().is_none() {
                    try!(self.skipTombstonesBackward());
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
enum BlocksForParent {
    List(BlockList),
    Count(PageCount),
}

#[derive(Debug, Clone)]
// this struct is used to remember pages we have written, and to
// provide info needed to write parent nodes.
// TODO rename, revisit pub, etc
// TODO ChildItem?
pub struct pgitem {
    pub page: PageNum,
    blocks: BlocksForParent,
    // blocks does NOT contain page

    first_key: KeyWithLocation,
    last_key: Option<KeyWithLocation>,
}

impl pgitem {
    #[cfg(remove_me)]
    fn new(page: PageNum, blocks: BlockList, first_key: KeyWithLocation, last_key: Option<KeyWithLocation>) -> pgitem {
        assert!(!blocks.contains_page(page));
        pgitem {
            page: page,
            blocks: blocks,
            first_key: first_key,
            last_key: last_key,
        }
    }

    fn need(&self, prefix_len: usize, depth: u8) -> usize {
        let needed = 
            varint::space_needed_for(self.page as u64) 
            //if cfg!(child_block_list) 
            + match &self.blocks {
                &BlocksForParent::List(ref blocks) => {
                    assert!(depth == 1);
                    blocks.encoded_len()
                },
                &BlocksForParent::Count(count) => {
                    assert!(depth > 1);
                    varint::space_needed_for(count as u64)
                },
            }
            + self.first_key.need(prefix_len)
            + 
            match self.last_key {
                Some(ref last_key) => {
                    last_key.need(prefix_len)
                },
                None => {
                    varint::space_needed_for(0)
                },
            };
        needed
    }

    fn key_in_range(&self, k: &[u8]) -> Result<KeyInRange> {
        match self.last_key {
            Some(ref last_key) => {
                match k.cmp(&last_key.key) {
                    Ordering::Less => {
                        match k.cmp(&self.first_key.key) {
                            Ordering::Less => {
                                Ok(KeyInRange::Less)
                            },
                            Ordering::Equal => {
                                Ok(KeyInRange::EqualFirst)
                            },
                            Ordering::Greater => {
                                Ok(KeyInRange::Within)
                            },
                        }
                    },
                    Ordering::Equal => {
                        return Ok(KeyInRange::EqualLast);
                    },
                    Ordering::Greater => {
                        return Ok(KeyInRange::Greater);
                    },
                }
            },
            None => {
                match k.cmp(&self.first_key.key) {
                    Ordering::Less => {
                        Ok(KeyInRange::Less)
                    },
                    Ordering::Equal => {
                        Ok(KeyInRange::EqualFirst)
                    },
                    Ordering::Greater => {
                        Ok(KeyInRange::Greater)
                    },
                }
            },
        }
    }

    fn verify(&self,
              pgsz: usize,
              path: &str, 
              f: std::rc::Rc<std::cell::RefCell<File>>,
             ) -> Result<()> {

        let buf = try!(read_and_alloc_page(&f, self.page, pgsz));
        let done_page = move |_| -> () {
        };
        let buf = Lend::new(buf, box done_page);

        let pt = try!(PageType::from_u8(buf[0]));
        match pt {
            PageType::LEAF_NODE => {
                let page = try!(LeafPage::new_already_read_page(path, f.clone(), self.page, buf));
                let range = try!(page.range()).into_keyrange();
                assert!(Ordering::Equal == range.min.cmp(&self.first_key.key));
                match self.last_key {
                    Some(ref last_key) => {
                        assert!(Ordering::Equal == range.max.cmp(&last_key.key));
                    },
                    None => {
                        assert!(page.count_keys() == 1);
                    },
                }
            },
            PageType::PARENT_NODE => {
                let parent = try!(ParentPage::new_already_read_page(path, f.clone(), self.page, buf));
                let range = try!(parent.range()).into_keyrange();
                assert!(Ordering::Equal == range.min.cmp(&self.first_key.key));
                match self.last_key {
                    Some(ref last_key) => {
                        assert!(Ordering::Equal == range.max.cmp(&last_key.key));
                    },
                    None => {
                        assert!(parent.count_items() == 1);
                        assert!(parent.children[0].last_key.is_none());
                        // TODO and assert the only child also has only one key
                        let pg = try!(parent.child_pgitem(0));
                        assert!(pg.last_key.is_none());
                        try!(pg.verify(pgsz, path, f.clone()));
                    },
                }
                try!(parent.verify_child_keys());
            },
        }
        Ok(())
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
    prev_key: Option<Box<[u8]>>,

}

fn write_overflow(
                    ba: &mut Read, 
                    pw: &mut PageWriter,
                    limit : usize,
                   ) -> Result<(u64, BlockList)> {

    fn write_page(ba: &mut Read, pb: &mut PageBuilder, pgsz: usize, pw: &mut PageWriter, blocks: &mut BlockList, limit: usize) -> Result<(usize, bool)> {
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

fn build_leaf(st: &mut LeafState, pb: &mut PageBuilder) -> (KeyWithLocation, Option<KeyWithLocation>, BlockList, usize) {
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

    fn f(pb: &mut PageBuilder, prefixLen: usize, lp: &LeafPair, list: &mut BlockList) {
        match lp.key.location {
            KeyLocation::Inline => {
                pb.PutVarint(lp.key.len_with_overflow_flag());
                pb.PutArray(&lp.key.key[prefixLen .. ]);
            },
            KeyLocation::Overflowed(ref blocks) => {
                pb.PutVarint(lp.key.len_with_overflow_flag());
                // TODO capacity, no temp vec
                let mut v = vec![];
                blocks.encode(&mut v);
                pb.PutArray(&v);
                list.add_blocklist_no_reorder(blocks);
            },
        }
        match lp.value {
            ValueLocation::Tombstone => {
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
                // TODO capacity, no temp vec
                let mut v = vec![];
                blocks.encode(&mut v);
                pb.PutArray(&v);
                list.add_blocklist_no_reorder(blocks);
            },
        }
    }

    let mut blocks = BlockList::new();

    // deal with the first key separately
    let first_key = {
        let lp = st.keys_in_this_leaf.remove(0); 
        assert!(st.keys_in_this_leaf.len() == count_keys_in_this_leaf - 1);
        f(pb, st.prefixLen, &lp, &mut blocks);
        lp.key
    };

    if st.keys_in_this_leaf.len() == 0 {
        // there was only one key in this leaf.
        blocks.sort_and_consolidate();
        (first_key, None, blocks, pb.sofar())
    } else {
        if st.keys_in_this_leaf.len() > 1 {
            // deal with all the remaining keys except the last one
            for lp in st.keys_in_this_leaf.drain(0 .. count_keys_in_this_leaf - 2) {
                f(pb, st.prefixLen, &lp, &mut blocks);
            }
        }
        assert!(st.keys_in_this_leaf.len() == 1);

        // now the last key
        let last_key = {
            let lp = st.keys_in_this_leaf.remove(0); 
            assert!(st.keys_in_this_leaf.is_empty());
            f(pb, st.prefixLen, &lp, &mut blocks);
            lp.key
        };
        blocks.sort_and_consolidate();
        (first_key, Some(last_key), blocks, pb.sofar())
    }
}

fn write_leaf(st: &mut LeafState, 
                pb: &mut PageBuilder, 
                pw: &mut PageWriter,
               ) -> Result<(usize, pgitem)> {
    let (first_key, last_key, blocks, len_page) = build_leaf(st, pb);
    //println!("leaf blocklist: {:?}", blocks);
    //println!("leaf blocklist, len: {}   encoded_len: {:?}", blocks.len(), blocks.encoded_len());
    assert!(st.keys_in_this_leaf.is_empty());
    let thisPageNumber = try!(pw.write_page(pb.buf()));
    assert!(!blocks.contains_page(thisPageNumber));
    // TODO pgitem::new
    let pg = pgitem {
        page: thisPageNumber, 
        blocks: BlocksForParent::List(blocks),
        first_key: first_key,
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
            let (len, blocks) = try!(write_overflow(&mut &*k, pw, hard_limit));
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
                    let (len, blocks) = try!(write_overflow(&mut &*a, pw, hard_limit_for_value_overflow));
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

    let fits = {
        let would_be_prefix_len = calc_prefix_len(&st, &k, &kloc);
        assert!(would_be_prefix_len <= k.len());
        let would_be_sofar = 
            if would_be_prefix_len != st.prefixLen {
                assert!(st.prefixLen == 0 || would_be_prefix_len < st.prefixLen);
                // the prefixLen would change with the addition of this key,
                // so we need to recalc sofar
                let sum = st.keys_in_this_leaf.iter().map(|lp| lp.need(would_be_prefix_len) ).sum();;
                sum
            } else {
                st.sofarLeaf
            };
        let would_be_len_page = calc_leaf_page_len(would_be_prefix_len, would_be_sofar);
        if pgsz > would_be_len_page {
            let available = pgsz - would_be_len_page;
            let needed = kloc.need(&k, would_be_prefix_len) + vloc.need();
            available >= needed
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
            Some(pg)
        } else {
            None
        };

    // see if the prefix len actually did change
    let new_prefix_len = calc_prefix_len(&st, &k, &kloc);
    assert!(new_prefix_len <= k.len());
    let sofar = 
        if new_prefix_len != st.prefixLen {
            assert!(st.prefixLen == 0 || new_prefix_len < st.prefixLen);
            // the prefixLen will change with the addition of this key,
            // so we need to recalc sofar
            let sum = st.keys_in_this_leaf.iter().map(|lp| lp.need(new_prefix_len) ).sum();;
            sum
        } else {
            st.sofarLeaf
        };
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

    st.sofarLeaf = sofar + lp.need(new_prefix_len);
    st.prefixLen = new_prefix_len;
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

    let mut chain = ParentNodeWriter::new(pw.page_size(), 0);

    for result_pair in pairs {
        let pair = try!(result_pair);
        if let Some(pg) = try!(process_pair_into_leaf(&mut st, &mut pb, pw, &mut vbuf, pair)) {
            //try!(pg.verify(pw.page_size(), path, f.clone()));
            try!(chain.add_child(pw, pg));
        }
    }
    if let Some(pg) = try!(flush_leaf(&mut st, &mut pb, pw)) {
        //try!(pg.verify(pw.page_size(), path, f.clone()));
        try!(chain.add_child(pw, pg));
    }

    // TODO this assumes the last page written is still in pb.  it has to be.
    // TODO unless it wrote no pages?
    let (count_parent_nodes, seg) = try!(chain.done(pw, pb.into_buf()));

    Ok(seg)
}

struct WroteMerge {
    segment: Option<SegmentHeaderInfo>,
    leaves_rewritten: Vec<PageNum>,
    overflows_freed: Vec<BlockList>, // TODO in rewritten leaves
}

fn merge_process_pair(
    pair: kvp,
    st: &mut LeafState,
    pb: &mut PageBuilder,
    pw: &mut PageWriter,
    vbuf: &mut [u8],
    behind: &mut Vec<PageCursor>,
    chain: &mut ParentNodeWriter,
    dest_level: DestLevel,
    ) -> Result<()>
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
        match dest_level {
            DestLevel::Young | DestLevel::Other(0) => {
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
            _ => {
                assert!(behind.is_empty());
                true
            },
        };
    if keep {
        if let Some(pg) = try!(process_pair_into_leaf(st, pb, pw, vbuf, pair)) {
            try!(chain.add_child(pw, pg));
        }
    }

    Ok(())
}

fn merge_rewrite_leaf(
                    st: &mut LeafState,
                    pb: &mut PageBuilder,
                    pw: &mut PageWriter,
                    vbuf: &mut [u8],
                    pairs: &mut CursorIterator,
                    leafreader: &mut LeafPage,
                    behind: &mut Vec<PageCursor>,
                    chain: &mut ParentNodeWriter,
                    overflows_freed: &mut Vec<BlockList>,
                    dest_level: DestLevel,
                    ) -> Result<(usize, usize)> {

    #[derive(Debug)]
    enum Action {
        Pairs,
        LeafPair(usize),
    }

    let mut cur_in_other = Some(0); // TODO no need for this to be an option
    let mut keys_promoted = 0;
    let mut keys_rewritten = 0;

    loop {
        let action = 
            match (pairs.peek(), cur_in_other) {
                (Some(&Err(ref e)), _) => {
                    // TODO have the action return this error
                    return Err(Error::Misc(format!("inside error pairs: {}", e)));
                },
                (Some(&Ok(ref peek_pair)), Some(i)) => {
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
                            // whatever value is coming from the rewritten leaf, it is superceded
// TODO if the key was overflowed, we need that too.
                            let pair = try!(leafreader.kvp_for_merge(i));
                            match &pair.Value {
                                &Blob::SameFileOverflow(_, ref blocks) => {
                                    overflows_freed.push(blocks.clone());
                                },
                                _ => {
                                },
                            }
                            if i + 1 < leafreader.count_keys() {
                                cur_in_other = Some(i + 1);
                            } else {
                                cur_in_other = None;
                            }
                            Action::Pairs
                        },
                        Ordering::Less => {
                            if i + 1 < leafreader.count_keys() {
                                cur_in_other = Some(i + 1);
                            } else {
                                cur_in_other = None;
                            }
                            Action::LeafPair(i)
                        },
                    }
                },
                (None, Some(i)) => {
                    if i + 1 < leafreader.count_keys() {
                        cur_in_other = Some(i + 1);
                    } else {
                        cur_in_other = None;
                    }
                    Action::LeafPair(i)
                },
                (Some(&Ok(_)), None) => {
                    break;
                },
                (None, None) => {
                    break;
                },
            };
        //println!("dest,{:?},action,{:?}", dest_level, action);
        match action {
            Action::Pairs => {
                let pair = try!(misc::inside_out(pairs.next())).unwrap();
                try!(merge_process_pair(pair, st, pb, pw, vbuf, behind, chain, dest_level));
                keys_promoted += 1;
            },
            Action::LeafPair(i) => {
                let pair = try!(leafreader.kvp_for_merge(i));
                // TODO it is interesting to note that (in not-very-thorough testing), if we
                // put a tombstone check here, it never skips a tombstone.
                if let Some(pg) = try!(process_pair_into_leaf(st, pb, pw, vbuf, pair)) {
                    try!(chain.add_child(pw, pg));
                }
                keys_rewritten += 1;
            },
        }
    }

    //println!("dest,{:?},keys_promoted,{},keys_rewritten,{}", dest_level, keys_promoted, keys_rewritten);

    Ok((keys_promoted, keys_rewritten))
}

fn write_merge<J: Iterator<Item=Result<pgitem>>>(
                    pw: &mut PageWriter,
                    pairs: &mut CursorIterator,
                    mut leaves: J,
                    behind: &mut Vec<PageCursor>,
                    path: &str,
                    f: std::rc::Rc<std::cell::RefCell<File>>,
                    dest_level: DestLevel,
                    ) -> Result<WroteMerge> {

    // TODO could pb and vbuf move into LeafState?

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

    let mut chain = ParentNodeWriter::new(pw.page_size(), 0);

    #[derive(Debug)]
    enum Action {
        Pairs,
        RewriteLeaf,
        RecycleLeaf,
        Done,
    }

    // TODO how would this algorithm be adjusted to work at a different depth?
    // like, suppose instead of leaves, we were given depth 1 parents?

    let mut leafreader = LeafPage::new(path, f.clone(), pw.page_size(), );

    let mut leaves = leaves.peekable();

    let mut keys_promoted = 0;
    let mut keys_rewritten = 0;
    let mut leaves_recycled = 0;
    let mut leaves_rewritten = vec![];
    let mut overflows_freed = vec![];

    loop {
        let action = 
            match (pairs.peek(), leaves.peek()) {
                (Some(&Err(ref e)), _) => {
                    // TODO have the action return this error
                    return Err(Error::Misc(format!("inside error pairs: {}", e)));
                },
                (_, Some(&Err(ref e))) => {
                    // TODO have the action return this error
                    return Err(Error::Misc(format!("inside error other: {}", e)));
                },
                (Some(&Ok(_)), None) => {
                    Action::Pairs
                },
                (None, Some(&Ok(_))) => {
                    Action::RecycleLeaf
                },
                (Some(&Ok(ref peek_pair)), Some(&Ok(ref peek_pg))) => {
                    match try!(peek_pg.key_in_range(&peek_pair.Key)) {
                        KeyInRange::Less => {
                            Action::Pairs
                        },
                        KeyInRange::Greater => {
                            // TODO we *could* decide to rewrite this leaf anyway.
                            // like, for example, if the leaf we have been constructing is
                            // mostly empty.

                            Action::RecycleLeaf
                        },
                        KeyInRange::EqualFirst | KeyInRange::EqualLast | KeyInRange::Within => {
                            // TODO technically, EqualFirst could start at 1, since the first key
                            // of the rewritten page will get skipped anyway because it is equal to
                            // the current key from the merge.

                            // TODO EqualLast could just ignore the other leaf, since it won't matter.

                            Action::RewriteLeaf
                        },
                    }
                },
                (None, None) => {
                    Action::Done
                },
            };
        //println!("dest,{:?},action,{:?}", dest_level, action);
        match action {
            Action::Pairs => {
                let pair = try!(misc::inside_out(pairs.next())).unwrap();
                try!(merge_process_pair(pair, &mut st, &mut pb, pw, &mut vbuf, behind, &mut chain, dest_level));
                keys_promoted += 1;
            },
            Action::RecycleLeaf => {
                if let Some(pg) = try!(flush_leaf(&mut st, &mut pb, pw)) {
                    try!(chain.add_child(pw, pg));
                }
                let pg = try!(misc::inside_out(leaves.next())).unwrap();
                try!(chain.add_child(pw, pg));
                leaves_recycled += 1;
            },
            Action::RewriteLeaf => {
                let pg = try!(misc::inside_out(leaves.next())).unwrap();
                leaves_rewritten.push(pg.page);
                try!(leafreader.read_page(pg.page));
                let (leaf_keys_promoted, leaf_keys_rewritten) = try!(merge_rewrite_leaf(&mut st, &mut pb, pw, &mut vbuf, pairs, &mut leafreader, behind, &mut chain, &mut overflows_freed, dest_level));
                keys_promoted += leaf_keys_promoted;
                keys_rewritten += leaf_keys_rewritten;
            },
            Action::Done => {
                if let Some(pg) = try!(flush_leaf(&mut st, &mut pb, pw)) {
                    //println!("dest,{:?},child,{:?}", dest_level, pg);
                    try!(chain.add_child(pw, pg));
                } else {
                    //println!("dest,{:?},empty_done", dest_level);
                }
                break;
            },
        }
    }

// TODO currently key overflows never get reused, do they?

    // TODO this assumes the last page written is still in pb.  it has to be.
    // TODO unless it wrote no pages?
    let (count_parent_nodes, seg) = try!(chain.done(pw, pb.into_buf()));

    println!("dest,{:?},leaves_rewritten,{},leaves_recycled,{},keys_promoted,{},keys_rewritten,{},count_parent_nodes,{}", dest_level, leaves_rewritten.len(), leaves_recycled, keys_promoted, keys_rewritten, count_parent_nodes);

    let wrote = WroteMerge {
        segment: seg,
        leaves_rewritten: leaves_rewritten,
        overflows_freed: overflows_freed,
    };
    Ok(wrote)
}

struct ParentNodeWriter {
    pb: PageBuilder,
    st: ParentState,
    prev_child: Option<pgitem>,
    depth: u8,

    result_one: Option<pgitem>,
    results_chain: Option<Box<ParentNodeWriter>>,

    count_emit: usize,
}

impl ParentNodeWriter {
    fn new(
        pgsz: usize, 
        children_depth: u8,
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
            depth: children_depth + 1,
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
                // TODO capacity, no temp vec
                let mut v = vec![];
                blocks.encode(&mut v);
                self.pb.PutArray(&v);
            },
        }
    }

    fn put_item(&mut self, count_pages: &mut PageCount, item: &pgitem, prefix_len: usize) {
        self.pb.PutVarint(item.page as u64);
        *count_pages += 1;
        match &item.blocks {
            &BlocksForParent::List(ref blocks) => {
                assert!(self.depth == 1);
                // TODO capacity, no temp vec
                let mut v = vec![];
                blocks.encode(&mut v);
                self.pb.PutArray(&v);
                *count_pages += blocks.count_pages();
            },
            &BlocksForParent::Count(count) => {
                assert!(self.depth > 1);
                self.pb.PutVarint(count as u64);
                *count_pages += count;
            },
        }

        self.pb.PutVarint(item.first_key.len_with_overflow_flag());
        self.put_key(&item.first_key, prefix_len);

        match item.last_key {
            Some(ref last_key) => {
                self.pb.PutVarint(last_key.len_with_overflow_flag());
                self.put_key(&last_key, prefix_len);
            },
            None => {
                self.pb.PutVarint(0);
            },
        }
    }

    fn build_parent_page(&mut self,
                      ) -> (KeyWithLocation, Option<KeyWithLocation>, PageCount, usize) {
        // TODO? assert!(st.items.len() > 1);
        //println!("build_parent_page, prefixLen: {:?}", st.prefixLen);
        //println!("build_parent_page, items: {:?}", st.items);
        self.pb.Reset();
        self.pb.PutByte(PageType::PARENT_NODE.to_u8());
        self.pb.PutByte(0u8);
        self.pb.PutByte(self.depth);
        self.pb.PutVarint(self.st.prefixLen as u64);
        if self.st.prefixLen > 0 {
            self.pb.PutArray(&self.st.items[0].first_key.key[0 .. self.st.prefixLen]);
        }
        self.pb.PutInt16(self.st.items.len() as u16);
        //println!("self.st.items.len(): {}", self.st.items.len());

        let mut count_pages = 0;

        // deal with the first item separately
        let (first_key, last_key_from_first_item) = {
            let item = self.st.items.remove(0); 
            let prefix_len = self.st.prefixLen;
            self.put_item(&mut count_pages, &item, prefix_len);
            (item.first_key, item.last_key)
        };

        if self.st.items.len() == 0 {
            // there was only one item in this page
            (first_key, last_key_from_first_item, count_pages, self.pb.sofar())
        } else {
            if self.st.items.len() > 1 {
                // deal with all the remaining items except the last one
                let tmp_count = self.st.items.len() - 1;
                let tmp_vec = self.st.items.drain(0 .. tmp_count).collect::<Vec<_>>();
                let prefix_len = self.st.prefixLen;
                for item in tmp_vec {
                    self.put_item(&mut count_pages, &item, prefix_len);
                }
            }
            assert!(self.st.items.len() == 1);

            // now the last item
            let last_key = {
                let item = self.st.items.remove(0); 
                let prefix_len = self.st.prefixLen;
                self.put_item(&mut count_pages, &item, prefix_len);
                match item.last_key {
                    Some(last_key) => last_key,
                    None => item.first_key,
                }
            };
            assert!(self.st.items.is_empty());

            (first_key, Some(last_key), count_pages, self.pb.sofar())
        }
    }

    fn write_parent_page(&mut self,
                          pw: &mut PageWriter,
                         ) -> Result<(usize, pgitem)> {
        // assert st.sofar > 0
        let (first_key, last_key, count_pages, len_page) = self.build_parent_page();
        assert!(self.st.items.is_empty());
        //println!("parent blocklist: {:?}", blocks);
        //println!("parent blocklist, len: {}   encoded_len: {:?}", blocks.len(), blocks.encoded_len());
        let thisPageNumber = try!(pw.write_page(self.pb.buf()));
        // TODO pgitem::new
        let pg = pgitem {
            page: thisPageNumber, 
            blocks: BlocksForParent::Count(count_pages),
            first_key: first_key,
            last_key: last_key,
        };
        self.st.sofar = 0;
        self.st.prefixLen = 0;
        Ok((len_page, pg))
    }

    fn calc_prefix_len(&self, item: &pgitem) -> usize {
        if self.st.items.is_empty() {
            match item.last_key {
                Some(ref last_key) => {
                    bcmp::PrefixMatch(&*item.first_key.key, &last_key.key, last_key.key.len())
                },
                None => {
                    item.first_key.key.len()
                },
            }
        } else {
            if self.st.prefixLen > 0 {
                let a =
                    match &item.first_key.location {
                        &KeyLocation::Inline => {
                            bcmp::PrefixMatch(&*self.st.items[0].first_key.key, &item.first_key.key, self.st.prefixLen)
                        },
                        &KeyLocation::Overflowed(_) => {
                            // an overflowed key does not change the prefix
                            self.st.prefixLen
                        },
                    };
                let b = 
                    match item.last_key {
                        Some(ref last_key) => {
                            match &last_key.location {
                                &KeyLocation::Inline => {
                                    bcmp::PrefixMatch(&*self.st.items[0].first_key.key, &last_key.key, a)
                                },
                                &KeyLocation::Overflowed(_) => {
                                    // an overflowed key does not change the prefix
                                    a
                                },
                            }
                        },
                        None => {
                            a
                        },
                    };
                b
            } else {
                0
            }
        }
    }

    fn add_child(&mut self, pw: &mut PageWriter, child: pgitem) -> Result<()> {
        let pgsz = pw.page_size();

        if cfg!(expensive_check) 
        {
            // TODO FYI this code is the only reason we need to derive Clone on
            // pgitem and its parts
            match self.prev_child {
                None => {
                },
                Some(ref prev_child) => {
                    let c = child.first_key.key.cmp(&prev_child.first_key.key);
                    if c != Ordering::Greater {
                        println!("prev_child first_key: {:?}", prev_child.first_key);
                        println!("cur child first_key: {:?}", child.first_key);
                        panic!("unsorted child pages");
                    }
                    match &prev_child.last_key {
                        &Some(ref last_key) => {
                            let c = child.first_key.key.cmp(&last_key.key);
                            if c != Ordering::Greater {
                                println!("prev_child first_key: {:?}", prev_child.first_key);
                                println!("prev_child last_key: {:?}", last_key);
                                println!("cur child first_key: {:?}", child.first_key);
                                panic!("overlapping child pages");
                            }
                        },
                        &None => {
                        },
                    }
                },
            }
            self.prev_child = Some(child.clone());
        }

        // to fit this child into this parent page, we need room for
        // the root page
        // the block list
        // prefixLen, varint
        // (prefix)
        // key len 1, varint, shifted for overflow flag
        // key 1
        //     if inline, the key, minus prefix
        //     if overflow, the blocklist (borrowed from child)
        // key len 2, varint, shifted for overflow flag, 0 if absent
        // key 2, if present
        //     if inline, the key, minus prefix
        //     if overflow, the blocklist (borrowed from child)

        // each key is stored just as it was in the child, inline or overflow.
        // if it is overflowed, we just store the same blocklist reference.

        // claim:  if both keys fit inlined in the child, they can both
        // fit inlined here in the parent page.

        let fits = {
            let would_be_prefix_len = self.calc_prefix_len(&child);
            let would_be_sofar = 
                if would_be_prefix_len != self.st.prefixLen {
                    assert!(self.st.prefixLen == 0 || would_be_prefix_len < self.st.prefixLen);
                    // the prefixLen would change with the addition of this key,
                    // so we need to recalc sofar
                    let sum = self.st.items.iter().map(|lp| lp.need(would_be_prefix_len, self.depth) ).sum();;
                    sum
                } else {
                    self.st.sofar
                };
            let would_be_len_page = Self::calc_page_len(would_be_prefix_len, would_be_sofar);
            if pgsz > would_be_len_page {
                let available = pgsz - would_be_len_page;
                let fits = available >= child.need(would_be_prefix_len, self.depth);
                if !fits && self.st.items.len() == 0 {
                    println!("would_be_len_page: {}", would_be_len_page);
                    println!("would_be_so_far: {}", would_be_sofar);
                    println!("child: {:?}", child);
                    println!("child need: {}",child.need(would_be_prefix_len, self.depth));
                    //println!("child blocklist blocks: {}", child.blocks.len());
                    //println!("child blocklist pages: {}", child.blocks.count_pages());
                    //println!("child blocklist encoded_len: {}", child.blocks.encoded_len());
                    panic!();
                }
                fits
            } else {
                if self.st.items.len() == 0 {
                    println!("would_be_len_page: {}", would_be_len_page);
                    println!("would_be_so_far: {}", would_be_sofar);
                    println!("child: {:?}", child);
                    panic!();
                }
                false
            }
        };

        if !fits {
            // if the assert below fires, that's bad.  it means we have a child item which
            // is too small for a parent page even if it is the only thing on that page.
            // it probably means the block list for that child item got out of control.
            //println!("emitting a parent page of depth {} with {} items", self.depth, self.st.items.len());
            assert!(self.st.items.len() > 0);
            let should_be = Self::calc_page_len(self.st.prefixLen, self.st.sofar);
            let (len_page, pg) = try!(self.write_parent_page(pw));
            // TODO try!(pg.verify(pw.page_size(), path, f.clone()));
            try!(self.emit(pw, pg));
            //println!("should_be = {}   len_page = {}", should_be, len_page);
            assert!(should_be == len_page);
            assert!(self.st.items.is_empty());
        }

        // see if the prefix len actually did change
        let new_prefix_len = self.calc_prefix_len(&child);
        let sofar = 
            if new_prefix_len != self.st.prefixLen {
                assert!(self.st.prefixLen == 0 || new_prefix_len < self.st.prefixLen);
                // the prefixLen changed with the addition of this item,
                // so we need to recalc sofar
                let sum = self.st.items.iter().map(|lp| lp.need(new_prefix_len, self.depth) ).sum();;
                sum
            } else {
                self.st.sofar
            };
        self.st.sofar = sofar + child.need(new_prefix_len, self.depth);
        self.st.prefixLen = new_prefix_len;
        self.st.items.push(child);

        Ok(())
    }

    fn emit(&mut self, pw: &mut PageWriter, pg: pgitem) -> Result<()> {
        self.count_emit += 1;
        if self.results_chain.is_some() {
            assert!(self.result_one.is_none());
            let mut chain = self.results_chain.as_mut().unwrap();
            try!(chain.add_child(pw, pg));
        } else if self.result_one.is_some() {
            let first = self.result_one.take().unwrap();
            //println!("adding a depth level: {}", self.depth);
            let mut chain = ParentNodeWriter::new(self.pb.buf.len(), self.depth);
            try!(chain.add_child(pw, first));
            try!(chain.add_child(pw, pg));
            self.results_chain = Some(box chain);
        } else {
            self.result_one = Some(pg);
        }
        Ok(())
    }

    fn flush_page(&mut self, pw: &mut PageWriter) -> Result<()> {
        if !self.st.items.is_empty() {
            let should_be = Self::calc_page_len(self.st.prefixLen, self.st.sofar);
            let (len_page, pg) = try!(self.write_parent_page(pw));
            // TODO try!(pg.verify(pw.page_size(), path, f.clone()));
            try!(self.emit(pw, pg));
            //println!("should_be = {}   len_page = {}", should_be, len_page);
            assert!(should_be == len_page);
            assert!(self.st.items.is_empty());
        }
        Ok(())
    }

    fn done(mut self, pw: &mut PageWriter, buf_last_child: Box<[u8]>) -> Result<(usize, Option<SegmentHeaderInfo>)> {
        if self.result_one.is_none() && self.results_chain.is_none() && self.st.items.len() == 1 {
            let pg = self.st.items.remove(0);
            let seg = SegmentHeaderInfo::new(pg.page, buf_last_child);
            assert!(self.count_emit == 0);
            Ok((self.count_emit, Some(seg)))
        } else {
            try!(self.flush_page(pw));
            assert!(self.st.items.is_empty());
            if let Some(chain) = self.results_chain {
                assert!(self.result_one.is_none());
                // TODO this assumes the last page written is still in pb.  it has to be.
                // TODO unless it wrote no pages?
                let buf = self.pb.into_buf();
                let (count_chain, seg) = try!(chain.done(pw, buf));
                Ok((self.count_emit + count_chain, seg))
            } else if let Some(pg) = self.result_one {
                // TODO this assumes the last page written is still in pb.  it has to be.
                // TODO unless it wrote no pages?
                let buf = self.pb.into_buf();
                let seg = SegmentHeaderInfo::new(pg.page, buf);
                assert!(self.count_emit == 1);
                Ok((self.count_emit, Some(seg)))
            } else {
                assert!(self.count_emit == 0);
                Ok((self.count_emit, None))
            }
        }
    }

}

fn create_segment<I>(mut pw: PageWriter, 
                        source: I,
                        f: std::rc::Rc<std::cell::RefCell<File>>,
                       ) -> Result<Option<SegmentHeaderInfo>> where I: Iterator<Item=Result<kvp>> {

    let seg = try!(write_leaves(&mut pw, source));

    try!(pw.end());

    Ok(seg)
}

struct OverflowReader {
    fs: File,
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
    fn new(path: &str, pgsz: usize, firstPage: PageNum, len: u64) -> Result<OverflowReader> {
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
                bytesOnThisPage: 0,
                offsetOnThisPage: 0,
            };
        try!(res.ReadPage());
        Ok(res)
    }

    // TODO consider supporting Seek trait

    fn ReadPage(&mut self) -> Result<()> {
        try!(utils::SeekPage(&mut self.fs, self.buf.len(), self.currentPage));
        try!(misc::io::read_fully(&mut self.fs, &mut *self.buf));
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
    path: String,
    f: std::rc::Rc<std::cell::RefCell<File>>,
    pr: Lend<Box<[u8]>>,
    pagenum: PageNum,

    prefix: Option<Box<[u8]>>,

    pairs: Vec<PairInLeaf>,
    bytes_used_on_page: usize,
}

impl LeafPage {
    fn new_already_read_page(path: &str, 
           f: std::rc::Rc<std::cell::RefCell<File>>,
           pagenum: PageNum,
           buf: Lend<Box<[u8]>>
          ) -> Result<LeafPage> {

        let mut pairs = vec![];
        let (prefix, bytes_used_on_page) = try!(Self::parse_page(&buf, &mut pairs));

        let mut res = LeafPage {
            path: String::from(path),
            f: f,
            pagenum: pagenum,
            pr: buf,
            pairs: pairs,
            prefix: prefix,
            bytes_used_on_page: bytes_used_on_page,
        };

        Ok(res)
    }

    fn new(
        path: &str, 
           f: std::rc::Rc<std::cell::RefCell<File>>,
           pgsz: usize,
          ) -> LeafPage {

        // TODO it's a little silly here to construct a Lend<>
        let buf = vec![0; pgsz].into_boxed_slice();
        let done_page = move |_| -> () {
        };
        let mut buf = Lend::new(buf, box done_page);

        let res = LeafPage {
            path: String::from(path),
            f: f,
            pagenum: 0,
            pr: buf,
            pairs: Vec::new(),
            prefix: None,
            bytes_used_on_page: 0, // temporary
        };

        res
    }

    fn count_keys(&self) -> usize {
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

    pub fn blocklist_unsorted_no_overflows(&self) -> BlockList {
        BlockList::new()
    }

    fn overlaps(&self, range: &KeyRange) -> Result<Overlap> {
        // TODO get a KeyRangeRef first?
        match try!(self.key(0)).compare_with(&range.max) {
            Ordering::Greater => {
                Ok(Overlap::Greater)
            },
            Ordering::Less | Ordering::Equal => {
                let last_pair = self.pairs.len() - 1;
                match try!(self.key(last_pair)).compare_with(&range.min) {
                    Ordering::Less => {
                        Ok(Overlap::Less)
                    },
                    Ordering::Greater | Ordering::Equal => {
                        Ok(Overlap::Yes)
                    },
                }
            },
        }
    }

    fn first_key_with_location(&self) -> Result<KeyWithLocation> {
        self.key_with_location(0)
    }

    fn last_key_with_location(&self) -> Result<Option<KeyWithLocation>> {
        if self.pairs.len() == 1 {
            Ok(None)
        } else {
            let i = self.pairs.len() - 1;
            let kw = try!(self.key_with_location(i));
            Ok(Some(kw))
        }
    }

    fn pgitem(&self) -> Result<pgitem> {
        let mut blocks = self.blocklist_unsorted();
        blocks.sort_and_consolidate();
        assert!(!blocks.contains_page(self.pagenum));
        let first_key = try!(self.first_key_with_location());
        let last_key = try!(self.last_key_with_location());
        // TODO pgitem::new
        let pg = pgitem {
            page: self.pagenum,
            blocks: BlocksForParent::List(blocks),
            first_key: first_key,
            last_key: last_key,
        };
        Ok(pg)
    }

    fn parse_page(pr: &[u8], pairs: &mut Vec<PairInLeaf>) -> Result<(Option<Box<[u8]>>, usize)> {
        let mut prefix = None;

        let mut cur = 0;
        let pt = try!(PageType::from_u8(misc::buf_advance::get_byte(pr, &mut cur)));
        if pt != PageType::LEAF_NODE {
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

    pub fn len_on_page(&self) -> usize {
        self.bytes_used_on_page
    }

    pub fn read_page(&mut self, pgnum: PageNum) -> Result<()> {
        // TODO
        // this code is the only reason this object needs to own its buffer.
        // for the top Leaf/Parent Page object, the one corresponding to a
        // segment, we want it to borrow the buffer in the header.
        // but for a child, we want to be able to switch it from one
        // page to another without re-allocating memory.
        try!(read_page_into_buf(&self.f, pgnum, &mut self.pr));
        self.pagenum = pgnum;
        let (prefix, bytes_used_on_page) = try!(Self::parse_page(&self.pr, &mut self.pairs));
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
        let k = try!(self.pairs[n].key.keyref(&self.pr, prefix, &self.path));
        Ok(k)
    }

    fn key_with_location(&self, n: usize) -> Result<KeyWithLocation> { 
        let prefix: Option<&[u8]> = 
            match self.prefix {
                Some(ref b) => Some(b),
                None => None,
            };
        let k = try!(self.pairs[n].key.key_with_location(&self.pr, prefix, &self.path));
        Ok(k)
    }

    fn range(&self) -> Result<KeyRangeRef> {
        let min = try!(self.key(0));
        let max = {
            let i = self.pairs.len() - 1;
            try!(self.key(i))
        };
        let range = KeyRangeRef {
            min: min,
            max: max,
        };
        Ok(range)
    }

    fn grow_range(&self, cur: Option<KeyRange>) -> Result<KeyRange> {
        let range = try!(self.range());
        match cur {
            None => {
                Ok(range.into_keyrange())
            },
            Some(cur) => {
                Ok(range.grow(cur))
            },
        }
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
                Ok(ValueRef::Overflowed(self.path.clone(), self.pr.len(), vlen, blocks.clone()))
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
        let tmp_countLeafKeys = self.page.count_keys();
        let (newCur, equal) = try!(self.page.search(k, 0, (tmp_countLeafKeys - 1), sop, None, None));
        self.cur = newCur;
        if self.cur.is_none() {
            Ok(SeekResult::Invalid)
        } else if equal {
            Ok(SeekResult::Equal)
        } else {
            Ok(SeekResult::Unequal)
        }
    }

    fn read_page(&mut self, pgnum: PageNum) -> Result<()> {
        self.page.read_page(pgnum)
    }

    pub fn blocklist_unsorted(&self) -> BlockList {
        self.page.blocklist_unsorted()
    }

    pub fn blocklist_unsorted_no_overflows(&self) -> BlockList {
        // TODO silly.  just an empty list, right?
        self.page.blocklist_unsorted_no_overflows()
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
    fn new_already_read_page(path: &str, 
           f: std::rc::Rc<std::cell::RefCell<File>>,
           pagenum: PageNum,
           mut buf: Lend<Box<[u8]>>
          ) -> Result<PageCursor> {

        let pt = try!(PageType::from_u8(buf[0]));
        let sub = 
            match pt {
                PageType::LEAF_NODE => {
                    let page = try!(LeafPage::new_already_read_page(path, f, pagenum, buf));
                    let sub = LeafCursor::new(page);
                    PageCursor::Leaf(sub)
                },
                PageType::PARENT_NODE => {
                    let page = try!(ParentPage::new_already_read_page(path, f, pagenum, buf));
                    if cfg!(expensive_check) 
                    {
                        try!(page.verify_child_keys());
                    }
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

    pub fn blocklist_unsorted_no_overflows(&self) -> Result<BlockList> {
        match self {
            &PageCursor::Leaf(ref c) => {
                // TODO silly.  just an empty list, right?
                Ok(c.blocklist_unsorted_no_overflows())
            },
            &PageCursor::Parent(ref c) => {
                c.blocklist_unsorted_no_overflows()
            },
        }
    }

    fn read_page(&mut self, pg: PageNum) -> Result<()> {
        match self {
            &mut PageCursor::Leaf(ref mut c) => {
                try!(c.read_page(pg));
            },
            &mut PageCursor::Parent(ref mut c) => {
                try!(c.read_page(pg));
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
        let k = try!(Self::read_optional(pr, cur, prefix_len));
        match k {
            Some(k) => Ok(k),
            None => Err(Error::CorruptFile("key cannot be zero length")),
        }
    }

    #[inline]
    fn read_optional(pr: &[u8], cur: &mut usize, prefix_len: usize) -> Result<Option<Self>> {
        let klen = varint::read(pr, cur) as usize;
        if klen == 0 {
            return Ok(None);
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
        Ok(Some(k))
    }

    #[inline]
    fn keyref<'a>(&self, pr: &'a [u8], prefix: Option<&'a [u8]>, path: &str) -> Result<KeyRef<'a>> { 
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
                let mut ostrm = try!(OverflowReader::new(path, pr.len(), blocks.blocks[0].firstPage, klen as u64));
                let mut x_k = Vec::with_capacity(klen);
                try!(ostrm.read_to_end(&mut x_k));
                let x_k = x_k.into_boxed_slice();
                Ok(KeyRef::Boxed(x_k))
            },
        }
    }

    #[inline]
    fn key_with_location(&self, pr: &[u8], prefix: Option<&[u8]>, path: &str) -> Result<KeyWithLocation> { 
        match self {
            &KeyInPage::Inline(klen, at) => {
                let k = 
                    match prefix {
                        Some(a) => {
                            let k = {
                                let mut k = Vec::with_capacity(klen);
                                k.push_all(a);
                                k.push_all(&pr[at .. at + klen - a.len()]);
                                k.into_boxed_slice()
                            };
                            k
                        },
                        None => {
                            let k = {
                                let mut k = Vec::with_capacity(klen);
                                k.push_all(&pr[at .. at + klen]);
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
                    let mut ostrm = try!(OverflowReader::new(path, pr.len(), blocks.blocks[0].firstPage, klen as u64));
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
}

#[derive(Debug)]
struct PairInLeaf {
    key: KeyInPage,
    value: ValueInLeaf,
}

#[derive(Debug)]
pub struct ParentPageItem {
    page: PageNum,

    blocks: BlocksForParent,

    // blocks does NOT contain page

    first_key: KeyInPage,
    last_key: Option<KeyInPage>,
}

#[derive(Debug)]
enum KeyInRange {
    Less,
    Greater,
    EqualFirst,
    EqualLast,
    Within,
}

impl ParentPageItem {
    pub fn page(&self) -> PageNum {
        self.page
    }

    pub fn first_key(&self) -> &KeyInPage {
        &self.first_key
    }

    pub fn last_key(&self) -> &Option<KeyInPage> {
        &self.last_key
    }

}

struct DepthIterator {
    stack: Vec<(ParentPage, usize)>,
    depth: u8,
}

impl DepthIterator {
    fn new(top: ParentPage, depth: u8) -> Self {
        assert!(top.depth() > depth);
        DepthIterator {
            stack: vec![(top, 0)],
            depth: depth,
        }
    }

    fn get_next(&mut self) -> Result<Option<pgitem>> {
        loop {
            match self.stack.pop() {
                None => {
                    return Ok(None);
                },
                Some((parent, cur)) => {
                    if parent.depth() == self.depth + 1 {
                        let pg = try!(parent.child_pgitem(cur));
                        if cur + 1 < parent.count_items() {
                            self.stack.push((parent, cur + 1));
                        }
                        return Ok(Some(pg));
                    } else {
                        let child = try!(parent.fetch_item_parent(cur));
                        if cur + 1 < parent.count_items() {
                            self.stack.push((parent, cur + 1));
                        }
                        self.stack.push((child, 0));
                    }
                },
            }
        }
    }
}

impl Iterator for DepthIterator {
    type Item = Result<pgitem>;
    fn next(&mut self) -> Option<Result<pgitem>> {
        match self.get_next() {
            Ok(None) => {
                None
            },
            Ok(Some(pg)) => {
                Some(Ok(pg))
            },
            Err(e) => {
                Some(Err(e))
            },
        }
    }
}

struct NodeIterator {
    stack: Vec<(ParentPage, Option<usize>)>,
    min_depth: u8,
}

impl NodeIterator {
    fn new(top: ParentPage, min_depth: u8) -> Self {
        assert!(top.depth() >= min_depth);
        NodeIterator {
            stack: vec![(top, None)],
            min_depth: min_depth,
        }
    }

    fn get_next(&mut self) -> Result<Option<(u8, PageNum)>> {
        loop {
            match self.stack.pop() {
                None => {
                    return Ok(None);
                },
                Some((parent, None)) => {
                    let depth = parent.depth();
                    let page = parent.pagenum;
                    if depth > self.min_depth {
                        self.stack.push((parent, Some(0)));
                    }
                    return Ok(Some((depth, page)));
                },
                Some((parent, Some(cur))) => {
                    if parent.depth() == self.min_depth + 1 {
                        let pg = parent.child_pagenum(cur);
                        if cur + 1 < parent.children.len() {
                            self.stack.push((parent, Some(cur + 1)));
                        }
                        return Ok(Some((self.min_depth, pg)));
                    } else {
                        let child = try!(parent.fetch_item_parent(cur));
                        if cur + 1 < parent.children.len() {
                            self.stack.push((parent, Some(cur + 1)));
                        }
                        self.stack.push((child, None));
                    }
                },
            }
        }
    }
}

impl Iterator for NodeIterator {
    type Item = Result<(u8, PageNum)>;
    fn next(&mut self) -> Option<Result<(u8, PageNum)>> {
        match self.get_next() {
            Ok(None) => {
                None
            },
            Ok(Some(pg)) => {
                Some(Ok(pg))
            },
            Err(e) => {
                Some(Err(e))
            },
        }
    }
}

pub struct ParentPage {
    path: String,
    f: std::rc::Rc<std::cell::RefCell<File>>,
    pr: Lend<Box<[u8]>>,
    pagenum: PageNum,

    prefix: Option<Box<[u8]>>,
    children: Vec<ParentPageItem>,

}

impl ParentPage {
    fn new_already_read_page(path: &str, 
           f: std::rc::Rc<std::cell::RefCell<File>>,
           pagenum: PageNum,
           buf: Lend<Box<[u8]>>
          ) -> Result<ParentPage> {

        let (prefix, children) = try!(Self::parse_page(&buf));
        assert!(children.len() > 0);

        let res = ParentPage {
            path: String::from(path),
            f: f,
            pr: buf,
            pagenum: pagenum,

            prefix: prefix,
            children: children,

        };

        if cfg!(expensive_check) 
        {
            try!(res.verify_child_keys());
        }

        Ok(res)
    }

    #[cfg(remove_me)]
    fn pgitem(&self) -> Result<pgitem> {
        let mut blocks = try!(self.blocklist_unsorted());
        blocks.sort_and_consolidate();
        let first_key = try!(self.first_key_with_location());
        let last_key = try!(self.last_key_with_location());
        // TODO pgitem::new
        let pg = pgitem {
            page: self.pagenum,
            blocks: blocks,
            first_key: first_key,
            last_key: last_key,
        };
        assert!(!pg.blocks.contains_page(pg.page));
        Ok(pg)
    }

    fn child_blocklist(&self, i: usize) -> Result<BlockList> {
        match self.children[i].blocks {
            BlocksForParent::List(ref blocks) => {
                assert!(self.depth() == 1);
                Ok(blocks.clone())
            },
            BlocksForParent::Count(_) => {
                assert!(self.depth() > 1);
                let pagenum = self.children[i].page;

                let buf = try!(read_and_alloc_page(&self.f, pagenum, self.pr.len()));
                let done_page = move |_| -> () {
                };
                let buf = Lend::new(buf, box done_page);

                let page = try!(ParentPage::new_already_read_page(&self.path, self.f.clone(), pagenum, buf));
                page.blocklist_unsorted()
                // TODO assert that count matches the blocklist?
            },
        }
    }

    fn child_blocklist_no_overflows(&self, i: usize) -> Result<BlockList> {
        let pagenum = self.children[i].page;
        if self.depth() == 1 {
            Ok(BlockList::new())
        } else {
            assert!(self.depth() > 1);

            let buf = try!(read_and_alloc_page(&self.f, pagenum, self.pr.len()));
            let done_page = move |_| -> () {
            };
            let buf = Lend::new(buf, box done_page);

            let page = try!(ParentPage::new_already_read_page(&self.path, self.f.clone(), pagenum, buf));
            page.blocklist_unsorted_no_overflows()
            // TODO assert that count matches the blocklist?
        }
    }

    fn child_pgitem(&self, i: usize) -> Result<pgitem> {
        let first_key = try!(self.key_with_location(&self.children[i].first_key));
        let last_key = {
            match &self.children[i].last_key {
                &Some(ref last_key) => {
                    let kw = try!(self.key_with_location(last_key));
                    Some(kw)
                },
                &None => {
                    None
                },
            }
        };
        // TODO pgitem::new
        let pg = pgitem {
            page: self.children[i].page,
            blocks: self.children[i].blocks.clone(),
            first_key: first_key,
            last_key: last_key,
        };
        Ok(pg)
    }

// TODO dislike
    fn first_key<'a>(&'a self) -> Result<KeyRef<'a>> {
        self.key(&self.children[0].first_key)
    }

// TODO dislike
    fn last_key<'a>(&'a self) -> Result<KeyRef<'a>> {
        let i = self.children.len() - 1;
        let last_key =
            match &self.children[i].last_key {
                &Some(ref last_key) => {
                    last_key
                },
                &None => {
                    &self.children[i].first_key
                },
            };
        self.key(last_key)
    }

    fn overlaps(&self, first_key: &[u8], last_key: &[u8]) -> Result<Overlap> {
        match try!(self.first_key()).compare_with(last_key) {
            Ordering::Greater => {
                Ok(Overlap::Greater)
            },
            Ordering::Less | Ordering::Equal => {
                match try!(self.last_key()).compare_with(first_key) {
                    Ordering::Less => {
                        Ok(Overlap::Less)
                    },
                    Ordering::Greater | Ordering::Equal => {
                        Ok(Overlap::Yes)
                    },
                }
            },
        }
    }

    fn siblings_for(&self, skip: Option<(usize, usize)>) -> Result<Vec<pgitem>> {
        let mut v = Vec::with_capacity(self.children.len());
        for i in 0 .. self.children.len() {
            let include =
                match skip {
                    Some((first, last)) => {
                        i < first || i > last
                    },
                    None => {
                        true
                    },
                };
            if include {
                let pg = try!(self.child_pgitem(i));
                v.push(pg);
            }
        }
        Ok(v)
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
        LeafPage::new(&self.path, self.f.clone(), self.pr.len(), )
    }

    pub fn into_node_iter(self, min_depth: u8) -> Box<Iterator<Item=Result<(u8, PageNum)>>> {
        box NodeIterator::new(self, min_depth)
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

    fn blocklist_unsorted_no_overflows(&self) -> Result<BlockList> {
        let mut list = BlockList::new();
        for i in 0 .. self.children.len() {
            // we do not add the blocklist for any overflow keys,
            // because we don't own that blocklist.  it is simply a reference
            // to the blocklist for an overflow key when it was written into
            // its leaf.
            list.add_page_no_reorder(self.children[i].page);
            let blocks = try!(self.child_blocklist_no_overflows(i));
            list.add_blocklist_no_reorder(&blocks);
        }
        Ok(list)
    }

    pub fn blocklist_clean(&self) -> Result<BlockList> {
        let mut blocks = try!(self.blocklist_unsorted());
        blocks.sort_and_consolidate();
        Ok(blocks)
    }

    pub fn count_items(&self) -> usize {
        self.children.len()
    }

    pub fn verify_child_keys(&self) -> Result<()> {
        for i in 0 .. self.children.len() {
            // for each child, make sure the last key > first key
            match &self.children[i].last_key {
                &Some(ref last_key) => {
                    let first_key = try!(self.key(&self.children[i].first_key));
                    let last_key = try!(self.key(last_key));
                    let c = KeyRef::cmp(&last_key, &first_key);
                    assert!(c == Ordering::Greater);
                },
                &None => {
                },
            };

            // for each child, make sure it provides the same first and
            // last key as the ones we've got.

            let buf = try!(read_and_alloc_page(&self.f, self.children[i].page, self.pr.len()));
            let done_page = move |_| -> () {
            };
            let buf = Lend::new(buf, box done_page);

            let mut sub = try!(PageCursor::new_already_read_page(&self.path, self.f.clone(), self.children[i].page, buf));
            try!(sub.First());
            assert!(sub.IsValid());
            {
                let k = try!(sub.KeyRef());
                let first_key = try!(self.key(&self.children[i].first_key));
                let c = KeyRef::cmp(&k, &first_key);
                if c != Ordering::Equal {
                    println!("mismatch on first key:");
                    println!("parent page {}  child page {}", self.pagenum, self.children[i].page);
                    panic!();
                }
                assert!(c == Ordering::Equal);
            }
            try!(sub.Last());
            assert!(sub.IsValid());
            let last_key =
                match &self.children[i].last_key {
                    &Some(ref last_key) => {
                        last_key
                    },
                    &None => {
                        &self.children[i].first_key
                    },
                };
            {
                let k = try!(sub.KeyRef());
                let last_key = try!(self.key(last_key));
                let c = KeyRef::cmp(&k, &last_key);
                if c != Ordering::Equal {
                    println!("mismatch on last key:");
                    println!("parent page {}  child page {}", self.pagenum, self.children[i].page);
                    println!("child.Leaf says ({}): {:?}", k.len(), k);
                    println!("parent says ({}): {:?}", last_key.len(), last_key);
                    println!("parent also says: {:?}", self.children[i].last_key);
                    panic!();
                }
                assert!(c == Ordering::Equal);
            }
        }
        Ok(())
    }

    #[inline]
    fn key<'a>(&'a self, k: &KeyInPage) -> Result<KeyRef<'a>> { 
        let prefix: Option<&[u8]> = 
            match self.prefix {
                Some(ref b) => Some(b),
                None => None,
            };
        let k = try!(k.keyref(&self.pr, prefix, &self.path));
        Ok(k)
    }

    fn key_with_location(&self, k: &KeyInPage) -> Result<KeyWithLocation> { 
        let prefix: Option<&[u8]> = 
            match self.prefix {
                Some(ref b) => Some(b),
                None => None,
            };
        let k = try!(k.key_with_location(&self.pr, prefix, &self.path));
        Ok(k)
    }

    fn first_key_with_location(&self) -> Result<KeyWithLocation> {
        self.key_with_location(&self.children[0].first_key)
    }

    fn last_key_with_location(&self) -> Result<Option<KeyWithLocation>> {
        let i = self.children.len() - 1;
        match &self.children[i].last_key {
            &Some(ref last_key) => {
                let kw = try!(self.key_with_location(last_key));
                Ok(Some(kw))
            },
            &None => {
                if i > 0 {
                    let kw = try!(self.key_with_location(&self.children[i].first_key));
                    Ok(Some(kw))
                } else {
                    Ok(None)
                }
            },
        }
    }

    pub fn range(&self) -> Result<KeyRangeRef> {
        let min = try!(self.key(&self.children[0].first_key));
        let max = {
            let i = self.children.len() - 1;
            let key =
                match &self.children[i].last_key {
                    &Some(ref last_key) => {
                        last_key
                    },
                    &None => {
                        &self.children[i].first_key
                    },
                };
            try!(self.key(key))
        };
        let range = KeyRangeRef {
            min: min,
            max: max,
        };
        Ok(range)
    }

    fn parse_page(pr: &[u8]) -> Result<(Option<Box<[u8]>>, Vec<ParentPageItem>)> {
        let mut cur = 0;
        let pt = try!(PageType::from_u8(misc::buf_advance::get_byte(pr, &mut cur)));
        if  pt != PageType::PARENT_NODE {
            panic!();
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

            let blocks = 
                if depth == 1 {
                    BlocksForParent::List((BlockList::read(pr, &mut cur)))
                } else {
                    BlocksForParent::Count(varint::read(pr, &mut cur) as PageCount)
                };

            let key_1 = try!(KeyInPage::read(pr, &mut cur, prefix_len));
            let key_2 = try!(KeyInPage::read_optional(pr, &mut cur, prefix_len));

            let pg = ParentPageItem {
                page: page, 
                //if cfg!(child_block_list) 
                blocks: blocks,
                first_key: key_1,
                last_key: key_2,
            };
            children.push(pg);
        }

        //println!("children parsed: {:?}", children);

        Ok((prefix, children))
    }

    fn count_pages(buf: &[u8]) -> Result<PageCount> {
        let (_, children) = try!(Self::parse_page(buf));
        let mut count_pages = 0;
        for item in children {
            match item.blocks {
                BlocksForParent::List(blocks) => {
                    count_pages += blocks.count_pages();
                },
                BlocksForParent::Count(count) => {
                    count_pages += count;
                },
            }
        }
        Ok(count_pages)
    }

    fn read_page(&mut self, pgnum: PageNum) -> Result<()> {
        // TODO
        // this code is the only reason this object needs to own its buffer.
        // for the top Leaf/Parent Page object, the one corresponding to a
        // segment, we want it to borrow the buffer in the header.
        // but for a child, we want to be able to switch it from one
        // page to another without re-allocating memory.
        try!(read_page_into_buf(&self.f, pgnum, &mut self.pr));
        self.pagenum = pgnum;
        let (prefix, children) = try!(Self::parse_page(&self.pr));
        self.prefix = prefix;
        self.children = children;

        Ok(())
    }

    fn key_in_child_range(&self, i: usize, kq: &KeyRef) -> Result<KeyInRange> {
        match self.children[i].last_key {
            Some(ref last_key) => {
                let last_key = try!(self.key(last_key));
                match KeyRef::cmp(kq, &last_key) {
                    Ordering::Less => {
                    },
                    Ordering::Equal => {
                        return Ok(KeyInRange::EqualLast);
                    },
                    Ordering::Greater => {
                        return Ok(KeyInRange::Greater);
                    },
                }
            },
            None => {
            },
        }
        let first_key = try!(self.key(&self.children[i].first_key));
        match KeyRef::cmp(kq, &first_key) {
            Ordering::Less => {
                Ok(KeyInRange::Less)
            },
            Ordering::Equal => {
                Ok(KeyInRange::EqualFirst)
            },
            Ordering::Greater => {
                if self.children[i].last_key.is_some() {
                    Ok(KeyInRange::Within)
                } else {
                    Ok(KeyInRange::Greater)
                }
            },
        }
    }

    pub fn child_range(&self, i: usize) -> Result<KeyRangeRef> {
        let min = try!(self.key(&self.children[i].first_key));
        let max = {
            let key =
                match &self.children[i].last_key {
                    &Some(ref last_key) => {
                        last_key
                    },
                    &None => {
                        &self.children[i].first_key
                    },
                };
            try!(self.key(key))
        };
        let range = KeyRangeRef {
            min: min,
            max: max,
        };
        Ok(range)
    }

    fn child_overlaps(&self, i: usize, range: &KeyRange) -> Result<Overlap> {
        match self.children[i].last_key {
            Some(ref my_last_key) => {
                let my_last_key = try!(self.key(my_last_key));
                match my_last_key.compare_with(&range.min) {
                    Ordering::Less => {
                        Ok(Overlap::Less)
                    },
                    Ordering::Equal => {
                        Ok(Overlap::Yes)
                    },
                    Ordering::Greater => {
                        let my_first_key = try!(self.key(&self.children[i].first_key));
                        match my_first_key.compare_with(&range.max) {
                            Ordering::Greater => {
                                Ok(Overlap::Greater)
                            },
                            Ordering::Less | Ordering::Equal => {
                                Ok(Overlap::Yes)
                            },
                        }
                    },
                }
            },
            None => {
                let my_first_key = try!(self.key(&self.children[i].first_key));
                match my_first_key.compare_with(&range.max) {
                    Ordering::Greater => {
                        Ok(Overlap::Greater)
                    },
                    Ordering::Equal => {
                        Ok(Overlap::Yes)
                    },
                    Ordering::Less => {
                        match my_first_key.compare_with(&range.min) {
                            Ordering::Greater => {
                                Ok(Overlap::Yes)
                            },
                            Ordering::Equal => {
                                Ok(Overlap::Yes)
                            },
                            Ordering::Less => {
                                Ok(Overlap::Less)
                            },
                        }
                    },
                }
            },
        }
    }

    fn get_child_cursor(&self, i: usize) -> Result<PageCursor> {
        let pagenum = self.children[i].page;
        let buf = try!(read_and_alloc_page(&self.f, pagenum, self.pr.len()));
        let done_page = move |_| -> () {
        };
        let buf = Lend::new(buf, box done_page);

        let sub = try!(PageCursor::new_already_read_page(&self.path, self.f.clone(), self.children[i].page, buf));
        Ok(sub)
    }

    pub fn child_pagenum(&self, i: usize) -> PageNum {
        self.children[i].page
    }

    fn fetch_item_parent(&self, i: usize) -> Result<ParentPage> {
        let pagenum = self.children[i].page;
        let buf = try!(read_and_alloc_page(&self.f, pagenum, self.pr.len()));
        let done_page = move |_| -> () {
        };
        let buf = Lend::new(buf, box done_page);

        let child = try!(ParentPage::new_already_read_page(&self.path, self.f.clone(), pagenum, buf));
        Ok(child)
    }

}

// TODO generic for child type?
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
        try!(self.sub.read_page(pagenum));
        self.cur = Some(i);
        Ok(())
    }

    fn read_page(&mut self, pgnum: PageNum) -> Result<()> {
        try!(self.page.read_page(pgnum));
        let pagenum = self.page.child_pagenum(0);
        try!(self.sub.read_page(pagenum));
        self.cur = Some(0);
        Ok(())
    }

    pub fn blocklist_unsorted(&self) -> Result<BlockList> {
        self.page.blocklist_unsorted()
    }

    pub fn blocklist_unsorted_no_overflows(&self) -> Result<BlockList> {
        self.page.blocklist_unsorted_no_overflows()
    }

    fn seek(&mut self, k: &KeyRef, sop: SeekOp) -> Result<SeekResult> {
        //println!("parent page: {}  search: kq = {:?},  sop = {:?}", self.pagenum, k, sop);

        for i in 0 .. self.page.count_items() {
            let look = try!(self.page.key_in_child_range(i, k));
            //println!("    in page {:?} : {:?}", self.children[i].page, look);
            match look {
                KeyInRange::EqualFirst => {
                    try!(self.set_child(i));
                    try!(self.sub.First());
                    // TODO assert something?
                    return Ok(SeekResult::Equal);
                },
                KeyInRange::EqualLast => {
                    try!(self.set_child(i));
                    try!(self.sub.Last());
                    // TODO assert something?
                    return Ok(SeekResult::Equal);
                },
                KeyInRange::Within => {
                    try!(self.set_child(i));
                    let sr = try!(self.sub.SeekRef(k, sop));
                    return Ok(sr)
                },
                KeyInRange::Less => {
                    // there should be no case here where the loop continues.
                    // the children are sorted ascending.  if the key is
                    // less than this one, it will be less than all the others
                    // as well.
                    if i == 0 {
                        // k is less than the first one
                        match sop {
                            SeekOp::SEEK_LE => {
                                self.cur = None;
                                return Ok(SeekResult::Invalid);
                            },
                            SeekOp::SEEK_GE => {
                                try!(self.set_child(0));
                                try!(self.sub.First());
                                return Ok(SeekResult::Unequal);
                            },
                            SeekOp::SEEK_EQ => {
                                self.cur = None;
                                return Ok(SeekResult::Invalid);
                            },
                        }
                    } else {
                        // had to be greater than the last one
                        // in between
                        match sop {
                            SeekOp::SEEK_LE => {
                                try!(self.set_child(i - 1));
                                try!(self.sub.Last());
                                return Ok(SeekResult::Unequal);
                            },
                            SeekOp::SEEK_GE => {
                                try!(self.set_child(i));
                                try!(self.sub.First());
                                return Ok(SeekResult::Unequal);
                            },
                            SeekOp::SEEK_EQ => {
                                self.cur = None;
                                return Ok(SeekResult::Invalid);
                            },
                        }
                    }
                },
                KeyInRange::Greater => {
                    // keep looking
                },
            }
        }
        //println!("after loop");
        // the only way to exit the loop is for the key to be
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

// TODO er, this isn't used anymore?
pub struct MultiPageCursor {
    path: String,
    children: Vec<PageNum>,
    cur: Option<usize>,
    sub: Box<PageCursor>,
}

impl MultiPageCursor {
    fn new(path: &str, 
           f: std::rc::Rc<std::cell::RefCell<File>>,
           pagesize: usize,
           children: Vec<PageNum>,
          ) -> Result<MultiPageCursor> {

        assert!(children.len() > 0);

        let buf = try!(read_and_alloc_page(&f, children[0], pagesize));
        let done_page = move |_| -> () {
        };
        let buf = Lend::new(buf, box done_page);

        let sub = try!(PageCursor::new_already_read_page(path, f, children[0], buf));

        let res = MultiPageCursor {
            path: String::from(path),
            children: children,
            cur: Some(0),
            sub: box sub,

        };

        Ok(res)
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
        try!(self.sub.read_page(pagenum));
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
    levels: Vec<SegmentHeaderInfo>,

    changeCounter: u64,
    mergeCounter: u64,
}

// TODO how big should the header be?  this defines the minimum size of a
// database file.
const HEADER_SIZE_IN_BYTES: usize = 4096;

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

    fn parse(pr: &Box<[u8]>, f: std::rc::Rc<std::cell::RefCell<File>>, path: &str) -> Result<(HeaderData, usize)> {
        fn read_segment_list(pr: &Box<[u8]>, cur: &mut usize) -> Result<Vec<PageNum>> {
            let count = varint::read(&pr, cur) as usize;
            let mut a = Vec::with_capacity(count);
            for _ in 0 .. count {
                let root_page = varint::read(&pr, cur) as PageNum;
                a.push(root_page);
            }
            Ok(a)
        }

        fn fix_segment_list(segments: Vec<PageNum>, pgsz: usize, f: std::rc::Rc<std::cell::RefCell<File>>, path: &str) -> Result<Vec<SegmentHeaderInfo>> {
            let mut v = Vec::with_capacity(segments.len());
            for page in segments.iter() {
                let pagenum = *page;

                let buf = try!(read_and_alloc_page(&f, pagenum, pgsz));

                let seg = SegmentHeaderInfo::new(pagenum, buf);

                v.push(seg);
            }
            Ok(v)
        }

        let mut cur = 0;

        let pgsz = misc::buf_advance::get_u32(&pr, &mut cur) as usize;
        let changeCounter = varint::read(&pr, &mut cur);
        let mergeCounter = varint::read(&pr, &mut cur);

        let fresh = try!(read_segment_list(pr, &mut cur));
        let young = try!(read_segment_list(pr, &mut cur));
        let levels = try!(read_segment_list(pr, &mut cur));

        let fresh = try!(fix_segment_list(fresh, pgsz, f.clone(), path));
        let young = try!(fix_segment_list(young, pgsz, f.clone(), path));
        let levels = try!(fix_segment_list(levels, pgsz, f.clone(), path));

        let hd = 
            HeaderData {
                fresh: fresh,
                young: young,
                levels: levels,
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

    let mut f = try!(OpenOptions::new()
            .read(true)
            .create(true)
            .open(&path));

    let len = try!(f.metadata()).len();
    if len > 0 {
        let pr = try!(read(&mut f));
        let f = std::cell::RefCell::new(f);
        let f = std::rc::Rc::new(f);
        let (h, pgsz) = try!(parse(&pr, f, &path));
        let nextAvailablePage = calcNextPage(pgsz, len as usize);
        Ok((h, pgsz, nextAvailablePage))
    } else {
        // TODO shouldn't this use settings passed in?
        let defaultPageSize = DEFAULT_SETTINGS.DefaultPageSize;
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
        Ok((h, defaultPageSize, nextAvailablePage))
    }

}

fn list_all_blocks(
    path: &str,
    f: std::rc::Rc<std::cell::RefCell<File>>,
    h: &HeaderData, 
    pgsz: usize,
    ) -> Result<BlockList> {
    let mut blocks = BlockList::new();

    let headerBlock = PageBlock::new(1, (HEADER_SIZE_IN_BYTES / pgsz) as PageNum);
    blocks.add_block_no_reorder(headerBlock);

    fn do_seglist(path: &str, f: std::rc::Rc<std::cell::RefCell<File>>, segments: &Vec<SegmentHeaderInfo>, blocks: &mut BlockList) -> Result<()> {
        for seg in segments.iter() {
            let b = try!(seg.blocklist_unsorted(path, f.clone()));
            blocks.add_blocklist_no_reorder(&b);
            blocks.add_page_no_reorder(seg.root_page);
        }
        Ok(())
    }

    try!(do_seglist(path, f.clone(), &h.fresh, &mut blocks));
    try!(do_seglist(path, f.clone(), &h.young, &mut blocks));
    try!(do_seglist(path, f.clone(), &h.levels, &mut blocks));

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
}

impl Space {
    fn add_rlock(&mut self, segments: HashSet<PageNum>) -> u64 {
        let rlock = self.next_rlock;
        self.next_rlock += 1;
        let was = self.rlocks.insert(rlock, segments);
        assert!(was.is_none());
        rlock
    }

    fn has_rlock(&self, pgnum: PageNum) -> bool {
        for h in self.rlocks.values() {
            if h.contains(&pgnum) {
                return true;
            }
        }
        false
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
        if self.zombies.is_empty() {
            // if there are no zombies, there is nothing more to do here
            return;
        }
        // the rlock we released might not be the only one for those
        // segments.  anything that still has an rlock has gotta be
        // left alone.

        let segments = 
            segments
            .into_iter()
            .filter(|seg| !self.has_rlock(*seg))
            .collect::<HashSet<_>>();
        if segments.is_empty() {
            return;
        }

        // OK, now anything in segments which is also in zombies
        // can be added to the free list and removed from zombies.

        let freeable_keys = 
            segments
            .into_iter()
            .filter(|seg| self.zombies.contains_key(seg))
            .collect::<HashSet<_>>();
        if freeable_keys.is_empty() {
            return;
        }

        let mut free_blocks = BlockList::new();
        for seg in freeable_keys {
            let blocks = self.zombies.remove(&seg).unwrap();
            free_blocks.add_blocklist_no_reorder(&blocks);
        }
        self.add_free_blocks(free_blocks);
    }

    fn add_inactive(&mut self, mut blocks: HashMap<PageNum, BlockList>) {
        // everything in blocks should go in either free or zombie

        if !blocks.is_empty() {
            let segments = blocks.keys().map(|p| *p).collect::<HashSet<PageNum>>();
            let new_zombie_segments = 
                segments
                .into_iter()
                .filter(|seg| self.has_rlock(*seg))
                .collect::<HashSet<_>>();
            for pg in new_zombie_segments {
                let b = blocks.remove(&pg).unwrap();
                self.zombies.insert(pg, b);
            }
            if !blocks.is_empty() {
                for (pg, b) in blocks {
                    self.add_free_blocks(b);
                }
            }
        }
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

#[derive(Debug)]
enum MergeFrom {
    Fresh{segments: Vec<PageNum>},
    Young{segments: Vec<PageNum>},
    Other{level: usize, old_segment: PageNum, new_segment: SegmentHeaderInfo},
}

impl MergeFrom {
    fn get_dest_level(&self) -> DestLevel {
        match self {
            &MergeFrom::Fresh{..} => DestLevel::Young,
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
    // TODO vec, or boxed slice?
    notify_levels: Vec<mpsc::Sender<MergeMessage>>,
}

// there can be only one InnerPart instance per path
struct InnerPart {
    path: String,
    pgsz: usize,
    settings: DbSettings,

    // TODO are we concerned here about readers starving the
    // writers?  In other words, so many cursors that a merge
    // cannot get committed?
    header: RwLock<HeaderData>,

    space: Mutex<Space>,
    pagepool: Mutex<SafePagePool>,
    senders: Mutex<Senders>,

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
        let (header, pgsz, first_available_page) = try!(read_header(&path));

        // when we first open the file, we find all the blocks that are in use by
        // an active segment.  all OTHER blocks are considered free.
        let f = 
            try!(OpenOptions::new()
                    .read(true)
                    .open(&path));
        let f = std::cell::RefCell::new(f);
        let f = std::rc::Rc::new(f);

        let mut blocks = try!(list_all_blocks(&path, f, &header, pgsz));

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
            page_size: pgsz,
            nextPage: first_available_page, 
            pages_per_block: settings.PagesPerBlock,
            fresh_free: vec![],
            free_blocks: blocks,
            next_rlock: 1,
            rlocks: HashMap::new(),
            zombies: HashMap::new(),
        };

        let pagepool = SafePagePool {
            pages: vec![],
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

        let inner = InnerPart {
            path: path,
            pgsz: pgsz,
            settings: settings, 
            header: RwLock::new(header),
            space: Mutex::new(space),
            pagepool: Mutex::new(pagepool),
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

        fn guts(inner: &std::sync::Arc<InnerPart>, write_lock: &std::sync::Arc<Mutex<WriteLock>>, level: FromLevel) -> Result<Option<u32>> {
            match try!(InnerPart::needs_merge(&inner, level)) {
                NeedsMerge::No => {
                    Ok(None)
                },
                _ => {
                    match try!(InnerPart::needs_merge(&inner, level.get_dest_level().as_from_level())) {
                        NeedsMerge::Desperate => {
                            try!(inner.notify_work(level.get_dest_level().as_from_level()));
                            Ok(Some(50))
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
                    std::thread::sleep_ms(delay);
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
                    std::thread::sleep_ms(delay);
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
                    std::thread::sleep_ms(delay);
                }
            },
        }
        Ok(())
    }

    // TODO func to ask for the write lock without blocking?

    pub fn get_write_lock(&self) -> Result<std::sync::MutexGuard<WriteLock>> {
        while NeedsMerge::Desperate == try!(InnerPart::needs_merge(&self.inner, FromLevel::Fresh)) {
            // TODO if we need to sleep more than once, do we need to notify_work
            // every time?
            try!(self.inner.notify_work(FromLevel::Fresh));
            println!("fresh too big, sleeping");
            std::thread::sleep_ms(10);
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

    pub fn list_segments(&self) -> Result<(Vec<(PageNum, PageCount)>, Vec<(PageNum, PageCount)>, Vec<(PageNum, PageCount)>)> {
        InnerPart::list_segments(&self.inner)
    }

    pub fn release_pending_segment(&self, location: PageNum) -> Result<()> {
        InnerPart::release_pending_segment(&self.inner, location)
    }

    pub fn list_free_blocks(&self) -> Result<BlockList> {
        InnerPart::list_free_blocks(&self.inner)
    }

    pub fn get_page(&self, pgnum: PageNum) -> Result<Box<[u8]>> {
        InnerPart::get_page(&self.inner, pgnum)
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

            fn add_list(pb: &mut Vec<u8>, v: &Vec<SegmentHeaderInfo>) {
                misc::push_varint(pb, v.len() as u64);
                for seg in v.iter() {
                    misc::push_varint(pb, seg.root_page as u64);
                }
            }

            add_list(&mut pb, &h.fresh);
            add_list(&mut pb, &h.young);
            add_list(&mut pb, &h.levels);

            pb
        }

        println!("header,fresh,{},young,{},levels,{}", hdr.fresh.len(), hdr.young.len(), hdr.levels.len());

        let mut pb = PageBuilder::new(HEADER_SIZE_IN_BYTES);
        // TODO format version number
        pb.PutInt32(self.pgsz as u32);

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

        try!(fs.seek(SeekFrom::Start(0)));
        try!(pb.Write(fs));
        try!(fs.flush());
        *dest = hdr;
        Ok(())
    }

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
        let mut buf = try!(Self::get_loaner_page(inner));
        let f = try!(inner.open_file_for_cursor());

        try!(read_page_into_buf(&f, pg, &mut buf));

        let cursor = try!(PageCursor::new_already_read_page(&inner.path, f, pg, buf));
        Ok(cursor)
    }

    fn open_cursor_on_leaf_page(inner: &std::sync::Arc<InnerPart>, pg: PageNum) -> Result<LeafCursor> {
        let mut buf = try!(Self::get_loaner_page(inner));
        let f = try!(inner.open_file_for_cursor());

        try!(read_page_into_buf(&f, pg, &mut buf));

        let page = try!(LeafPage::new_already_read_page(&inner.path, f, pg, buf));
        let cursor = LeafCursor::new(page);
        Ok(cursor)
    }

    fn open_cursor_on_parent_page(inner: &std::sync::Arc<InnerPart>, pg: PageNum) -> Result<ParentCursor> {
        let mut buf = try!(Self::get_loaner_page(inner));
        let f = try!(inner.open_file_for_cursor());

        try!(read_page_into_buf(&f, pg, &mut buf));

        let page = try!(ParentPage::new_already_read_page(&inner.path, f, pg, buf));
        let cursor = try!(ParentCursor::new(page));
        Ok(cursor)
    }

    fn read_parent_page(inner: &std::sync::Arc<InnerPart>, pg: PageNum) -> Result<ParentPage> {
        let mut buf = try!(Self::get_loaner_page(inner));
        let f = try!(inner.open_file_for_cursor());

        try!(read_page_into_buf(&f, pg, &mut buf));

        let page = try!(ParentPage::new_already_read_page(&inner.path, f, pg, buf));
        Ok(page)
    }

    fn open_cursor(inner: &std::sync::Arc<InnerPart>) -> Result<LivingCursor> {
        let header = try!(inner.header.read());
        let f = try!(inner.open_file_for_cursor());

        let cursors = 
            header.fresh.iter()
            .chain(header.young.iter())
            .chain(header.levels.iter())
            .map(|seg| {
                let buf = seg.buf.clone();
// TODO it would be nice to just let pagecursor have a reference. Arc?
                let done_page = move |_| -> () {
                };
                let buf = Lend::new(buf, box done_page);
                let csr = try!(PageCursor::new_already_read_page(&inner.path, f.clone(), seg.root_page, buf));
                Ok(csr)
            })
            .collect::<Result<Vec<_>>>();
        let cursors = try!(cursors);

        let segments = 
            header.fresh.iter()
            .chain(header.young.iter())
            .chain(header.levels.iter())
            .map(|seg| {
                seg.root_page
            })
            .collect::<HashSet<_>>();

        let rlock = {
            let mut space = try!(inner.space.lock());
            let rlock = space.add_rlock(segments);
            rlock
        };

        let foo = inner.clone();
        let done = move |_| -> () {
            // TODO this wants to propagate errors
            foo.cursor_dropped(rlock);
        };

        let mc = MultiCursor::new(cursors);
        let mc = Lend::new(mc, box done);
        let lc = LivingCursor::new(mc);

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
        let header = try!(inner.header.read());

        fn do_group(segments: &[SegmentHeaderInfo]) -> Result<Vec<(PageNum, PageCount)>> {
            let mut v = vec![];
            for seg in segments.iter() {
                let count = try!(seg.count_pages());
                v.push((seg.root_page, count));
            }
            Ok(v)
        }

        let fresh = try!(do_group(&header.fresh));
        let young = try!(do_group(&header.young));
        let levels = try!(do_group(&header.levels));

        Ok((fresh, young, levels))
    }

    fn commit_segment(&self, seg: SegmentHeaderInfo) -> Result<()> {
        {
            let mut header = try!(self.header.write());

            // TODO assert new seg shares no pages with any seg in current state

            let mut newHeader = header.clone();

            newHeader.fresh.insert(0, seg);

            newHeader.changeCounter = newHeader.changeCounter + 1;

            {
                let mut fs = try!(self.OpenForWriting());
                try!(self.write_header(&mut header, &mut fs, newHeader));
            }
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
        let f = try!(inner.open_file_for_cursor());
        let seg = try!(create_segment(pw, source, f));
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
        let header = try!(inner.header.read());
        match from_level {
            FromLevel::Fresh => {
                // TODO constant
                if header.fresh.len() < 2 {
                    return Ok(NeedsMerge::No);
                }

                // TODO constant
                if header.fresh.len() > 100 {
                    return Ok(NeedsMerge::Desperate);
                }

                return Ok(NeedsMerge::Yes);
            },
            FromLevel::Young => {
                // TODO constant
                if header.young.len() < 4 {
                    return Ok(NeedsMerge::No);
                }

                // TODO constant
                if header.young.len() > 100 {
                    return Ok(NeedsMerge::Desperate);
                }

                return Ok(NeedsMerge::Yes);
            },
            FromLevel::Other(i) => {
                if header.levels.len() <= i {
                    // this level doesn't need a merge because it doesn't exist
                    return Ok(NeedsMerge::No);
                }
                let pt = try!(PageType::from_u8(header.levels[i].buf[0]));
                if pt == PageType::LEAF_NODE {
                    return Ok(NeedsMerge::No);
                }
                if header.levels[i].buf[2] < 1 {
// TODO this check is silly now.  leaf check done above.  comment below wrong.
                    // we currently require the from segment to be at least a grandparent,
                    // because we want to promote a parent that is not the root.

                    // this level doesn't need a merge because promoting anything out of it would
                    // deplete it.
                    return Ok(NeedsMerge::No);
                }
                // TODO this is a fairly expensive way to count the pages under a parent.
// store the count in SegmentHeaderInfo ?
                let count_pages = try!(ParentPage::count_pages(&header.levels[i].buf)) as u64;
                let size = count_pages * (inner.pgsz as u64);
                if size < get_level_size(i) {
                    // this level doesn't need a merge because it is doesn't have enough data in it
                    return Ok(NeedsMerge::No);
                }
                // TODO constant
                if size > 2 * get_level_size(i) {
                    return Ok(NeedsMerge::Desperate);
                }
                return Ok(NeedsMerge::Yes);
            },
        }
    }

    fn prepare_merge(inner: &std::sync::Arc<InnerPart>, from_level: FromLevel) -> Result<PendingMerge> {
        struct FromWholeSegment {
            // TODO it would be nice if this were a &SegmentHeaderInfo
            root_page: PageNum,
            node_pages: BlockList,
        }

        enum MergingFrom {
            Fresh{
                segments: Vec<FromWholeSegment>,
            },
            Young{
                segments: Vec<FromWholeSegment>,
            },
            Other{
                level: usize,  // TODO why is this here?
                old_segment: PageNum, 
                chosen_page: PageNum, 
                chosen_depth: u8, 
                chosen_node_pages: BlockList, 
                parents: Vec<PageNum>, 
                survivors: Box<Iterator<Item=Result<pgitem>>>,
            },
        }

        enum MergingInto {
            None,
            Level{
                level: usize,  // TODO why is this here?
                old_segment: PageNum, 
                leaves: Box<Iterator<Item=Result<pgitem>>>, 
                parents: Vec<PageNum>, 
            },
        }

        let f = try!(inner.open_file_for_cursor());

        let (cursor, from, into, behind, behind_rlock) = {
            let header = try!(inner.header.read());

            let (cursors, from) = {
                // find all the stuff that is getting promoted.  
                // we need a cursor on this so we can rewrite it into the next level.
                // we also need to remember where it came from, so we can remove it from the header segments lists.

                // we actually do not need read locks on this stuff, because
                // a read lock is simply to prevent commit_merge() from freeing
                // something that is still being read by something else.
                // two merges promoting the same stuff are not allowed.

                fn get_cursors(inner: &std::sync::Arc<InnerPart>, f: std::rc::Rc<std::cell::RefCell<File>>, merge_segments: &[SegmentHeaderInfo]) -> Result<Vec<PageCursor>> {
                    let mut cursors = Vec::with_capacity(merge_segments.len());
                    for i in 0 .. merge_segments.len() {
                        let pagenum = merge_segments[i].root_page;

                        // TODO it's a little silly here to construct a Lend<>
                        let done_page = move |_| -> () {
                        };
                        // TODO and the clone below is silly too
                        let buf = Lend::new(merge_segments[i].buf.clone(), box done_page);

                        let cursor = try!(PageCursor::new_already_read_page(&inner.path, f.clone(), pagenum, buf));
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
                        // TODO constant
                        let merge_segments = slice_from_end(&header.fresh, 4);

                        //println!("dest_level: {:?}   segments from: {:?}", from_level.get_dest_level(), merge_segments);
                        let cursors = try!(get_cursors(inner, f.clone(), &merge_segments));

                        let merge_segments = 
                            merge_segments
                            .iter()
                            .map(
                                |seg| {
// TODO use node iterator
                                    let node_pages = try!(seg.blocklist_unsorted_no_overflows(&inner.path, f.clone()));
                                    let seg = FromWholeSegment {
                                        root_page: seg.root_page,
                                        node_pages: node_pages,
                                    };
                                    Ok(seg)
                                }
                                )
                            .collect::<Result<Vec<_>>>();;
                        let merge_segments = try!(merge_segments);

                        (cursors, MergingFrom::Fresh{segments: merge_segments})
                    },
                    FromLevel::Young => {
                        // TODO constant
                        let merge_segments = slice_from_end(&header.young, 8);

                        //println!("dest_level: {:?}   segments from: {:?}", from_level.get_dest_level(), merge_segments);
                        let cursors = try!(get_cursors(inner, f.clone(), &merge_segments));

                        let merge_segments = 
                            merge_segments
                            .iter()
                            .map(
                                |seg| {
// TODO use node iterator
                                    let node_pages = try!(seg.blocklist_unsorted_no_overflows(&inner.path, f.clone()));
                                    let seg = FromWholeSegment {
                                        root_page: seg.root_page,
                                        node_pages: node_pages,
                                    };
                                    Ok(seg)
                                }
                                )
                            .collect::<Result<Vec<_>>>();;
                        let merge_segments = try!(merge_segments);

                        (cursors, MergingFrom::Young{segments: merge_segments})
                    },
                    FromLevel::Other(level) => {
                        assert!(header.levels.len() > level);
                        let depth_root = header.levels[level].buf[2];

                        let old_from_segment = &header.levels[level];

                        let (depth_promote, mut candidates) = {
                            let mut depth_promote =
                                if depth_root == 0 {
                                    // TODO gotta catch this case earlier
                                    unreachable!();
                                } else if depth_root == 1 {
                                    0
                                } else {
                                    1
                                };
                            let mut candidates = None;
                            loop {
                                // TODO it's a little silly here to construct a Lend<>
                                let done_page = move |_| -> () {
                                };
                                let buf = Lend::new(header.levels[level].buf.clone(), box done_page);

                                let root_parent = try!(ParentPage::new_already_read_page(&inner.path, f.clone(), old_from_segment.root_page, buf));
                                // TODO ouch.  we might end up loading this page more than once?
                                // because DepthIterator takes ownership of it.

                                let mut group = try!(DepthIterator::new(root_parent, depth_promote).collect::<Result<Vec<_>>>());

                                if group.len() < 2 {
                                    assert!(depth_promote > 0);
                                    depth_promote -= 1;
                                } else {
                                    candidates = Some(group);
                                    break;
                                }
                            }
                            (depth_promote, candidates.unwrap())
                        };

                        // TODO we probably need to be more clever about which one we
                        // choose.  for now, the following hack just tries to make sure
                        // the choice moves around the key range.
                        let i_chosen =
                            match old_from_segment.root_page % 3 {
                                0 => 0,
                                1 => candidates.len() - 1,
                                2 => candidates.len() / 2,
                                _ => unreachable!(),
                            };
                        let pg_chosen = candidates.remove(i_chosen);
                        //println!("chosen_page: {:?}", pg_chosen.page);
                        //println!("survivors will be: {:?}", candidates);
                        let survivors = candidates.into_iter().map(|pg| Ok(pg));
                        let chosen_page = pg_chosen.page;
                        let cursor = {
                            let buf = try!(read_and_alloc_page(&f, chosen_page, inner.pgsz));
                            // TODO it's a little silly here to construct a Lend<>
                            let done_page = move |_| -> () {
                            };
                            let buf = Lend::new(buf, box done_page);
                            let cursor = try!(PageCursor::new_already_read_page(&inner.path, f.clone(), chosen_page, buf));
                            cursor
                        };
                        let parents = {
                            // TODO it's a little silly here to construct a Lend<>
                            let done_page = move |_| -> () {
                            };
                            let buf = Lend::new(header.levels[level].buf.clone(), box done_page);
                            let parent = try!(ParentPage::new_already_read_page(&inner.path, f.clone(), old_from_segment.root_page, buf));
                            let dest_parents = 
                                NodeIterator::new(parent, depth_promote + 1)
                                .map(|r| r.map(|(depth, pagenum)| pagenum))
                                .collect::<Result<Vec<_>>>();
                            let dest_parents = try!(dest_parents);
                            dest_parents
                        };
                        //println!("parents above chosen and survivors: {:?}", parents);
// TODO use node iterator
                        let chosen_node_pages = try!(cursor.blocklist_unsorted_no_overflows());
                        let from = MergingFrom::Other{
                            level: level, 
                            old_segment: old_from_segment.root_page, 
                            chosen_page: chosen_page, 
                            chosen_depth: depth_promote, 
                            chosen_node_pages: chosen_node_pages, 
                            survivors: box survivors, 
                            parents: parents, 
                        };
                        (vec![cursor], from)

                    },
                }
            };

            let cursor = {
                let mc = MergeCursor::new(cursors);
                mc
            };

            // for the dest segment, we need an iterator of its leaves which
            // will be given to write_merge() so that it can be blended with
            // the stuff being promoted.
            let into = 
                match from_level.get_dest_level() {
                    DestLevel::Young => {
                        // for merges from Fresh into Young, there is no dest segment.
                        MergingInto::None
                    },
                    DestLevel::Other(dest_level) => {
                        if header.levels.len() > dest_level {
                            let dest_segment = &header.levels[dest_level];
                            let pt = try!(PageType::from_u8(dest_segment.buf[0]));

                            // TODO it's a little silly here to construct a Lend<>
                            let done_page = move |_| -> () {
                            };
                            // TODO and the clone below is silly too
                            let buf = Lend::new(dest_segment.buf.clone(), box done_page);

                            match pt {
                                PageType::LEAF_NODE => {
                                    //println!("root of the dest segment is a leaf");
                                    let leaf = try!(LeafPage::new_already_read_page(&inner.path, f.clone(), dest_segment.root_page, buf));
                                    let pg = try!(leaf.pgitem());
                                    let dest_leaves: Box<Iterator<Item=Result<pgitem>>> = box vec![Ok(pg)].into_iter();
                                    // TODO MergingInto::Leaf ?
                                    MergingInto::Level{
                                        level: dest_level, 
                                        old_segment: dest_segment.root_page, 
                                        leaves: dest_leaves, 
                                        parents: vec![],
                                    }
                                },
                                PageType::PARENT_NODE => {
                                    let parent = try!(ParentPage::new_already_read_page(&inner.path, f.clone(), dest_segment.root_page, buf));
                                    let depth = parent.depth();
                                    // TODO for large segments, probably need to reconsider decision
                                    // to go all the way down to the leaves level.  A 5 GB segment
                                    // would have over a million leaves.
                                    let dest_leaves: Box<Iterator<Item=Result<pgitem>>> = box DepthIterator::new(parent, 0);

                                    let dest_parents =
                                        if depth == 1 {
                                            vec![dest_segment.root_page]
                                        } else {
                                            // TODO it's a little silly here to construct a Lend<>
                                            let done_page = move |_| -> () {
                                            };
                                            // TODO and the clone below is silly too
                                            let buf = Lend::new(dest_segment.buf.clone(), box done_page);

                                            let parent = try!(ParentPage::new_already_read_page(&inner.path, f.clone(), dest_segment.root_page, buf));
                                            let dest_parents = 
                                                NodeIterator::new(parent, 1)
                                                .map(|r| r.map(|(depth, pagenum)| pagenum))
                                                .collect::<Result<Vec<_>>>();
                                            let dest_parents = try!(dest_parents);
                                            dest_parents
                                        };

                                    MergingInto::Level{
                                        level: dest_level, 
                                        old_segment: dest_segment.root_page, 
                                        leaves: dest_leaves, 
                                        parents: dest_parents,
                                    }
                                },
                            }

                        } else {
                            // the dest segment does not exist yet.
                            MergingInto::None
                        }
                    },
                };

            let (behind, behind_rlock) = {

                match from_level {
                    FromLevel::Fresh | FromLevel::Young => {
                        // during merge, a tombstone can be removed iff there is nothing
                        // for that key left in the segments behind the dest segment.
                        // so we need cursors on all those segments so that write_merge()
                        // can check.

                        let (behind_cursors, behind_segments) = {
                            fn get_cursor(
                                path: &str, 
                                f: std::rc::Rc<std::cell::RefCell<File>>,
                                seg: &SegmentHeaderInfo,
                                ) -> Result<PageCursor> {

                                let done_page = move |_| -> () {
                                };
                                // TODO and the clone below is silly too
                                let buf = Lend::new(seg.buf.clone(), box done_page);

                                let cursor = try!(PageCursor::new_already_read_page(path, f, seg.root_page, buf));
                                Ok(cursor)
                            }

                            let mut behind_cursors = vec![];
                            let mut behind_segments = HashSet::new();
                            match from_level.get_dest_level() {
                                DestLevel::Young => {
                                    for i in 0 .. header.young.len() {
                                        let seg = &header.young[i];

                                        behind_segments.insert(seg.root_page);

                                        let cursor = try!(get_cursor(&inner.path, f.clone(), seg));
                                        behind_cursors.push(cursor);
                                    }
                                    for i in 0 .. header.levels.len() {
                                        let seg = &header.levels[i];

                                        behind_segments.insert(seg.root_page);

                                        let cursor = try!(get_cursor(&inner.path, f.clone(), seg));
                                        behind_cursors.push(cursor);
                                    }
                                },
                                DestLevel::Other(dest_level) => {
                                    for i in dest_level + 1 .. header.levels.len() {
                                        let seg = &header.levels[i];

                                        behind_segments.insert(seg.root_page);

                                        let cursor = try!(get_cursor(&inner.path, f.clone(), seg));
                                        behind_cursors.push(cursor);
                                    }
                                },
                            }
                            (behind_cursors, behind_segments)
                        };

                        let behind_rlock =
                            if behind_segments.is_empty() {
                                None
                            } else {
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
                    _ => {
                        (vec![], None)
                    },
                }

            };

            (cursor, from, into, behind, behind_rlock)
        };

        let mut pw = try!(PageWriter::new(inner.clone()));

        enum MergedInto {
            None,
            Level{
                level: DestLevel, 
                old_segment: PageNum, 
                parents: Vec<PageNum>, 
                leaves_rewritten: Vec<PageNum>, 
                overflows_freed: Vec<BlockList>, 
            },
        }

        let (new_dest_segment, overflows_eaten, into) = {
            // note that cursor.First() should NOT have already been called
            let mut cursor = cursor;
            try!(cursor.First());
            if cursor.IsValid() {
                let mut source = CursorIterator::new(cursor);
                let mut behind = behind;
                match into {
                    MergingInto::None => {
                        let leaves: Box<Iterator<Item=Result<pgitem>>> = box std::iter::empty();
                        let wrote = try!(write_merge(&mut pw, &mut source, leaves, &mut behind, &inner.path, f.clone(), from_level.get_dest_level()));
                        assert!(wrote.leaves_rewritten.is_empty());
                        // TODO asserts here
                        let overflows_eaten = source.eaten();
                        (wrote.segment, overflows_eaten, MergedInto::None)
                    },
                    MergingInto::Level{old_segment, leaves, parents, ..} => {
                        let wrote = try!(write_merge(&mut pw, &mut source, leaves, &mut behind, &inner.path, f.clone(), from_level.get_dest_level()));
                        // TODO asserts here
                        let overflows_eaten = source.eaten();
                        let into = MergedInto::Level{
                            level: from_level.get_dest_level(),
                            old_segment: old_segment, 
                            parents: parents, 
                            leaves_rewritten: wrote.leaves_rewritten, 
                            overflows_freed: wrote.overflows_freed, 
                        };
                        (wrote.segment, overflows_eaten, into)
                    },
                }
            } else {
                (None, vec![], MergedInto::None)
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
                &MergedInto::None => {
                    None
                },
                &MergedInto::Level{old_segment, ..} => {
                    Some(old_segment)
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

        let now_inactive: HashMap<PageNum, BlockList> = {
            let mut now_inactive = HashMap::new();
            match from {
                MergingFrom::Fresh{ref segments} => {
                    for seg in segments.iter() {
                        let mut blocks = seg.node_pages.clone();
                        blocks.add_page_no_reorder(seg.root_page);
                        // TODO overflows_eaten should be a hashmap
                        for &(s,ref b) in overflows_eaten.iter() {
                            if s == seg.root_page {
                                blocks.add_blocklist_no_reorder(b);
                            }
                        }
                        now_inactive.insert(seg.root_page, blocks);
                    }
                },
                MergingFrom::Young{ref segments} => {
                    for seg in segments.iter() {
                        let mut blocks = seg.node_pages.clone();
                        blocks.add_page_no_reorder(seg.root_page);
                        // TODO overflows_eaten should be a hashmap
                        for &(s,ref b) in overflows_eaten.iter() {
                            if s == seg.root_page {
                                blocks.add_blocklist_no_reorder(b);
                            }
                        }
                        now_inactive.insert(seg.root_page, blocks);
                    }
                },
                MergingFrom::Other{old_segment, chosen_page, ref chosen_node_pages, ref parents, ..} => {
                    let mut blocks = chosen_node_pages.clone();
                    blocks.add_page_no_reorder(chosen_page);
                    // add all the old parent nodes above the survivors
                    for pgnum in parents {
                        blocks.add_page_no_reorder(*pgnum);
                    }
                    // TODO need overflows_eaten here?  probably not, because
                    // this case always has only one thing in the merge cursor, right?
                    now_inactive.insert(old_segment, blocks);
                },
            }
            match into {
                MergedInto::Level{old_segment, parents, leaves_rewritten, overflows_freed, ..} => {
                    let mut blocks = BlockList::new();
                    for pgnum in leaves_rewritten {
                        blocks.add_page_no_reorder(pgnum);
                    }
                    for pgnum in parents {
                        blocks.add_page_no_reorder(pgnum);
                    }
                    for b in overflows_freed {
                        blocks.add_blocklist_no_reorder(&b);
                    }
                    now_inactive.insert(old_segment, blocks);
                },
                MergedInto::None => {
                },
            }
            now_inactive
        };

        let from = 
            match from {
                MergingFrom::Fresh{segments} => {
                    let segments = segments.into_iter().map(|seg| seg.root_page).collect::<Vec<_>>();
                    MergeFrom::Fresh{
                        segments: segments,
                    }
                },
                MergingFrom::Young{segments} => {
                    let segments = segments.into_iter().map(|seg| seg.root_page).collect::<Vec<_>>();
                    MergeFrom::Young{
                        segments: segments,
                    }
                },
                MergingFrom::Other{level, old_segment, chosen_depth, survivors, ..} => {
                    let mut survivors = survivors.peekable();

                    let mut chain = ParentNodeWriter::new(pw.page_size(), chosen_depth);
                    let mut last_page = None;
                    loop {
                        match survivors.next() {
                            None => {
                                // should have caught this on peek
                                unreachable!();
                            },
                            Some(Ok(pg)) => {
                                let pgnum = pg.page;
                                try!(chain.add_child(&mut pw, pg));
                                if survivors.peek().is_none() {
                                    last_page = Some(pgnum);
                                    break;
                                }
                            },
                            Some(Err(e)) => {
                                return Err(e);
                            },
                        }
                    }
                    match last_page {
                        Some(page) => {
                            let buf = try!(read_and_alloc_page(&f, page, pw.page_size()));
                            let (count_parent_nodes, seg) = try!(chain.done(&mut pw, buf));
                            let seg = seg.unwrap();
                            MergeFrom::Other{
                                level: level, 
                                old_segment: old_segment, 
                                new_segment: seg
                            }
                        },
                        None => {
                            // TODO should never happen.  this means there were no survivors,
                            // so we chose the root of the segment, which should not happen.
                            unreachable!();
                        },
                    }
                },
            };

        try!(pw.end());

        if cfg!(expensive_check) 
        {
            let old_now_inactive = {
                let mut now_inactive = HashMap::new();
                match from {
                    MergeFrom::Fresh{ref segments} => {
                        for &seg in segments.iter() {
                            let blocks = try!(get_blocklist_for_segment_including_root(seg, inner.pgsz, &inner.path, f.clone()));
                            now_inactive.insert(seg, blocks);
                        }
                    },
                    MergeFrom::Young{ref segments} => {
                        for &seg in segments.iter() {
                            let blocks = try!(get_blocklist_for_segment_including_root(seg, inner.pgsz, &inner.path, f.clone()));
                            now_inactive.insert(seg, blocks);
                        }
                    },
                    MergeFrom::Other{old_segment, ..} => {
                        let blocks = try!(get_blocklist_for_segment_including_root(old_segment, inner.pgsz, &inner.path, f.clone()));
                        now_inactive.insert(old_segment, blocks);
                    },
                }
                match old_dest_segment {
                    Some(seg) => {
                        let blocks = try!(get_blocklist_for_segment_including_root(seg, inner.pgsz, &inner.path, f.clone()));
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
                        let mut blocks = try!(seg.blocklist_unsorted(&inner.path, f.clone()));
                        blocks.add_page_no_reorder(seg.root_page);
                        for (k,b) in old_now_inactive.iter_mut() {
                            b.remove_anything_in(&blocks);
                        }
                    },
                    None => {
                    },
                }
                match from {
                    MergeFrom::Other{ref new_segment, ..} => {
                        let mut blocks = try!(new_segment.blocklist_unsorted(&inner.path, f.clone()));
                        blocks.add_page_no_reorder(new_segment.root_page);
                        for (k,b) in old_now_inactive.iter_mut() {
                            b.remove_anything_in(&blocks);
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

                        match new_dest_segment {
                            Some(ref seg) => {
                                //let blocks = try!(seg.blocklist_unsorted(&inner.path, f.clone()));
                                //println!("new_dest_segment: {:?}", blocks);
                                println!("new_dest_segment: {:?}", seg.root_page);
                            },
                            None => {
                                println!("new_dest_segment: None");
                            },
                        }
                        match from {
                            MergeFrom::Other{ref new_segment, ..} => {
                                println!("new_from_segment: {:?}", new_segment.root_page);
                            },
                            _ => {
                                println!("new_from_segment: None");
                            },
                        }

                        panic!("inactive mismatch");
                    }
                }
            }
        }

        let pm = 
            PendingMerge {
                from: from,
                old_dest_segment: old_dest_segment,
                new_dest_segment: new_dest_segment,
                now_inactive: now_inactive,
            };
        //println!("PendingMerge: {:?}", pm);
        Ok(pm)
    }

    fn commit_merge(&self, pm: PendingMerge) -> Result<()> {
        let dest_level = pm.from.get_dest_level();
        //println!("commit_merge: {:?}", pm);
        {
            let mut header = try!(self.header.write());

            // TODO assert new seg shares no pages with any seg in current state

            let mut newHeader = header.clone();

            fn update_header(newHeader: &mut HeaderData, old_dest_segment: Option<PageNum>, new_dest_segment: Option<SegmentHeaderInfo>, dest_level: usize) {
                match (old_dest_segment, new_dest_segment) {
                    (None, None) => {
                        // a merge resulted in what would have been an empty segment.
                        // multiple segments from the young level cancelled each other out.
                        // there wasn't anything in this level anyway.
                        assert!(newHeader.levels.len() == dest_level);
                    },
                    (None, Some(new_seg)) => {
                        // first merge into this new level
                        assert!(newHeader.levels.len() == dest_level);
                        newHeader.levels.push(new_seg);
                    },
                    (Some(_), None) => {
                        // a merge resulted in what would have been an empty segment.
                        // segments from young cancelled out everything that was in
                        // the dest level.
                        assert!(dest_level < newHeader.levels.len());
                        // TODO what do we do about this?
                        panic!();
                    },
                    (Some(old), Some(new_seg)) => {
                        // level already exists
                        assert!(dest_level < newHeader.levels.len());
                        assert!(newHeader.levels[dest_level].root_page == old);
                        newHeader.levels[dest_level] = new_seg;
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

            match pm.from {
                MergeFrom::Fresh{segments} => {
                    let ndx = find_segments_in_list(&segments, &header.fresh);
                    for _ in &segments {
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
                MergeFrom::Young{segments} => {
                    let ndx = find_segments_in_list(&segments, &header.young);
                    for _ in &segments {
                        newHeader.young.remove(ndx);
                    }

                    let dest_level = 0;
                    update_header(&mut newHeader, pm.old_dest_segment, pm.new_dest_segment, dest_level);
                },
                MergeFrom::Other{level, old_segment, new_segment} => {
                    assert!(old_segment == newHeader.levels[level].root_page);
                    newHeader.levels[level] = new_segment;

                    let dest_level = level + 1;
                    update_header(&mut newHeader, pm.old_dest_segment, pm.new_dest_segment, dest_level);
                },
            }

            newHeader.mergeCounter = newHeader.mergeCounter + 1;

            let mut fs = try!(self.OpenForWriting());
            try!(self.write_header(&mut header, &mut fs, newHeader));
        }

        //println!("merge committed");

        if !pm.now_inactive.is_empty() {
            let mut space = try!(self.space.lock());
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
        self.inner.pgsz
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
            try!(utils::SeekPage(&mut self.f, self.inner.pgsz, pg));
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

