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
#![feature(associated_consts)]
#![feature(vec_push_all)]
#![feature(iter_arith)]

use std::collections::HashMap;
use std::collections::HashSet;

extern crate bson;

extern crate misc;
extern crate elmo;
extern crate lsm;

use lsm::ICursor;

pub type Result<T> = elmo::Result<T>;

/*

this doesn't help.

pub struct WrapError {
    err: lsm::Error,
}

impl From<WrapError> for elmo::Error {
    fn from(err: WrapError) -> elmo::Error {
        elmo::Error::Whatever(box err.err)
    }
}

impl From<lsm::Error> for WrapError {
    fn from(err: lsm::Error) -> WrapError {
        WrapError {
            err: err
        }
    }
}

impl Into<WrapError> for lsm::Error {
    fn into(self) -> WrapError {
        WrapError {
            err: self
        }
    }
}
*/

/*

the compiler won't allow this

the impl does not reference any types defined in this crate; 
only traits defined in the current crate can be implemented for arbitrary types

impl From<lsm::Error> for elmo::Error {
    fn from(err: lsm::Error) -> elmo::Error {
        elmo::Error::Whatever(box err)
    }
}
*/

struct MyIndexPrep {
    index_id: u64,
    spec: bson::Document,
    options: bson::Document,
    normspec: Vec<(String,elmo::IndexType)>,
    weights: Option<HashMap<String,i32>>,
    // TODO maybe keep the options we need here directly, sparse and unique
}

struct MyCollectionWriter {
    // TODO might want db and coll names here for caching
    indexes: Vec<MyIndexPrep>,
    collection_id: u64,
}

struct MyCollectionReader {
    seq: Box<Iterator<Item=Result<elmo::Row>>>,

    // TODO need counts here
}

// TODO LivingCursorBsonValueIterator
// and PrefixCursorBsonValueIterator 
// are basically identical.

struct LivingCursorBsonValueIterator {
    cursor: lsm::LivingCursor,
}

impl LivingCursorBsonValueIterator {
    fn iter_next(&mut self) -> Result<Option<elmo::Row>> {
        try!(self.cursor.Next().map_err(elmo::wrap_err));
        if self.cursor.IsValid() {
            let v = try!(self.cursor.LiveValueRef().map_err(elmo::wrap_err));
            let v = try!(v.map(lsm_map_to_bson).map_err(elmo::wrap_err));
            let v = v.into_value();
            let row = elmo::Row {
                doc: v,
                pos: None,
                score: None,
            };
            Ok(Some(row))
        } else {
            Ok(None)
        }
    }
}

impl Iterator for LivingCursorBsonValueIterator {
    type Item = Result<elmo::Row>;
    fn next(&mut self) -> Option<Self::Item> {
        match self.iter_next() {
            Err(e) => {
                return Some(Err(e));
            },
            Ok(v) => {
                match v {
                    None => {
                        return None;
                    },
                    Some(v) => {
                        return Some(Ok(v));
                    }
                }
            },
        }
    }
}

struct PrefixCursorBsonValueIterator {
    cursor: lsm::PrefixCursor,
}

impl PrefixCursorBsonValueIterator {
    fn iter_next(&mut self) -> Result<Option<elmo::Row>> {
        try!(self.cursor.Next().map_err(elmo::wrap_err));
        if self.cursor.IsValid() {
            let v = try!(self.cursor.LiveValueRef().map_err(elmo::wrap_err));
            let v = try!(v.map(lsm_map_to_bson).map_err(elmo::wrap_err));
            let v = v.into_value();
            let row = elmo::Row {
                doc: v,
                pos: None,
                score: None,
            };
            Ok(Some(row))
        } else {
            Ok(None)
        }
    }
}

impl Iterator for PrefixCursorBsonValueIterator {
    type Item = Result<elmo::Row>;
    fn next(&mut self) -> Option<Self::Item> {
        match self.iter_next() {
            Err(e) => {
                return Some(Err(e));
            },
            Ok(v) => {
                match v {
                    None => {
                        return None;
                    },
                    Some(v) => {
                        return Some(Ok(v));
                    }
                }
            },
        }
    }
}

struct RangeCursorVarintIterator {
    cursor: lsm::RangeCursor,
}

impl RangeCursorVarintIterator {
    fn iter_next(&mut self) -> Result<Option<u64>> {
        try!(self.cursor.Next().map_err(elmo::wrap_err));
        if self.cursor.IsValid() {
            let v = try!(self.cursor.LiveValueRef().map_err(elmo::wrap_err));
            let v = try!(v.map(lsm_map_to_varint).map_err(elmo::wrap_err));
            Ok(Some(v))
        } else {
            Ok(None)
        }
    }
}

impl Iterator for RangeCursorVarintIterator {
    type Item = Result<u64>;
    fn next(&mut self) -> Option<Self::Item> {
        match self.iter_next() {
            Err(e) => {
                return Some(Err(e));
            },
            Ok(v) => {
                match v {
                    None => {
                        return None;
                    },
                    Some(v) => {
                        return Some(Ok(v));
                    }
                }
            },
        }
    }
}

struct MyReader {
    myconn: std::rc::Rc<MyConn>,
}

struct MyWriter<'a> {
    myconn: std::rc::Rc<MyConn>,
    tx: std::sync::MutexGuard<'a, lsm::WriteLock>,
    pending: HashMap<Box<[u8]>,lsm::Blob>,
    // TODO cache the collection writer
    orig_next_collection_id: u64,
    orig_next_index_id: u64,
    orig_next_record_id: u64,
    next_collection_id: u64,
    next_index_id: u64,
    next_record_id: u64,
}

struct MyConn {
    conn: lsm::db,
}

struct MyPublicConn {
    myconn: std::rc::Rc<MyConn>,
}

/// key:
///     (tag)
/// value:
///     varint
pub const NEXT_COLLECTION_ID: u8 = 1;

/// key:
///     (tag)
/// value:
///     varint
pub const NEXT_INDEX_ID: u8 = 2;

// TODO should we have record ids?  or just have the _id of each record
// be its actual key?  
//
// the pk can be big, and it will be duplicated,
// once in the key, and once in the bson doc itself.
//
// the pk or id is also duplicated in the index entries.
// and in their backlinks.
//
// if we don't have a recid, how would we store a document that doesn't
// have any _id at all?

/// key:
///     (tag)
/// value:
///     recid (varint)
pub const NEXT_RECORD_ID: u8 = 3;

/// key:
///     (tag)
///     db name (len + str)
///     coll name (len + str)
/// value:
///     collid (varint)
pub const NAME_TO_COLLECTION_ID: u8 = 10;

/// key:
///     (tag)
///     collid (varint)
/// value:
///     properties (bson):
///         d: db name (str)
///         c: coll name (str)
///         o: options (document)
pub const COLLECTION_ID_TO_PROPERTIES: u8 = 11;

/// key:
///     (tag)
///     collid (varint)
///     index name (len + str)
/// value:
///     indexid (varint)
pub const NAME_TO_INDEX_ID: u8 = 20;

/// key:
///     (tag)
///     indexid (varint)
/// value:
///     properties (bson):
///         n: name (str)
///         s: spec (bson)
///         o: options (bson)
pub const INDEX_ID_TO_PROPERTIES: u8 = 21;

/// key:
///     (tag)
///     collid (varint)
///     recid (varint)
/// value:
///     doc (bson)
pub const RECORD: u8 = 30;

// TODO do we want the collid included below as well?  so we can
// do a range delete and get all index entries for a given coll?

/// key:
///     (tag)
///     indexid (varint)
///     k (len + bytes)
///     recid (varint) (not present when index option unique)
/// value:
///     recid (varint) (present only when index option unique?)
pub const INDEX_ENTRY: u8 = 40;

/// key:
///     (tag)
///     collid (varint)
///     recid (varint)
///     (complete index key)
/// value:
///    (none)
pub const RECORD_ID_TO_INDEX_ENTRY: u8 = 41;

fn encode_key_name_to_collection_id(db: &str, coll: &str) -> Box<[u8]> {
    // TODO capacity
    let mut k = vec![];
    k.push(NAME_TO_COLLECTION_ID);

    // From the mongo docs:
    // The maximum length of the collection namespace, which includes the database name, the dot
    // (.) separator, and the collection name (i.e. <database>.<collection>), is 120 bytes.

    let b = db.as_bytes();
    k.push(b.len() as u8);
    k.push_all(b);

    let b = coll.as_bytes();
    k.push(b.len() as u8);
    k.push_all(b);

    k.into_boxed_slice()
}

fn decode_key_name_to_collection_id(k: &lsm::KeyRef) -> Result<(String, String)> {
    let len_db = try!(k.u8_at(1).map_err(elmo::wrap_err)) as usize;
    let begin_db = 2;
    let db = try!(k.map_range(begin_db, begin_db + len_db, lsm_map_to_string).map_err(elmo::wrap_err));
    let len_coll = try!(k.u8_at(begin_db + len_db).map_err(elmo::wrap_err)) as usize;
    let begin_coll = begin_db + len_db + 1;
    let coll = try!(k.map_range(begin_coll, begin_coll + len_coll, lsm_map_to_string).map_err(elmo::wrap_err));
    Ok((db, coll))
}

fn decode_key_name_to_index_id(k: &lsm::KeyRef) -> Result<(u64, String)> {
    let first_byte_of_collection_id = try!(k.u8_at(1).map_err(elmo::wrap_err));
    let size_of_collection_id = misc::varint::first_byte_to_space_needed(first_byte_of_collection_id);
    let collection_id = try!(k.map_range(1, 1 + size_of_collection_id, lsm_map_to_varint).map_err(elmo::wrap_err));
    let begin_name = 1 + size_of_collection_id;
    let name = try!(k.map_range(begin_name, k.len(), lsm_map_to_string).map_err(elmo::wrap_err));
    Ok((collection_id, name))
}

fn push_varint(v: &mut Vec<u8>, n: u64) {
    let mut buf = [0; 9];
    let mut cur = 0;
    misc::varint::write(&mut buf, &mut cur, n);
    v.push_all(&buf[0 .. cur]);
}

fn encode_key_tag_and_varint(tag: u8, id: u64) -> Vec<u8> {
    // TODO capacity
    let mut k = vec![];
    k.push(tag);

    push_varint(&mut k, id);

    k
}

fn encode_key_collection_id_to_properties(id: u64) -> Vec<u8> {
    encode_key_tag_and_varint(COLLECTION_ID_TO_PROPERTIES, id)
}

fn encode_key_index_id_to_properties(id: u64) -> Vec<u8> {
    encode_key_tag_and_varint(INDEX_ID_TO_PROPERTIES, id)
}

fn encode_key_name_to_index_id(collection_id: u64, name: &str) -> Vec<u8> {
    // TODO capacity
    let mut k = vec![];
    k.push(NAME_TO_INDEX_ID);

    // From the mongo docs:
    // The maximum length of the collection namespace, which includes the database name, the dot
    // (.) separator, and the collection name (i.e. <database>.<collection>), is 120 bytes.

    let ba = u64_to_boxed_varint(collection_id);
    k.push_all(&ba);

    let b = name.as_bytes();
    k.push(b.len() as u8);
    k.push_all(b);

    k
}

fn lsm_map_to_string(ba: &[u8]) -> lsm::Result<String> {
    let s = try!(std::str::from_utf8(&ba));
    Ok(String::from(s))
}

fn lsm_map_to_varint(ba: &[u8]) -> lsm::Result<u64> {
    let mut cur = 0;
    let n = misc::varint::read(ba, &mut cur);
    // TODO assert cur used up all of ba?
    Ok(n)
}

fn u64_to_boxed_varint(n: u64) -> Box<[u8]> {
    let mut buf = [0; 9];
    let mut cur = 0;
    misc::varint::write(&mut buf, &mut cur, n);
    let mut v = Vec::with_capacity(cur);
    v.push_all(&buf[0 .. cur]);
    let v = v.into_boxed_slice();
    v
}

fn lsm_map_to_bson(ba: &[u8]) -> lsm::Result<bson::Document> {
    let r = bson::Document::from_bson(ba);
    let r = r.map_err(lsm::wrap_err);
    r
}

impl MyConn {
    fn get_next_id(&self, tag: u8) -> Result<u64> {
        let mut k = Vec::with_capacity(1);
        k.push(tag);
        let k = k.into_boxed_slice();

        let n = {
            let mut csr = try!(self.conn.OpenCursor().map_err(elmo::wrap_err));
            try!(csr.SeekRef(&lsm::KeyRef::for_slice(&k), lsm::SeekOp::SEEK_EQ).map_err(elmo::wrap_err));
            if csr.IsValid() {
                let v = try!(csr.LiveValueRef().map_err(elmo::wrap_err));
                let n = try!(v.map(lsm_map_to_varint).map_err(elmo::wrap_err));
                n
            } else {
                1
            }
        };

        Ok(n)
    }

    fn get_value_for_key_as_varint(&self, k: &[u8]) -> Result<Option<u64>> {
        // TODO this should probably take a cursor parameter, not create one
        let mut csr = try!(self.conn.OpenCursor().map_err(elmo::wrap_err));
        try!(csr.SeekRef(&lsm::KeyRef::for_slice(&k), lsm::SeekOp::SEEK_EQ).map_err(elmo::wrap_err));
        if csr.IsValid() {
            let v = try!(csr.LiveValueRef().map_err(elmo::wrap_err));
            let id = try!(v.map(lsm_map_to_varint).map_err(elmo::wrap_err));
            Ok(Some(id))
        } else {
            Ok(None)
        }
    }

    fn get_value_for_key_as_bson(&self, k: &[u8]) -> Result<Option<bson::Document>> {
        // TODO this should probably take a cursor parameter, not create one
        let mut csr = try!(self.conn.OpenCursor().map_err(elmo::wrap_err));
        try!(csr.SeekRef(&lsm::KeyRef::for_slice(&k), lsm::SeekOp::SEEK_EQ).map_err(elmo::wrap_err));
        if csr.IsValid() {
            let v = try!(csr.LiveValueRef().map_err(elmo::wrap_err));
            let id = try!(v.map(lsm_map_to_bson).map_err(elmo::wrap_err));
            Ok(Some(id))
        } else {
            Ok(None)
        }
    }

    fn get_reader_collection_scan(&self, myconn: std::rc::Rc<MyConn>, db: &str, coll: &str) -> Result<MyCollectionReader> {
        // check to see if the collection exists and get its id
        let k = encode_key_name_to_collection_id(db, coll);
        match try!(self.get_value_for_key_as_varint(&k)) {
            None => {
                let rdr = 
                    MyCollectionReader {
                        seq: box std::iter::empty(),
                    };
                Ok(rdr)
            },
            Some(collection_id) => {
                let mut k = vec![];
                k.push(RECORD);
                push_varint(&mut k, collection_id);
                let cursor = try!(self.conn.OpenCursor().map_err(elmo::wrap_err));
                let cursor = lsm::PrefixCursor::new(cursor, k.into_boxed_slice());
                let seq = 
                    PrefixCursorBsonValueIterator {
                        cursor: cursor,
                    };
                let rdr = 
                    MyCollectionReader {
                        seq: box seq,
                    };
                Ok(rdr)
            },
        }
    }

    fn get_reader_text_index_scan(&self, myconn: std::rc::Rc<MyConn>, commit_on_drop: bool, ndx: &elmo::IndexInfo, eq: elmo::QueryKey, terms: Vec<elmo::TextQueryTerm>) -> Result<MyCollectionReader> {
        unimplemented!();
    }

    fn get_reader_regular_index_scan(&self, myconn: std::rc::Rc<MyConn>, ndx: &elmo::IndexInfo, bounds: elmo::QueryBounds) -> Result<MyCollectionReader> {
        let collection_id = 
            match try!(self.get_value_for_key_as_varint(&encode_key_name_to_collection_id(&ndx.db, &ndx.coll))) {
                Some(id) => id,
                None => return Err(elmo::Error::Misc(String::from("collection does not exist"))),
            };
        let index_id = 
            match try!(self.get_value_for_key_as_varint(&encode_key_name_to_index_id(collection_id, &ndx.name))) {
                Some(id) => id,
                None => return Err(elmo::Error::Misc(String::from("index does not exist"))),
            };

        fn add_one(ba: &Vec<u8>) -> Vec<u8> {
            let mut a = ba.clone();
            let mut i = a.len() - 1;
            loop {
                if a[i] == 255 {
                    a[i] = 0;
                    if i == 0 {
                        panic!("TODO handle case where add_one to binary array overflows the first byte");
                    } else {
                        i = i - 1;
                    }
                } else {
                    a[i] = a[i] + 1;
                    break;
                }
            }
            a
        }

        fn f_twok(cursor: lsm::LivingCursor, kmin: Box<[u8]>, kmax: Box<[u8]>, min_cmp: lsm::OpGt, max_cmp: lsm::OpLt) -> lsm::RangeCursor {
            let min = lsm::Min::new(kmin, min_cmp);
            let max = lsm::Max::new(kmax, max_cmp);
            let cursor = lsm::RangeCursor::new(cursor, Some(min), Some(max));
            cursor
        }

        fn f_two(preface: Vec<u8>, cursor: lsm::LivingCursor, eqvals: elmo::QueryKey, minvals: elmo::QueryKey, maxvals: elmo::QueryKey, min_cmp: lsm::OpGt, max_cmp: lsm::OpLt) -> lsm::RangeCursor {
            let mut kmin = preface.clone();
            bson::Value::push_encode_multi_for_index(&mut kmin, &eqvals, Some(&minvals));
            let mut kmax = preface;
            bson::Value::push_encode_multi_for_index(&mut kmax, &eqvals, Some(&maxvals));
            let kmin = kmin.into_boxed_slice();
            let kmax = kmax.into_boxed_slice();
            f_twok(cursor, kmin, kmax, min_cmp, max_cmp)
        }

        fn f_gt(preface: Vec<u8>, cursor: lsm::LivingCursor, vals: elmo::QueryKey, min_cmp: lsm::OpGt) -> lsm::RangeCursor {
            let mut kmin = preface.clone();
            bson::Value::push_encode_multi_for_index(&mut kmin, &vals, None);
            let kmin = kmin.into_boxed_slice();
            let min = lsm::Min::new(kmin, min_cmp);
            let cursor = lsm::RangeCursor::new(cursor, Some(min), None);
            cursor
        }

        fn f_lt(preface: Vec<u8>, cursor: lsm::LivingCursor, vals: elmo::QueryKey, max_cmp: lsm::OpLt) -> lsm::RangeCursor {
            let mut kmax = preface.clone();
            bson::Value::push_encode_multi_for_index(&mut kmax, &vals, None);
            let kmax = kmax.into_boxed_slice();
            let max = lsm::Max::new(kmax, max_cmp);
            let cursor = lsm::RangeCursor::new(cursor, None, Some(max));
            cursor
        }

        let mut key_preface = vec![];
        key_preface.push(INDEX_ENTRY);
        push_varint(&mut key_preface, index_id);

        let cursor = try!(self.conn.OpenCursor().map_err(elmo::wrap_err));
        let cursor =
            match bounds {
                elmo::QueryBounds::GT(vals) => f_gt(key_preface, cursor, vals, lsm::OpGt::GT),
                elmo::QueryBounds::GTE(vals) => f_gt(key_preface, cursor, vals, lsm::OpGt::GTE),
                elmo::QueryBounds::LT(vals) => f_lt(key_preface, cursor, vals, lsm::OpLt::LT),
                elmo::QueryBounds::LTE(vals) => f_lt(key_preface, cursor, vals, lsm::OpLt::LTE),
                elmo::QueryBounds::GT_LT(eqvals, minvals, maxvals) => f_two(key_preface, cursor, eqvals, minvals, maxvals, lsm::OpGt::GT, lsm::OpLt::LT),
                elmo::QueryBounds::GTE_LT(eqvals, minvals, maxvals) => f_two(key_preface, cursor, eqvals, minvals, maxvals, lsm::OpGt::GTE, lsm::OpLt::LT),
                elmo::QueryBounds::GT_LTE(eqvals, minvals, maxvals) => f_two(key_preface, cursor, eqvals, minvals, maxvals, lsm::OpGt::GT, lsm::OpLt::LTE),
                elmo::QueryBounds::GTE_LTE(eqvals, minvals, maxvals) => f_two(key_preface, cursor, eqvals, minvals, maxvals, lsm::OpGt::GTE, lsm::OpLt::LTE),
                elmo::QueryBounds::EQ(vals) => {
                    let mut kmin = key_preface.clone();
                    bson::Value::push_encode_multi_for_index(&mut kmin, &vals, None);
                    let kmax = add_one(&kmin);
                    let kmin = kmin.into_boxed_slice();
                    let kmax = kmax.into_boxed_slice();
                    f_twok(cursor, kmin, kmax, lsm::OpGt::GTE, lsm::OpLt::LT)
                },
            };

        let seq = 
            RangeCursorVarintIterator {
                cursor: cursor,
            };

        // TODO DISTINCT problem here? we don't want this producing the same record twice

        // the iterator above yields record ids.
        // now we need something that, for each record id yielded by an
        // index entry, looks up the actual record and yields THAT.  in
        // sqlite, this was a join.

        let mut cursor = try!(self.conn.OpenCursor().map_err(elmo::wrap_err));
        let seq = seq.map(
            move |record_id: Result<u64>| -> Result<elmo::Row> {
                match record_id {
                    Ok(record_id) => {
                        let mut k = vec![];
                        k.push(RECORD);
                        push_varint(&mut k, collection_id);
                        push_varint(&mut k, record_id);
                        try!(cursor.SeekRef(&lsm::KeyRef::for_slice(&k), lsm::SeekOp::SEEK_EQ).map_err(elmo::wrap_err));
                        if cursor.IsValid() {
                            let v = try!(cursor.LiveValueRef().map_err(elmo::wrap_err));
                            let v = try!(v.map(lsm_map_to_bson).map_err(elmo::wrap_err));
                            let v = v.into_value();
                            let row = elmo::Row {
                                doc: v,
                                pos: None,
                                score: None,
                            };
                            Ok(row)
                        } else {
                            Err(elmo::Error::Misc(String::from("record id not found?!?")))
                        }
                    },
                    Err(e) => {
                        Err(e)
                    },
                }
            });

        let rdr = 
            MyCollectionReader {
                seq: box seq,
            };

        Ok(rdr)
    }

    // TODO this func could take an option collection_id and constrain easily
    fn base_list_indexes(&self) -> Result<Vec<elmo::IndexInfo>> {
        let csr = try!(self.conn.OpenCursor().map_err(elmo::wrap_err));
        let csr = lsm::PrefixCursor::new(csr, box [NAME_TO_INDEX_ID]);
        let mut a = vec![];

        while csr.IsValid() {
            let k = try!(csr.KeyRef().map_err(elmo::wrap_err));
            let (collection_id, name) = try!(decode_key_name_to_index_id(&k));

            let k = encode_key_collection_id_to_properties(collection_id);
            let mut collection_properties = try!(self.get_value_for_key_as_bson(&k)).unwrap_or(bson::Document::new());
            let db = try!(collection_properties.must_remove_string("d"));
            let coll = try!(collection_properties.must_remove_string("c"));
            //let options = try!(collection_properties.must_remove_document("o"));

            let v = try!(csr.LiveValueRef().map_err(elmo::wrap_err));
            let index_id = try!(v.map(lsm_map_to_varint).map_err(elmo::wrap_err));

            let k = encode_key_index_id_to_properties(index_id);
            let mut index_properties = try!(self.get_value_for_key_as_bson(&k)).unwrap_or(bson::Document::new());
            //let name = try!(index_properties.must_remove_string("n"));
            let spec = try!(index_properties.must_remove_document("s"));
            let options = try!(index_properties.must_remove_document("o"));

            let info = elmo::IndexInfo {
                db: String::from(db),
                coll: String::from(coll),
                name: String::from(name),
                spec: spec,
                options: options,
            };
            a.push(info);
        }
        Ok(a)
    }

    // TODO this function could be implemented in terms of the other one above
    fn list_indexes_for_collection(&self, collection_id: u64) -> Result<Vec<MyIndexPrep>> {
        let q = encode_key_tag_and_varint(NAME_TO_INDEX_ID, collection_id);
        let csr = try!(self.conn.OpenCursor().map_err(elmo::wrap_err));
        let csr = lsm::PrefixCursor::new(csr, q.into_boxed_slice());
        let mut a = vec![];

        while csr.IsValid() {
            // let k = try!(csr.KeyRef().map_err(elmo::wrap_err));
            // the name of the index is on the end of this key, but we don't need it

            let v = try!(csr.LiveValueRef().map_err(elmo::wrap_err));
            let index_id = try!(v.map(lsm_map_to_varint).map_err(elmo::wrap_err));

            let k = encode_key_index_id_to_properties(index_id);
            let mut index_properties = try!(self.get_value_for_key_as_bson(&k)).unwrap_or(bson::Document::new());
            //let name = try!(index_properties.must_remove_string("n"));
            let spec = try!(index_properties.must_remove_document("s"));
            let options = try!(index_properties.must_remove_document("o"));

            let unique = 
                match options.get("unique") {
                    Some(&bson::Value::BBoolean(b)) => b,
                    _ => false,
                };

            let sparse = 
                match options.get("sparse") {
                    Some(&bson::Value::BBoolean(b)) => b,
                    _ => false,
                };

            let (normspec, weights) = try!(elmo::get_normalized_spec(&spec, &options));
            let info = MyIndexPrep {
                index_id: index_id,
                spec: spec,
                options: options,
                normspec: normspec,
                weights: weights,
            };

            a.push(info);
        }
        Ok(a)
    }

    fn base_list_collections(&self) -> Result<Vec<elmo::CollectionInfo>> {
        let csr = try!(self.conn.OpenCursor().map_err(elmo::wrap_err));
        let mut csr = lsm::PrefixCursor::new(csr, box [NAME_TO_COLLECTION_ID]);
        let mut a = vec![];
        // TODO might need to sort by the coll name?  the sqlite version does.
        while csr.IsValid() {
            {
                let k = try!(csr.KeyRef().map_err(elmo::wrap_err));
                let (db, coll) = try!(decode_key_name_to_collection_id(&k));

                let v = try!(csr.LiveValueRef().map_err(elmo::wrap_err));
                let collection_id = try!(v.map(lsm_map_to_varint).map_err(elmo::wrap_err));

                let k = encode_key_collection_id_to_properties(collection_id);
                let mut collection_properties = try!(self.get_value_for_key_as_bson(&k)).unwrap_or(bson::Document::new());
                //let db = try!(collection_properties.must_remove_string("d"));
                //let coll = try!(collection_properties.must_remove_string("c"));
                let options = try!(collection_properties.must_remove_document("o"));

                let info = elmo::CollectionInfo {
                    db: db,
                    coll: coll,
                    options: options,
                };
                a.push(info);
            }
            try!(csr.Next().map_err(elmo::wrap_err));
        }
        Ok(a)
    }

}

impl<'a> MyWriter<'a> {
    fn pend_next_id(&mut self, tag: u8, val: u64) {
        let k = box [tag];
        let v = u64_to_boxed_varint(val);
        let v = lsm::Blob::Array(v);
        self.pending.insert(k, v);
    }

    fn use_next_collection_id(&mut self) -> u64 {
        let n = self.next_collection_id;
        self.next_collection_id += 1;
        n
    }

    fn use_next_index_id(&mut self) -> u64 {
        let n = self.next_index_id;
        self.next_index_id += 1;
        n
    }

    fn use_next_record_id(&mut self) -> u64 {
        let n = self.next_record_id;
        self.next_record_id += 1;
        n
    }

    fn get_collection_writer(&mut self, db: &str, coll: &str) -> Result<MyCollectionWriter> {
        let (_created, collection_id) = try!(self.base_create_collection(db, coll, bson::Document::new()));
        let indexes = try!(self.myconn.list_indexes_for_collection(collection_id));
        let c = MyCollectionWriter {
            indexes: indexes,
            collection_id: collection_id,
        };
        Ok(c)
    }

    fn base_create_collection(&mut self, db: &str, coll: &str, options: bson::Document) -> Result<(bool, u64)> {
        let k = encode_key_name_to_collection_id(db, coll);
        match try!(self.myconn.get_value_for_key_as_varint(&k)) {
            Some(id) => Ok((false, id)),
            None => {
                let collection_id = self.use_next_collection_id();
                self.pending.insert(k, lsm::Blob::Array(u64_to_boxed_varint(collection_id)));

                // create mongo index for _id
                match options.get("autoIndexId") {
                    Some(&bson::Value::BBoolean(false)) => {
                    },
                    _ => {
                        let index_id = self.use_next_index_id();
                        let k = encode_key_name_to_index_id(collection_id, "_id_");
                        self.pending.insert(k.into_boxed_slice(), lsm::Blob::Array(u64_to_boxed_varint(index_id)));

                        let k = encode_key_index_id_to_properties(index_id);
                        let mut properties = bson::Document::new();
                        properties.set_str("n", "_id_");
                        let spec = bson::Document {pairs: vec![(String::from("_id"), bson::Value::BInt32(1))]};
                        let options = bson::Document {pairs: vec![(String::from("unique"), bson::Value::BBoolean(true))]};
                        properties.set_document("s", spec);
                        properties.set_document("o", options);
                        self.pending.insert(k.into_boxed_slice(), lsm::Blob::Array(properties.to_bson_array().into_boxed_slice()));
                    },
                }

                let k = encode_key_collection_id_to_properties(collection_id);
                let mut properties = bson::Document::new();
                properties.set_str("d", db);
                properties.set_str("c", coll);
                properties.set_document("o", options);
                self.pending.insert(k.into_boxed_slice(), lsm::Blob::Array(properties.to_bson_array().into_boxed_slice()));

                Ok((true, collection_id))
            },
        }
    }

    fn update_indexes_delete(&mut self, indexes: &Vec<MyIndexPrep>, ba_collection_id: &Box<[u8]>, ba_record_id: &Box<[u8]>) -> Result<()> {
        for ndx in indexes {
            // TODO delete all index entries (and their back links) which involve this record_id
            // this *could* be done by simply iterating over all the index entries,
            // unpacking each one, seeing if the record id matches, and remove it if so, etc.
        }
        Ok(())
    }

    fn update_indexes_insert(&mut self, indexes: &Vec<MyIndexPrep>, ba_collection_id: &Box<[u8]>, ba_record_id: &Box<[u8]>, v: &bson::Document) -> Result<()> {
        for ndx in indexes {
            let entries = try!(elmo::get_index_entries(&v, &ndx.normspec, &ndx.weights, &ndx.options));
            // TODO don't look this up here.  store it in the cached info.
            let unique = 
                match ndx.options.get("unique") {
                    Some(&bson::Value::BBoolean(b)) => b,
                    _ => false,
                };
            // TODO store this in the cache?
            let ba_index_id = u64_to_boxed_varint(ndx.index_id);
            for vals in entries {
                let vref = vals.iter().map(|&(ref v,neg)| (v,neg)).collect::<Vec<_>>();
                let k = bson::Value::encode_multi_for_index(&vref, None);
                // TODO capacity
                let mut index_entry = vec![];
                index_entry.push(INDEX_ENTRY);
                push_varint(&mut index_entry, ndx.index_id);
                push_varint(&mut index_entry, k.len() as u64);
                index_entry.push_all(&k);
                if !unique {
                    index_entry.push_all(&ba_record_id);
                }

                // TODO maybe the index_id shouldn't go in the backward entry.  
                // would that make it easier to delete all entries for a given record_id?
                // but harder to drop an index?

                // do the backward entry first, because the other one takes ownership
                let mut backward_entry = vec![];
                backward_entry.clear();
                backward_entry.push(RECORD_ID_TO_INDEX_ENTRY);
                backward_entry.push_all(ba_collection_id);
                backward_entry.push_all(&ba_index_id);
                backward_entry.push_all(ba_record_id);
                backward_entry.push_all(&index_entry);
                self.pending.insert(backward_entry.into_boxed_slice(), lsm::Blob::Array(box []));

                // now the index entry itself, since ownership is transferred
                self.pending.insert(index_entry.into_boxed_slice(), lsm::Blob::Array(ba_record_id.clone()));
            }
        }
        Ok(())
    }

}

impl<'a> elmo::StorageWriter for MyWriter<'a> {
    fn update(&mut self, db: &str, coll: &str, v: &bson::Document) -> Result<()> {
        match v.get("_id") {
            None => Err(elmo::Error::Misc(String::from("cannot update without _id"))),
            Some(id) => {
                unimplemented!();
            },
        }
    }

    fn delete(&mut self, db: &str, coll: &str, v: &bson::Value) -> Result<bool> {
        unimplemented!();
    }

    fn insert(&mut self, db: &str, coll: &str, v: &bson::Document) -> Result<()> {
        let cw = try!(self.get_collection_writer(db, coll));
        // TODO capacity
        let mut k = vec![];
        k.push(RECORD);
        let ba_collection_id = u64_to_boxed_varint(cw.collection_id);
        k.push_all(&ba_collection_id);
        let record_id = self.use_next_record_id();
        let ba_record_id = u64_to_boxed_varint(record_id);
        k.push_all(&ba_record_id);
        self.pending.insert(k.into_boxed_slice(), lsm::Blob::Array(v.to_bson_array().into_boxed_slice()));

        try!(self.update_indexes_insert(&cw.indexes, &ba_collection_id, &ba_record_id, v));

        Ok(())
    }

    fn commit(mut self: Box<Self>) -> Result<()> {
        if self.next_collection_id != self.orig_next_collection_id {
            let t = self.next_collection_id;
            self.pend_next_id(NEXT_COLLECTION_ID, t);
        }
        if self.next_index_id != self.orig_next_index_id {
            let t = self.next_index_id;
            self.pend_next_id(NEXT_INDEX_ID, t);
        }
        if self.next_record_id != self.orig_next_record_id {
            let t = self.next_record_id;
            self.pend_next_id(NEXT_RECORD_ID, t);
        }
        if !self.pending.is_empty() {
            let pending = std::mem::replace(&mut self.pending, HashMap::new());
            let g = try!(self.myconn.conn.WriteSegment2(pending).map_err(elmo::wrap_err));
            try!(self.tx.commitSegments(vec![g]).map_err(elmo::wrap_err));
        }
        Ok(())
    }

    fn rollback(mut self: Box<Self>) -> Result<()> {
        // since we haven't been writing segments, do nothing here
        Ok(())
    }

    fn create_collection(&mut self, db: &str, coll: &str, options: bson::Document) -> Result<bool> {
        let (created, _collection_id) = try!(self.base_create_collection(db, coll, options));
        Ok(created)
    }

    fn drop_collection(&mut self, db: &str, coll: &str) -> Result<bool> {
        unimplemented!();
    }

    fn create_indexes(&mut self, what: Vec<elmo::IndexInfo>) -> Result<Vec<bool>> {
        unimplemented!();
    }

    fn rename_collection(&mut self, old_name: &str, new_name: &str, drop_target: bool) -> Result<bool> {
        unimplemented!();
    }

    fn drop_index(&mut self, db: &str, coll: &str, name: &str) -> Result<bool> {
        unimplemented!();
    }

    fn drop_database(&mut self, db: &str) -> Result<bool> {
        unimplemented!();
    }

    fn clear_collection(&mut self, db: &str, coll: &str) -> Result<bool> {
        unimplemented!();
    }

}

// TODO do we need to declare that StorageWriter must implement Drop ?
impl<'a> Drop for MyWriter<'a> {
    fn drop(&mut self) {
        // TODO rollback
    }
}

// TODO do we need to declare that StorageReader must implement Drop ?
impl Drop for MyReader {
    fn drop(&mut self) {
    }
}

impl Drop for MyCollectionReader {
    fn drop(&mut self) {
    }
}

impl Iterator for MyCollectionReader {
    type Item = Result<elmo::Row>;
    fn next(&mut self) -> Option<Self::Item> {
        self.seq.next()
    }
}

impl elmo::StorageBase for MyReader {
    fn get_reader_collection_scan(&self, db: &str, coll: &str) -> Result<Box<Iterator<Item=Result<elmo::Row>> + 'static>> {
        let rdr = try!(self.myconn.get_reader_collection_scan(self.myconn.clone(), db, coll));
        Ok(box rdr)
    }

    fn get_reader_text_index_scan(&self, ndx: &elmo::IndexInfo, eq: elmo::QueryKey, terms: Vec<elmo::TextQueryTerm>) -> Result<Box<Iterator<Item=Result<elmo::Row>> + 'static>> {
        let rdr = try!(self.myconn.get_reader_text_index_scan(self.myconn.clone(), false, ndx, eq, terms));
        Ok(box rdr)
    }

    fn get_reader_regular_index_scan(&self, ndx: &elmo::IndexInfo, bounds: elmo::QueryBounds) -> Result<Box<Iterator<Item=Result<elmo::Row>> + 'static>> {
        let rdr = try!(self.myconn.get_reader_regular_index_scan(self.myconn.clone(), ndx, bounds));
        Ok(box rdr)
    }

    fn list_collections(&self) -> Result<Vec<elmo::CollectionInfo>> {
        self.myconn.base_list_collections()
    }

    fn list_indexes(&self) -> Result<Vec<elmo::IndexInfo>> {
        self.myconn.base_list_indexes()
    }

}

impl elmo::StorageReader for MyReader {
    fn into_reader_collection_scan(mut self: Box<Self>, db: &str, coll: &str) -> Result<Box<Iterator<Item=Result<elmo::Row>> + 'static>> {
        let rdr = try!(self.myconn.get_reader_collection_scan(self.myconn.clone(), db, coll));
        Ok(box rdr)
    }

    fn into_reader_text_index_scan(&self, ndx: &elmo::IndexInfo, eq: elmo::QueryKey, terms: Vec<elmo::TextQueryTerm>) -> Result<Box<Iterator<Item=Result<elmo::Row>> + 'static>> {
        let rdr = try!(self.myconn.get_reader_text_index_scan(self.myconn.clone(), true, ndx, eq, terms));
        Ok(box rdr)
    }

    fn into_reader_regular_index_scan(&self, ndx: &elmo::IndexInfo, bounds: elmo::QueryBounds) -> Result<Box<Iterator<Item=Result<elmo::Row>> + 'static>> {
        let rdr = try!(self.myconn.get_reader_regular_index_scan(self.myconn.clone(), ndx, bounds));
        Ok(box rdr)
    }

}

impl<'a> elmo::StorageBase for MyWriter<'a> {
    fn get_reader_collection_scan(&self, db: &str, coll: &str) -> Result<Box<Iterator<Item=Result<elmo::Row>> + 'static>> {
        let rdr = try!(self.myconn.get_reader_collection_scan(self.myconn.clone(), db, coll));
        Ok(box rdr)
    }

    fn get_reader_text_index_scan(&self, ndx: &elmo::IndexInfo, eq: elmo::QueryKey, terms: Vec<elmo::TextQueryTerm>) -> Result<Box<Iterator<Item=Result<elmo::Row>> + 'static>> {
        let rdr = try!(self.myconn.get_reader_text_index_scan(self.myconn.clone(), false, ndx, eq, terms));
        Ok(box rdr)
    }

    fn get_reader_regular_index_scan(&self, ndx: &elmo::IndexInfo, bounds: elmo::QueryBounds) -> Result<Box<Iterator<Item=Result<elmo::Row>> + 'static>> {
        let rdr = try!(self.myconn.get_reader_regular_index_scan(self.myconn.clone(), ndx, bounds));
        Ok(box rdr)
    }

    fn list_collections(&self) -> Result<Vec<elmo::CollectionInfo>> {
        self.myconn.base_list_collections()
    }

    fn list_indexes(&self) -> Result<Vec<elmo::IndexInfo>> {
        self.myconn.base_list_indexes()
    }

}

impl elmo::StorageConnection for MyPublicConn {
    fn begin_write<'a>(&'a self) -> Result<Box<elmo::StorageWriter + 'a>> {
        let tx = try!(self.myconn.conn.GetWriteLock().map_err(elmo::wrap_err));
        // TODO we should use one cursor/seek to get all three of these.
        // configure their keys so that they will be all together.
        // or maybe just put all three of them in the same record value.
        let next_collection_id = try!(self.myconn.get_next_id(NEXT_COLLECTION_ID));
        let next_index_id = try!(self.myconn.get_next_id(NEXT_INDEX_ID));
        let next_record_id = try!(self.myconn.get_next_id(NEXT_RECORD_ID));
        let w = MyWriter {
            myconn: self.myconn.clone(),
            tx: tx,
            pending: HashMap::new(),
            next_collection_id: next_collection_id,
            next_index_id: next_index_id,
            next_record_id: next_record_id,
            orig_next_collection_id: next_collection_id,
            orig_next_index_id: next_index_id,
            orig_next_record_id: next_record_id,
        };
        Ok(box w)
    }

    fn begin_read(&self) -> Result<Box<elmo::StorageReader + 'static>> {
        let r = MyReader {
            myconn: self.myconn.clone(),
        };
        Ok(box r)
    }
}

fn base_connect(name: &str) -> lsm::Result<lsm::db> {
    lsm::db::new(String::from(name), lsm::DEFAULT_SETTINGS)
}

pub fn connect(name: &str) -> Result<Box<elmo::StorageConnection>> {
    let conn = try!(base_connect(name).map_err(elmo::wrap_err));
    let c = MyConn {
        conn: conn,
    };
    let c = MyPublicConn {
        myconn: std::rc::Rc::new(c)
    };
    Ok(box c)
}

#[derive(Clone)]
pub struct MyFactory {
    filename: String,
}

impl MyFactory {
    pub fn new(filename: String) -> MyFactory {
        MyFactory {
            filename: filename,
        }
    }
}

impl elmo::ConnectionFactory for MyFactory {
    fn open(&self) -> elmo::Result<elmo::Connection> {
        let conn = try!(connect(&self.filename));
        let conn = elmo::Connection::new(conn);
        Ok(conn)
    }

    fn clone_for_new_thread(&self) -> Box<elmo::ConnectionFactory + Send> {
        box self.clone()
    }
}

