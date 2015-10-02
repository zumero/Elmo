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

struct MyIndexInfo {
    index_id: u64,
    spec: bson::Document,
    options: bson::Document,
    normspec: Vec<(String,elmo::IndexType)>,
    weights: Option<HashMap<String,i32>>,
    // TODO maybe keep the options we need here directly, sparse and unique
}

struct MyCollectionWriter {
    // TODO might want db and coll names here for caching
    indexes: Vec<MyIndexInfo>,
    collection_id: u64,
}

struct MyCollectionReader {
    commit_on_drop: bool,
    seq: Box<Iterator<Item=Result<elmo::Row>>>,
    myconn: std::rc::Rc<MyConn>,

    // TODO need counts here
}

struct MyReader {
    myconn: std::rc::Rc<MyConn>,
    cursor: lsm::LivingCursor,
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

// TODO maybe the options should just go with above
// instead of in a separate record?

/// key:
///     (tag)
///     collid (varint)
/// value:
///     options (bson)
pub const COLLECTION_ID_TO_OPTIONS: u8 = 11;

/// key:
///     (tag)
///     collid (varint)
///     index name (len + str)
/// value:
///     indexid (varint)
pub const NAME_TO_INDEX_ID: u8 = 20;

// TODO maybe the spec/options should just go with above
// instead of in a separate record?

/// key:
///     (tag)
///     indexid (varint)
/// value:
///     spec (bson)
pub const INDEX_ID_TO_SPEC: u8 = 21;

/// key:
///     (tag)
///     indexid (varint)
/// value:
///     options (bson)
pub const INDEX_ID_TO_OPTIONS: u8 = 22;

/// key:
///     (tag)
///     collid (varint)
///     recid (varint)
/// value:
///     doc (bson)
pub const RECORD: u8 = 30;

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

fn encode_key_collection_id_to_options(id: u64) -> Vec<u8> {
    encode_key_tag_and_varint(COLLECTION_ID_TO_OPTIONS, id)
}

fn encode_key_index_id_to_spec(id: u64) -> Vec<u8> {
    encode_key_tag_and_varint(INDEX_ID_TO_SPEC, id)
}

fn encode_key_index_id_to_options(id: u64) -> Vec<u8> {
    encode_key_tag_and_varint(INDEX_ID_TO_OPTIONS, id)
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

    fn get_collection_options(&self, k: &[u8]) -> Result<Option<bson::Document>> {
        // TODO this is all wrong now
        let mut csr = try!(self.conn.OpenCursor().map_err(elmo::wrap_err));
        try!(csr.SeekRef(&lsm::KeyRef::for_slice(&k), lsm::SeekOp::SEEK_EQ).map_err(elmo::wrap_err));
        if csr.IsValid() {
            let v = try!(csr.LiveValueRef().map_err(elmo::wrap_err));
            let doc = try!(v.map(lsm_map_to_bson).map_err(elmo::wrap_err));
            Ok(Some(doc))
        } else {
            Ok(None)
        }
    }

    fn get_reader_collection_scan(&self, myconn: std::rc::Rc<MyConn>, commit_on_drop: bool, db: &str, coll: &str) -> Result<MyCollectionReader> {
        unimplemented!();
    }

    fn get_reader_text_index_scan(&self, myconn: std::rc::Rc<MyConn>, commit_on_drop: bool, ndx: &elmo::IndexInfo, eq: elmo::QueryKey, terms: Vec<elmo::TextQueryTerm>) -> Result<MyCollectionReader> {
        unimplemented!();
    }

    fn get_reader_regular_index_scan(&self, myconn: std::rc::Rc<MyConn>, commit_on_drop: bool, ndx: &elmo::IndexInfo, bounds: elmo::QueryBounds) -> Result<MyCollectionReader> {
        unimplemented!();
    }

    fn base_list_indexes(&self) -> Result<Vec<elmo::IndexInfo>> {
        unimplemented!();
    }

    fn list_indexes_for_collection(&self, collection_id: u64) -> Result<Vec<MyIndexInfo>> {
        let q = encode_key_tag_and_varint(NAME_TO_INDEX_ID, collection_id);
        let mut csr = try!(self.conn.OpenCursor().map_err(elmo::wrap_err));
        try!(csr.SeekRef(&lsm::KeyRef::for_slice(&q), lsm::SeekOp::SEEK_GE).map_err(elmo::wrap_err));
        let mut a = vec![];

        while csr.IsValid() {
            let k = try!(csr.KeyRef().map_err(elmo::wrap_err));
            
            // if q is not a prefix of k, stop
            if k.len() < q.len() {
                break;
            }

            let check_prefix = |ba: &[u8]| -> lsm::Result<bool> {
                Ok(ba == &*q)
            };

            if !try!(k.map_range(0, q.len(), check_prefix).map_err(elmo::wrap_err)) {
                break;
            }

            // the name of the index is on the end of this key, but we don't need it

            let v = try!(csr.LiveValueRef().map_err(elmo::wrap_err));
            let index_id = try!(v.map(lsm_map_to_varint).map_err(elmo::wrap_err));

            let k = encode_key_index_id_to_spec(index_id);
            let spec = try!(self.get_value_for_key_as_bson(&k)).unwrap_or(bson::Document::new());

            let k = encode_key_index_id_to_options(index_id);
            let options = try!(self.get_value_for_key_as_bson(&k)).unwrap_or(bson::Document::new());
            
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
            let info = MyIndexInfo {
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
        let mut csr = try!(self.conn.OpenCursor().map_err(elmo::wrap_err));
        let k = [NAME_TO_COLLECTION_ID];
        try!(csr.SeekRef(&lsm::KeyRef::for_slice(&k), lsm::SeekOp::SEEK_GE).map_err(elmo::wrap_err));
        let mut a = vec![];
        // TODO might need to sort by the coll name
        while csr.IsValid() {
            {
                let k = try!(csr.KeyRef().map_err(elmo::wrap_err));
                if try!(k.u8_at(0).map_err(elmo::wrap_err)) != NAME_TO_COLLECTION_ID {
                    // TODO maybe lsm should have an easy way to iterate over
                    // all keys in a prefix?
                    break;
                }
                let (db, coll) = try!(decode_key_name_to_collection_id(&k));

                let v = try!(csr.LiveValueRef().map_err(elmo::wrap_err));
                let collection_id = try!(v.map(lsm_map_to_varint).map_err(elmo::wrap_err));

                let k = encode_key_collection_id_to_options(collection_id);
                let options = try!(self.get_value_for_key_as_bson(&k)).unwrap_or(bson::Document::new());

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

                let k = encode_key_collection_id_to_options(collection_id);
                self.pending.insert(k.into_boxed_slice(), lsm::Blob::Array(options.to_bson_array().into_boxed_slice()));

                // now create mongo index for _id
                match options.get("autoIndexId") {
                    Some(&bson::Value::BBoolean(false)) => {
                    },
                    _ => {
                        let index_id = self.use_next_index_id();
                        let k = encode_key_name_to_index_id(collection_id, "_id_");
                        self.pending.insert(k.into_boxed_slice(), lsm::Blob::Array(u64_to_boxed_varint(index_id)));

                        let spec = bson::Document {pairs: vec![(String::from("_id"), bson::Value::BInt32(1))]};
                        let k = encode_key_index_id_to_spec(index_id);
                        self.pending.insert(k.into_boxed_slice(), lsm::Blob::Array(spec.to_bson_array().into_boxed_slice()));

                        let options = bson::Document {pairs: vec![(String::from("unique"), bson::Value::BBoolean(true))]};
                        let k = encode_key_index_id_to_options(index_id);
                        self.pending.insert(k.into_boxed_slice(), lsm::Blob::Array(spec.to_bson_array().into_boxed_slice()));
                    },
                }

                Ok((true, collection_id))
            },
        }
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
        let mut k = encode_key_tag_and_varint(RECORD, cw.collection_id);
        let record_id = self.use_next_record_id();
        let ba_record_id = u64_to_boxed_varint(record_id);
        k.push_all(&ba_record_id);
        self.pending.insert(k.into_boxed_slice(), lsm::Blob::Array(v.to_bson_array().into_boxed_slice()));

        for ndx in cw.indexes {
            let (normspec, weights) = try!(elmo::get_normalized_spec(&ndx.spec, &ndx.options));
            let entries = try!(elmo::get_index_entries(&v, &normspec, &weights, &ndx.options));
            let unique = 
                match ndx.options.get("unique") {
                    Some(&bson::Value::BBoolean(b)) => b,
                    _ => false,
                };
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
                self.pending.insert(index_entry.into_boxed_slice(), lsm::Blob::Array(ba_record_id.clone()));

                // TODO need to add the backward index entry as well
            }
        }
        unimplemented!();
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
        let rdr = try!(self.myconn.get_reader_collection_scan(self.myconn.clone(), false, db, coll));
        Ok(box rdr)
    }

    fn get_reader_text_index_scan(&self, ndx: &elmo::IndexInfo, eq: elmo::QueryKey, terms: Vec<elmo::TextQueryTerm>) -> Result<Box<Iterator<Item=Result<elmo::Row>> + 'static>> {
        let rdr = try!(self.myconn.get_reader_text_index_scan(self.myconn.clone(), false, ndx, eq, terms));
        Ok(box rdr)
    }

    fn get_reader_regular_index_scan(&self, ndx: &elmo::IndexInfo, bounds: elmo::QueryBounds) -> Result<Box<Iterator<Item=Result<elmo::Row>> + 'static>> {
        let rdr = try!(self.myconn.get_reader_regular_index_scan(self.myconn.clone(), false, ndx, bounds));
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
        let rdr = try!(self.myconn.get_reader_collection_scan(self.myconn.clone(), true, db, coll));
        Ok(box rdr)
    }

    fn into_reader_text_index_scan(&self, ndx: &elmo::IndexInfo, eq: elmo::QueryKey, terms: Vec<elmo::TextQueryTerm>) -> Result<Box<Iterator<Item=Result<elmo::Row>> + 'static>> {
        let rdr = try!(self.myconn.get_reader_text_index_scan(self.myconn.clone(), true, ndx, eq, terms));
        Ok(box rdr)
    }

    fn into_reader_regular_index_scan(&self, ndx: &elmo::IndexInfo, bounds: elmo::QueryBounds) -> Result<Box<Iterator<Item=Result<elmo::Row>> + 'static>> {
        let rdr = try!(self.myconn.get_reader_regular_index_scan(self.myconn.clone(), true, ndx, bounds));
        Ok(box rdr)
    }

}

impl<'a> elmo::StorageBase for MyWriter<'a> {
    fn get_reader_collection_scan(&self, db: &str, coll: &str) -> Result<Box<Iterator<Item=Result<elmo::Row>> + 'static>> {
        let rdr = try!(self.myconn.get_reader_collection_scan(self.myconn.clone(), false, db, coll));
        Ok(box rdr)
    }

    fn get_reader_text_index_scan(&self, ndx: &elmo::IndexInfo, eq: elmo::QueryKey, terms: Vec<elmo::TextQueryTerm>) -> Result<Box<Iterator<Item=Result<elmo::Row>> + 'static>> {
        let rdr = try!(self.myconn.get_reader_text_index_scan(self.myconn.clone(), false, ndx, eq, terms));
        Ok(box rdr)
    }

    fn get_reader_regular_index_scan(&self, ndx: &elmo::IndexInfo, bounds: elmo::QueryBounds) -> Result<Box<Iterator<Item=Result<elmo::Row>> + 'static>> {
        let rdr = try!(self.myconn.get_reader_regular_index_scan(self.myconn.clone(), false, ndx, bounds));
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
        let csr = try!(self.myconn.conn.OpenCursor().map_err(elmo::wrap_err));
        let r = MyReader {
            myconn: self.myconn.clone(),
            cursor: csr,
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

