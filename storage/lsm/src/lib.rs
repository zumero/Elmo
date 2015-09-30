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

struct IndexPrep {
    info: elmo::IndexInfo,
}

struct MyCollectionWriter {
    indexes: Vec<IndexPrep>,
    myconn: std::rc::Rc<MyConn>,
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

/// key:
///     (tag)
///     db name (len + str)
///     coll name (len + str)
/// value:
///     collid (varint)
pub const NAME_TO_COLLECTION_ID: u8 = 3;

/// key:
///     (tag)
///     collid (varint)
/// value:
///     options (bson)
pub const COLLECTION_ID_TO_OPTIONS: u8 = 4;

/// key:
///     (tag)
///     db name (len + str)
///     coll name (len + str)
///     index name (len + str)
/// value:
///     indexid (varint)
pub const NAME_TO_INDEX_ID: u8 = 5;

/// key:
///     (tag)
///     indexid (varint)
/// value:
///     spec (bson)
///     options (bson)
pub const INDEX_ID_TO_INFO: u8 = 6;

// TODO should we have record ids?  or just have the _id of each record
// be its actual key?  the pk can be big, and it will be duplicated,
// once in the key, and once in the bson doc itself.

/// key:
///     (tag)
///     collid (varint)
/// value:
///     recid (varint)
pub const NEXT_RECORD_ID: u8 = 7;

/// key:
///     (tag)
///     collid (varint)
///     recid (varint)
/// value:
///     doc (bson)
pub const RECORD: u8 = 8;

// TODO do we actually need the two kinds of index entries to be
// different tags?

/// key:
///     (tag)
///     indexid (varint)
///     k (len + bytes)
///     recid (varint)
/// value:
///    (none)
pub const INDEX_ENTRY_PLAIN: u8 = 9;

/// key:
///     (tag)
///     indexid (varint)
///     k (len + bytes)
/// value:
///     recid (varint)
pub const INDEX_ENTRY_UNIQUE: u8 = 10;

/// key:
///     (tag)
///     collid (varint)
///     recid (varint)
///     (complete index key)
/// value:
///    (none)
pub const RECORD_ID_TO_INDEX_ENTRY: u8 = 11;

fn encode_collection_key(db: &str, coll: &str) -> Vec<u8> {
    // TODO maybe the options should just go here in the key too?

    let mut k = vec![];
    k.push(1u8);

    // From the mongo docs:
    // The maximum length of the collection namespace, which includes the database name, the dot
    // (.) separator, and the collection name (i.e. <database>.<collection>), is 120 bytes.

    let b = db.as_bytes();
    k.push(b.len() as u8);
    k.push_all(b);

    let b = coll.as_bytes();
    k.push(b.len() as u8);
    k.push_all(b);

    k
}

fn lsm_map_to_string(ba: &[u8]) -> lsm::Result<String> {
    let s = try!(std::str::from_utf8(&ba));
    Ok(String::from(s))
}

fn decode_collection_key(k: &lsm::KeyRef) -> Result<(String, String)> {
    let len_db = try!(k.u8_at(1).map_err(elmo::wrap_err)) as usize;
    let begin_db = 2;
    let db = try!(k.map_range(begin_db, begin_db + len_db, lsm_map_to_string).map_err(elmo::wrap_err));
    let len_coll = try!(k.u8_at(begin_db + len_db).map_err(elmo::wrap_err)) as usize;
    let begin_coll = begin_db + len_db + 1;
    let coll = try!(k.map_range(begin_coll, begin_coll + len_coll, lsm_map_to_string).map_err(elmo::wrap_err));
    Ok((db, coll))
}

fn lsm_map_to_bson(ba: &[u8]) -> lsm::Result<bson::Document> {
    let r = bson::Document::from_bson(ba);
    let r = r.map_err(lsm::wrap_err);
    r
}

impl MyConn {
    fn get_collection_options(&self, k: &[u8]) -> Result<Option<bson::Document>> {
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

    fn base_list_collections(&self) -> Result<Vec<elmo::CollectionInfo>> {
        let mut csr = try!(self.conn.OpenCursor().map_err(elmo::wrap_err));
        let k = [1u8];
        try!(csr.SeekRef(&lsm::KeyRef::for_slice(&k), lsm::SeekOp::SEEK_GE).map_err(elmo::wrap_err));
        let mut a = vec![];
        // TODO might need to sort by the coll name
        while csr.IsValid() {
            {
                let k = try!(csr.KeyRef().map_err(elmo::wrap_err));
                if try!(k.u8_at(0).map_err(elmo::wrap_err)) != 1 {
                    // TODO maybe we should have an easy way to iterate over
                    // all keys in a prefix?
                    break;
                }
                let (db, coll) = try!(decode_collection_key(&k));
                let v = try!(csr.LiveValueRef().map_err(elmo::wrap_err));
                let options = try!(v.map(lsm_map_to_bson).map_err(elmo::wrap_err));
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

impl MyCollectionWriter {
}

impl elmo::StorageCollectionWriter for MyCollectionWriter {
    fn update(&mut self, v: &bson::Document) -> Result<()> {
        match v.get("_id") {
            None => Err(elmo::Error::Misc(String::from("cannot update without _id"))),
            Some(id) => {
                unimplemented!();
            },
        }
    }

    fn delete(&mut self, v: &bson::Value) -> Result<bool> {
        unimplemented!();
    }

    fn insert(&mut self, v: &bson::Document) -> Result<()> {
        unimplemented!();
    }

}

impl<'a> MyWriter<'a> {
    fn base_create_collection(&self, db: &str, coll: &str, options: bson::Document) -> Result<bool> {
        let k = encode_collection_key(db, coll);
        match try!(self.myconn.get_collection_options(&k)) {
            Some(_) => Ok(false),
            None => {
                let v_options = options.to_bson_array();
                let mut d = std::collections::HashMap::new();
                d.insert(k.into_boxed_slice(), v_options.into_boxed_slice());
                let g = try!(self.myconn.conn.WriteSegment(d).map_err(elmo::wrap_err));
                try!(self.tx.commitSegments(vec![g]).map_err(elmo::wrap_err));
                // TODO gotta create the _id index here
                Ok(true)
            },
        }
    }

}

impl<'a> elmo::StorageWriter for MyWriter<'a> {
    fn get_collection_writer(&self, db: &str, coll: &str) -> Result<Box<elmo::StorageCollectionWriter + 'static>> {
        unimplemented!();
    }

    fn commit(mut self: Box<Self>) -> Result<()> {
        unimplemented!();
    }

    fn rollback(mut self: Box<Self>) -> Result<()> {
        unimplemented!();
    }

    fn create_collection(&self, db: &str, coll: &str, options: bson::Document) -> Result<bool> {
        self.base_create_collection(db, coll, options)
    }

    fn drop_collection(&self, db: &str, coll: &str) -> Result<bool> {
        unimplemented!();
    }

    fn create_indexes(&self, what: Vec<elmo::IndexInfo>) -> Result<Vec<bool>> {
        unimplemented!();
    }

    fn rename_collection(&self, old_name: &str, new_name: &str, drop_target: bool) -> Result<bool> {
        unimplemented!();
    }

    fn drop_index(&self, db: &str, coll: &str, name: &str) -> Result<bool> {
        unimplemented!();
    }

    fn drop_database(&self, db: &str) -> Result<bool> {
        unimplemented!();
    }

    fn clear_collection(&self, db: &str, coll: &str) -> Result<bool> {
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
        let w = MyWriter {
            myconn: self.myconn.clone(),
            tx: tx,
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

