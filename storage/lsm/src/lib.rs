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

fn get_collection_key(db: &str, coll: &str) -> Vec<u8> {
    let mut k = vec![];
    k.push(1u8);
    k.push_all(db.as_bytes());
    k.push(0u8);
    k.push_all(coll.as_bytes());
    k.push(0u8);
    k
}

impl MyConn {
    fn get_collection_options(&self, k: &[u8]) -> Result<Option<bson::Document>> {
        let mut csr = try!(self.conn.OpenCursor().map_err(elmo::wrap_err));
        try!(csr.SeekRef(&lsm::KeyRef::for_slice(&k), lsm::SeekOp::SEEK_EQ).map_err(elmo::wrap_err));
        if csr.IsValid() {
            let v = try!(csr.ValueRef().map_err(elmo::wrap_err));
            let func = |ba: &[u8]| -> lsm::Result<bson::Document> {
                let r = bson::Document::from_bson(ba);
                let r = r.map_err(lsm::wrap_err);
                r
            };
            let doc = try!(v.plok(func).map_err(elmo::wrap_err));
            // TODO doc should be is_some() here, since the value cannot be a tombstone, because
            // this is the LivingCursor from the db object.
            Ok(doc)
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
        unimplemented!();
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
        let k = get_collection_key(db, coll);
        match try!(self.myconn.get_collection_options(&k)) {
            Some(_) => Ok(false),
            None => {
                let v_options = options.to_bson_array();
                let mut d = std::collections::HashMap::new();
                d.insert(k.into_boxed_slice(), v_options.into_boxed_slice());
                let g = try!(self.myconn.conn.WriteSegment(d).map_err(elmo::wrap_err));
                try!(self.tx.commitSegments(vec![g]).map_err(elmo::wrap_err));
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

