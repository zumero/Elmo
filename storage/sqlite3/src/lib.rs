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

pub type Result<T> = elmo::Result<T>;

extern crate sqlite3;

struct IndexPrep {
    info: elmo::IndexInfo,
    stmt_insert: sqlite3::PreparedStatement,
    stmt_delete: sqlite3::PreparedStatement,
    normspec: Vec<(String,elmo::IndexType)>,
    weights: Option<HashMap<String,i32>>,
}

struct MyCollectionWriter {
    db: String,
    coll: String,
    insert: sqlite3::PreparedStatement,
    delete: sqlite3::PreparedStatement,
    update: sqlite3::PreparedStatement,
    stmt_find_rowid: Option<sqlite3::PreparedStatement>,
    indexes: Vec<IndexPrep>,
}

struct StatementBsonValueIterator {
    stmt: sqlite3::PreparedStatement,
}

impl StatementBsonValueIterator {
    fn iter_next(&mut self) -> Result<Option<elmo::Row>> {
        match try!(self.stmt.step().map_err(elmo::wrap_err)) {
            None => {
                Ok(None)
            },
            Some(r) => {
                let b = r.column_blob(0).expect("NOT NULL");
                let v = try!(bson::Document::from_bson(&b));
                //println!("doc in row: {:?}", v);
                let v = bson::Value::BDocument(v);
                let row = elmo::Row {
                    doc: v,
                    pos: None,
                    score: None,
                };
                Ok(Some(row))
            },
        }
    }
}

impl Iterator for StatementBsonValueIterator {
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

// TODO it is sad to have two completely distinct versions of
// this iterator, one which owns the statement, and one which
// does not.

struct RefStatementBsonValueIterator<'a> {
    stmt: &'a mut sqlite3::PreparedStatement,
}

impl<'a> RefStatementBsonValueIterator<'a> {
    fn iter_next(&mut self) -> Result<Option<elmo::Row>> {
        match try!(self.stmt.step().map_err(elmo::wrap_err)) {
            None => {
                Ok(None)
            },
            Some(r) => {
                let b = r.column_blob(0).expect("NOT NULL");
                let v = try!(bson::Document::from_bson(&b));
                //println!("doc: {:?}", v);
                let v = bson::Value::BDocument(v);
                let row = elmo::Row {
                    doc: v,
                    pos: None,
                    score: None,
                };
                Ok(Some(row))
            },
        }
    }
}

impl<'a> Iterator for RefStatementBsonValueIterator<'a> {
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

struct MyCollectionReader {
    commit_on_drop: bool,
    seq: Box<Iterator<Item=Result<elmo::Row>>>,
    myconn: std::rc::Rc<MyConn>,

    // TODO need counts here
}

struct MyReader {
    myconn: std::rc::Rc<MyConn>,
    in_tx: bool,
}

struct MyWriter {
    myconn: std::rc::Rc<MyConn>,
    cw: Option<MyCollectionWriter>,
    in_tx: bool,
}

struct MyConn {
    conn: sqlite3::DatabaseConnection,
}

struct MyPublicConn {
    myconn: std::rc::Rc<MyConn>,
}

fn step_done(stmt: &mut sqlite3::PreparedStatement) -> Result<()> {
    match try!(stmt.step().map_err(elmo::wrap_err)) {
        Some(_) => {
            Err(elmo::Error::Misc(String::from("step_done() returned a row")))
        },
        None => {
            Ok(())
        },
    }
}

fn verify_changes(stmt: &sqlite3::PreparedStatement, shouldbe: u64) -> Result<()> {
    if stmt.changes() == shouldbe {
        Ok(())
    } else {
        // TODO or should this be an assert?
        Err(elmo::Error::Misc(String::from("changes() is wrong")))
    }
}

fn get_table_name_for_collection(db: &str, coll: &str) -> String { 
    // TODO cleanse?
    format!("docs.{}.{}", db, coll) 
}

fn get_table_name_for_index(db: &str, coll: &str, name: &str) -> String { 
    // TODO cleanse?
    format!("ndx.{}.{}.{}", db, coll, name) 
}

fn get_index_info_from_row(r: &sqlite3::ResultRow) -> Result<elmo::IndexInfo> {
    let name = r.column_text(0).expect("NOT NULL");
    let spec = try!(bson::Document::from_bson(&r.column_slice(1).expect("NOT NULL")));
    let options = try!(bson::Document::from_bson(&r.column_slice(2).expect("NOT NULL")));
    let db = r.column_text(3).expect("NOT NULL");
    let coll = r.column_text(4).expect("NOT NULL");
    let info = elmo::IndexInfo {
        db: String::from(db),
        coll: String::from(coll),
        name: String::from(name),
        spec: spec,
        options: options,
    };
    Ok(info)
}

fn get_collection_info_from_row(r: &sqlite3::ResultRow) -> Result<elmo::CollectionInfo> {
    let db = r.column_text(0).expect("NOT NULL");
    let coll = r.column_text(1).expect("NOT NULL");
    let options = try!(bson::Document::from_bson(&r.column_slice(2).expect("NOT NULL")));
    let info = elmo::CollectionInfo {
        db: String::from(db),
        coll: String::from(coll),
        options: options,
    };
    Ok(info)
}

fn index_insert_step(stmt: &mut sqlite3::PreparedStatement, k: Vec<u8>, doc_rowid: i64) -> Result<()> {
    stmt.clear_bindings();
    try!(stmt.bind_blob(1, &k).map_err(elmo::wrap_err));
    try!(stmt.bind_int64(2, doc_rowid).map_err(elmo::wrap_err));
    try!(step_done(stmt));
    try!(verify_changes(stmt, 1));
    stmt.reset();
    Ok(())
}

impl MyConn {
    fn get_collection_options(&self, db: &str, coll: &str) -> Result<Option<bson::Document>> {
        let mut stmt = try!(self.conn.prepare("SELECT options FROM \"collections\" WHERE dbName=? AND collName=?").map_err(elmo::wrap_err));
        try!(stmt.bind_text(1, db).map_err(elmo::wrap_err));
        try!(stmt.bind_text(2, coll).map_err(elmo::wrap_err));
        // TODO step_row() ?
        match try!(stmt.step().map_err(elmo::wrap_err)) {
            None => Ok(None),
            Some(r) => {
                let v = try!(bson::Document::from_bson(&r.column_slice(0).expect("NOT NULL")));
                Ok(Some(v))
            },
        }
    }

    fn get_stmt_for_index_scan(myconn: &MyConn, ndx: &elmo::IndexInfo, bounds: elmo::QueryBounds) -> Result<sqlite3::PreparedStatement> {
        let tbl_coll = get_table_name_for_collection(&ndx.db, &ndx.coll);
        let tbl_ndx = get_table_name_for_index(&ndx.db, &ndx.coll, &ndx.name);

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

        // note that one of the reasons we need to do DISTINCT here is because a
        // single index in a single document can produce multiple index entries,
        // because, for example, when a value is an array, we don't just index
        // the array as a value, but we also index each of its elements.
        //
        // TODO it would be nice if the DISTINCT here was happening on the rowids, not on the blobs

        let f_twok = |kmin: Vec<u8>, kmax: Vec<u8>, op1: &str, op2: &str| -> Result<sqlite3::PreparedStatement> {
            let sql = format!("SELECT DISTINCT d.bson FROM \"{}\" d INNER JOIN \"{}\" i ON (d.did = i.doc_rowid) WHERE k {} ? AND k {} ?", tbl_coll, tbl_ndx, op1, op2);
            //println!("using sql: {}", sql);
            let mut stmt = try!(myconn.conn.prepare(&sql).map_err(elmo::wrap_err));
            try!(stmt.bind_blob(1, &kmin).map_err(elmo::wrap_err));
            try!(stmt.bind_blob(2, &kmax).map_err(elmo::wrap_err));
            Ok(stmt)
        };

        let f_two = |eqvals: elmo::QueryKey, minvals: elmo::QueryKey, maxvals: elmo::QueryKey, op1: &str, op2: &str| -> Result<sqlite3::PreparedStatement> {
            let kmin = bson::Value::encode_multi_for_index(&eqvals, Some(&minvals));
            let kmax = bson::Value::encode_multi_for_index(&eqvals, Some(&maxvals));
            f_twok(kmin, kmax, op1, op2)
        };

        let f_one = |vals: elmo::QueryKey, op: &str| -> Result<sqlite3::PreparedStatement> {
            let k = bson::Value::encode_multi_for_index(&vals, None);
            let sql = format!("SELECT DISTINCT d.bson FROM \"{}\" d INNER JOIN \"{}\" i ON (d.did = i.doc_rowid) WHERE k {} ?", tbl_coll, tbl_ndx, op);
            let mut stmt = try!(myconn.conn.prepare(&sql).map_err(elmo::wrap_err));
            try!(stmt.bind_blob(1, &k).map_err(elmo::wrap_err));
            Ok(stmt)
        };

        match bounds {
            elmo::QueryBounds::GT(vals) => f_one(vals, ">"),
            elmo::QueryBounds::LT(vals) => f_one(vals, "<"),
            elmo::QueryBounds::GTE(vals) => f_one(vals, ">="),
            elmo::QueryBounds::LTE(vals) => f_one(vals, "<="),
            elmo::QueryBounds::GT_LT(eqvals, minvals, maxvals) => f_two(eqvals, minvals, maxvals, ">", "<"),
            elmo::QueryBounds::GTE_LT(eqvals, minvals, maxvals) => f_two(eqvals, minvals, maxvals, ">=", "<"),
            elmo::QueryBounds::GT_LTE(eqvals, minvals, maxvals) => f_two(eqvals, minvals, maxvals, ">", "<="),
            elmo::QueryBounds::GTE_LTE(eqvals, minvals, maxvals) => f_two(eqvals, minvals, maxvals, ">=", "<="),
            elmo::QueryBounds::EQ(vals) => {
                let kmin = bson::Value::encode_multi_for_index(&vals, None);
                let kmax = add_one(&kmin);
                f_twok(kmin, kmax, ">=", "<")
            },
        }
    }

    fn get_table_scan_reader(myconn: std::rc::Rc<MyConn>, commit_on_drop: bool, db: &str, coll: &str) -> Result<MyCollectionReader> {
        let tbl = get_table_name_for_collection(db, coll);
        let stmt = try!(myconn.conn.prepare(&format!("SELECT bson FROM \"{}\"", tbl)).map_err(elmo::wrap_err));
        // TODO keep track of total keys examined, etc.
        let seq = 
            StatementBsonValueIterator {
                     stmt: stmt,
            };
        let rdr = 
            MyCollectionReader {
                commit_on_drop: commit_on_drop,
                seq: box seq,
                myconn: myconn,
            };
        Ok(rdr)
    }

    fn get_nontext_index_scan_reader(myconn: std::rc::Rc<MyConn>, commit_on_drop: bool, ndx: &elmo::IndexInfo, bounds: elmo::QueryBounds) -> Result<MyCollectionReader> {
        let stmt = try!(Self::get_stmt_for_index_scan(&myconn, ndx, bounds));

        // TODO keep track of total keys examined, etc.
        let seq = 
            StatementBsonValueIterator {
                     stmt: stmt,
            };
        let rdr = 
            MyCollectionReader {
                commit_on_drop: commit_on_drop,
                seq: box seq,
                myconn: myconn,
            };
        Ok(rdr)
    }

    // TODO this function has a bunch of logic that would prefer to be up above the storage layer API
    fn get_text_index_scan_reader(myconn: std::rc::Rc<MyConn>, commit_on_drop: bool, ndx: &elmo::IndexInfo,  eq: elmo::QueryKey, terms: Vec<elmo::TextQueryTerm>) -> Result<MyCollectionReader> {
        let tbl_coll = get_table_name_for_collection(&ndx.db, &ndx.coll);
        let tbl_ndx = get_table_name_for_index(&ndx.db, &ndx.coll, &ndx.name);
        // TODO we wish we didn't have to call get_normalized_spec() here just to get weights
        let (_, weights) = try!(elmo::get_normalized_spec(&ndx.spec, &ndx.options));
        let weights = 
            match weights {
                None => return Err(elmo::Error::Misc(String::from("non text index"))),
                Some(w) => w,
            };

        fn lookup(stmt: &mut sqlite3::PreparedStatement, vals: &Vec<(&bson::Value, bool)>, word: &str) -> Result<Vec<(i64,i32)>> {
            // TODO if we just search for the word without the weight, we could
            // use the add_one trick from EQ.  Probably need key encoding of an array
            // to omit the array length.  See comment there.
            let vmin = bson::Value::BArray(bson::Array {items: vec![bson::Value::BString(String::from(word)), bson::Value::BInt32(0)]});
            let vmax = bson::Value::BArray(bson::Array {items: vec![bson::Value::BString(String::from(word)), bson::Value::BInt32(100000)]});

            let kmin = bson::Value::encode_multi_for_index(vals, Some(&vec![(&vmin, false)]));
            let kmax = bson::Value::encode_multi_for_index(vals, Some(&vec![(&vmax, false)]));
            stmt.clear_bindings();
            try!(stmt.bind_blob(1, &kmin).map_err(elmo::wrap_err));
            try!(stmt.bind_blob(2, &kmax).map_err(elmo::wrap_err));
            let mut entries = Vec::new();
            loop {
                match try!(stmt.step().map_err(elmo::wrap_err)) {
                    None => break,
                    Some(row) => {
                        let k = row.column_slice(0).expect("NOT NULL");
                        let w = try!(bson::Value::get_weight_from_index_entry(k));
                        let did = row.column_int64(1);
                        entries.push((did,w));
                    },
                }
            }
            stmt.reset();
            Ok(entries)
        };

        let sql = format!("SELECT k, doc_rowid FROM \"{}\" i WHERE k > ? AND k < ?", tbl_ndx);
        let mut stmt = try!(myconn.conn.prepare(&sql).map_err(elmo::wrap_err));

        let mut found = Vec::new();
        for term in &terms {
            let entries = 
                match term {
                    &elmo::TextQueryTerm::Word(neg, ref s) => {
                        let entries = try!(lookup(&mut stmt, &eq, &s));
                        entries
                    },
                    &elmo::TextQueryTerm::Phrase(neg, ref s) => {
                        // TODO tokenize properly
                        let words = s.split(" ");
                        let mut entries = Vec::new();
                        for w in words {
                            entries.push_all(&try!(lookup(&mut stmt, &eq, w)));
                        }
                        entries
                    },
                };
            let v = (term, entries);
            found.push(v);
        };

        fn contains_phrase(weights: &HashMap<String, i32>, doc: &bson::Value, p: &str) -> bool {
            weights.keys().any(
                |k|
                doc.walk_path(k).leaves().any(
                    |leaf|
                    match leaf.v {
                        Some(v) => {
                            match v {
                                &bson::Value::BString(ref s) => s.find(p).is_some(),
                                _ => false,
                            }
                        },
                        None => {
                            false
                        },
                    }
                    )
                )
        }

        fn check_phrase(terms: &Vec<elmo::TextQueryTerm>, weights: &HashMap<String, i32>, doc: &bson::Value) -> bool {
            for term in terms {
                let b = 
                    match term {
                        &elmo::TextQueryTerm::Word(neg, ref s) => true,
                        &elmo::TextQueryTerm::Phrase(neg, ref s) => {
                            let has = contains_phrase(weights, doc, s);
                            if neg {
                                !has
                            } else {
                                has
                            }
                        },
                    };
                if !b {
                    return false;
                }
            }
            return true;
        }

        let mut pos_entries = Vec::new();
        let mut neg_entries = Vec::new();
        for e in found {
            let (term, entries) = e;
            match term {
                &elmo::TextQueryTerm::Word(neg, ref s) => {
                    if neg {
                        neg_entries.push_all(&entries);
                    } else {
                        pos_entries.push_all(&entries);
                    }
                },
                &elmo::TextQueryTerm::Phrase(neg, ref s) => {
                    if neg {
                        // TODO probably should not negate a doc just because it contains one of the words in a negated phrase
                        // neg_entries.push_all(&entries);
                    } else {
                        pos_entries.push_all(&entries);
                    }
                },
            };
        }

        let neg_docids = neg_entries.into_iter().map(|t| t.0).collect::<HashSet<_>>();
        let mut remaining = Vec::new();
        for t in pos_entries {
            let (did, w) = t;
            if !neg_docids.contains(&did) {
                remaining.push((did, w));
            }
        }

        let mut doc_weights: HashMap<i64, Vec<i32>> = HashMap::new();
        for t in remaining {
            let (did, w) = t;
            if doc_weights.contains_key(&did) {
                let v = doc_weights.get_mut(&did).expect("just checked this");
                v.push(w);
            } else {
                doc_weights.insert(did, vec![w]);
            }
        }

        let sql = format!("SELECT bson FROM \"{}\" WHERE did=?", tbl_coll);
        let mut stmt = try!(myconn.conn.prepare(&sql).map_err(elmo::wrap_err));

        let mut res = Vec::new();
        for (did, cur_weights) in doc_weights {
            try!(stmt.bind_int64(1, did).map_err(elmo::wrap_err));
            {
                let rdr = 
                    RefStatementBsonValueIterator {
                        stmt: &mut stmt,
                    };
                for r in rdr {
                    let mut r = try!(r);
                    let keep = check_phrase(&terms, &weights, &r.doc);
                    if keep {
                        // TODO this is not the way mongo does this calculation
                        let score = cur_weights.iter().sum::<i32>() as f64;
                        r.score = Some(score);
                        res.push(Ok(r));
                    }
                }
            }
            stmt.reset();
        }

        let rdr = 
            MyCollectionReader {
                commit_on_drop: commit_on_drop,
                seq: box res.into_iter(),
                myconn: myconn,
            };
        Ok(rdr)
    }

    fn get_reader_collection_scan(&self, myconn: std::rc::Rc<MyConn>, commit_on_drop: bool, db: &str, coll: &str) -> Result<MyCollectionReader> {
        match try!(self.get_collection_options(db, coll)) {
            None => {
                let rdr = 
                    MyCollectionReader {
                        commit_on_drop: commit_on_drop,
                        seq: box std::iter::empty(),
                        myconn: myconn,
                    };
                Ok(rdr)
            },
            Some(_) => {
                let rdr = try!(Self::get_table_scan_reader(myconn, commit_on_drop, db, coll));
                return Ok(rdr);
            },
        }
    }

    fn get_reader_text_index_scan(&self, myconn: std::rc::Rc<MyConn>, commit_on_drop: bool, ndx: &elmo::IndexInfo, eq: elmo::QueryKey, terms: Vec<elmo::TextQueryTerm>) -> Result<MyCollectionReader> {
        // TODO is this check right?
        // should we instead check for the existence of the index?
        match try!(self.get_collection_options(&ndx.db, &ndx.coll)) {
            None => {
                let rdr = 
                    MyCollectionReader {
                        commit_on_drop: commit_on_drop,
                        seq: box std::iter::empty(),
                        myconn: myconn,
                    };
                Ok(rdr)
            },
            Some(_) => {
                let rdr = try!(Self::get_text_index_scan_reader(myconn, commit_on_drop, ndx, eq, terms));
                return Ok(rdr);
            },
        }
    }

    fn get_reader_regular_index_scan(&self, myconn: std::rc::Rc<MyConn>, commit_on_drop: bool, ndx: &elmo::IndexInfo, bounds: elmo::QueryBounds) -> Result<MyCollectionReader> {
        // TODO is this check right?
        // should we instead check for the existence of the index?
        match try!(self.get_collection_options(&ndx.db, &ndx.coll)) {
            None => {
                let rdr = 
                    MyCollectionReader {
                        commit_on_drop: commit_on_drop,
                        seq: box std::iter::empty(),
                        myconn: myconn,
                    };
                Ok(rdr)
            },
            Some(_) => {
                let rdr = try!(Self::get_nontext_index_scan_reader(myconn, commit_on_drop, ndx, bounds));
                return Ok(rdr);
            },
        }
    }

    fn get_index_info(&self, db: &str, coll: &str, name: &str) -> Result<Option<elmo::IndexInfo>> {
        // TODO DRY this string, below
        let mut stmt = try!(self.conn.prepare("SELECT ndxName, spec, options, dbName, collName FROM \"indexes\" WHERE dbName=? AND collName=? AND ndxName=?").map_err(elmo::wrap_err));
        try!(stmt.bind_text(1, db).map_err(elmo::wrap_err));
        try!(stmt.bind_text(2, coll).map_err(elmo::wrap_err));
        try!(stmt.bind_text(3, name).map_err(elmo::wrap_err));
        match try!(stmt.step().map_err(elmo::wrap_err)) {
            None => Ok(None),
            Some(row) => {
                let info = try!(get_index_info_from_row(&row));
                Ok(Some(info))
            },
        }
    }

    fn base_list_indexes(&self) -> Result<Vec<elmo::IndexInfo>> {
        // TODO DRY this string, above
        let mut stmt = try!(self.conn.prepare("SELECT ndxName, spec, options, dbName, collName FROM \"indexes\"").map_err(elmo::wrap_err));
        let mut v = Vec::new();
        loop {
            match try!(stmt.step().map_err(elmo::wrap_err)) {
                None => break,
                Some(row) => {
                    let info = try!(get_index_info_from_row(&row));
                    v.push(info);
                },
            }
        }
        Ok(v)
    }

    fn base_list_collections(&self) -> Result<Vec<elmo::CollectionInfo>> {
        let mut stmt = try!(self.conn.prepare("SELECT dbName, collName, options FROM \"collections\" ORDER BY collName ASC").map_err(elmo::wrap_err));
        let mut v = Vec::new();
        loop {
            match try!(stmt.step().map_err(elmo::wrap_err)) {
                None => break,
                Some(row) => {
                    let info = try!(get_collection_info_from_row(&row));
                    v.push(info);
                },
            }
        }
        Ok(v)
    }

}

impl MyCollectionWriter {
    fn find_rowid(&mut self, v: &bson::Value) -> Result<Option<i64>> {
        match self.stmt_find_rowid {
            None => Ok(None),
            Some(ref mut stmt) => {
                stmt.clear_bindings();
                let ba = bson::Value::encode_one_for_index(v, false);
                try!(stmt.bind_blob(1, &ba).map_err(elmo::wrap_err));
                let r =
                    match try!(stmt.step().map_err(elmo::wrap_err)) {
                        None => Ok(None),
                        Some(r) => {
                            let rowid = r.column_int64(0);
                            Ok(Some(rowid))
                        },
                    };
                stmt.reset();
                r
            },
        }
    }

}

impl MyWriter {
    fn update_indexes_delete(indexes: &mut Vec<IndexPrep>, rowid: i64) -> Result<()> {
        for t in indexes {
            t.stmt_delete.clear_bindings();
            try!(t.stmt_delete.bind_int64(1, rowid).map_err(elmo::wrap_err));
            try!(step_done(&mut t.stmt_delete));
            t.stmt_delete.reset();
        }
        Ok(())
    }

    fn update_indexes_insert(indexes: &mut Vec<IndexPrep>, rowid: i64, v: &bson::Document) -> Result<()> {
        for t in indexes {
            let entries = try!(elmo::get_index_entries(&v, &t.normspec, &t.weights, &t.info.options));
            for vals in entries {
                let vref = vals.iter().map(|&(ref v,neg)| (v,neg)).collect::<Vec<_>>();
                let k = bson::Value::encode_multi_for_index(&vref, None);
                try!(index_insert_step(&mut t.stmt_insert, k, rowid));
            }
        }
        Ok(())
    }

    fn get_collection_writer(&self, db: &str, coll: &str) -> Result<MyCollectionWriter> {
        let _created = try!(self.base_create_collection(db, coll, bson::Document::new()));
        let tbl = get_table_name_for_collection(db, coll);
        let stmt_insert = try!(self.myconn.conn.prepare(&format!("INSERT INTO \"{}\" (bson) VALUES (?)", tbl)).map_err(elmo::wrap_err));
        let stmt_delete = try!(self.myconn.conn.prepare(&format!("DELETE FROM \"{}\" WHERE rowid=?", tbl)).map_err(elmo::wrap_err));
        let stmt_update = try!(self.myconn.conn.prepare(&format!("UPDATE \"{}\" SET bson=? WHERE rowid=?", tbl)).map_err(elmo::wrap_err));
        let indexes = try!(self.myconn.base_list_indexes());
        let indexes = indexes.into_iter().filter(
            |ndx| ndx.db == db && ndx.coll == coll
            ).collect::<Vec<_>>();
        let mut find_rowid = None;
        for info in &indexes {
            if info.name == "_id_" {
                let tbl = get_table_name_for_index(db, coll, &info.name);
                find_rowid = Some(try!(self.myconn.conn.prepare(&format!("SELECT doc_rowid FROM \"{}\" WHERE k=?", tbl)).map_err(elmo::wrap_err)));
                break;
            }
        }
        let mut index_stmts = Vec::new();
        for info in indexes {
            let tbl_ndx = get_table_name_for_index(db, coll, &info.name);
            let stmt_insert = try!(self.prepare_index_insert(&tbl_ndx));
            let stmt_delete = try!(self.myconn.conn.prepare(&format!("DELETE FROM \"{}\" WHERE doc_rowid=?", tbl_ndx)).map_err(elmo::wrap_err));
            let (normspec, weights) = try!(elmo::get_normalized_spec(&info.spec, &info.options));
            let t = IndexPrep {
                info: info, 
                stmt_insert: stmt_insert, 
                stmt_delete: stmt_delete,
                normspec: normspec,
                weights: weights,
            };
            index_stmts.push(t);
        }
        let c = MyCollectionWriter {
            db: String::from(db),
            coll: String::from(coll),
            insert: stmt_insert,
            delete: stmt_delete,
            update: stmt_update,
            stmt_find_rowid: find_rowid,
            indexes: index_stmts,
        };
        Ok(c)
    }

    fn prep_collection_writer(&mut self, db: &str, coll: &str) -> Result<()> {
        let need_cw =
            if self.cw.is_none() {
                true
            } else {
                let cw = self.cw.as_ref().unwrap();
                if cw.db != db || cw.coll != coll {
                    true
                } else {
                    false
                }
            };
        if need_cw {
            let cw = try!(self.get_collection_writer(db, coll));
            self.cw = Some(cw);
        }
        Ok(())
    }

    fn prepare_index_insert(&self, tbl: &str) -> Result<sqlite3::PreparedStatement> {
        let stmt = try!(self.myconn.conn.prepare(&format!("INSERT INTO \"{}\" (k,doc_rowid) VALUES (?,?)",tbl)).map_err(elmo::wrap_err));
        Ok(stmt)
    }

    fn create_index(&self, info: elmo::IndexInfo) -> Result<bool> {
        //println!("create_index: {:?}", info);
        let _created = try!(self.base_create_collection(&info.db, &info.coll, bson::Document::new()));
        match try!(self.myconn.get_index_info(&info.db, &info.coll, &info.name)) {
            Some(already) => {
                if already.spec != info.spec {
                    // note that we do not compare the options.
                    // I think mongo does it this way too.
                    Err(elmo::Error::Misc(String::from("index already exists with different keys")))
                } else {
                    Ok(false)
                }
            },
            None => {
                // TODO if we already have a text index (where any of its spec keys are text)
                // then fail.

                let ba_spec = info.spec.to_bson_array();
                let ba_options = info.options.to_bson_array();
                let mut stmt = try!(self.myconn.conn.prepare("INSERT INTO \"indexes\" (dbName,collName,ndxName,spec,options) VALUES (?,?,?,?,?)").map_err(elmo::wrap_err));
                try!(stmt.bind_text(1, &info.db).map_err(elmo::wrap_err));
                try!(stmt.bind_text(2, &info.coll).map_err(elmo::wrap_err));
                try!(stmt.bind_text(3, &info.name).map_err(elmo::wrap_err));
                try!(stmt.bind_blob(4, &ba_spec).map_err(elmo::wrap_err));
                try!(stmt.bind_blob(5, &ba_options).map_err(elmo::wrap_err));
                match try!(stmt.step().map_err(elmo::wrap_err)) {
                    None => {
                        let tbl_coll = get_table_name_for_collection(&info.db, &info.coll);
                        let tbl_ndx = get_table_name_for_index(&info.db, &info.coll, &info.name);
                        let s =
                        match info.options.get("unique") {
                            Some(&bson::Value::BBoolean(true)) => {
                                format!("CREATE TABLE \"{}\" (k BLOB NOT NULL, doc_rowid int NOT NULL REFERENCES \"{}\"(did) ON DELETE CASCADE, PRIMARY KEY (k))", tbl_ndx, tbl_coll)
                            },
                            _ => {
                                format!("CREATE TABLE \"{}\" (k BLOB NOT NULL, doc_rowid int NOT NULL REFERENCES \"{}\"(did) ON DELETE CASCADE, PRIMARY KEY (k,doc_rowid))", tbl_ndx, tbl_coll)
                            },
                        };
                        try!(self.myconn.conn.exec(&s).map_err(elmo::wrap_err));
                        try!(self.myconn.conn.exec(&format!("CREATE INDEX \"childndx_{}\" ON \"{}\" (doc_rowid)", tbl_ndx, tbl_ndx)).map_err(elmo::wrap_err));
                        // now insert index entries for every doc that already exists
                        let (normspec, weights) = try!(elmo::get_normalized_spec(&info.spec, &info.options));
                        let mut stmt2 = try!(self.myconn.conn.prepare(&format!("SELECT did,bson FROM \"{}\"", tbl_coll)).map_err(elmo::wrap_err));
                        let mut stmt_insert = try!(self.prepare_index_insert(&tbl_ndx));
                        loop {
                            match try!(stmt2.step().map_err(elmo::wrap_err)) {
                                None => break,
                                Some(row) => {
                                    let doc_rowid = row.column_int64(0);
                                    let new_doc = try!(bson::Document::from_bson(&row.column_slice(1).expect("NOT NULL")));
                                    let entries = try!(elmo::get_index_entries(&new_doc, &normspec, &weights, &info.options));
                                    for vals in entries {
                                        //println!("index entry: {:?}", vals);
                                        let vref = vals.iter().map(|&(ref v,neg)| (v,neg)).collect::<Vec<_>>();
                                        let k = bson::Value::encode_multi_for_index(&vref, None);
                                        try!(index_insert_step(&mut stmt_insert, k, doc_rowid));
                                    }
                                },
                            }
                        }
                        Ok(true)
                    },
                    Some(_) => {
                        Err(elmo::Error::Misc(String::from("insert stmt step() returned a row")))
                    },
                }
            },
        }
    }

    fn base_clear_collection(&self, db: &str, coll: &str) -> Result<bool> {
        match try!(self.myconn.get_collection_options(db, coll)) {
            None => {
                let created = try!(self.base_create_collection(db, coll, bson::Document::new()));
                Ok(created)
            },
            Some(_) => {
                let tbl = get_table_name_for_collection(db, coll);
                try!(self.myconn.conn.exec(&format!("DELETE FROM \"{}\"", tbl)).map_err(elmo::wrap_err));
                Ok(false)
            },
        }
    }

    fn base_rename_collection(&self, old_name: &str, new_name: &str, drop_target: bool) -> Result<bool> {
        let (old_db, old_coll) = try!(bson::split_name(old_name));
        let (new_db, new_coll) = try!(bson::split_name(new_name));

        // jstests/core/rename8.js seems to think that renaming to/from a system collection is illegal unless
        // that collection is system.users, which is "whitelisted".  for now, we emulate this behavior, even
        // though system.users isn't supported.
        if old_coll != "system.users" && old_coll.starts_with("system.") {
            return Err(elmo::Error::Misc(String::from("renameCollection with a system collection not allowed.")))
        }
        if new_coll != "system.users" && new_coll.starts_with("system.") {
            return Err(elmo::Error::Misc(String::from("renameCollection with a system collection not allowed.")))
        }

        if drop_target {
            let _deleted = try!(self.base_drop_collection(new_db, new_coll));
        }

        match try!(self.myconn.get_collection_options(old_db, old_coll)) {
            None => {
                let created = try!(self.base_create_collection(new_db, new_coll, bson::Document::new()));
                Ok(created)
            },
            Some(_) => {
                let old_tbl = get_table_name_for_collection(old_db, old_coll);
                let new_tbl = get_table_name_for_collection(new_db, new_coll);
                let indexes = try!(self.myconn.base_list_indexes());
                let indexes = indexes.into_iter().filter(|info| info.db == old_db && info.coll == old_coll ).collect::<Vec<_>>();

                let mut stmt = try!(self.myconn.conn.prepare("UPDATE \"collections\" SET dbName=?, collName=? WHERE dbName=? AND collName=?").map_err(elmo::wrap_err));
                try!(stmt.bind_text(1, new_db).map_err(elmo::wrap_err));
                try!(stmt.bind_text(2, new_coll).map_err(elmo::wrap_err));
                try!(stmt.bind_text(3, old_db).map_err(elmo::wrap_err));
                try!(stmt.bind_text(4, old_coll).map_err(elmo::wrap_err));
                try!(step_done(&mut stmt));
                stmt.reset();

                try!(self.myconn.conn.exec(&format!("ALTER TABLE \"{}\" RENAME TO \"{}\"", old_tbl, new_tbl)).map_err(elmo::wrap_err));

                for info in indexes {
                    let old_ndx_tbl = get_table_name_for_index(old_db, old_coll, &info.name);
                    let new_ndx_tbl = get_table_name_for_index(new_db, new_coll, &info.name);
                    try!(self.myconn.conn.exec(&format!("ALTER TABLE \"{}\" RENAME TO \"{}\"", old_ndx_tbl, new_ndx_tbl)).map_err(elmo::wrap_err));
                }
                Ok(false)
            },
        }
    }

    fn base_create_collection(&self, db: &str, coll: &str, options: bson::Document) -> Result<bool> {
        match try!(self.myconn.get_collection_options(db, coll)) {
            Some(_) => Ok(false),
            None => {
                let v_options = options.to_bson_array();
                let mut stmt = try!(self.myconn.conn.prepare("INSERT INTO \"collections\" (dbName,collName,options) VALUES (?,?,?)").map_err(elmo::wrap_err));
                try!(stmt.bind_text(1, db).map_err(elmo::wrap_err));
                try!(stmt.bind_text(2, coll).map_err(elmo::wrap_err));
                try!(stmt.bind_blob(3, &v_options).map_err(elmo::wrap_err));
                match try!(stmt.step().map_err(elmo::wrap_err)) {
                    None => {
                        let tbl = get_table_name_for_collection(db, coll);
                        try!(self.myconn.conn.exec(&format!("CREATE TABLE \"{}\" (did INTEGER PRIMARY KEY, bson BLOB NOT NULL)", tbl)).map_err(elmo::wrap_err));
                        // now create mongo index for _id
                        match options.get("autoIndexId") {
                            Some(&bson::Value::BBoolean(false)) => (),
                            _ => {
                                let info = elmo::IndexInfo {
                                    db: String::from(db),
                                    coll: String::from(coll),
                                    name: String::from("_id_"),
                                    spec: bson::Document {pairs: vec![(String::from("_id"), bson::Value::BInt32(1))]},
                                    options: bson::Document {pairs: vec![(String::from("unique"), bson::Value::BBoolean(true))]},
                                };
                                let _created = self.create_index(info);
                            },
                        }
                        Ok(true)
                    },
                    Some(_) => {
                        Err(elmo::Error::Misc(String::from("insert stmt step() returned a row")))
                    },
                }
            },
        }
    }

    fn base_create_indexes(&self, what: Vec<elmo::IndexInfo>) -> Result<Vec<bool>> {
        let mut v = Vec::new();
        for info in what {
            let b = try!(self.create_index(info));
            v.push(b);
        }
        Ok(v)
    }

    fn base_drop_index(&self, db: &str, coll: &str, name: &str) -> Result<bool> {
        match try!(self.myconn.get_index_info(db, coll, name)) {
            None => Ok(false),
            Some(_) => {
                let mut stmt = try!(self.myconn.conn.prepare("DELETE FROM \"indexes\" WHERE dbName=? AND collName=? AND ndxName=?").map_err(elmo::wrap_err));
                try!(stmt.bind_text(1, db).map_err(elmo::wrap_err));
                try!(stmt.bind_text(2, coll).map_err(elmo::wrap_err));
                try!(stmt.bind_text(3, name).map_err(elmo::wrap_err));
                try!(step_done(&mut stmt));
                try!(verify_changes(&stmt, 1));
                stmt.reset();
                let tbl = get_table_name_for_index(db, coll, name);
                try!(self.myconn.conn.exec(&format!("DROP TABLE \"{}\"", tbl)).map_err(elmo::wrap_err));
                Ok(true)
            },
        }
    }

    fn base_drop_database(&self, db: &str) -> Result<bool> {
        let collections = try!(self.myconn.base_list_collections());
        let mut b = false;
        for t in collections {
            if t.db == db {
                let _deleted = try!(self.base_drop_collection(&t.db, &t.coll));
                assert!(_deleted);
                b = true;
            }
        }
        Ok(b)
    }

    fn base_drop_collection(&self, db: &str, coll: &str) -> Result<bool> {
        match try!(self.myconn.get_collection_options(db, coll)) {
            None => Ok(false),
            Some(_) => {
                let indexes = try!(self.myconn.base_list_indexes());
                for info in indexes {
                    if info.db == db && info.coll == coll {
                        try!(self.base_drop_index(&info.db, &info.coll, &info.name));
                    }
                }
                let mut stmt = try!(self.myconn.conn.prepare("DELETE FROM \"collections\" WHERE dbName=? AND collName=?").map_err(elmo::wrap_err));
                try!(stmt.bind_text(1, db).map_err(elmo::wrap_err));
                try!(stmt.bind_text(2, coll).map_err(elmo::wrap_err));
                try!(step_done(&mut stmt));
                try!(verify_changes(&stmt, 1));
                stmt.reset();
                let tbl = get_table_name_for_collection(db, coll);
                try!(self.myconn.conn.exec(&format!("DROP TABLE \"{}\"", tbl)).map_err(elmo::wrap_err));
                Ok(true)
            },
        }
    }

}

impl elmo::StorageWriter for MyWriter {
    fn update(&mut self, db: &str, coll: &str, v: &bson::Document) -> Result<()> {
        match v.get("_id") {
            None => Err(elmo::Error::Misc(String::from("cannot update without _id"))),
            Some(id) => {
                try!(self.prep_collection_writer(db, coll));
                let mut cw = self.cw.as_mut().unwrap();
                match try!(cw.find_rowid(&id).map_err(elmo::wrap_err)) {
                    None => Err(elmo::Error::Misc(String::from("update but does not exist"))),
                    Some(rowid) => {
                                let ba = v.to_bson_array();
                                cw.update.clear_bindings();
                                try!(cw.update.bind_blob(1,&ba).map_err(elmo::wrap_err));
                                try!(cw.update.bind_int64(2, rowid).map_err(elmo::wrap_err));
                                try!(step_done(&mut cw.update));
                                try!(verify_changes(&cw.update, 1));
                                cw.update.reset();
                                try!(Self::update_indexes_delete(&mut cw.indexes, rowid));
                                try!(Self::update_indexes_insert(&mut cw.indexes, rowid, &v));
                                Ok(())
                            },
                }
            },
        }
    }

    fn delete(&mut self, db: &str, coll: &str, v: &bson::Value) -> Result<bool> {
        // TODO is v supposed to be the id?
        try!(self.prep_collection_writer(db, coll));
        let mut cw = self.cw.as_mut().unwrap();
        match try!(cw.find_rowid(&v).map_err(elmo::wrap_err)) {
            None => Ok(false),
            Some(rowid) => {
                cw.delete.clear_bindings();
                try!(cw.delete.bind_int64(1, rowid).map_err(elmo::wrap_err));
                try!(step_done(&mut cw.delete));
                cw.delete.reset();
                let count = self.myconn.conn.changes();
                if count == 1 {
                    // TODO might not need index update here.  foreign key cascade?
                    try!(Self::update_indexes_delete(&mut cw.indexes, rowid));
                    Ok(true)
                } else if count == 0 {
                    Ok(false)
                } else {
                    Err(elmo::Error::Misc(String::from("changes() after delete is wrong")))
                }
            },
        }
    }

    fn insert(&mut self, db: &str, coll: &str, v: &bson::Document) -> Result<()> {
        try!(self.prep_collection_writer(db, coll));
        let mut cw = self.cw.as_mut().unwrap();
        let ba = v.to_bson_array();
        cw.insert.clear_bindings();
        try!(cw.insert.bind_blob(1,&ba).map_err(elmo::wrap_err));
        try!(step_done(&mut cw.insert));
        try!(verify_changes(&cw.insert, 1));
        cw.insert.reset();
        let rowid = self.myconn.conn.last_insert_rowid();
        try!(Self::update_indexes_delete(&mut cw.indexes, rowid));
        try!(Self::update_indexes_insert(&mut cw.indexes, rowid, &v));
        Ok(())
    }

    fn commit(mut self: Box<Self>) -> Result<()> {
        try!(self.myconn.conn.exec("COMMIT TRANSACTION").map_err(elmo::wrap_err));
        self.in_tx = false;
        Ok(())
    }

    fn rollback(mut self: Box<Self>) -> Result<()> {
        try!(self.myconn.conn.exec("ROLLBACK TRANSACTION").map_err(elmo::wrap_err));
        self.in_tx = false;
        Ok(())
    }

    // TODO maybe just move all the stuff below from the private section into here?

    fn create_collection(&mut self, db: &str, coll: &str, options: bson::Document) -> Result<bool> {
        self.base_create_collection(db, coll, options)
    }

    fn drop_collection(&mut self, db: &str, coll: &str) -> Result<bool> {
        self.base_drop_collection(db, coll)
    }

    fn create_indexes(&mut self, what: Vec<elmo::IndexInfo>) -> Result<Vec<bool>> {
        self.base_create_indexes(what)
    }

    fn rename_collection(&mut self, old_name: &str, new_name: &str, drop_target: bool) -> Result<bool> {
        self.base_rename_collection(old_name, new_name, drop_target)
    }

    fn drop_index(&mut self, db: &str, coll: &str, name: &str) -> Result<bool> {
        self.base_drop_index(db, coll, name)
    }

    fn drop_database(&mut self, db: &str) -> Result<bool> {
        self.base_drop_database(db)
    }

    fn clear_collection(&mut self, db: &str, coll: &str) -> Result<bool> {
        self.base_clear_collection(db, coll)
    }

}

// TODO do we need to declare that StorageWriter must implement Drop ?
impl Drop for MyWriter {
    fn drop(&mut self) {
        // TODO consider panic here if still in tx.  force caller to
        // explicitly commit or rollback.
        if self.in_tx {
            // TODO should rollback be the default here?  or commit?
            let _ignored = self.myconn.conn.exec("ROLLBACK TRANSACTION");
        }
    }
}

// TODO do we need to declare that StorageReader must implement Drop ?
impl Drop for MyReader {
    fn drop(&mut self) {
        // TODO consider panic here if still in tx.  force caller to
        // explicitly end the tx.

        // this transaction was [supposed to be] read-only, so it doesn't
        // matter in principle whether we commit or rollback.  in SQL Server,
        // if temp tables were created, commit is MUCH faster than rollback.
        // but this is sqlite.  anyway...
        if self.in_tx {
            let _ignored = self.myconn.conn.exec("COMMIT TRANSACTION");
        }
    }
}

impl Drop for MyCollectionReader {
    fn drop(&mut self) {
        // this transaction was [supposed to be] read-only, so it doesn't
        // matter in principle whether we commit or rollback.  in SQL Server,
        // if temp tables were created, commit is MUCH faster than rollback.
        // but this is sqlite.  anyway...
        if self.commit_on_drop {
            let _ignored = self.myconn.conn.exec("COMMIT TRANSACTION");
        }
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
        self.in_tx = false;
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

impl elmo::StorageBase for MyWriter {
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
    fn begin_write(&self) -> Result<Box<elmo::StorageWriter + 'static>> {
        // TODO retry/sleep loop here
        try!(self.myconn.conn.exec("BEGIN IMMEDIATE TRANSACTION").map_err(elmo::wrap_err));
        let w = MyWriter {
            myconn: self.myconn.clone(),
            in_tx: true,
            cw: None,
        };
        Ok(box w)
    }

    fn begin_read(&self) -> Result<Box<elmo::StorageReader + 'static>> {
        try!(self.myconn.conn.exec("BEGIN TRANSACTION").map_err(elmo::wrap_err));
        let r = MyReader {
            myconn: self.myconn.clone(),
            in_tx: true,
        };
        Ok(box r)
    }
}

fn base_connect(name: &str) -> sqlite3::SqliteResult<sqlite3::DatabaseConnection> {
    let access = sqlite3::access::ByFilename { flags: sqlite3::access::flags::OPEN_READWRITE | sqlite3::access::flags::OPEN_CREATE, filename: name};
    let conn = try!(sqlite3::DatabaseConnection::new(access));
    try!(conn.exec("PRAGMA journal_mode=WAL"));
    try!(conn.exec("PRAGMA foreign_keys=ON"));
    let mut tries = 0;
    loop {
        tries = tries + 1;
        match conn.exec("BEGIN IMMEDIATE TRANSACTION") {
            Ok(_) => {
                try!(conn.exec("CREATE TABLE IF NOT EXISTS \"collections\" (dbName TEXT NOT NULL, collName TEXT NOT NULL, options BLOB NOT NULL, PRIMARY KEY (dbName,collName))"));
                try!(conn.exec("CREATE TABLE IF NOT EXISTS \"indexes\" (dbName TEXT NOT NULL, collName TEXT NOT NULL, ndxName TEXT NOT NULL, spec BLOB NOT NULL, options BLOB NOT NULL, PRIMARY KEY (dbName, collName, ndxName), FOREIGN KEY (dbName,collName) REFERENCES \"collections\" ON DELETE CASCADE ON UPDATE CASCADE, UNIQUE (spec,dbName,collName))"));
                try!(conn.exec("COMMIT TRANSACTION"));
                break;
            },
            Err(e) => {
                // TODO we could maaaaaybe just punt here if we get SQLITE_BUSY.
                // the idea would be that if somebody else has the write lock, then
                // the tables we want to create are already created.  So just ignore
                // the error.

                if e.kind == sqlite3::SqliteErrorCode::SQLITE_BUSY {
                    if tries > 10 {
                        return Err(e);
                    }

                    println!("error on begin immediate: {:?}", e);
                    println!("tries: {:?}", tries);
                    println!("sleeping to try again");
                    std::thread::sleep_ms(50);
                } else {
                    return Err(e);
                }
            },
        }
    }

    Ok(conn)
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

/*

look at the non-allocating alternatives to column_text() and column_blob()

*/

