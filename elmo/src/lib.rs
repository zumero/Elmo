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

#![feature(convert)]
#![feature(box_syntax)]
#![feature(associated_consts)]
#![feature(append)]

use std::collections::HashMap;
use std::collections::HashSet;
use std::cmp::Ordering;

extern crate time;

extern crate misc;

extern crate bson;

#[derive(Debug)]
pub enum Error {
    // TODO remove Misc
    Misc(String),

    MongoCode(i32, String),

    // TODO more detail within CorruptFile
    CorruptFile(&'static str),

    Bson(bson::Error),
    Io(std::io::Error),
    Utf8(std::str::Utf8Error),
    Whatever(Box<std::error::Error>),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match *self {
            Error::Bson(ref err) => write!(f, "bson error: {}", err),
            Error::Io(ref err) => write!(f, "IO error: {}", err),
            Error::Utf8(ref err) => write!(f, "Utf8 error: {}", err),
            Error::Whatever(ref err) => write!(f, "Other error: {}", err),
            Error::Misc(ref s) => write!(f, "Misc error: {}", s),
            Error::MongoCode(code, ref s) => write!(f, "Mongo error code {}: {}", code, s),
            Error::CorruptFile(s) => write!(f, "Corrupt file: {}", s),
        }
    }
}

impl std::error::Error for Error {
    fn description(&self) -> &str {
        match *self {
            Error::Bson(ref err) => std::error::Error::description(err),
            Error::Io(ref err) => std::error::Error::description(err),
            Error::Utf8(ref err) => std::error::Error::description(err),
            Error::Whatever(ref err) => std::error::Error::description(&**err),
            Error::Misc(ref s) => s.as_str(),
            Error::MongoCode(code, ref s) => s.as_str(),
            Error::CorruptFile(s) => s,
        }
    }

    // TODO cause
}

pub fn wrap_err<E: std::error::Error + 'static>(err: E) -> Error {
    Error::Whatever(box err)
}

impl From<bson::Error> for Error {
    fn from(err: bson::Error) -> Error {
        Error::Bson(err)
    }
}

impl From<std::io::Error> for Error {
    fn from(err: std::io::Error) -> Error {
        Error::Io(err)
    }
}

// TODO not sure this is useful
impl From<Box<std::error::Error>> for Error {
    fn from(err: Box<std::error::Error>) -> Error {
        Error::Whatever(err)
    }
}

impl From<std::str::Utf8Error> for Error {
    fn from(err: std::str::Utf8Error) -> Error {
        Error::Utf8(err)
    }
}

/*
impl<T> From<std::sync::PoisonError<T>> for Error {
    fn from(_err: std::sync::PoisonError<T>) -> Error {
        Error::Poisoned
    }
}

impl<'a, E: Error + 'a> From<E> for Error {
    fn from(err: E) -> Error {
        Error::Whatever(err)
    }
}
*/

pub type Result<T> = std::result::Result<T, Error>;

pub fn mongo_strftime(fmt: &str, tm: &time::Tm) -> Result<String> {
    //println!("mongo_strftime on: {:?}", tm);
    let mut s = String::from(fmt).chars().collect::<Vec<char>>();
    let mut cur = 0;
    while cur < s.len() {
        let mut n = cur;
        while n < s.len() && s[n] != '%' {
            n = n + 1;
        }
        if n == s.len() {
            break;
        } else if n+1 == s.len() {
            return Err(Error::MongoCode(18535, format!("strftime format ends with single %")));
        } else {
            let repl = match s[n+1] {
                'Y' => format!("{}", tm.tm_year + 1900),
                'm' => format!("{:02}", tm.tm_mon + 1),
                'd' => format!("{:02}", tm.tm_mday),
                'H' => format!("{:02}", tm.tm_hour),
                'M' => format!("{:02}", tm.tm_min),
                'S' => format!("{:02}", tm.tm_sec),
                'L' => format!("{:03}", tm.tm_nsec / 1000000),
                'j' => format!("{:03}", tm.tm_yday + 1),
                'w' => format!("{}", tm.tm_wday + 1),
                'U' => format!("{:02}", (tm.tm_yday - tm.tm_wday + 7) / 7),
                '%' => String::from("%"),
                _ => return Err(Error::MongoCode(18536, format!("strftime format contains invalid specifier: {}", fmt))),
            };
            let repl = repl.chars().collect::<Vec<char>>();
            s.remove(n + 1);
            s.remove(n);
            // TODO I wish there were a nicer way to insert the contents of one vec into another
            for i in 0 .. repl.len() {
                let c = repl[repl.len() - i - 1];
                s.insert(n, c);
            }
            cur = n + repl.len();
        }
    }
    let s = s.iter().cloned().collect::<String>();
    Ok(s)
}

mod matcher;

pub struct CollectionInfo {
    pub db: String,
    pub coll: String,
    pub options: bson::Document,
}

// TODO remove derive Clone later
#[derive(Clone,Debug)]
pub struct IndexInfo {
    pub db: String,
    pub coll: String,
    pub name: String,
    pub spec: bson::Document,
    pub options: bson::Document,
}

impl IndexInfo {
    pub fn full_collection_name(&self) -> String {
        format!("{}.{}", self.db, self.coll)
    }

    fn is_sparse(&self) -> bool {
        match self.options.get("sparse") {
            Some(&bson::Value::BBoolean(b)) => b,
            _ => false,
        }
    }
}

// TODO should be called IndexKey?
pub type QueryKey<'a> = Vec<(&'a bson::Value, bool)>;

#[derive(Hash,PartialEq,Eq,Debug,Clone)]
pub enum TextQueryTerm {
    Word(bool, String),
    Phrase(bool, String),
}

// TODO should be called IndexBounds?
#[derive(Debug)]
pub enum QueryBounds<'a> {
    EQ(QueryKey<'a>),
    GT(QueryKey<'a>),
    GTE(QueryKey<'a>),
    LT(QueryKey<'a>),
    LTE(QueryKey<'a>),
    GT_LT(QueryKey<'a>, QueryKey<'a>, QueryKey<'a>),
    GT_LTE(QueryKey<'a>, QueryKey<'a>, QueryKey<'a>),
    GTE_LT(QueryKey<'a>, QueryKey<'a>, QueryKey<'a>),
    GTE_LTE(QueryKey<'a>, QueryKey<'a>, QueryKey<'a>),
}

struct Comps<'a> {
    eq: HashMap<&'a str, &'a bson::Value>,
    ineq: HashMap<&'a str, (Option<(OpGt, &'a bson::Value)>, Option<(OpLt, &'a bson::Value)>)>,
}

// TODO the IndexInfos below should be references

#[derive(Debug)]
enum QueryPlan<'a,'i> {
    Regular(&'i IndexInfo, QueryBounds<'a>),
    Text(&'i IndexInfo, QueryKey<'a>, Vec<TextQueryTerm>),
}

impl<'a,'i> QueryPlan<'a,'i> {
    fn get_ndx(&self) -> &'i IndexInfo {
        match self {
            &QueryPlan::Regular(ndx, _) => ndx,
            &QueryPlan::Text(ndx,_,_) => ndx,
        }
    }
}

#[derive(PartialEq,Copy,Clone)]
enum OpIneq {
    LT,
    GT,
    LTE,
    GTE,
}

impl OpIneq {
    fn is_gt(self) -> bool {
        match self {
            OpIneq::LT => false,
            OpIneq::LTE => false,
            OpIneq::GT => true,
            OpIneq::GTE => true,
        }
    }
}

#[derive(PartialEq,Copy,Clone)]
enum OpLt {
    LT,
    LTE,
}

#[derive(PartialEq,Copy,Clone)]
enum OpGt {
    GT,
    GTE,
}

// TODO I dislike the name of this.  also, consider making it a trait.
#[derive(Debug,Clone)]
pub struct Row {
    // TODO I wish this were bson::Document.  but when you have a reference to a
    // bson::Document and what you need is a bson::Value, you can't get there,
    // because you need ownership and you don't have it.  So clone.  Which is
    // awful.
    pub doc: bson::Value,
    pub pos: Option<usize>,
    pub score: Option<f64>,
    // TODO stats for explain
}

#[derive(Copy,Clone,Debug)]
pub enum ProjectionMode {
    Include,
    Exclude,
}

#[derive(Debug)]
pub enum ProjectionOperator {
    Slice1(i32),
    Slice2(i32, usize),
    MetaTextScore,
    ElemMatch(matcher::QueryDoc),
}

fn i64_can_be_i32(f: i64) -> bool {
    let n = f as i32;
    let f2 = n as i64;
    f == f2
}

fn f64_can_be_i32(f: f64) -> bool {
    let n = f as i32;
    let f2 = n as f64;
    f == f2
}

fn f64_can_be_i64(f: f64) -> bool {
    let n = f as i64;
    let f2 = n as f64;
    f == f2
}

fn fix_positional(s: &str, pos: Option<usize>) -> String {
    match pos {
        None => String::from(s),
        Some(pos) => {
            //s.replace(".$", &format!(".{}", i))
            let mut parts = s.split('.').map(|s| String::from(s)).collect::<Vec<_>>();
            match parts.iter().position(|s| *s=="$") {
                Some(i) => {
                    // TODO is format!() really the best way to convert
                    // a usize to a string?
                    parts[i] = format!("{}", pos);
                    parts.join(".")
                },
                None => {
                    parts.join(".")
                },
            }
        },
    }
}

#[derive(Debug)]
pub struct Projection {
    mode: ProjectionMode,
    paths: Vec<String>,
    ops: Vec<(String, ProjectionOperator)>,
    id: Option<bool>,
}

impl Projection {
    fn is_explicit_include(v: &bson::Value) -> bool {
        match v {
            &bson::Value::BBoolean(b) => b == true,
            &bson::Value::BInt32(n) => n != 0,
            &bson::Value::BInt64(n) => n != 0,
            &bson::Value::BDouble(n) => n != 0.0,
            _ => false,
        }
    }

    fn is_explicit_exclude(v: &bson::Value) -> bool {
        match v {
            &bson::Value::BBoolean(b) => b == false,
            &bson::Value::BInt32(n) => n == 0,
            &bson::Value::BInt64(n) => n == 0,
            &bson::Value::BDouble(n) => n == 0.0,
            _ => false,
        }
    }

    fn has_position_operator(s: &str) -> Result<bool> {
        let parts = s.split('.').collect::<Vec<_>>();
        let len_parts = parts.len();
        let mut posops = parts.into_iter().enumerate().filter(|&(_,s)| s == "$").collect::<Vec<_>>();
        if posops.len() == 0 {
            Ok(false)
        } else if posops.len() > 1 {
            Err(Error::Misc(format!("invalid projection: only one position operator allowed: {:?}", s)))
        } else {
            let (i,_) = posops.remove(0);
            if i == len_parts - 1 {
                Ok(true)
            } else {
                Err(Error::Misc(format!("invalid projection: position operator must appear at the end of the path: {:?}", s)))
            }
        }
    }

    pub fn parse(proj: bson::Document) -> Result<Projection> {
        //println!("parsing projection: {:?}", proj);
        let pairs = proj.pairs;

        let (paths, pairs, maybe_mode) = {
            let (excludes, pairs): (Vec<_>, Vec<_>) = pairs.into_iter().partition(|&(ref k, ref v)| k != "_id" && Self::is_explicit_exclude(v));
            let (includes, pairs): (Vec<_>, Vec<_>) = pairs.into_iter().partition(|&(ref k, ref v)| k != "_id" && Self::is_explicit_include(v));
            let (paths, maybe_mode) = 
                if includes.len() > 0 {
                    if excludes.len() > 0 {
                        return Err(Error::Misc(format!("invalid projection: cannot have both includes and excludes {:?}, {:?}", includes, excludes)));
                    } else {
                        (includes, Some(ProjectionMode::Include))
                    }
                } else if excludes.len() > 0 {
                    (excludes, Some(ProjectionMode::Exclude))
                } else {
                    // we have no explicit includes or excludes.
                    // the two empty vecs are the same.  pick one.
                    (includes, None)
                };
            (paths, pairs, maybe_mode)
        };

        let (id, pairs): (Vec<_>, Vec<_>) = pairs.into_iter().partition(|&(ref k, _)| k == "_id");
        let (ops, pairs): (Vec<_>, Vec<_>) = pairs.into_iter().partition(|&(_, ref v)| 
                                         match v {
                                             &bson::Value::BDocument(ref bd) => {
                                                 bd.len() == 1 && bd.pairs[0].0.starts_with("$")
                                             },
                                             _ => false,
                                         }
                                        );
        if pairs.len() > 0 {
            return Err(Error::Misc(format!("invalid stuff in projection: {:?}", pairs)));
        }

        let paths = paths.into_iter().map(|(k,_)| k).collect::<Vec<_>>();
        let posop = {
            fn fetch_paths(a: Vec<bool>, paths: &Vec<String>) -> Vec<String> {
                a
                .into_iter()
                .enumerate()
                .filter_map(|(i,b)| 
                            if b {
                                Some(paths[i].clone())
                            } else {
                                None
                            }
                            )
                .collect::<Vec<_>>()
            }

            let paths_with_posop = try!(paths
                                        .iter()
                                        .map(|p| Self::has_position_operator(p))
                                        .collect::<Result<Vec<_>>>());
            let mut paths_with_posop = fetch_paths(paths_with_posop, &paths);
            if paths_with_posop.len() > 0 {
                match maybe_mode {
                    Some(ProjectionMode::Exclude) => {
                        return Err(Error::Misc(format!("projection posop not allowed in exclude: {:?}", paths)));
                    },
                    _ => {
                        // okay
                    },
                }
            }
            let ops_with_posop = try!(ops
                                        .iter()
                                        .map(|&(ref p,_)| Self::has_position_operator(p))
                                        .collect::<Result<Vec<_>>>());
            let ops_paths = ops.iter().map(|&(ref p,_)| p.clone()).collect::<Vec<_>>();
            let mut ops_with_posop = fetch_paths(ops_with_posop, &ops_paths);
            paths_with_posop.append(&mut ops_with_posop);
            let r =
                if paths_with_posop.len() > 1 {
                    return Err(Error::Misc(format!("only one posop allowed")));
                } else {
                    match paths_with_posop.pop() {
                        None => None,
                        Some(s) => {
                            Some(String::from(s))
                        },
                    }
                };
            r
        };
        // TODO now check posop against matcher query paths

        let id = id.into_iter().map(|(_,v)| v).collect::<Vec<_>>();
        assert!(id.len() <= 1);
        let id = {
            let mut id = id;
            match id.pop() {
                None => None,
                Some(v) => {
                    Some(try!(v.to_bool()))
                },
            }
        };

        let ops = try!(ops.into_iter()
            .map(|(k,d)|
                 match d {
                    bson::Value::BDocument(mut bd) => {
                        let (op, arg) = bd.pairs.remove(0);
                        let op =
                            match op.as_str() {
                                "$meta" => {
                                    let arg = try!(arg.into_string());
                                    if arg.as_str() == "textScore" {
                                        Ok(ProjectionOperator::MetaTextScore)
                                    } else {
                                        Err(Error::Misc(format!("invalid projection op $meta keyword: {:?}", arg)))
                                    }
                                },
                                "$slice" => {
                                    match arg {
                                        bson::Value::BInt32(_) 
                                        | bson::Value::BInt64(_) 
                                        | bson::Value::BDouble(_) 
                                        => {
                                            let n = try!(arg.numeric_to_i32());
                                            Ok(ProjectionOperator::Slice1(n))
                                        },
                                        bson::Value::BArray(ba) => {
                                            if ba.len() == 2 {
                                                let n0 = try!(ba.items[0].numeric_to_i32());
                                                let n1 = try!(ba.items[1].numeric_to_i32());
                                                if n1 < 0 {
                                                    Err(Error::Misc(format!("invalid arg to projection op $slice: {:?}", ba)))
                                                } else {
                                                    Ok(ProjectionOperator::Slice2(n0, n1 as usize))
                                                }
                                            } else {
                                                Err(Error::Misc(format!("invalid arg to projection op $slice: {:?}", ba)))
                                            }
                                        },
                                        _ => {
                                            Err(Error::Misc(format!("invalid arg to projection op $slice: {:?}", arg)))
                                        },
                                    }
                                },
                                "$elemMatch" => {
                                    let m = try!(matcher::parse_query(try!(arg.into_document())));
                                    Ok(ProjectionOperator::ElemMatch(m))
                                },
                                _ => Err(Error::Misc(format!("invalid projection op: {:?}", op)))
                            };
                        let op = try!(op);
                        Ok((k,op))
                    },
                    _ => {
                        // because we already checked this above
                        unreachable!();
                    },
                 }
            )
            .collect::<Result<Vec<_>>>());

        let mode = 
            match maybe_mode {
                Some(m) => m,
                None => {
                    match id {
                        Some(true) => {
                            // TODO what if ops is not empty?
                            ProjectionMode::Include
                        },
                        Some(false) => {
                            // TODO what if ops is not empty?
                            ProjectionMode::Exclude
                        },
                        None => {
                            //return Err(Error::Misc(format!("TODO what projection mode to use? id={:?} ops={:?}", id, ops)));
                            // TODO what mode to use?

                            // TODO maybe we should leave the projection object with mode None and let the
                            // later code decide how to handle that.  but the projection code
                            // needs to know whether to start with an empty document or the incoming
                            // document.  it's one or the other.

                            // TODO actual question is whether the code to make this decision should live
                            // here, during parsing, or later, during the actual projection.

                            // mongo's rules for deciding whether to use exclude mode or include mode seem
                            // inconsistent for cases where there are no explicit includes or excludes.
                            // elemMatchProjection.js has one test where a projection has only a $slice,
                            // and another test where the projection has only an $elemMatch, and these
                            // two cases end up in different modes.  So... what mode to use?

                            ProjectionMode::Exclude
                            //ProjectionMode::Include
                        },
                    }
                },
            };

        let proj = Projection {
            mode: mode,
            paths: paths,
            ops: ops,
            id: id,
        };
        Ok(proj)
    }

    pub fn project(&self, r: Row) -> Result<Row> {
        let Row {
            doc,
            pos,
            score,
        } = r;

        let doc = try!(doc.into_document());
        let original_id = try!(doc.must_get("_id")).clone();

        let mut d;
        match self.mode {
            ProjectionMode::Include => {
                d = bson::Document::new();
                for path in self.paths.iter() {
                    let path = fix_positional(path, pos);

                    // {comments: [{id:0, text:'a'},{id:1, text:'b'},{id:2, text:'c'},{id:3, text:'d'}]}
                    // comments.id should be
                    // {comments: [{id:0},{id:1},{id:2},{id:3}]}
                    // not
                    // {comments.id: [0,1,2,3]}

                    //println!("walk_path: path = {}", &path);
                    //println!("walk_path: doc = {:?}", doc);
                    //println!("walk_path: walk = {:?}", doc.walk_path(&path));
                    //println!("");

                    let walk = doc.walk_path(&path);
                    try!(walk.project(&mut d));
                }
                // we need to include things that are in ops so we can modify them.
                for &(ref path, _) in self.ops.iter() {
                    let path = fix_positional(path, pos);
                    match try!(d.entry(&path)) {
                        bson::Entry::Found(_) => {
                            // something might already be there from the include loop above,
                            // so this is not an error in this case, and we do not overwrite.
                        },
                        bson::Entry::Absent(e) => {
                            // TODO is hack_like_find_path() what we want here?
                            // do we NEED the synthesized array behavior here?
                            let v = doc.walk_path(&path).hack_like_find_path();
                            try!(e.insert(v));
                        },
                    }
                }
            },
            ProjectionMode::Exclude => {
                d = doc;
                for path in self.paths.iter() {
                    d.exclude_path(&path);
                }
            },
        }

        for &(ref path, ref op) in self.ops.iter() {
            //println!("op: {:?}", op);
            match op {
                &ProjectionOperator::Slice1(n) => {
                    match try!(d.entry(&path)) {
                        bson::Entry::Found(mut e) => {
                            match e.get_mut() {
                                &mut bson::Value::BArray(ref mut ba) => {
                                    if n > 0 {
                                        let n = n as usize;
                                        if ba.len() > n {
                                            ba.items.truncate(n);
                                        }
                                    } else {
                                        let n = -n;
                                        let n = n as usize;
                                        if ba.len() > n {
                                            ba.items.reverse();
                                            ba.items.truncate(n);
                                            ba.items.reverse();
                                        }
                                    }
                                },
                                v => {
                                    return Err(Error::Misc(format!("projection $slice.1 got a non-array: {:?}", v)));
                                },
                            }
                        },
                        bson::Entry::Absent(_) => {
                            // test slice1.js thinks this should not be an error
                            // return Err(Error::Misc(format!("projection $slice.1 got an absent")));
                        },
                    }
                },
                &ProjectionOperator::Slice2(skip,limit) => {
                    match try!(d.entry(&path)) {
                        bson::Entry::Found(mut e) => {
                            match e.get_mut() {
                                &mut bson::Value::BArray(ref mut ba) => {
                                    if skip >= 0 {
                                        let skip = skip as usize;
                                        //println!("before slice2: {:?}", ba.items);
                                        if skip >= ba.items.len() {
                                            ba.items.clear();
                                        } else {
                                            for _ in 0 .. skip {
                                                ba.items.remove(0);
                                            }
                                            //println!("after slice2 skip: {:?}", ba.items);
                                            if limit < ba.items.len() {
                                                ba.items.truncate(limit);
                                            }
                                        }
                                        //println!("after slice2: {:?}", ba.items);
                                    } else {
                                        let skip = -skip;
                                        let skip = skip as usize;
                                        if skip >= ba.items.len() {
                                            ba.items.clear();
                                        } else {
                                            for _ in 0 .. ba.items.len() - skip {
                                                ba.items.remove(0);
                                            }
                                            if limit < ba.items.len() {
                                                ba.items.truncate(limit);
                                            }
                                        }
                                    }
                                },
                                _ => {
                                    return Err(Error::Misc(format!("projection $slice.2 got a non-array")));
                                },
                            }
                        },
                        bson::Entry::Absent(_) => {
                            return Err(Error::Misc(format!("projection $slice.2 got an absent")));
                        },
                    }
                },
                &ProjectionOperator::MetaTextScore => {
                    let score = score.unwrap_or(0.0);
                    match try!(d.entry(&path)) {
                        bson::Entry::Found(e) => {
                            // jstests/core/fts_projection.js says yes, clobber
                            e.replace(bson::Value::BDouble(score));
                        },
                        bson::Entry::Absent(e) => {
                            try!(e.insert(bson::Value::BDouble(score)));
                        },
                    }
                },
                &ProjectionOperator::ElemMatch(ref m) => {
                    match try!(d.entry(&path)) {
                        bson::Entry::Found(mut e) => {
                            match e.get_mut() {
                                &mut bson::Value::BArray(ref mut ba) => {
                                    return Err(Error::Misc(format!("TODO projection $elemMatch")));
                                },
                                _ => {
                                    return Err(Error::Misc(format!("projection $elemMatch got a non-array")));
                                },
                            }
                        },
                        bson::Entry::Absent(_) => {
                            return Err(Error::Misc(format!("projection $elemMatch got an absent")));
                        },
                    }
                },
            }
        }

        match (self.id, self.mode) {
            (Some(true), ProjectionMode::Include) => {
                match try!(d.entry("_id")) {
                    bson::Entry::Found(_) => {
                        return Err(Error::Misc(format!("projection error: _id should not be here yet")));
                    },
                    bson::Entry::Absent(e) => {
                        try!(e.insert(original_id));
                    },
                }
                let _ = try!(d.validate_id());
            },
            (Some(false), ProjectionMode::Include) => {
                match try!(d.entry("_id")) {
                    bson::Entry::Found(_) => {
                        return Err(Error::Misc(format!("projection error: _id should not be here yet")));
                    },
                    bson::Entry::Absent(e) => {
                        // not there.  good.
                    },
                }
            },
            (Some(true), ProjectionMode::Exclude) => {
                match try!(d.entry("_id")) {
                    bson::Entry::Found(_) => {
                        // already there.  as it should be.
                    },
                    bson::Entry::Absent(_) => {
                        return Err(Error::Misc(format!("projection error: _id should be here")));
                    },
                }
            },
            (Some(false), ProjectionMode::Exclude) => {
                match try!(d.entry("_id")) {
                    bson::Entry::Found(e) => {
                        e.remove();
                    },
                    bson::Entry::Absent(_) => {
                        return Err(Error::Misc(format!("projection error: _id should be here")));
                    },
                }
            },
            (None, ProjectionMode::Include) => {
                // if a projection for the _id was not specified, and if the mode
                // is Include, the _id gets included.
                match try!(d.entry("_id")) {
                    bson::Entry::Found(_) => {
                        return Err(Error::Misc(format!("projection error: _id should not be here yet")));
                    },
                    bson::Entry::Absent(e) => {
                        try!(e.insert(original_id));
                    },
                }
                let _ = try!(d.validate_id());
            },
            (None, ProjectionMode::Exclude) => {
                match try!(d.entry("_id")) {
                    bson::Entry::Found(e) => {
                        // TODO the id is here, as we expect, but should it be?
                    },
                    bson::Entry::Absent(_) => {
                        return Err(Error::Misc(format!("projection error: _id should be here")));
                    },
                }
            },
        }

        let result = Row {
            doc: d.into_value(),
            pos: pos,
            score: score,
        };
        Ok(result)
    }

}

pub fn cmp_row(d: &Row, lit: &Row) -> Ordering {
    matcher::cmp(&d.doc, &lit.doc)
}

#[derive(Debug)]
enum UpdateOp {
    Min(String, bson::Value),
    Max(String, bson::Value),
    Inc(String, bson::Value),
    Mul(String, bson::Value),
    Set(String, bson::Value),
    PullValue(String, bson::Value),
    SetOnInsert(String, bson::Value),
    BitAnd(String, i64),
    BitOr(String, i64),
    BitXor(String, i64),
    Unset(String),
    Date(String),
    TimeStamp(String),
    Rename(String, String),
    AddToSet(String, bson::Array),
    PullAll(String, bson::Array),
    Push(String, bson::Array, Option<i32>, Option<bson::Value>, Option<usize>),
    PullQuery(String, matcher::QueryDoc),
    PullPredicates(String, Vec<matcher::Pred>),
    Pop(String, i32),
}

pub trait StorageBase {
    // TODO maybe these two should return an iterator
    // TODO maybe these two should accept params to limit the rows returned
    fn list_collections(&self) -> Result<Vec<CollectionInfo>>;
    fn list_indexes(&self) -> Result<Vec<IndexInfo>>;

    fn get_reader_collection_scan(&self, db: &str, coll: &str) -> Result<Box<Iterator<Item=Result<Row>> + 'static>>;
    // TODO QueryKey in text_index_scan should be an option
    fn get_reader_text_index_scan(&self, ndx: &IndexInfo, eq: QueryKey, terms: Vec<TextQueryTerm>) -> Result<Box<Iterator<Item=Result<Row>> + 'static>>;
    fn get_reader_regular_index_scan(&self, ndx: &IndexInfo, bounds: QueryBounds) -> Result<Box<Iterator<Item=Result<Row>> + 'static>>;
}

pub trait StorageCollectionWriter {
    fn insert(&mut self, v: &bson::Document) -> Result<()>;
    fn update(&mut self, v: &bson::Document) -> Result<()>;
    fn delete(&mut self, v: &bson::Value) -> Result<bool>;
}

// TODO should implement Drop = rollback
// TODO do we need to declare that StorageWriter must implement Drop ?
// TODO or is it enough that the actual implementation of this trait impl Drop?

pub trait StorageReader : StorageBase {
    fn into_reader_collection_scan(self: Box<Self>, db: &str, coll: &str) -> Result<Box<Iterator<Item=Result<Row>> + 'static>>;
    fn into_reader_text_index_scan(&self, ndx: &IndexInfo, eq: QueryKey, terms: Vec<TextQueryTerm>) -> Result<Box<Iterator<Item=Result<Row>> + 'static>>;
    fn into_reader_regular_index_scan(&self, ndx: &IndexInfo, bounds: QueryBounds) -> Result<Box<Iterator<Item=Result<Row>> + 'static>>;
}

pub trait StorageWriter : StorageBase {
    fn create_collection(&self, db: &str, coll: &str, options: bson::Document) -> Result<bool>;
    fn rename_collection(&self, old_name: &str, new_name: &str, drop_target: bool) -> Result<bool>;
    fn clear_collection(&self, db: &str, coll: &str) -> Result<bool>;
    fn drop_collection(&self, db: &str, coll: &str) -> Result<bool>;

    fn create_indexes(&self, Vec<IndexInfo>) -> Result<Vec<bool>>;
    fn drop_index(&self, db: &str, coll: &str, name: &str) -> Result<bool>;

    fn drop_database(&self, db: &str) -> Result<bool>;

    fn get_collection_writer(&self, db: &str, coll: &str) -> Result<Box<StorageCollectionWriter + 'static>>;

    fn commit(self: Box<Self>) -> Result<()>;
    fn rollback(self: Box<Self>) -> Result<()>;

}

// TODO I'm not sure this type is worth the trouble anymore.
// maybe we should go back to just keeping a bool that specifies
// whether we need to negate or not.
#[derive(PartialEq,Copy,Clone)]
pub enum IndexType {
    Forward,
    Backward,
    Geo2d,
}

fn decode_index_type(v: &bson::Value) -> Result<IndexType> {
    match v {
        &bson::Value::BInt32(n) => if n<0 { Ok(IndexType::Backward) } else { Ok(IndexType::Forward) },
        &bson::Value::BInt64(n) => if n<0 { Ok(IndexType::Backward) } else { Ok(IndexType::Forward) },
        &bson::Value::BDouble(n) => if n<0.0 { Ok(IndexType::Backward) } else { Ok(IndexType::Forward) },
        &bson::Value::BString(ref s) => 
            if s == "2d" { 
                Ok(IndexType::Geo2d)
            } else {
                Err(Error::Misc(format!("invalid index type: {:?}", v)))
            },
        _ => Err(Error::Misc(format!("invalid index type: {:?}", v)))
    }
}

// TODO this is basically iter().position()
fn slice_find(pairs: &[(String, bson::Value)], s: &str) -> Option<usize> {
    for i in 0 .. pairs.len() {
        match pairs[i].1 {
            bson::Value::BString(ref t) => {
                if t == s {
                    return Some(i);
                }
            },
            _ => (),
        }
    }
    None
}

// this function gets the index spec (its keys) into a form that
// is simplified and cleaned up.
//
// if there are text indexes in index.spec, they are removed
//
// all text indexes, including any that were in index.spec, and
// anything implied by options.weights, are stored in a new Map<string,int>
// called weights.
//
// any non-text indexes that appeared in spec AFTER any text
// indexes are discarded.  I *think* Mongo keeps these, but only
// for the purpose of grabbing their data later when used as a covering
// index, which we're ignoring.
//
pub fn get_normalized_spec(info: &IndexInfo) -> Result<(Vec<(String,IndexType)>,Option<HashMap<String,i32>>)> {
    //println!("info: {:?}", info);
    let first_text = slice_find(&info.spec.pairs, "text");
    //println!("first_text: {:?}", first_text);
    let w1 = info.options.get("weights");
    match (first_text, w1) {
        (None, None) => {
            let decoded = try!(info.spec.pairs.iter().map(|&(ref k, ref v)| Ok((k.clone(), try!(decode_index_type(v))))).collect::<Result<Vec<(String,IndexType)>>>());
            //printfn "no text index: %A" decoded
            Ok((decoded, None))
        },
        _ => {
            let (scalar_keys, text_keys) = 
                match first_text {
                    Some(i) => {
                        let scalar_keys = &info.spec.pairs[0 .. i];
                        // note that any non-text index after the first text index is getting discarded
                        let mut text_keys = Vec::new();
                        for t in &info.spec.pairs {
                            match t.1 {
                                bson::Value::BString(ref s) => {
                                    if s == "text" {
                                        text_keys.push(t.0.clone());
                                    }
                                },
                                _ => (),
                            }
                        }
                        (scalar_keys, text_keys)
                    },
                    None => (&info.spec.pairs[0 ..], Vec::new())
                };
            //println!("scalar_keys: {:?}", scalar_keys);
            //println!("text_keys: {:?}", text_keys);
            let mut weights = HashMap::new();
            match w1 {
                Some(&bson::Value::BDocument(ref bd)) => {
                    for t in &bd.pairs {
                        let n = 
                            match &t.1 {
                                &bson::Value::BInt32(n) => n,
                                &bson::Value::BInt64(n) => n as i32,
                                &bson::Value::BDouble(n) => n as i32,
                                _ => panic!("weight must be numeric")
                            };
                        weights.insert(t.0.clone(), n);
                    }
                },
                Some(_) => {
                    return Err(Error::Misc(format!("weights must be a document")));
                },
                None => (),
            };
            for k in text_keys {
                if !weights.contains_key(&k) {
                    weights.insert(String::from(k), 1);
                }
            }
            // TODO if the wildcard is present, remove everything else?
            //println!("scalar_keys: {:?}", scalar_keys);
            let decoded = try!(scalar_keys.iter().map(|&(ref k, ref v)| Ok((k.clone(), try!(decode_index_type(v))))).collect::<Result<Vec<(String,IndexType)>>>());
            let r = Ok((decoded, Some(weights)));
            //printfn "%A" r
            r
        }
    }
}


pub trait StorageConnection {
    fn begin_write(&self) -> Result<Box<StorageWriter + 'static>>;
    fn begin_read(&self) -> Result<Box<StorageReader + 'static>>;
    // TODO note that only one tx can exist at a time per connection.

    // but it would be possible to have multiple iterators at the same time.
    // as long as they live within the same tx.
}

pub struct Connection {
    conn: Box<StorageConnection>,
}

pub trait ConnectionFactory {
    fn open(&self) -> Result<Connection>;
    fn clone_for_new_thread(&self) -> Box<ConnectionFactory + Send>;
}

// TODO this type was created so that all the projection operations
// could be done in the order they appeared, which we are not really
// doing.  So now the parser is constructing these values and then
// we unconstruct them later.  Messy.
#[derive(Debug)]
enum AggProj {
    Include,
    Expr(Expr),
}

impl AggProj {
    fn is_include(&self) -> bool {
        match self {
            &AggProj::Include => true,
            &AggProj::Expr(_) => false,
        }
    }
}

#[derive(Debug)]
enum GroupAccum {
    Sum(Expr),
    Avg(Expr),
    First(Expr),
    Last(Expr),
    Max(Expr),
    Min(Expr),
    Push(Expr),
    AddToSet(Expr),
}

#[derive(Debug)]
enum AggOp {
    Skip(i32),
    Limit(i32),
    Sort(bson::Value),
    Out(String),
    Unwind(String),
    Match(matcher::QueryDoc),
    Project(Vec<(String,AggProj)>),
    Group(Expr, Vec<(String, GroupAccum)>),
    GeoNear(bson::Value),
    Redact(Expr),
}

#[derive(Debug)]
enum Expr {
    Var(String),
    Literal(bson::Value),

    AllElementsTrue(Box<Expr>),
    AnyElementTrue(Box<Expr>),
    DayOfMonth(Box<Expr>),
    DayOfWeek(Box<Expr>),
    DayOfYear(Box<Expr>),
    Hour(Box<Expr>),
    Millisecond(Box<Expr>),
    Minute(Box<Expr>),
    Month(Box<Expr>),
    Not(Box<Expr>),
    Second(Box<Expr>),
    Size(Box<Expr>),
    ToLower(Box<Expr>),
    ToUpper(Box<Expr>),
    Week(Box<Expr>),
    Year(Box<Expr>),

    Cmp(Box<(Expr, Expr)>),
    Eq(Box<(Expr, Expr)>),
    Ne(Box<(Expr, Expr)>),
    Gt(Box<(Expr, Expr)>),
    Lt(Box<(Expr, Expr)>),
    Gte(Box<(Expr, Expr)>),
    Lte(Box<(Expr, Expr)>),
    Subtract(Box<(Expr, Expr)>),
    Divide(Box<(Expr, Expr)>),
    Mod(Box<(Expr, Expr)>),
    IfNull(Box<(Expr, Expr)>),
    SetDifference(Box<(Expr, Expr)>),
    SetIsSubset(Box<(Expr, Expr)>),
    StrCaseCmp(Box<(Expr, Expr)>),

    Substr(Box<(Expr, Expr, Expr)>),
    Cond(Box<(Expr, Expr, Expr)>),

    And(Vec<Expr>),
    Or(Vec<Expr>),
    Add(Vec<Expr>),
    Multiply(Vec<Expr>),
    Concat(Vec<Expr>),
    SetEquals(Vec<Expr>),
    SetIntersection(Vec<Expr>),
    SetUnion(Vec<Expr>),

    Let(Vec<(String, Expr)>, Box<Expr>),
    Map(Box<(Expr, String, Expr)>),
    DateToString(String, Box<Expr>),

    // TODO meta
}

impl Connection {
    pub fn new(conn: Box<StorageConnection>) -> Connection {
        Connection {
            conn: conn,
        }
    }

    // TODO maybe this could/should take ownership of ops?
    fn apply_update_ops(doc: &mut bson::Document, ops: &Vec<UpdateOp>, is_upsert: bool, pos: Option<usize>) -> Result<()> {
        for op in ops {
            match op {
                &UpdateOp::Min(ref path, ref v) => {
                    let path = fix_positional(path, pos);
                    match try!(doc.entry(&path)) {
                        bson::Entry::Found(e) => {
                            let c = matcher::cmp(v, e.get());
                            if c == Ordering::Less {
                                e.replace(v.clone());
                            }
                        },
                        bson::Entry::Absent(e) => {
                            // when the key isn't found, this works like $set
                            try!(e.insert(v.clone()));
                        },
                    }
                },
                &UpdateOp::Max(ref path, ref v) => {
                    let path = fix_positional(path, pos);
                    match try!(doc.entry(&path)) {
                        bson::Entry::Found(e) => {
                            let c = matcher::cmp(v, e.get());
                            if c == Ordering::Greater {
                                e.replace(v.clone());
                            }
                        },
                        bson::Entry::Absent(e) => {
                            // when the key isn't found, this works like $set
                            try!(e.insert(v.clone()));
                        },
                    }
                },
                &UpdateOp::Inc(ref path, ref v) => {
                    let path = fix_positional(path, pos);
                    if !v.is_numeric() {
                        return Err(Error::Misc(format!("argument to $inc must be numeric")));
                    }
                    match try!(doc.entry(&path)) {
                        bson::Entry::Found(mut e) => {
                            if try!(v.numeric_to_i64()) != 0 {
                                match e.get_mut() {
                                    &mut bson::Value::BInt32(ref mut n) => {
                                        *n = *n + try!(v.numeric_to_i32())
                                    },
                                    &mut bson::Value::BInt64(ref mut n) => {
                                        *n = *n + try!(v.numeric_to_i64())
                                    },
                                    &mut bson::Value::BDouble(ref mut n) => {
                                        *n = *n + try!(v.numeric_to_f64())
                                    },
                                    _ => return Err(Error::Misc(format!("can't $inc to this type"))),
                                }
                            }
                        },
                        bson::Entry::Absent(e) => {
                            // when the key isn't found, this works like $set
                            try!(e.insert(v.clone()));
                        },
                    }
                },
                &UpdateOp::Mul(ref path, ref v) => {
                    let path = fix_positional(path, pos);
                    if !v.is_numeric() {
                        return Err(Error::Misc(format!("argument to $mul must be numeric")));
                    }
                    match try!(doc.entry(&path)) {
                        bson::Entry::Found(mut e) => {
                            match e.get_mut() {
                                &mut bson::Value::BInt32(ref mut n) => {
                                    *n = *n * try!(v.numeric_to_i32())
                                },
                                &mut bson::Value::BInt64(ref mut n) => {
                                    *n = *n * try!(v.numeric_to_i64())
                                },
                                &mut bson::Value::BDouble(ref mut n) => {
                                    *n = *n * try!(v.numeric_to_f64())
                                },
                                _ => return Err(Error::Misc(format!("can't $mul to this type"))),
                            }
                        },
                        bson::Entry::Absent(e) => {
                            // when the key isn't found, this works like $set
                            try!(e.insert(v.clone()));
                        },
                    }
                },
                &UpdateOp::Set(ref path, ref v) => {
                    println!("at {}:{}", file!(), line!());
                    let path = fix_positional(path, pos);
                    println!("at {}:{}", file!(), line!());
                    try!(doc.set_path(&path, v.clone()));
                    println!("at {}:{}", file!(), line!());
                },
                &UpdateOp::Push(ref path, ref each, slice, ref sort, position) => {
                    let path = fix_positional(path, pos);
                    match try!(doc.entry(&path)) {
                        bson::Entry::Found(mut e) => {
                            match e.get_mut() {
                                &mut bson::Value::BArray(ref mut a) => {
                                    let pos = match position {
                                        Some(n) => n,
                                        None => a.len(),
                                    };
                                    for i in 0 .. each.len() {
                                        let v = each.items[each.len() - i - 1].clone();
                                        a.items.insert(pos, v);
                                    }
                                    match sort {
                                        &None => (),
                                        &Some(ref ord) => {
                                            try!(Self::do_sort_docs(&mut a.items, ord));
                                        },
                                    }
                                    match slice {
                                        None => (),
                                        Some(n) => {
                                            if n == 0 {
                                                a.items.clear();
                                            } else if n > 0 {
                                                let len = std::cmp::min(a.items.len(), n as usize);
                                                a.items.truncate(len);
                                            } else {
                                                let n = -n;
                                                let len = std::cmp::min(a.items.len(), n as usize);
                                                a.items.reverse();
                                                a.items.truncate(len);
                                                a.items.reverse();
                                            }
                                        },
                                    }
                                },
                                _ => return Err(Error::Misc(format!("$push not an array: {}", path))),
                            }
                        },
                        bson::Entry::Absent(e) => {
                            try!(e.insert(each.clone().into_value()));
                        },
                    }
                },
                &UpdateOp::PullValue(ref path, ref v) => {
                    let path = fix_positional(path, pos);
                    match try!(doc.entry(&path)) {
                        bson::Entry::Found(mut e) => {
                            match e.get_mut() {
                                &mut bson::Value::BArray(ref mut a) => {
                                    a.items.retain(|va| va != v)
                                },
                                _ => return Err(Error::Misc(format!("$pull not an array: {}", path))),
                            }
                        },
                        bson::Entry::Absent(_) => {
                            return Err(Error::Misc(format!("$pull path not found: {}", path)));
                        },
                    }
                },
                &UpdateOp::SetOnInsert(ref path, ref v) => {
                    if is_upsert {
                        let path = fix_positional(path, pos);
                        try!(doc.set_path(&path, v.clone()));
                    }
                },
                &UpdateOp::BitAnd(ref path, v) => {
                    let path = fix_positional(path, pos);
                    match try!(doc.entry(&path)) {
                        bson::Entry::Found(mut e) => {
                            match e.get_mut() {
                                &mut bson::Value::BInt32(ref mut n) => {
                                    *n = *n & (v as i32)
                                },
                                &mut bson::Value::BInt64(ref mut n) => {
                                    *n = *n & v
                                },
                                _ => return Err(Error::Misc(format!("can't $bit.and to this type"))),
                            }
                        },
                        bson::Entry::Absent(_) => {
                            return Err(Error::Misc(format!("$bit.and path not found")));
                        },
                    }
                },
                &UpdateOp::BitOr(ref path, v) => {
                    let path = fix_positional(path, pos);
                    match try!(doc.entry(&path)) {
                        bson::Entry::Found(mut e) => {
                            match e.get_mut() {
                                &mut bson::Value::BInt32(ref mut n) => {
                                    *n = *n | (v as i32)
                                },
                                &mut bson::Value::BInt64(ref mut n) => {
                                    *n = *n | v
                                },
                                _ => return Err(Error::Misc(format!("can't $bit.or to this type"))),
                            }
                        },
                        bson::Entry::Absent(_) => {
                            return Err(Error::Misc(format!("$bit.or path not found")));
                        },
                    }
                },
                &UpdateOp::BitXor(ref path, v) => {
                    let path = fix_positional(path, pos);
                    match try!(doc.entry(&path)) {
                        bson::Entry::Found(mut e) => {
                            match e.get_mut() {
                                &mut bson::Value::BInt32(ref mut n) => {
                                    *n = *n ^ (v as i32)
                                },
                                &mut bson::Value::BInt64(ref mut n) => {
                                    *n = *n ^ v
                                },
                                _ => return Err(Error::Misc(format!("can't $bit.xor to this type"))),
                            }
                        },
                        bson::Entry::Absent(_) => {
                            return Err(Error::Misc(format!("$bit.xor path not found")));
                        },
                    }
                },
                &UpdateOp::Unset(ref path) => {
                    let path = fix_positional(path, pos);
                    let _ = try!(doc.unset_path(&path));
                },
                &UpdateOp::Rename(ref old_path, ref new_path) => {
                    // TODO so we use the same positional op for both paths?
                    let old_path = fix_positional(old_path, pos);
                    let new_path = fix_positional(new_path, pos);
                    if doc.dives_into_any_array(&old_path) {
                        return Err(Error::Misc(format!("UpdateOp::Rename, array path: {}", old_path)));
                    }
                    if doc.dives_into_any_array(&new_path) {
                        return Err(Error::Misc(format!("UpdateOp::Rename, array path: {}", new_path)));
                    }
                    match try!(doc.unset_path(&old_path)) {
                        Some(v) => {
                            try!(doc.set_path(&new_path, v));
                        },
                        None => {
                            //return Err(Error::Misc(format!("UpdateOp::Rename, path not found: {}", old_path)));
                        },
                    }
                },
                &UpdateOp::Date(ref path) => {
                    let path = fix_positional(path, pos);
                    let ts = time::get_time();
                    let v = bson::Value::BDateTime(ts.sec * 1000);
                    try!(doc.set_path(&path, v));
                },
                &UpdateOp::TimeStamp(ref path) => {
                    // TODO a timestamp is a little different, actually
                    let path = fix_positional(path, pos);
                    let ts = time::get_time();
                    let v = bson::Value::BTimeStamp(ts.sec * 1000);
                    try!(doc.set_path(&path, v));
                },
                &UpdateOp::AddToSet(ref path, ref vals) => {
                    let path = fix_positional(path, pos);
                    for v in vals.items.iter() {
                        match try!(doc.entry(&path)) {
                            bson::Entry::Found(mut e) => {
                                match e.get_mut() {
                                    &mut bson::Value::BArray(ref mut a) => {
                                        if !a.items.iter().any(|va| va == v) {
                                            a.push(v.clone());
                                        }
                                    },
                                    _ => return Err(Error::Misc(format!("$addToSet not an array: {}", path))),
                                }
                            },
                            bson::Entry::Absent(e) => {
                                let mut ba = bson::Array::new();
                                ba.push(v.clone());
                                try!(e.insert(ba.into_value()));
                            },
                        }
                    }
                },
                &UpdateOp::PullAll(ref path, ref vals) => {
                    let path = fix_positional(path, pos);
                    for v in vals.items.iter() {
                        match try!(doc.entry(&path)) {
                            bson::Entry::Found(mut e) => {
                                match e.get_mut() {
                                    &mut bson::Value::BArray(ref mut a) => {
                                        a.items.retain(|va| va != v)
                                    },
                                    _ => return Err(Error::Misc(format!("$pull not an array: {}", path))),
                                }
                            },
                            bson::Entry::Absent(_) => {
                                return Err(Error::Misc(format!("$pull path not found: {}", path)));
                            },
                        }
                    }
                },
                &UpdateOp::PullQuery(ref path, ref m) => {
                    let path = fix_positional(path, pos);
                    match try!(doc.entry(&path)) {
                        bson::Entry::Found(mut e) => {
                            match e.get_mut() {
                                &mut bson::Value::BArray(ref mut a) => {
                                    a.items.retain(|va| !matcher::match_query(m, &va).0)
                                },
                                _ => return Err(Error::Misc(format!("$pull not an array: {}", path))),
                            }
                        },
                        bson::Entry::Absent(_) => {
                            return Err(Error::Misc(format!("$pull path not found: {}", path)));
                        },
                    }
                },
                &UpdateOp::PullPredicates(ref path, ref preds) => {
                    let path = fix_positional(path, pos);
                    match try!(doc.entry(&path)) {
                        bson::Entry::Found(mut e) => {
                            match e.get_mut() {
                                &mut bson::Value::BArray(ref mut a) => {
                                    a.items.retain(|va| !matcher::match_pred_list(preds, &va).0)
                                },
                                _ => return Err(Error::Misc(format!("$pull not an array: {}", path))),
                            }
                        },
                        bson::Entry::Absent(_) => {
                            return Err(Error::Misc(format!("$pull path not found: {}", path)));
                        },
                    }
                },
                &UpdateOp::Pop(ref path, i) => {
                    let path = fix_positional(path, pos);
                    match try!(doc.entry(&path)) {
                        bson::Entry::Found(mut e) => {
                            match e.get_mut() {
                                &mut bson::Value::BArray(ref mut a) => {
                                    if a.len() == 0 {
                                        // do nothing
                                    } else {
                                        if i > 0 {
                                            a.items.pop();
                                        } else {
                                            a.items.remove(0);
                                        }
                                    }
                                },
                                _ => return Err(Error::Misc(format!("$pop not an array: {}", path))),
                            }
                        },
                        bson::Entry::Absent(_) => {
                            // do nothing
                        },
                    }
                },
            }
        }
        Ok(())
    }

    // this function is used to check two paths to see if one of them
    // is a prefix of the other, which, for example, in the case of two
    // update operators, is a conflict.
    //
    // the check cannot be done correctly with simple string.StartsWith()
    // calls, because x.fu is not actually a prefix of x.fubar, since x
    // can happily have both fu and fubar as a key.

    fn check_prefix(a: &str, b: &str) -> bool {
        let a_parts = a.split('.').collect::<Vec<_>>();
        let b_parts = b.split('.').collect::<Vec<_>>();
        let len = std::cmp::min(a_parts.len(), b_parts.len());
        let a_sub = &a_parts[0 .. len];
        let b_sub = &b_parts[0 .. len];
        a_sub == b_sub
    }

    fn any_prefix(a: &[&str], s: &str) -> bool {
        a.iter().any(|a| Self::check_prefix(a,s))
    }

    fn check_update_doc_for_conflicts(ops: &Vec<UpdateOp>) -> Result<()> {
        let mut a = vec![];
        for op in ops {
            match op {
                &UpdateOp::Min(ref path, _)
                | &UpdateOp::Max(ref path, _)
                | &UpdateOp::Inc(ref path, _)
                | &UpdateOp::Mul(ref path, _)
                | &UpdateOp::Set(ref path, _)
                | &UpdateOp::Push(ref path, _, _, _, _)
                | &UpdateOp::PullValue(ref path, _)
                | &UpdateOp::SetOnInsert(ref path, _)
                | &UpdateOp::BitAnd(ref path, _)
                | &UpdateOp::BitOr(ref path, _)
                | &UpdateOp::BitXor(ref path, _)
                | &UpdateOp::Unset(ref path)
                | &UpdateOp::Date(ref path)
                | &UpdateOp::TimeStamp(ref path)
                | &UpdateOp::AddToSet(ref path, _)
                | &UpdateOp::PullAll(ref path, _)
                | &UpdateOp::PullQuery(ref path, _)
                | &UpdateOp::PullPredicates(ref path, _)
                | &UpdateOp::Pop(ref path, _)
                    => {
                    if Self::any_prefix(&a, path) {
                        return Err(Error::Misc(format!("update op path conflict: {}", path)));
                    }
                    a.push(path);
                },
                &UpdateOp::Rename(ref old_path, ref new_path) => {
                    if Self::any_prefix(&a, old_path) {
                        return Err(Error::Misc(format!("update op path conflict: {}", old_path)));
                    }
                    a.push(old_path);
                    if Self::any_prefix(&a, new_path) {
                        return Err(Error::Misc(format!("update op path conflict: {}", new_path)));
                    }
                    a.push(new_path);
                },
            }
        }
        Ok(())
    }

    fn any_part_starts_with_dollar_sign(s: &str) -> bool {
        let parts = s.split('.').collect::<Vec<_>>();
        parts.into_iter().any(|s| s.starts_with("$"))
    }

    fn parse_update_doc(d: bson::Document) -> Result<Vec<UpdateOp>> {
        // TODO benefit of map/collect over for loop is that it forces something for every item
        let mut result = vec![];
        for (k, v) in d.pairs {
            // TODO consider v.into_document() up here instead of in every case below
            match k.as_str() {
                "$min" => {
                    for (path, v) in try!(v.into_document()).pairs {
                        result.push(UpdateOp::Min(path, v));
                    }
                },
                "$max" => {
                    for (path, v) in try!(v.into_document()).pairs {
                        result.push(UpdateOp::Max(path, v));
                    }
                },
                "$inc" => {
                    for (path, v) in try!(v.into_document()).pairs {
                        result.push(UpdateOp::Inc(path, v));
                    }
                },
                "$mul" => {
                    for (path, v) in try!(v.into_document()).pairs {
                        result.push(UpdateOp::Mul(path, v));
                    }
                },
                "$set" => {
                    for (path, v) in try!(v.into_document()).pairs {
                        result.push(UpdateOp::Set(path, v));
                    }
                },
                "$unset" => {
                    for (path, _) in try!(v.into_document()).pairs {
                        result.push(UpdateOp::Unset(path));
                    }
                },
                "$setOnInsert" => {
                    for (path, v) in try!(v.into_document()).pairs {
                        result.push(UpdateOp::SetOnInsert(path,v));
                    }
                },
                "$pop" => {
                    for (path, v) in try!(v.into_document()).pairs {
                        result.push(UpdateOp::Pop(path,try!(v.numeric_to_i32())));
                    }
                },
                "$pushAll" => {
                    for (path, v) in try!(v.into_document()).pairs {
                        result.push(UpdateOp::Push(path, try!(v.into_array()), None, None, None));
                    }
                },
                "$push" => {
                    for (path, v) in try!(v.into_document()).pairs {
                        match v {
                            bson::Value::BDocument(mut bd) => {
                                fn extract(bd: &mut bson::Document, s: &str) -> Option<bson::Value> {
                                    match bd.pairs.iter().position(|&(ref k, _)| k == s) {
                                        Some(i) => {
                                            let (_,v) = bd.pairs.remove(i);
                                            Some(v)
                                        },
                                        None => {
                                            None
                                        },
                                    }
                                }

                                match extract(&mut bd, "$each") {
                                    Some(v) => {
                                        let a = try!(v.into_array());
                                        let slice = match extract(&mut bd, "$slice") {
                                            Some(v) => Some(try!(v.numeric_to_i32())),
                                            None => None,
                                        };
                                        let sort = match extract(&mut bd, "$sort") {
                                            Some(v) => {
                                                if v.is_numeric() {
                                                    let n = try!(v.numeric_to_i32());
                                                    Some(bson::Value::BInt32(n))
                                                } else if v.is_document() {
                                                    Some(v)
                                                } else {
                                                    return Err(Error::Misc(format!("$sort must be number or document")));
                                                }
                                            },
                                            None => None,
                                        };
                                        let position = match extract(&mut bd, "$position") {
                                            Some(v) => Some(try!(v.numeric_to_i32()) as usize),
                                            None => None,
                                        };
                                        result.push(UpdateOp::Push(path, a, slice, sort, position));
                                    },
                                    None => {
                                        // TODO dry
                                        let mut a = bson::Array::new();
                                        a.push(bd.into_value());
                                        result.push(UpdateOp::Push(path, a, None, None, None));
                                    },
                                }
                            },
                            _ => {
                                // TODO dry
                                let mut a = bson::Array::new();
                                a.push(v);
                                result.push(UpdateOp::Push(path, a, None, None, None));
                            },
                        }
                    }
                },
                "$pull" => {
                    for (path, v) in try!(v.into_document()).pairs {
                        match v {
                            bson::Value::BDocument(bd) => {
                                if matcher::doc_is_query_doc(&bd) {
                                    let qd = try!(matcher::parse_query(bd));
                                    result.push(UpdateOp::PullQuery(path, qd));
                                } else {
                                    let preds = try!(matcher::parse_pred_list(bd.pairs));
                                    result.push(UpdateOp::PullPredicates(path, preds));
                                }
                            },
                            _ => {
                                result.push(UpdateOp::PullValue(path, v));
                            },
                        }
                    }
                },
                "$pullAll" => {
                    for (path, v) in try!(v.into_document()).pairs {
                        result.push(UpdateOp::PullAll(path, try!(v.into_array())));
                    }
                },
                "$rename" => {
                    for (old_path, v) in try!(v.into_document()).pairs {
                        let new_path = try!(v.into_string());
                        // TODO even mongo has problems in this area.  it seems to have
                        // different rules for key/path names in its rename code than in
                        // other places.

                        // TODO it may be problematic that all these checks here are being
                        // done before the positional operator is applied to the paths.

                        if old_path.as_str() == "" {
                            // TODO why not?
                            return Err(Error::Misc(format!("empty key cannot be renamed")));
                        }
                        if new_path.as_str() == "" {
                            // TODO why not?
                            return Err(Error::Misc(format!("cannot rename to empty key")));
                        }
                        if old_path.as_str() == "_id" {
                            return Err(Error::Misc(format!("_id cannot be renamed")));
                        }
                        // TODO what about rename something to _id?
                        if old_path.starts_with(".") {
                            return Err(Error::Misc(format!("bad path")));
                        }
                        if new_path.starts_with(".") {
                            return Err(Error::Misc(format!("bad path")));
                        }
                        if old_path.ends_with(".") {
                            return Err(Error::Misc(format!("bad path")));
                        }
                        if new_path.ends_with(".") {
                            return Err(Error::Misc(format!("bad path")));
                        }
                        if old_path == new_path {
                            return Err(Error::Misc(format!("cannot rename to same path")));
                        }
                        if old_path.starts_with(new_path.as_str()) {
                            // TODO use correct prefix func
                            return Err(Error::Misc(format!("overlap rename path")));
                        }
                        if new_path.starts_with(old_path.as_str()) {
                            // TODO use correct prefix func
                            return Err(Error::Misc(format!("overlap rename path")));
                        }
                        if Self::any_part_starts_with_dollar_sign(&old_path) {
                            return Err(Error::Misc(format!("key starts with dollar sign: {}", old_path)));
                        }
                        if Self::any_part_starts_with_dollar_sign(&new_path) {
                            return Err(Error::Misc(format!("key starts with dollar sign: {}", new_path)));
                        }
                        result.push(UpdateOp::Rename(old_path, new_path));
                    }
                },
                "$bit" => {
                    for (path, v) in try!(v.into_document()).pairs {
                        match v {
                            bson::Value::BDocument(bd) => {
                                if bd.len() != 1 {
                                    return Err(Error::Misc(format!("invalid $bit: {:?}", bd)));
                                }
                                let num = try!(bd.pairs[0].1.integer_to_i64());
                                match bd.pairs[0].0.as_str() {
                                    "and" => result.push(UpdateOp::BitAnd(path, num)),
                                    "or" => result.push(UpdateOp::BitOr(path, num)),
                                    "xor" => result.push(UpdateOp::BitXor(path, num)),
                                    _ => return Err(Error::Misc(format!("invalid $bit op: {:?}", k))),
                                }
                            },
                            _ => {
                                return Err(Error::Misc(format!("invalid $bit: {:?}", v)));
                            },
                        }
                    }
                },
                "$currentDate" => {
                    for (path, v) in try!(v.into_document()).pairs {
                        match v {
                            bson::Value::BBoolean(true) => {
                                result.push(UpdateOp::Date(path));
                            },
                            bson::Value::BDocument(bd) => {
                                if bd.len() != 1 {
                                    return Err(Error::Misc(format!("invalid $currentDate: {:?}", bd)));
                                }
                                if bd.pairs[0].0.as_str() != "$type" {
                                    return Err(Error::Misc(format!("invalid $currentDate: {:?}", bd)));
                                }
                                match try!(bd.pairs[0].1.as_str()) {
                                    "date" => result.push(UpdateOp::Date(path)),
                                    "timestamp" => result.push(UpdateOp::TimeStamp(path)),
                                    s => return Err(Error::Misc(format!("invalid $currentDate: {:?}", s))),
                                }
                            },
                            _ => {
                                return Err(Error::Misc(format!("invalid $currentDate: {:?}", v)));
                            },
                        }
                    }
                },
                "$addToSet" => {
                    for (path, v) in try!(v.into_document()).pairs {
                        let each = 
                            match v {
                                bson::Value::BDocument(mut bd) => {
                                    if bd.len() == 1 &&  bd.pairs[0].0 == "$each" {
                                        let (_,v) = bd.pairs.remove(0);
                                        try!(v.into_array())
                                    } else {
                                        // TODO dry
                                        let mut a = bson::Array::new();
                                        a.push(bd.into_value());
                                        a
                                    }
                                },
                                _ => {
                                    // TODO dry
                                    let mut a = bson::Array::new();
                                    a.push(v);
                                    a
                                },
                            };
                        result.push(UpdateOp::AddToSet(path, each));
                    }
                },
                _ => return Err(Error::Misc(format!("unknown update op: {}", k))),
            }
        }
        try!(Self::check_update_doc_for_conflicts(&result));
        Ok(result)
    }

    fn into_collection_reader(r: Box<StorageReader>, db: &str, coll: &str, plan: Option<QueryPlan>) -> Result<Box<Iterator<Item=Result<Row>>>> {
        match plan {
            Some(plan) => {
                match plan {
                    QueryPlan::Text(ndx, eq, terms) => {
                        let rdr = try!(r.into_reader_text_index_scan(ndx, eq, terms));
                        return Ok(rdr);
                    },
                    QueryPlan::Regular(ndx, bounds) => {
                        let rdr = try!(r.into_reader_regular_index_scan(ndx, bounds));
                        return Ok(rdr);
                    },
                }
            },
            None => {
                let rdr = try!(r.into_reader_collection_scan(db, coll));
                return Ok(rdr);
            },
        };
    }

    fn get_collection_reader_r(r: &StorageReader, db: &str, coll: &str, plan: Option<QueryPlan>) -> Result<Box<Iterator<Item=Result<Row>>>> {
        match plan {
            Some(plan) => {
                match plan {
                    QueryPlan::Text(ndx, eq, terms) => {
                        let rdr = try!(r.get_reader_text_index_scan(ndx, eq, terms));
                        return Ok(rdr);
                    },
                    QueryPlan::Regular(ndx, bounds) => {
                        let rdr = try!(r.get_reader_regular_index_scan(ndx, bounds));
                        return Ok(rdr);
                    },
                }
            },
            None => {
                let rdr = try!(r.get_reader_collection_scan(db, coll));
                return Ok(rdr);
            },
        };
    }

    fn get_collection_reader_w(w: &StorageWriter, db: &str, coll: &str, plan: Option<QueryPlan>) -> Result<Box<Iterator<Item=Result<Row>>>> {
        match plan {
            Some(plan) => {
                match plan {
                    QueryPlan::Text(ndx, eq, terms) => {
                        let rdr = try!(w.get_reader_text_index_scan(ndx, eq, terms));
                        return Ok(rdr);
                    },
                    QueryPlan::Regular(ndx, bounds) => {
                        let rdr = try!(w.get_reader_regular_index_scan(ndx, bounds));
                        return Ok(rdr);
                    },
                }
            },
            None => {
                let rdr = try!(w.get_reader_collection_scan(db, coll));
                return Ok(rdr);
            },
        };
    }

    fn get_one_match(db: &str, coll: &str, w: &StorageWriter, m: &matcher::QueryDoc, orderby: Option<&bson::Value>) -> Result<Option<Row>> {
        // TODO dry
                    println!("at {}:{}", file!(), line!());
        let indexes = try!(w.list_indexes()).into_iter().filter(
            |ndx| ndx.db == db && ndx.coll == coll
            ).collect::<Vec<_>>();
        //println!("indexes: {:?}", indexes);
                    println!("at {}:{}", file!(), line!());
        let plan = try!(Self::choose_index(&indexes, &m, None));
                    println!("at {}:{}", file!(), line!());
        //println!("plan: {:?}", plan);
        let seq: Box<Iterator<Item=Result<Row>>> = try!(Self::get_collection_reader_w(w, db, coll, plan));
        // TODO we shadow-let here because the type from seq_match_ref() doesn't match the original
        // type because of its explicit lifetime.
        let mut seq = Self::seq_match_ref(seq, &m);
                    println!("at {}:{}", file!(), line!());
        match orderby {
            None => (),
            Some(orderby) => {
                    println!("at {}:{}", file!(), line!());
                let mut a = try!(seq.collect::<Result<Vec<_>>>());
                    println!("at {}:{}", file!(), line!());
                try!(Self::do_sort(&mut a, orderby));
                    println!("at {}:{}", file!(), line!());
                seq = box a.into_iter().map(|d| Ok(d));
                    println!("at {}:{}", file!(), line!());
            },
        }
                    println!("at {}:{}", file!(), line!());
        match seq.next() {
            None => {
                    println!("at {}:{}", file!(), line!());
                Ok(None)
            },
            Some(Ok(v)) => {
                    println!("at {}:{}", file!(), line!());
                Ok(Some(v))
            },
            Some(Err(e)) => {
                    println!("at {}:{}", file!(), line!());
                Err(e)
            },
        }
    }

    fn build_upsert_with_update_operators(m: &matcher::QueryDoc, ops: &Vec<UpdateOp>) -> Result<bson::Document> {
        let a = matcher::get_eqs(m);
        let mut doc = bson::Document::new();
        for (path, v) in a {
            try!(doc.set_path(&path, v.clone()));
        }
        // save the id so we can make sure it didn't change
        let id1 =
            match doc.get("_id") {
                Some(v) => Some(v.clone()),
                None => None,
            };
        try!(Self::apply_update_ops(&mut doc, ops, true, None));
        // make sure the id didn't change
        match id1 {
            Some(id1) => {
                match doc.get("_id") {
                    Some(v) => {
                        if id1 != *v {
                            return Err(Error::Misc(String::from("cannot change _id")));
                        }
                    },
                    None => {
                    },
                }
            },
            None => {
            },
        }
        doc.ensure_id();
        Ok(doc)
    }

    fn build_simple_upsert(id_q: Option<bson::Value>, u: &mut bson::Document) -> Result<()> {
        // TODO I hate this code.  I want to match on u.get("_id"), but the
        // borrow survives the whole match, which means I can't modify it
        // in the None case.  This approach requires me to re-do the get()
        // just below, with an unwrap().  Ugly.  Use Entry?
        if u.get("_id").is_some() {
            match id_q {
                Some(id_q) => {
                    if id_q != *u.get("_id").unwrap() {
                        Err(Error::Misc(String::from("can't change _id")))
                    } else {
                        Ok(())
                    }
                },
                None => {
                    Ok(())
                },
            }
        } else {
            match id_q {
                Some(id_q) => {
                    u.set("_id", id_q);
                    Ok(())
                },
                None => {
                    u.set_objectid("_id", misc::new_bson_objectid_rand());
                    Ok(())
                },
            }
        }
    }

    fn validate_for_storage(d: &mut bson::Document) -> Result<bson::Value> {
        let id = try!(d.validate_id());
        try!(d.validate_keys(0));
        try!(d.validate_depth(0, 100));
        Ok(id)
    }

    fn id_changed(d1: &bson::Document, d2: &bson::Document) -> Result<bool> {
        let id1 = try!(d1.must_get("_id"));
        let id2 = try!(d2.must_get("_id"));
        let b = id1 != id2;
        Ok(b)
    }

    pub fn update(&self, db: &str, coll: &str, updates: &mut Vec<bson::Document>, factory: &ConnectionFactory) -> Result<Vec<Result<(i32, i32, Option<bson::Value>)>>> {
        let mut results = Vec::new();
        {
            // rconn needs to be opened here.  if we try to open it later,
            // just before the case where we actually need it, we can't,
            // because the process of opening a connection tries to create
            // the tables if they don't exist, which means it asks for a
            // write lock, which it can't get, because we're holding it
            // ourself.
            let rconn = try!(factory.open());
            let writer = try!(self.conn.begin_write());
            {
                let mut collwriter = try!(writer.get_collection_writer(db, coll));
                // TODO why does this closure need to be mut?
                let mut one_update_or_upsert = |upd: &mut bson::Document| -> Result<(i32, i32, Option<bson::Value>)> {
                    //println!("in closure: {:?}", upd);
                    let q = try!(upd.must_remove_document("q"));
                    let u = try!(upd.must_remove_document("u"));
                    let multi = try!(upd.must_remove_bool("multi"));
                    let upsert = try!(upd.must_remove_bool("upsert"));
                    // rescue _id from q if possible
                    let q_id =
                        match q.get("_id") {
                            Some(id) => Some(id.clone()),
                            None => None,
                        };
                    let m = try!(matcher::parse_query(q));
                    println!("at {}:{}", file!(), line!());
                    let has_update_operators = u.pairs.iter().any(|&(ref k, _)| k.starts_with("$"));
                    if has_update_operators {
                    println!("at {}:{}", file!(), line!());
                        let ops = try!(Self::parse_update_doc(u));
                    println!("at {}:{}", file!(), line!());
                        //println!("ops: {:?}", ops);
                        let (count_matches, count_modified) =
                            if multi {
                                let reader = try!(rconn.conn.begin_read());
                                // TODO DRY
                                let indexes = try!(reader.list_indexes()).into_iter().filter(
                                    |ndx| ndx.db == db && ndx.coll == coll
                                    ).collect::<Vec<_>>();
                                let plan = try!(Self::choose_index(&indexes, &m, None));
                                let seq: Box<Iterator<Item=Result<Row>>> = try!(Self::into_collection_reader(reader, db, coll, plan));
                                // TODO we shadow-let here because the type from seq_match_ref() doesn't match the original
                                // type because of its explicit lifetime.
                                let seq = Self::seq_match_ref(seq, &m);
                                let mut mods = 0;
                                let mut matches = 0;
                                for rr in seq {
                                    let row = try!(rr);
                                    //println!("matching row for update: {:?}", row);
                                    let old_doc = try!(row.doc.into_document());
                                    let mut new_doc = old_doc.clone();
                                    try!(Self::apply_update_ops(&mut new_doc, &ops, false, row.pos));
                                    if try!(Self::id_changed(&old_doc, &new_doc)) {
                                        return Err(Error::Misc(String::from("cannot change _id")));
                                    }
                                    matches = matches + 1;
                                    if new_doc != old_doc {
                                        let id = try!(Self::validate_for_storage(&mut new_doc));
                                        try!(collwriter.update(&new_doc));
                                        mods = mods + 1;
                                    }
                                }
                                (matches, mods)
                            } else {
                    println!("at {}:{}", file!(), line!());
                                match try!(Self::get_one_match(db, coll, &*writer, &m, None)) {
                                    Some(row) => {
                    println!("at {}:{}", file!(), line!());
                                        //println!("row found for update: {:?}", row);
                                        let old_doc = try!(row.doc.into_document());
                                        let mut new_doc = old_doc.clone();
                    println!("at {}:{}", file!(), line!());
                                        try!(Self::apply_update_ops(&mut new_doc, &ops, false, row.pos));
                    println!("at {}:{}", file!(), line!());
                                        if try!(Self::id_changed(&old_doc, &new_doc)) {
                                            return Err(Error::Misc(String::from("cannot change _id")));
                                        }
                    println!("at {}:{}", file!(), line!());
                                        if new_doc != old_doc {
                    println!("at {}:{}", file!(), line!());
                                            let id = try!(Self::validate_for_storage(&mut new_doc));
                    println!("at {}:{}", file!(), line!());
                                            try!(collwriter.update(&new_doc));
                    println!("at {}:{}", file!(), line!());
                                            (1, 1)
                                        } else {
                                            (1, 0)
                                        }
                                    },
                                    None => {
                    println!("at {}:{}", file!(), line!());
                                        //println!("get_one_match found nothing");
                                        (0, 0)
                                    },
                                }
                            };
                    println!("at {}:{}", file!(), line!());
                        if count_matches == 0 {
                    println!("at {}:{}", file!(), line!());
                            if upsert {
                                let mut doc = try!(Self::build_upsert_with_update_operators(&m, &ops));
                                let id = try!(Self::validate_for_storage(&mut doc));
                                try!(collwriter.insert(&doc));
                                Ok((0,0,Some(id)))
                            } else {
                    println!("at {}:{}", file!(), line!());
                                Ok((0,0,None))
                            }
                        } else {
                            Ok((count_matches, count_modified, None))
                        }
                    } else {
                        // TODO what happens if the update document has no update operators
                        // but it has keys which are dotted?
                        if multi {
                            return Err(Error::Misc(String::from("multi update requires $ update operators")));
                        }
                        match try!(Self::get_one_match(db, coll, &*writer, &m, None)) {
                            Some(row) => {
                                let old_doc = try!(row.doc.into_document());
                                let old_id = try!(old_doc.get("_id").ok_or(Error::Misc(String::from("_id not found in doc being updated")))).clone();
                                let mut new_doc = u;
                                let new_id = {
                                    match new_doc.get("_id") {
                                        Some(new_id) => Some(new_id.clone()),
                                        None => None,
                                    }
                                };
                                match new_id {
                                    Some(new_id) => {
                                        if old_id != new_id {
                                            return Err(Error::Misc(format!("Cannot change _id")));
                                        }
                                    },
                                    None => {
                                        new_doc.set("_id", old_id);
                                    },
                                }
                                if new_doc != old_doc {
                                    let id = try!(Self::validate_for_storage(&mut new_doc));
                                    try!(collwriter.update(&new_doc));
                                    Ok((1,1,None))
                                } else {
                                    Ok((1,0,None))
                                }
                            },
                            None => {
                                if upsert {
                                    let mut new_doc = u;
                                    try!(Self::build_simple_upsert(q_id, &mut new_doc));
                                    // TODO what if this doesn't have an id yet?
                                    let id = try!(Self::validate_for_storage(&mut new_doc));
                                    try!(collwriter.insert(&new_doc));
                                    Ok((0, 0, Some(id)))
                                } else {
                                    Ok((0, 0, None))
                                }
                            },
                        }
                    }
                };

                    println!("at {}:{}", file!(), line!());
                for upd in updates {
                    println!("at {}:{}", file!(), line!());
                    let r = one_update_or_upsert(upd);
                    println!("at {}:{}", file!(), line!());
                    results.push(r);
                    println!("at {}:{}", file!(), line!());
                }
                    println!("at {}:{}", file!(), line!());
            }
                    println!("at {}:{}", file!(), line!());
            try!(writer.commit());
                    println!("at {}:{}", file!(), line!());
        }
        Ok(results)
    }

    pub fn find_and_modify(&self, db: &str, coll: &str, filter: Option<bson::Value>, sort: Option<bson::Value>, remove: Option<bson::Value>, update: Option<bson::Value>, new: bool, upsert: bool) -> Result<(bool,Option<Error>,bool,Option<bson::Value>,Option<bson::Document>)> {
        let (m, q_id) = {
            let (q, id) =
                match filter {
                    Some(q) => {
                        let q = try!(q.into_document());
                        let id =
                            match q.get("_id") {
                                Some(id) => Some(id.clone()),
                                None => None,
                            };
                        (q,id)
                    },
                    None => {
                        (bson::Document::new(), None)
                    },
                };
            let m = try!(matcher::parse_query(q));
            (m, id)
        };
        let writer = try!(self.conn.begin_write());
        let mut collwriter = try!(writer.get_collection_writer(db, coll));
        let found = match Self::get_one_match(db, coll, &*writer, &m, sort.as_ref()) {
            Ok(v) => v,
            Err(e) => return Ok((false,Some(e),false,None,None)),
        };
        //println!("find_and_modify: {:?}", found);
        let was_found = found.is_some();
        let inner = || -> Result<(bool,Option<bson::Value>,Option<bson::Document>)> {
        if remove.is_some() && upsert {
            return Err(Error::Misc(String::from("find_and_modify: invalid. no upsert with remove.")))
        }
        let mut changed = false;
        let mut upserted = None;
        let mut result = None;
        match (update, remove, found) {
            (Some(_), Some(_), _) => {
                return Err(Error::Misc(String::from("find_and_modify: invalid. both update and remove.")))
            },
            (None, None, _) => {
                return Err(Error::Misc(String::from("find_and_modify: invalid. neither update nor remove.")))
            },
            (Some(u), None, Some(row)) => {
                // update, found
                let u = try!(u.into_document());
                let has_update_operators = u.pairs.iter().any(|&(ref k, _)| k.starts_with("$"));
                if has_update_operators {
                    let ops = try!(Self::parse_update_doc(u));
                    let old_doc = try!(row.doc.into_document());
                    let mut new_doc = old_doc.clone();
                    try!(Self::apply_update_ops(&mut new_doc, &ops, false, row.pos));
                    if try!(Self::id_changed(&old_doc, &new_doc)) {
                        return Err(Error::Misc(String::from("cannot change _id")));
                    }
                    if old_doc != new_doc {
                        let id = try!(Self::validate_for_storage(&mut new_doc));
                        try!(collwriter.update(&new_doc));
                        changed = true;
                    }
                    result = 
                        if new {
                            Some(new_doc)
                        } else {
                            Some(old_doc)
                        };
                } else {
                    let old_doc = try!(row.doc.into_document());
                    let old_id = try!(old_doc.get("_id").ok_or(Error::Misc(String::from("_id not found in doc being updated")))).clone();
                    match u.get("_id") {
                        Some(new_id) => {
                            if old_id != *new_id {
                                return Err(Error::Misc(String::from("cannot change _id")));
                            }
                        },
                        None => {
                        },
                    }
                    let mut new_doc = u;
                    new_doc.set("_id", old_id);
                    if old_doc != new_doc {
                        let id = try!(Self::validate_for_storage(&mut new_doc));
                        try!(collwriter.update(&new_doc));
                        changed = true;
                    }
                    result = 
                        if new {
                            Some(new_doc)
                        } else {
                            Some(old_doc)
                        };
                }
            },
            (Some(u), None, None) => {
                // update, not found, maybe upsert
                let u = try!(u.into_document());
                if upsert {
                    let has_update_operators = u.pairs.iter().any(|&(ref k, _)| k.starts_with("$"));
                    if has_update_operators {
                        let ops = try!(Self::parse_update_doc(u));
                        let mut new_doc = try!(Self::build_upsert_with_update_operators(&m, &ops));
                        let id = try!(Self::validate_for_storage(&mut new_doc));
                        try!(collwriter.insert(&new_doc));
                         changed = true;
                        upserted = Some(id);
                        if new {
                            result = Some(new_doc);
                        }
                    } else {
                        let mut new_doc = u;
                        try!(Self::build_simple_upsert(q_id, &mut new_doc));
                        let id = try!(Self::validate_for_storage(&mut new_doc));
                        try!(collwriter.insert(&new_doc));
                        changed = true;
                        upserted = Some(id);
                        if new {
                            result = Some(new_doc);
                        }
                    }
                }
            },
            (None, Some(_), Some(row)) => {
                // remove, found
                let old_doc = try!(row.doc.into_document());
                {
                    let id = try!(old_doc.get("_id").ok_or(Error::Misc(String::from("_id not found in doc being updated"))));
                    if try!(collwriter.delete(id)) {
                        changed = true;
                    }
                }
                result = Some(old_doc);
            },
            (None, Some(_), None) => {
                // remove, not found, nothing to do
            },
        }
        try!(writer.commit());
        Ok((changed, upserted, result))
        };

        match inner() {
            Ok((changed,upserted,result)) => {
                Ok((was_found, None, changed, upserted, result))
            },
            Err(e) => {
                Ok((was_found, Some(e), false, None, None))
            },
        }
    }

    pub fn insert_seq(&self, db: &str, coll: &str, docs: Box<Iterator<Item=Result<Row>>>) -> Result<Vec<Result<()>>> {
        let mut results = Vec::new();
        {
            let writer = try!(self.conn.begin_write());
            {
                let mut collwriter = try!(writer.get_collection_writer(db, coll));
                for rr in docs {
                    match rr {
                        Ok(row) => {
                            let doc = row.doc;
                            match doc.into_document() {
                                Ok(mut doc) => {
                                    doc.ensure_id();
                                    let id = try!(Self::validate_for_storage(&mut doc));
                                    let r = collwriter.insert(&doc);
                                    results.push(r);
                                },
                                Err(e) => {
                                    results.push(Err(wrap_err(e)));
                                },
                            }
                        },
                        Err(e) => {
                            results.push(Err(e));
                        },
                    }
                }
            }
            try!(writer.commit());
        }
        Ok(results)
    }

    pub fn insert(&self, db: &str, coll: &str, docs: &mut Vec<bson::Document>) -> Result<Vec<Result<()>>> {
        // make sure every doc has an _id
        for d in docs.iter_mut() {
            d.ensure_id();
        }
        let mut results = Vec::new();
        {
            let writer = try!(self.conn.begin_write());
            {
                let mut collwriter = try!(writer.get_collection_writer(db, coll));
                for mut doc in docs {
                    let id = try!(Self::validate_for_storage(&mut doc));
                    let r = collwriter.insert(doc);
                    results.push(r);
                }
            }
            try!(writer.commit());
        }
        Ok(results)
    }

    pub fn list_all_collections(&self) -> Result<Vec<CollectionInfo>> {
        let reader = try!(self.conn.begin_read());
        let v = try!(reader.list_collections());
        Ok(v)
    }

    pub fn list_collections(&self, db: &str, filter: Option<bson::Document>) -> Result<Box<Iterator<Item=Result<Row>> + 'static>> {
        let results = try!(self.list_all_collections());
        let mut seq: Box<Iterator<Item=Result<Row>>>;
        seq = box {
            // we need db to get captured by this closure which outlives
            // this function, so we create String from it and use a move
            // closure.

            let db = String::from(db);
            let results = results.into_iter().filter_map(
                move |c| {
                    if db.as_str() == c.db {
                        let mut doc = bson::Document::new();
                        doc.set_string("name", c.coll);
                        doc.set_document("options", c.options);
                        let r = Row {
                            doc: bson::Value::BDocument(doc),
                            pos: None,
                            score: None,
                        };
                        Some(Ok(r))
                    } else {
                        None
                    }
                }
                );
            results
        };

        match filter {
            Some(q) => {
                let m = try!(matcher::parse_query(q));
                seq = Self::seq_match(seq, m);
                Ok(box seq)
            },
            None => {
                Ok(box seq)
            },
        }

    }

    pub fn list_indexes(&self) -> Result<Vec<IndexInfo>> {
        let reader = try!(self.conn.begin_read());
        let v = try!(reader.list_indexes());
        Ok(v)
    }

    fn try_find_index_by_name_or_spec<'a>(indexes: &'a Vec<IndexInfo>, desc: &bson::Value) -> Option<&'a IndexInfo> {
        let mut a =
            match desc {
                &bson::Value::BString(ref s) => {
                    indexes.into_iter().filter(|ndx| ndx.name.as_str() == s.as_str()).collect::<Vec<_>>()
                },
                &bson::Value::BDocument(ref bd) => {
                    indexes.into_iter().filter(|ndx| ndx.spec == *bd).collect::<Vec<_>>()
                },
                _ => panic!("must be name or index spec doc"),
            };
        if a.len() > 1 {
            unreachable!();
        } else {
            a.pop()
        }
    }

    pub fn delete_indexes(&self, db: &str, coll: &str, index: &bson::Value) -> Result<(usize, usize)> {
        let writer = try!(self.conn.begin_write());
        // TODO DRY
        let indexes = try!(writer.list_indexes()).into_iter().filter(
            |ndx| ndx.db == db && ndx.coll == coll
            ).collect::<Vec<_>>();
        let count_before = indexes.len();
        let indexes = 
            if index.is_string() && try!(index.as_str()) == "*" {
                indexes.iter().filter(
                    |ndx| ndx.name != "_id_"
                ).collect::<Vec<_>>()
            } else {
                // TODO we're supposed to disallow delete of _id_, right?
                // TODO if let
                match Self::try_find_index_by_name_or_spec(&indexes, index) {
                    Some(ndx) => vec![ndx],
                    None => vec![],
                }
            };
        let mut count_deleted = 0;
        for ndx in indexes {
            if try!(writer.drop_index(&ndx.db, &ndx.coll, &ndx.name)) {
                count_deleted = count_deleted + 1;
            }
        }
        try!(writer.commit());
        Ok((count_before, count_deleted))
    }

    pub fn create_indexes(&self, indexes: Vec<IndexInfo>) -> Result<Vec<bool>> {
        let writer = try!(self.conn.begin_write());
        let results = try!(writer.create_indexes(indexes));
        try!(writer.commit());
        Ok(results)
    }

    pub fn drop_collection(&self, db: &str, coll: &str) -> Result<bool> {
        let deleted = {
            let writer = try!(self.conn.begin_write());
            let deleted = try!(writer.drop_collection(db, coll));
            try!(writer.commit());
            deleted
        };
        Ok(deleted)
    }

    pub fn clear_collection(&self, db: &str, coll: &str) -> Result<bool> {
        let b = {
            let writer = try!(self.conn.begin_write());
            let b = try!(writer.clear_collection(db, coll));
            try!(writer.commit());
            b
        };
        Ok(b)
    }

    pub fn rename_collection(&self, old_name: &str, new_name: &str, drop_target: bool) -> Result<bool> {
        let done = {
            let writer = try!(self.conn.begin_write());
            let done = try!(writer.rename_collection(old_name, new_name, drop_target));
            try!(writer.commit());
            done
        };
        Ok(done)
    }

    pub fn drop_database(&self, db: &str) -> Result<bool> {
        let deleted = {
            let writer = try!(self.conn.begin_write());
            let deleted = try!(writer.drop_database(db));
            try!(writer.commit());
            deleted
        };
        Ok(deleted)
    }

    pub fn delete(&self, db: &str, coll: &str, items: Vec<bson::Document>) -> Result<usize> {
        let mut count = 0;
        {
            let writer = try!(self.conn.begin_write());
            {
                let mut collwriter = try!(writer.get_collection_writer(db, coll));
                for mut del in items {
                    let q = try!(del.must_remove_document("q"));
                    let limit = del.get("limit");
                    let m = try!(matcher::parse_query(q));
                    let indexes = try!(writer.list_indexes()).into_iter().filter(
                        |ndx| ndx.db == db && ndx.coll == coll
                        ).collect::<Vec<_>>();
                    //println!("indexes: {:?}", indexes);
                    let mut seq = {
                        let plan = try!(Self::choose_index(&indexes, &m, None));
                        //println!("plan: {:?}", plan);
                        // TODO is this safe?  or do we need two-conn isolation like update?
                        let seq: Box<Iterator<Item=Result<Row>>> = try!(Self::get_collection_reader_w(&*writer, db, coll, plan));
                        seq
                    };
                    seq = Self::seq_match(seq, m);
                    for rr in seq {
                        let row = try!(rr);
                        let d = try!(row.doc.into_document());
                        match d.get("_id") {
                            Some(id) => {
                                if try!(collwriter.delete(id)) {
                                    count = count + 1;
                                }
                            },
                            None => {
                                return Err(Error::Misc(String::from("delete: invalid. no _id.")))
                            },
                        }
                    }
                }
            }
            try!(writer.commit());
        }
        Ok(count)
    }

    pub fn create_collection(&self, db: &str, coll: &str, options: bson::Document) -> Result<bool> {
        let writer = try!(self.conn.begin_write());
        let result = try!(writer.create_collection(db, coll, options));
        try!(writer.commit());
        Ok(result)
    }

    fn parse_index_min_max<'m>(m: &'m matcher::QueryDoc) -> Result<Vec<(&'m str, &'m bson::Value)>> {
        let &matcher::QueryDoc::QueryDoc(ref items) = m;
        items.iter().map(
            |it| match it {
                // TODO wish we could pattern match on the vec.
                &matcher::QueryItem::Compare(ref k, ref preds) => {
                    if preds.len() == 1 {
                        match &preds[0] {
                            &matcher::Pred::EQ(ref v) => {
                                Ok((k.as_str(), v))
                            },
                            _ => {
                                Err(Error::Misc(String::from("bad min max")))
                            },
                        }
                    } else {
                        Err(Error::Misc(String::from("bad min max")))
                    }
                },
                _ => {
                    Err(Error::Misc(String::from("bad min max")))
                },
            }
        ).collect::<Result<Vec<(_,_)>>>()
    }

    fn find_compares_eq(m: &matcher::QueryDoc) -> Result<HashMap<&str, &bson::Value>> {
        fn find<'a>(m: &'a matcher::QueryDoc, dest: &mut Vec<(&'a str, &'a bson::Value)>) {
            let &matcher::QueryDoc::QueryDoc(ref a) = m;
            for it in a {
                match it {
                    &matcher::QueryItem::Compare(ref k, ref preds) => {
                        for p in preds {
                            match p {
                                &matcher::Pred::EQ(ref v) => dest.push((k,v)),
                                _ => (),
                            }
                        }
                    },
                    &matcher::QueryItem::AND(ref docs) => {
                        for d in docs {
                            find(d, dest);
                        }
                    },
                    _ => {
                    },
                }
            }
        }

        let mut comps = vec![];
        find(m, &mut comps);

        let mc = misc::group_by_key(comps);

        // query for x=3 && x=4 is legit in mongo.
        // it can match a doc where x is an array that contains both 3 and 4
        // {x:[1,2,3,4,5]}
        // in terms of choosing an index to use, we can pick either one.
        // the index will give us, for example, "all documents where x is 3",
        // which will include the one above, and the matcher will then also
        // make sure that the 4 is there as well.

        let mc = 
            try!(mc.into_iter().map(
                    |(k, mut v)| 
                    if v.len() == 0 {
                        unreachable!();
                    } else if v.len() == 1 {
                        let v = v.pop().expect("len() == 1");
                        Ok((k, v))
                    } else {
                        let count_distinct = {
                            let uniq : HashSet<_> = v.iter().collect();
                            uniq.len()
                        };
                        if count_distinct > 1 {
                            Err(Error::Misc(String::from("conflicting $eq")))
                        } else {
                            let v = v.pop().expect("len() > 0");
                            Ok((k, v))
                        }
                    }
                    ).collect::<Result<HashMap<_,_>>>()
                );

        Ok(mc)
    }

    fn find_compares_ineq(m: &matcher::QueryDoc) -> Result<HashMap<&str, (Option<(OpGt, &bson::Value)>, Option<(OpLt, &bson::Value)>)>> {
        fn find<'a>(m: &'a matcher::QueryDoc, dest: &mut Vec<(&'a str, (OpIneq, &'a bson::Value))>) {
            let &matcher::QueryDoc::QueryDoc(ref a) = m;
            for it in a {
                match it {
                    &matcher::QueryItem::Compare(ref k, ref preds) => {
                        for p in preds {
                            match p {
                                &matcher::Pred::LT(ref v) => dest.push((k, (OpIneq::LT,v))),
                                &matcher::Pred::GT(ref v) => dest.push((k, (OpIneq::GT,v))),
                                &matcher::Pred::LTE(ref v) => dest.push((k, (OpIneq::LTE,v))),
                                &matcher::Pred::GTE(ref v) => dest.push((k, (OpIneq::GTE,v))),
                                _ => (),
                            }
                        }
                    },
                    &matcher::QueryItem::AND(ref docs) => {
                        for d in docs {
                            find(d, dest);
                        }
                    },
                    _ => {
                    },
                }
            }
        }

        fn cmp_gt(t1: &(OpGt, &bson::Value), t2: &(OpGt, &bson::Value)) -> Ordering {
            let c = matcher::cmp(t1.1, t2.1);
            match c {
                Ordering::Less => c,
                Ordering::Greater => c,
                Ordering::Equal => {
                    match (t1.0, t2.0) {
                        (OpGt::GT, OpGt::GT) => Ordering::Equal,
                        (OpGt::GTE, OpGt::GTE) => Ordering::Equal,
                        (OpGt::GT, OpGt::GTE) => Ordering::Less,
                        (OpGt::GTE, OpGt::GT) => Ordering::Greater,
                    }
                },
            }
        }

        fn cmp_lt(t1: &(OpLt, &bson::Value), t2: &(OpLt, &bson::Value)) -> Ordering {
            let c = matcher::cmp(t1.1, t2.1);
            match c {
                Ordering::Less => c,
                Ordering::Greater => c,
                Ordering::Equal => {
                    match (t1.0, t2.0) {
                        (OpLt::LT, OpLt::LT) => Ordering::Equal,
                        (OpLt::LTE, OpLt::LTE) => Ordering::Equal,
                        (OpLt::LT, OpLt::LTE) => Ordering::Less,
                        (OpLt::LTE, OpLt::LT) => Ordering::Greater,
                    }
                },
            }
        }

        fn to_lt(op: OpIneq) -> Option<OpLt> {
            match op {
                OpIneq::LT => Some(OpLt::LT),
                OpIneq::LTE => Some(OpLt::LTE),
                OpIneq::GT => None,
                OpIneq::GTE => None,
            }
        }

        fn to_gt(op: OpIneq) -> Option<OpGt> {
            match op {
                OpIneq::LT => None,
                OpIneq::LTE => None,
                OpIneq::GT => Some(OpGt::GT),
                OpIneq::GTE => Some(OpGt::GTE),
            }
        }

        let mut comps = vec![];
        find(m, &mut comps);

        let mc = misc::group_by_key(comps);

        let mut m2 = HashMap::new();

        for (k, a) in mc {
            let (gt, lt): (Vec<_>, Vec<_>) = a.into_iter().partition(|&(op, _)| op.is_gt());

            let mut gt = 
                gt
                .into_iter()
                // TODO in the following line, since we already partitioned, else/None should be unreachable
                .filter_map(|(op, v)| if let Some(gt) = to_gt(op) { Some((gt, v)) } else { None })
                .collect::<Vec<_>>();
            let gt = {
                gt.sort_by(cmp_gt);
                misc::remove_first_if_exists(&mut gt)
            };
            
            let mut lt = 
                lt
                .into_iter()
                // TODO in the following line, since we already partitioned, else/None should be unreachable
                .filter_map(|(op, v)| if let Some(lt) = to_lt(op) { Some((lt, v)) } else { None })
                .collect::<Vec<_>>();
            let lt = {
                lt.sort_by(cmp_lt);
                misc::remove_first_if_exists(&mut lt)
            };
            
            // Note that if we wanted to disallow > and < the same value, this is
            // where we would do it, but mongo allows this according to test case
            // find8.js

            // TODO issue here of diving into elemMatch or not:
            // TODO we cannot do a query with both bounds unless the two
            // comparisons came from the same elemMatch.
            // for example:
            // {x:{$gt:2,$lt:5}}
            // this query has to match the following document:
            // {x:[1,7]}
            // because the array x has
            // something that matches x>2 (the 7)
            // AND
            // something that matches x<5 (the 1)
            // even those two somethings are not the same thing,
            // they came from the same x.
            // we can choose x>2 or x<5 as our index, but we can't choose both.
            // unless elemMatch.
            //
            // note that if we have to satisfy two gt on x, such as:
            // x>5
            // x>9
            // it doesn't really matter which one we choose for the index.
            // both will be correct.  but choosing x>9 will result in us reviewing
            // fewer documents.

            // suppose there are three records:
            // {a: [1,2]}
            // {a: [1,2,6]}
            // {a: [1,4,6]}
            // this query:
            // find( {a:{$gte:3, $lte: 5}} )
            // cannot use either comparison for the bounds of the index
            // arrayfind3.js

            // TODO can't do this unless same elemMatch: m2.insert(k, (gt, lt));
            if gt.is_some() {
                m2.insert(k, (gt, None));
            } else {
                m2.insert(k, (None, lt));
            }
        }


        Ok(m2)
    }

    fn fit_index_to_query<'a,'i>(
        ndx: &'i IndexInfo, 
        comps: &Comps<'a>,
        text_query: &Option<Vec<TextQueryTerm>>
        ) 
        -> Result<Option<QueryPlan<'a,'i>>> 
    {
        let (scalar_keys, weights) = try!(get_normalized_spec(ndx));
        if weights.is_none() && text_query.is_some() {
            // if there is a textQuery but this is not a text index, give up now
            Ok(None)
        } else {
            // TODO this code assumes that everything is either scalar or text, which
            // will be wrong when geo comes along.
            if scalar_keys.len() == 0 {
                match weights {
                    Some(ref weights) => {
                        match text_query {
                            &None => {
                                // if there is no textQuery, give up
                                Ok(None)
                            },
                            &Some(ref text_query) => {
                                // TODO clone
                                let plan = QueryPlan::Text(&ndx, vec![], text_query.clone());
                                Ok(Some(plan))
                            },
                        }
                    },
                    None => {
                        // er, why are we here?
                        // index with no keys
                        // TODO or return Err?
                        unreachable!();
                    },
                }
            } else {
                // we have some scalar keys, and maybe a text index after it.
                // for every scalar key, find comparisons from the query.
                let matching_ineqs = 
                    scalar_keys.iter().map(
                        |&(ref k, ndx_type)| {
                            match comps.ineq.get(k.as_str()) {
                                Some(&(gt, lt)) => {
                                    let gt = gt.map(|(c,v)| (c,(v,ndx_type == IndexType::Backward)));
                                    let lt = lt.map(|(c,v)| (c,(v,ndx_type == IndexType::Backward)));
                                    Some((gt, lt))
                                },
                                None => None,
                            }
                        }
                        ).collect::<Vec<_>>();
                let mut first_no_eqs = None;
                let mut matching_eqs = vec![];
                for (i, &(ref k, ndx_type)) in scalar_keys.iter().enumerate() {
                    match comps.eq.get(k.as_str()) {
                        Some(a) => {
                            // TODO not sure this check belongs here.  might want to do it later so
                            // hint can force it.
                            if a.is_null() && ndx.is_sparse() {
                                first_no_eqs = Some(i);
                                break;
                            } else {
                                matching_eqs.push((*a, ndx_type == IndexType::Backward));
                            }
                        },
                        None => {
                            first_no_eqs = Some(i);
                            break;
                        },
                    }
                }

                match text_query {
                    &Some(ref text_query) => {
                        match first_no_eqs {
                            Some(_) => {
                                // if there is a text index, we need an EQ for every scalar key.
                                // so this won't work.
                                Ok(None)
                            },
                            None => {
                                // we have an EQ for every key.  this index will work.
                                // TODO clone
                                let plan = QueryPlan::Text(&ndx, matching_eqs, text_query.clone());
                                Ok(Some(plan))
                            },
                        }
                    },
                    &None => {
                        // there is no text query.  note that this might still be a text index,
                        // but at this point we don't care.  we are considering whether we can
                        // use the scalar keys to the left of the text index.

                        match first_no_eqs {
                            None => {
                                if matching_eqs.len() > 0 {
                                    let plan = QueryPlan::Regular(&ndx, QueryBounds::EQ(matching_eqs));
                                    Ok(Some(plan))
                                } else {
                                    // we can't use this index at all
                                    Ok(None)
                                }
                            },
                            Some(num_eq) => {
                                match matching_ineqs[num_eq] {
                                    None | Some((None,None)) => {
                                        if num_eq>0 {
                                            let plan = QueryPlan::Regular(&ndx, QueryBounds::EQ(matching_eqs));
                                            Ok(Some(plan))
                                        } else {
                                            // we can't use this index at all
                                            Ok(None)
                                        }
                                    },
                                    Some((Some(min),None)) => {
                                        let (op, v) = min;
                                        matching_eqs.push(v);
                                        match op {
                                            OpGt::GT => {
                                                let plan = QueryPlan::Regular(&ndx, QueryBounds::GT(matching_eqs));
                                                Ok(Some(plan))
                                            },
                                            OpGt::GTE => {
                                                let plan = QueryPlan::Regular(&ndx, QueryBounds::GTE(matching_eqs));
                                                Ok(Some(plan))
                                            },
                                        }
                                    },
                                    Some((None,Some(max))) => {
                                        let (op, v) = max;
                                        matching_eqs.push(v);
                                        match op {
                                            OpLt::LT => {
                                                let plan = QueryPlan::Regular(&ndx, QueryBounds::LT(matching_eqs));
                                                Ok(Some(plan))
                                            },
                                            OpLt::LTE => {
                                                let plan = QueryPlan::Regular(&ndx, QueryBounds::LTE(matching_eqs));
                                                Ok(Some(plan))
                                            },
                                        }
                                    },
                                    Some((Some(min),Some(max))) => {
                                        // this can probably only happen when the comps came
                                        // from an elemMatch
                                        let (op_gt, vmin) = min;
                                        let (op_lt, vmax) = max;

                                        match (op_gt, op_lt) {
                                            (OpGt::GT, OpLt::LT) => {
                                                let plan = QueryPlan::Regular(&ndx, QueryBounds::GT_LT(matching_eqs, vec![vmin], vec![vmax]));
                                                Ok(Some(plan))
                                            },
                                            (OpGt::GT, OpLt::LTE) => {
                                                let plan = QueryPlan::Regular(&ndx, QueryBounds::GT_LTE(matching_eqs, vec![vmin], vec![vmax]));
                                                Ok(Some(plan))
                                            },
                                            (OpGt::GTE, OpLt::LT) => {
                                                let plan = QueryPlan::Regular(&ndx, QueryBounds::GTE_LT(matching_eqs, vec![vmin], vec![vmax]));
                                                Ok(Some(plan))
                                            },
                                            (OpGt::GTE, OpLt::LTE) => {
                                                let plan = QueryPlan::Regular(&ndx, QueryBounds::GTE_LTE(matching_eqs, vec![vmin], vec![vmax]));
                                                Ok(Some(plan))
                                            },
                                        }
                                    },
                                }
                            },
                        }
                    },
                }
            }
        }
    }

    fn parse_text_query(s: &Vec<char>) -> Result<Vec<TextQueryTerm>> {
        fn is_delim(c: char) -> bool {
            match c {
            ' ' => true,
            ',' => true,
            ';' => true,
            '.' => true,
            _ => false,
            }
        }

        let mut i = 0;
        let len = s.len();
        let mut a = vec![];
        loop {
            //printfn "get_token: %s" (s.Substring(!i))
            while i<len && is_delim(s[i]) {
                i = i + 1;
            }
            //printfn "after skip_delim: %s" (s.Substring(!i))
            if i >= len {
                break;
            } else {
                let neg =
                    if '-' == s[i] {
                        i = i + 1;
                        true
                    } else {
                        false
                    };

                // TODO do we allow space between the - and the word or phrase?

                if i >= len {
                    return Err(Error::Misc(String::from("negate of nothing")));
                }

                if '"' == s[i] {
                    let tok_start = i + 1;
                    //printfn "in phrase"
                    i = i + 1;
                    while i < len && s[i] != '"' {
                        i = i + 1;
                    }
                    //printfn "after look for other quote: %s" (s.Substring(!i))
                    let tok_len = 
                        if i < len { 
                            i - tok_start
                        } else {
                            return Err(Error::Misc(String::from("unmatched phrase quote")));
                        };
                    //printfn "phrase tok_len: %d" tok_len
                    i = i + 1;
                    // TODO need to get the individual words out of the phrase here?
                    // TODO what if the phrase is an empty string?  error?
                    if tok_len > 0 {
                        let sub = &s[tok_start .. tok_start + tok_len];
                        let s = sub.iter().cloned().collect::<String>();
                        let term = TextQueryTerm::Phrase(neg, s);
                        a.push(term);
                    } else {
                        // TODO isn't this always an error?
                        break;
                    }
                } else {
                    let tok_start = i;
                    while i < len && !is_delim(s[i]) {
                        i = i + 1;
                    }
                    let tok_len = i - tok_start;
                    if tok_len > 0 {
                        let sub = &s[tok_start .. tok_start + tok_len];
                        let s = sub.iter().cloned().collect::<String>();
                        let term = TextQueryTerm::Word(neg, s);
                        a.push(term);
                    } else {
                        // TODO isn't this always an error?
                        break;
                    }
                }
            }
        }

        let terms = a.into_iter().collect::<HashSet<_>>().into_iter().collect::<Vec<_>>();
        Ok(terms)
    }

    fn find_text_query(m: &matcher::QueryDoc) -> Result<Option<&str>> {
        let &matcher::QueryDoc::QueryDoc(ref items) = m;
        let mut a = 
            items
            .iter()
            .filter_map(|it| if let &matcher::QueryItem::Text(ref s) = it { Some(s.as_str()) } else { None })
            .collect::<Vec<_>>();
        if a.len() > 1 {
            Err(Error::Misc(String::from("only one $text in a query")))
        } else {
            let s = misc::remove_first_if_exists(&mut a);
            Ok(s)
        }
    }

    fn find_fit_indexes<'a, 'm>(indexes: &'a Vec<IndexInfo>, m: &'m matcher::QueryDoc) -> Result<(Vec<QueryPlan<'m,'a>>, Option<Vec<TextQueryTerm>>)> {
        let text_query = if let Some(s) = try!(Self::find_text_query(m)) {
            let v = s.chars().collect::<Vec<char>>();
            Some(try!(Self::parse_text_query(&v)))
        } else {
            None
        };
        // TODO er, we don't know how to use an index for any other kind of
        // predicate.  like $exists
        let comps_eq = try!(Self::find_compares_eq(m));
        let comps_ineq = try!(Self::find_compares_ineq(m));
        let comps = Comps {
            eq: comps_eq,
            ineq: comps_ineq,
        };
        let mut fits = Vec::new();
        for ndx in indexes {
            if let Some(x) = try!(Self::fit_index_to_query(ndx, &comps, &text_query)) {
                fits.push(x);
            }
        }
        //println!("fits: {:?}", fits);
        Ok((fits, text_query))
    }

    fn choose_from_possibles<'a,'b>(m: &matcher::QueryDoc, possibles: Vec<QueryPlan<'a,'b>>) -> Option<QueryPlan<'a,'b>> {
        if possibles.len() == 0 {
            None
        } else {
            // prefer the _id_ index if we can use it
            // TODO otherwise prefer any unique index
            // TODO otherwise prefer any EQ index
            // TODO or any index which has both min_max bounds
            // otherwise any index at all.  just take the first one.
            let mut winner = None;
            for plan in possibles {
                if winner.is_none() || plan.get_ndx().name == "_id_" {
                    //if matcher::uses_exists_false(m) && plan.get_ndx().is_sparse() {
                        // ineligible
                        //println!("INELIGIBLE");
                    //} else {
                        winner = Some(plan);
                    //}
                }
            }
            winner
        }
    }

    fn choose_index<'a, 'm>(indexes: &'a Vec<IndexInfo>, m: &'m matcher::QueryDoc, hint: Option<&IndexInfo>) -> Result<Option<QueryPlan<'m,'a>>> {
        let (mut fits, text_query) = try!(Self::find_fit_indexes(indexes, m));
        match text_query {
            Some(_) => {
                // TODO if there is a $text query, disallow hint
                if fits.len() == 0 {
                    Err(Error::Misc(String::from("$text without index")))
                } else {
                    assert!(fits.len() == 1);
                    Ok(Some(fits.remove(0)))
                }
            },
            None => {
                // TODO the jstests seem to indicate that hint will be forced
                // even if it does not fit the query.  how does this work?
                // what bounds are used?

                match hint {
                    Some(hint) => {
                        match fits.iter().position(|plan| plan.get_ndx().spec == hint.spec) {
                            Some(i) => {
                                Ok(Some(fits.remove(i)))
                            },
                            None => Ok(Self::choose_from_possibles(m, fits))
                        }
                    },
                    None => {
                        Ok(Self::choose_from_possibles(m, fits))
                    },
                }
            },
        }
    }

    fn find_index_for_min_max<'a>(indexes: &'a Vec<IndexInfo>, keys: &Vec<&str>) -> Result<Option<&'a IndexInfo>> {
        for ndx in indexes {
            let (normspec, _) = try!(get_normalized_spec(ndx));
            let a = normspec.iter().map(|&(ref k,_)| k).collect::<Vec<_>>();
            if a.len() != keys.len() {
                continue;
            }
            // TODO this should just be a == *keys, or something similar
            let mut same = true;
            for i in 0 .. a.len() {
                if a[i] != keys[i] {
                    same = false;
                    break;
                }
            }
            if same {
                return Ok(Some(ndx));
            }
        }
        return Ok(None);
    }

    fn parse_expr(v: bson::Value) -> Result<Expr> {
        let get_one_arg = |v: bson::Value| -> Result<Expr> {
            match v {
                bson::Value::BArray(mut a) => {
                    if a.len() != 1 {
                        Err(Error::MongoCode(16020, String::from("wrong number of args")))
                    } else {
                        Self::parse_expr(a.items.remove(0))
                    }
                },
                _ => Self::parse_expr(v),
            }
        };

        let get_two_args = |v: bson::Value| -> Result<(Expr,Expr)> {
            match v {
                bson::Value::BArray(mut a) => {
                    if a.len() != 2 {
                        Err(Error::MongoCode(16020, String::from("wrong number of args")))
                    } else {
                        let v1 = a.items.remove(1);
                        let v0 = a.items.remove(0);
                        let e0 = try!(Self::parse_expr(v0));
                        let e1 = try!(Self::parse_expr(v1));
                        Ok((e0, e1))
                    }
                },
                _ => Err(Error::MongoCode(16020, String::from("wrong number of args")))
            }
        };

        let get_three_args = |v: bson::Value| -> Result<(Expr,Expr,Expr)> {
            match v {
                bson::Value::BArray(mut a) => {
                    if a.len() != 3 {
                        Err(Error::MongoCode(16020, String::from("wrong number of args")))
                    } else {
                        let v2 = a.items.remove(2);
                        let v1 = a.items.remove(1);
                        let v0 = a.items.remove(0);
                        let e0 = try!(Self::parse_expr(v0));
                        let e1 = try!(Self::parse_expr(v1));
                        let e2 = try!(Self::parse_expr(v2));
                        Ok((e0, e1, e2))
                    }
                },
                _ => Err(Error::MongoCode(16020, String::from("wrong number of args")))
            }
        };

        let parse_vec = |v: bson::Value| -> Result<Vec<Expr>> {
            let a = try!(v.into_array());
            a.items.into_iter().map(|v| Self::parse_expr(v)).collect::<Result<Vec<_>>>()
        };

        match v {
            bson::Value::BString(s) => {
                if s.starts_with("$$") {
                    Ok(Expr::Var(String::from(&s[2 ..])))
                } else if s.starts_with("$") {
                    Ok(Expr::Var(format!("CURRENT.{}", &s[1 ..])))
                } else {
                    Ok(Expr::Literal(bson::Value::BString(s)))
                }
            },
            bson::Value::BDocument(mut bd) => {
                if bd.pairs.len() == 1 {
                    let (k, v) = bd.pairs.remove(0);
                    if k.starts_with("$") {
                        match k.as_str() {
                            "$literal" => {
                                Ok(Expr::Literal(v))
                            },
                            "$allElementsTrue" => {
                                Ok(Expr::AllElementsTrue(box try!(get_one_arg(v))))
                            },
                            "$anyElementTrue" => {
                                Ok(Expr::AnyElementTrue(box try!(get_one_arg(v))))
                            },
                            "$dayOfMonth" => {
                                Ok(Expr::DayOfMonth(box try!(get_one_arg(v))))
                            },
                            "$dayOfWeek" => {
                                Ok(Expr::DayOfWeek(box try!(get_one_arg(v))))
                            },
                            "$dayOfYear" => {
                                Ok(Expr::DayOfYear(box try!(get_one_arg(v))))
                            },
                            "$hour" => {
                                Ok(Expr::Hour(box try!(get_one_arg(v))))
                            },
                            "$millisecond" => {
                                Ok(Expr::Millisecond(box try!(get_one_arg(v))))
                            },
                            "$minute" => {
                                Ok(Expr::Minute(box try!(get_one_arg(v))))
                            },
                            "$month" => {
                                Ok(Expr::Month(box try!(get_one_arg(v))))
                            },
                            "$not" => {
                                Ok(Expr::Not(box try!(get_one_arg(v))))
                            },
                            "$second" => {
                                Ok(Expr::Second(box try!(get_one_arg(v))))
                            },
                            "$size" => {
                                Ok(Expr::Size(box try!(get_one_arg(v))))
                            },
                            "$toLower" => {
                                Ok(Expr::ToLower(box try!(get_one_arg(v))))
                            },
                            "$toUpper" => {
                                Ok(Expr::ToUpper(box try!(get_one_arg(v))))
                            },
                            "$week" => {
                                Ok(Expr::Week(box try!(get_one_arg(v))))
                            },
                            "$year" => {
                                Ok(Expr::Year(box try!(get_one_arg(v))))
                            },

                            "$cmp" => {
                                Ok(Expr::Cmp(box try!(get_two_args(v))))
                            },
                            "$eq" => {
                                Ok(Expr::Eq(box try!(get_two_args(v))))
                            },
                            "$ne" => {
                                Ok(Expr::Ne(box try!(get_two_args(v))))
                            },
                            "$gt" => {
                                Ok(Expr::Gt(box try!(get_two_args(v))))
                            },
                            "$lt" => {
                                Ok(Expr::Lt(box try!(get_two_args(v))))
                            },
                            "$gte" => {
                                Ok(Expr::Gte(box try!(get_two_args(v))))
                            },
                            "$lte" => {
                                Ok(Expr::Lte(box try!(get_two_args(v))))
                            },
                            "$subtract" => {
                                Ok(Expr::Subtract(box try!(get_two_args(v))))
                            },
                            "$divide" => {
                                Ok(Expr::Divide(box try!(get_two_args(v))))
                            },
                            "$mod" => {
                                Ok(Expr::Mod(box try!(get_two_args(v))))
                            },
                            "$ifNull" => {
                                Ok(Expr::IfNull(box try!(get_two_args(v))))
                            },
                            "$setDifference" => {
                                Ok(Expr::SetDifference(box try!(get_two_args(v))))
                            },
                            "$setIsSubset" => {
                                Ok(Expr::SetIsSubset(box try!(get_two_args(v))))
                            },
                            "$strcasecmp" => {
                                Ok(Expr::StrCaseCmp(box try!(get_two_args(v))))
                            },

                            "$substr" => {
                                Ok(Expr::Substr(box try!(get_three_args(v))))
                            },

                            "$cond" => {
                                if v.is_array() {
                                    Ok(Expr::Cond(box try!(get_three_args(v))))
                                } else if v.is_document() {
                                    let mut v = try!(v.into_document());
                                    if v.pairs.iter().any(|&(ref k,_)| k != "if" && k != "then" && k != "else") {
                                        Err(Error::MongoCode(17083, String::from("unrecognized $cond arg")))
                                    } else {
                                        let arg_if = match v.remove("if") {
                                            Some(v) => v,
                                            None => {
                                                return Err(Error::MongoCode(17080, String::from("$cond missing if")));
                                            },
                                        };
                                        let arg_then = match v.remove("then") {
                                            Some(v) => v,
                                            None => {
                                                return Err(Error::MongoCode(17081, String::from("$cond missing then")));
                                            },
                                        };
                                        let arg_else = match v.remove("else") {
                                            Some(v) => v,
                                            None => {
                                                return Err(Error::MongoCode(17082, String::from("$cond missing else")));
                                            },
                                        };
                                        let e_if = try!(Self::parse_expr(arg_if));
                                        let e_then = try!(Self::parse_expr(arg_then));
                                        let e_else = try!(Self::parse_expr(arg_else));
                                        let t = (e_if, e_then, e_else);
                                        Ok(Expr::Cond(box t))
                                    }
                                } else {
                                    Err(Error::MongoCode(16020, String::from("wrong number of args")))
                                }
                            },

                            "$map" => {
                                let mut v = try!(v.into_document());
                                if v.pairs.iter().any(|&(ref k,_)| k != "input" && k != "as" && k != "in") {
                                    Err(Error::MongoCode(16879, String::from("unrecognized $map arg")))
                                } else {
                                    let arg_input = match v.remove("input") {
                                        Some(v) => v,
                                        None => {
                                            return Err(Error::MongoCode(16880, String::from("$map missing input")));
                                        },
                                    };
                                    let arg_as = match v.remove("as") {
                                        Some(v) => v,
                                        None => {
                                            return Err(Error::MongoCode(16881, String::from("$map missing as")));
                                        },
                                    };
                                    let arg_in = match v.remove("in") {
                                        Some(v) => v,
                                        None => {
                                            return Err(Error::MongoCode(16882, String::from("$map missing in")));
                                        },
                                    };
                                    let e_input = try!(Self::parse_expr(arg_input));
                                    let v_as = try!(arg_as.into_string());
                                    let expr_in = try!(Self::parse_expr(arg_in));
                                    let t = (e_input, v_as, expr_in);
                                    Ok(Expr::Map(box t))
                                }
                            },

                            "$let" => {
                                match v {
                                    bson::Value::BDocument(mut v) => {
                                        if v.pairs.iter().any(|&(ref k,_)| k != "vars" && k != "in") {
                                            Err(Error::MongoCode(16875, String::from("unrecognized $let arg")))
                                        } else {
                                            let arg_vars = match v.remove("vars") {
                                                Some(bson::Value::BDocument(bd)) => {
                                                    bd
                                                },
                                                Some(_) => {
                                                    return Err(Error::MongoCode(16876, String::from("$let vars must be a document")));
                                                },
                                                None => {
                                                    return Err(Error::MongoCode(16876, String::from("$let missing vars")));
                                                },
                                            };
                                            let arg_in = match v.remove("in") {
                                                Some(v) => v,
                                                None => {
                                                    return Err(Error::MongoCode(16877, String::from("$let missing in")));
                                                },
                                            };
                                            let mut vars = vec![];
                                            for (k,v) in arg_vars.pairs {
                                                let e = try!(Self::parse_expr(v));
                                                vars.push((k,e));
                                            }
                                            let expr_in = try!(Self::parse_expr(arg_in));
                                            Ok(Expr::Let(vars, box expr_in))
                                        }
                                    },
                                    _ => {
                                        return Err(Error::MongoCode(16874, String::from("$let requires a document as its argument")));
                                    },
                                }
                            },

                            "$and" => {
                                Ok(Expr::And(try!(parse_vec(v))))
                            },
                            "$or" => {
                                Ok(Expr::Or(try!(parse_vec(v))))
                            },
                            "$add" => {
                                Ok(Expr::Add(try!(parse_vec(v))))
                            },
                            "$multiply" => {
                                Ok(Expr::Multiply(try!(parse_vec(v))))
                            },
                            "$concat" => {
                                Ok(Expr::Concat(try!(parse_vec(v))))
                            },
                            "$setEquals" => {
                                Ok(Expr::SetEquals(try!(parse_vec(v))))
                            },
                            "$setIntersection" => {
                                Ok(Expr::SetIntersection(try!(parse_vec(v))))
                            },
                            "$setUnion" => {
                                Ok(Expr::SetUnion(try!(parse_vec(v))))
                            },
                            "$dateToString" => {
                                if !v.is_document() {
                                    return Err(Error::MongoCode(18629, format!("$dateToString requires a document")));
                                }
                                // TODO following could unwrap
                                let mut v = try!(v.into_document());
                                let date = match v.remove("date") {
                                    Some(v) => v,
                                    None => {
                                        return Err(Error::MongoCode(18628, format!("$dateToString requires date")));
                                    },
                                };
                                let format = match v.remove("format") {
                                    Some(bson::Value::BString(s)) => {
                                        s
                                    },
                                    Some(_) => {
                                        return Err(Error::MongoCode(18533, format!("$dateToString format must be a string")));
                                    },
                                    None => {
                                        return Err(Error::MongoCode(18627, format!("$dateToString requires format")));
                                    },
                                };
                                if v.len() > 0 {
                                    return Err(Error::MongoCode(18534, format!("$dateToString extra stuff")));
                                }
                                let date = try!(Self::parse_expr(date));
                                Ok(Expr::DateToString(format, box date))
                            },

                            _ => {
                                Err(Error::MongoCode(15999, format!("invalid expression operator: {}", k)))
                            },
                        }
                    } else {
                        Ok(Expr::Literal(bson::Value::BDocument(bd)))
                    }
                } else {
                    // TODO any cases where this is not a literal need to have
                    // been handled before this point.
                    Ok(Expr::Literal(bson::Value::BDocument(bd)))
                }
            },
            _ => {
                // TODO any cases where this is not a literal need to have
                // been handled before this point.
                Ok(Expr::Literal(v))
            },
        }
    }

    fn is_legal_var_name(s: &str) -> bool {
        if s == "CURRENT" {
            true
        } else {
            match s.chars().next() {
                Some(c) => {
                    c >= 'a' && c <= 'z'
                },
                None => {
                    false
                },
            }
        }
    }

    fn eval(ctx: &bson::Document, e: &Expr) -> Result<bson::Value> {
        let eval_tm = |v: &Expr| -> Result<time::Tm> {
            let d = try!(Self::eval(ctx, v));
            let n = 
                match d {
                    bson::Value::BDateTime(n) => n,
                    bson::Value::BTimeStamp(n) => {
                        let ms = (n >> 32) * 1000;
                        ms
                    },
                    _ => return Err(Error::MongoCode(16006, format!("datetime or timestamp required, but found {:?}", d))),
                };
            let (sec, ms) = misc::fix_ms(n);
            let ts = time::Timespec::new(sec, (ms * 1000000) as i32);
            let tm = time::at_utc(ts);
            Ok(tm)
        };

        match e {
            &Expr::Literal(ref v) => Ok(v.clone()),
            &Expr::Var(ref s) => {
                //println!("Var: {}", s);
                // if the var contains an object followed by a dotted path,
                // we need to dive into that path.
                let dot = s.find('.');
                let name = match dot { 
                    None => s.as_str(),
                    Some(i) => &s[0 .. i]
                };
                let v = try!(ctx.must_get(name));
                match dot {
                    None => Ok(v.clone()),
                    Some(i) => {
                        let subpath = &s[i + 1 ..];
                        if subpath.chars().any(|c| c == (0 as char)) {
                            return Err(Error::MongoCode(16419, format!("field path cannot contain NUL char: {:?}", subpath)));
                        }
                        // note that hack_like_find_path() isn't quite right here, since it
                        // keeps the empty leaves and we need them to be discarded for this case.
                        let mut vals = v.walk_path(subpath).leaves().filter_map(|leaf| leaf.v).collect::<Vec<_>>();
                        if vals.is_empty() {
                            Ok(bson::Value::BUndefined)
                        } else if vals.len() == 1 {
                            Ok(vals.remove(0).clone())
                        } else {
                            // so in this case, yes, when this path resolves to multiple values, 
                            // we need to construct an array for them.  test case arrayfind9
                            let vals = vals.into_iter().map(|v| v.clone()).collect::<Vec<_>>();
                            let a = bson::Array {
                                items: vals,
                            };
                            Ok(bson::Value::BArray(a))
                        }
                    },
                }
            },
            &Expr::Substr(ref t) => {
                let s = try!(Self::eval(ctx, &t.0));
                let s = try!(s.into_expr_string());
                let start = try!(Self::eval(ctx, &t.1));
                let start = try!(start.numeric_to_i32());
                if start < 0 {
                    Ok(bson::Value::BString(String::new()))
                } else if (start as usize) >= s.len() {
                    Ok(bson::Value::BString(String::new()))
                } else {
                    let start = start as usize;
                    let len = try!(Self::eval(ctx, &t.2));
                    let len = try!(len.numeric_to_i32());
                    if len < 0 {
                        let a = s.chars().collect::<Vec<char>>();
                        let s = &a[start ..];
                        let s = s.iter().cloned().collect::<String>();
                        Ok(bson::Value::BString(s))
                    } else {
                        let len = len as usize;
                        if (start + len) >= s.len() {
                            let a = s.chars().collect::<Vec<char>>();
                            let s = &a[start ..];
                            let s = s.iter().cloned().collect::<String>();
                            Ok(bson::Value::BString(s))
                        } else {
                            let a = s.chars().collect::<Vec<char>>();
                            let s = &a[start .. start + len];
                            let s = s.iter().cloned().collect::<String>();
                            Ok(bson::Value::BString(s))
                        }
                    }
                }
            },
            &Expr::Eq(ref t) => {
                let v0 = try!(Self::eval(ctx, &t.0));
                let v1 = try!(Self::eval(ctx, &t.1));
                let c = matcher::cmp(&v0, &v1);
                let b = c == Ordering::Equal;
                Ok(bson::Value::BBoolean(b))
            },
            &Expr::Ne(ref t) => {
                let v0 = try!(Self::eval(ctx, &t.0));
                let v1 = try!(Self::eval(ctx, &t.1));
                let c = matcher::cmp(&v0, &v1);
                let b = c != Ordering::Equal;
                Ok(bson::Value::BBoolean(b))
            },
            &Expr::Lt(ref t) => {
                let v0 = try!(Self::eval(ctx, &t.0));
                let v1 = try!(Self::eval(ctx, &t.1));
                let c = matcher::cmp(&v0, &v1);
                let b = c == Ordering::Less;
                Ok(bson::Value::BBoolean(b))
            },
            &Expr::Gt(ref t) => {
                let v0 = try!(Self::eval(ctx, &t.0));
                let v1 = try!(Self::eval(ctx, &t.1));
                let c = matcher::cmp(&v0, &v1);
                let b = c == Ordering::Greater;
                Ok(bson::Value::BBoolean(b))
            },
            &Expr::Lte(ref t) => {
                let v0 = try!(Self::eval(ctx, &t.0));
                let v1 = try!(Self::eval(ctx, &t.1));
                let c = matcher::cmp(&v0, &v1);
                let b = c != Ordering::Greater;
                Ok(bson::Value::BBoolean(b))
            },
            &Expr::Gte(ref t) => {
                let v0 = try!(Self::eval(ctx, &t.0));
                let v1 = try!(Self::eval(ctx, &t.1));
                let c = matcher::cmp(&v0, &v1);
                let b = c != Ordering::Less;
                Ok(bson::Value::BBoolean(b))
            },
            &Expr::Cmp(ref t) => {
                let v0 = try!(Self::eval(ctx, &t.0));
                let v1 = try!(Self::eval(ctx, &t.1));
                let c = matcher::cmp(&v0, &v1);
                let c = match c {
                    Ordering::Equal => 0,
                    Ordering::Less => -1,
                    Ordering::Greater => 1,
                };
                Ok(bson::Value::BInt32(c))
            },
            &Expr::StrCaseCmp(ref t) => {
                let s0 = try!(Self::eval(ctx, &t.0));
                let s1 = try!(Self::eval(ctx, &t.1));
                let s0 = try!(s0.into_expr_string());
                let s1 = try!(s1.into_expr_string());
                let c = 
                    {
                        use std::ascii::AsciiExt;
                        let s0 = s0.to_ascii_lowercase();
                        let s1 = s1.to_ascii_lowercase();
                        s0.cmp(&s1)
                    };
                let c = match c {
                    Ordering::Equal => 0,
                    Ordering::Less => -1,
                    Ordering::Greater => 1,
                };
                Ok(bson::Value::BInt32(c))
            },
            &Expr::Size(ref v) => {
                let s = try!(Self::eval(ctx, v));
                if !s.is_array() {
                    return Err(Error::MongoCode(17124, format!("must be an array: {:?}", s)));
                }
                let s = try!(s.into_array());
                Ok(bson::Value::BInt32(s.len() as i32))
            },
            &Expr::ToLower(ref v) => {
                let s = try!(Self::eval(ctx, v));
                let s = try!(s.into_expr_string());
                let s = 
                    {
                        use std::ascii::AsciiExt;
                        s.to_ascii_lowercase()
                    };
                Ok(bson::Value::BString(s))
            },
            &Expr::ToUpper(ref v) => {
                let s = try!(Self::eval(ctx, v));
                let s = try!(s.into_expr_string());
                let s = 
                    {
                        use std::ascii::AsciiExt;
                        s.to_ascii_uppercase()
                    };
                Ok(bson::Value::BString(s))
            },
            &Expr::Concat(ref a) => {
                let vals = try!(a.iter().map(|e| Self::eval(ctx, e)).collect::<Result<Vec<_>>>());
                let mut cur = bson::Value::BString(String::new());
                for v in vals {
                    if cur.is_null() {
                        // do nothing
                    } else if cur.is_undefined() {
                        cur = bson::Value::BNull;
                    } else if v.is_null() {
                        cur = bson::Value::BNull;
                    } else if v.is_undefined() {
                        cur = bson::Value::BNull;
                    } else if !v.is_string() {
                        return Err(Error::MongoCode(16702, format!("must be a string: {:?}", v)));
                    } else if !cur.is_string() {
                        return Err(Error::MongoCode(16702, format!("must be a string: {:?}", cur)));
                    } else {
                        let s1 = try!(cur.into_string());
                        let s2 = try!(v.into_string());
                        let s = s1 + &s2;
                        cur = bson::Value::BString(s);
                    }
                }
                Ok(cur)
            },
            &Expr::IfNull(ref t) => {
                let v0 = try!(Self::eval(ctx, &t.0));
                match v0 {
                    bson::Value::BNull
                    | bson::Value::BUndefined => {
                        let v1 = try!(Self::eval(ctx, &t.1));
                        Ok(v1)
                    },
                    _ => Ok(v0),
                }
            },
            &Expr::Mod(ref t) => {
                let v0 = try!(Self::eval(ctx, &t.0));
                let v1 = try!(Self::eval(ctx, &t.1));
                if !v0.is_numeric() || !v1.is_numeric() {
                    return Err(Error::MongoCode(16611, format!("numeric types only: {:?}", t)));
                }
                if 0 == try!(v1.numeric_to_i32()) {
                    return Err(Error::MongoCode(16610, format!("mod by 0: {:?}", t)));
                }

                match (v0,v1) {
                    (bson::Value::BInt32(n0),bson::Value::BInt32(n1)) => Ok(bson::Value::BInt32(n0 % n1)),
                    (bson::Value::BInt64(n0),bson::Value::BInt64(n1)) => Ok(bson::Value::BInt64(n0 % n1)),
                    (bson::Value::BDouble(n0),bson::Value::BDouble(n1)) => Ok(bson::Value::BDouble(n0 % n1)),

                    (bson::Value::BInt64(n0),bson::Value::BInt32(n1)) => Ok(bson::Value::BInt64(n0 % (n1 as i64))),
                    (bson::Value::BInt32(n0),bson::Value::BInt64(n1)) => Ok(bson::Value::BInt64((n0 as i64) % n1)),

                    (bson::Value::BDouble(n0),bson::Value::BInt32(n1)) if f64_can_be_i32(n0) => Ok(bson::Value::BInt32((n0 as i32) % n1)),
                    (bson::Value::BDouble(n0),bson::Value::BInt64(n1)) if f64_can_be_i64(n0) => Ok(bson::Value::BInt64((n0 as i64) % n1)),
                    (bson::Value::BInt32(n0),bson::Value::BDouble(n1)) if f64_can_be_i32(n1) => Ok(bson::Value::BInt32(n0 % (n1 as i32))),
                    (bson::Value::BInt64(n0),bson::Value::BDouble(n1)) if f64_can_be_i32(n1) => Ok(bson::Value::BInt64(n0 % (n1 as i64))),

                    (bson::Value::BDouble(n0),bson::Value::BInt32(n1)) => Ok(bson::Value::BDouble(n0 % (n1 as f64))),
                    (bson::Value::BDouble(n0),bson::Value::BInt64(n1)) => Ok(bson::Value::BDouble(n0 % (n1 as f64))),
                    (bson::Value::BInt32(n0),bson::Value::BDouble(n1)) => Ok(bson::Value::BDouble((n0 as f64) % n1)),
                    (bson::Value::BInt64(n0),bson::Value::BDouble(n1)) => Ok(bson::Value::BDouble((n0 as f64) % n1)),

                    (v0,v1) => Err(Error::Misc(format!("invalid types for mod: {:?}, {:?}", v0, v1)))
                }
            }
            &Expr::Subtract(ref t) => {
                let v0 = try!(Self::eval(ctx, &t.0));
                let v1 = try!(Self::eval(ctx, &t.1));
                match (v0,v1) {
                    (bson::Value::BInt32(n0),bson::Value::BInt32(n1)) => Ok(bson::Value::BInt32(n0 - n1)),
                    (bson::Value::BInt64(n0),bson::Value::BInt64(n1)) => Ok(bson::Value::BInt64(n0 - n1)),
                    (bson::Value::BDouble(n0),bson::Value::BDouble(n1)) => Ok(bson::Value::BDouble(n0 - n1)),

                    (bson::Value::BInt32(n0),bson::Value::BInt64(n1)) => Ok(bson::Value::BInt64((n0 as i64) - n1)),
                    (bson::Value::BInt32(n0),bson::Value::BDouble(n1)) => Ok(bson::Value::BDouble((n0 as f64) - n1)),

                    (bson::Value::BInt64(n0),bson::Value::BInt32(n1)) => Ok(bson::Value::BInt64(n0 - (n1 as i64))),
                    (bson::Value::BInt64(n0),bson::Value::BDouble(n1)) => Ok(bson::Value::BDouble((n0 as f64) - n1)),

                    (bson::Value::BDouble(n0),bson::Value::BInt32(n1)) => Ok(bson::Value::BDouble(n0 - (n1 as f64))),
                    (bson::Value::BDouble(n0),bson::Value::BInt64(n1)) => Ok(bson::Value::BDouble(n0 - (n1 as f64))),

                    (bson::Value::BDateTime(n0),bson::Value::BDateTime(n1)) => Ok(bson::Value::BInt64(n0 - n1)),
                    (bson::Value::BDateTime(n0),bson::Value::BInt32(n1)) => Ok(bson::Value::BDateTime(n0 - (n1 as i64))),
                    (bson::Value::BDateTime(n0),bson::Value::BInt64(n1)) => Ok(bson::Value::BDateTime(n0 - (n1 as i64))),
                    (bson::Value::BDateTime(n0),bson::Value::BDouble(n1)) => Ok(bson::Value::BDateTime(n0 - (n1 as i64))),

                    (v0,v1) => Err(Error::MongoCode(16556, format!("invalid types for subtract: {:?}, {:?}", v0, v1)))
                }
            },
            &Expr::Divide(ref t) => {
                let v0 = try!(Self::eval(ctx, &t.0));
                let v1 = try!(Self::eval(ctx, &t.1));
                if !v0.is_numeric() || !v1.is_numeric() {
                    return Err(Error::MongoCode(16609, format!("numeric types only: {:?}", t)));
                }
                match v1 {
                    bson::Value::BInt32(0)
                    | bson::Value::BInt64(0)
                    | bson::Value::BDouble(0.0) => {
                        return Err(Error::MongoCode(16608, format!("division by 0: {:?}", t)));
                    },
                    _ => {
                    },
                }
                let v0 = try!(v0.numeric_to_f64());
                let v1 = try!(v1.numeric_to_f64());
                Ok(bson::Value::BDouble(v0 / v1))
            },
            &Expr::Add(ref a) => {
                let vals = try!(a.iter().map(|e| Self::eval(ctx, e)).collect::<Result<Vec<_>>>());
                // TODO don't loop twice here.
                if vals.iter().any(|v| (!v.is_date()) && (!v.is_numeric())) {
                    return Err(Error::MongoCode(16554, format!("$add supports numeric or date: {:?}", a)));
                }
                let count_dates = vals.iter().filter(|v| v.is_date()).count();
                if count_dates > 1 {
                    Err(Error::MongoCode(16612, format!("only one date allowed: {:?}", a)))
                } else if count_dates == 0 {
                    let vals = try!(vals.iter().map(|v| {
                        let f = try!(v.numeric_to_f64());
                        Ok(f)
                    }).collect::<Result<Vec<_>>>());
                    // TODO use iter.sum
                    let sum = vals.iter().fold(0.0, |acc, &v| acc + v);
                    Ok(bson::Value::BDouble(sum))
                } else {
                    let vals = try!(vals.iter().map(|v| {
                        let f = try!(v.numeric_or_datetime_to_i64());
                        Ok(f)
                    }).collect::<Result<Vec<_>>>());
                    // TODO use iter.sum
                    let sum = vals.iter().fold(0, |acc, &v| acc + v);
                    Ok(bson::Value::BDateTime(sum))
                }
            },
            &Expr::Multiply(ref a) => {
                let vals = try!(a.iter().map(|e| Self::eval(ctx, e)).collect::<Result<Vec<_>>>());
                // TODO don't loop twice here.
                if vals.iter().any(|v| !v.is_numeric()) {
                    return Err(Error::MongoCode(16555, format!("$multiply supports numeric only: {:?}", a)));
                }
                let vals = try!(vals.iter().map(|v| {
                    let f = try!(v.numeric_to_f64());
                    Ok(f)
                }).collect::<Result<Vec<_>>>());
                // TODO use iter.product
                let product = vals.iter().fold(1.0, |acc, &v| acc * v);
                Ok(bson::Value::BDouble(product))
            },
            &Expr::And(ref a) => {
                // TODO what we actually want here is to stop on the first
                // one that returns false.
                let v = try!(a.iter().map(|e| {
                    let b = try!(Self::eval(ctx, e)).as_expr_bool();
                    Ok(b)
                }).collect::<Result<Vec<_>>>());
                let b = v.iter().all(|b| *b);
                Ok(bson::Value::BBoolean(b))
            },
            &Expr::Or(ref a) => {
                // TODO what we actually want here is to stop on the first
                // one that returns true.
                let v = try!(a.iter().map(|e| {
                    let b = try!(Self::eval(ctx, e)).as_expr_bool();
                    Ok(b)
                }).collect::<Result<Vec<_>>>());
                let b = v.iter().any(|b| *b);
                Ok(bson::Value::BBoolean(b))
            },
            &Expr::AnyElementTrue(_) => {
                Err(Error::Misc(format!("TODO eval {:?}", e)))
            },
            &Expr::AllElementsTrue(_) => {
                Err(Error::Misc(format!("TODO eval {:?}", e)))
            },
            &Expr::DayOfMonth(ref v) => {
                let tm = try!(eval_tm(v));
                // mongo wants 1 thru 31
                // tm is same
                Ok(bson::Value::BInt32(tm.tm_mday))
            },
            &Expr::DayOfWeek(ref v) => {
                let tm = try!(eval_tm(v));
                // mongo wants 1 thru 7
                // tm is 0 thru 6
                Ok(bson::Value::BInt32(tm.tm_wday + 1))
            },
            &Expr::DayOfYear(ref v) => {
                let tm = try!(eval_tm(v));
                // mongo wants 1 thru 366
                // tm is 0 thru 365
                Ok(bson::Value::BInt32(tm.tm_yday + 1))
            },
            &Expr::Hour(ref v) => {
                let tm = try!(eval_tm(v));
                // mongo wants 0 thru 23
                // tm is same
                Ok(bson::Value::BInt32(tm.tm_hour))
            },
            &Expr::Minute(ref v) => {
                let tm = try!(eval_tm(v));
                // mongo wants 0 thru 59
                // tm is same
                Ok(bson::Value::BInt32(tm.tm_min))
            },
            &Expr::Second(ref v) => {
                let tm = try!(eval_tm(v));
                // mongo wants 0 thru 59
                // tm is same
                Ok(bson::Value::BInt32(tm.tm_sec))
            },
            &Expr::Millisecond(ref v) => {
                let tm = try!(eval_tm(v));
                Ok(bson::Value::BInt32(tm.tm_nsec / 1000000))
            },
            &Expr::Week(ref v) => {
                // mongo wants 0 thru 53
                let tm = try!(eval_tm(v));
                let n = (tm.tm_yday - tm.tm_wday + 7) / 7;
                Ok(bson::Value::BInt32(n as i32))
            },
            &Expr::Month(ref v) => {
                let tm = try!(eval_tm(v));
                // mongo wants 1 thru 12
                // tm is 0 thru 11
                Ok(bson::Value::BInt32(tm.tm_mon + 1))
            },
            &Expr::Year(ref v) => {
                let tm = try!(eval_tm(v));
                // mongo wants full 4 digits
                // tm is since 1900
                Ok(bson::Value::BInt32(tm.tm_year + 1900))
            },
            &Expr::DateToString(ref format, ref v) => {
                {
                    // when given a bad format string as well as an invalid expression,
                    // mongo returns the error for the bad format string.  to emulate this
                    // behavior, we format the current time using the given format string
                    // before we do anything else.  server11118.js
                    let ts = time::get_time();
                    let tm = time::at_utc(ts);
                    let _s = try!(mongo_strftime(&format, &tm));
                }
                let d = try!(Self::eval(ctx, v));
                // TODO this could use eval_tm, except that it is supposed to
                // return null when the date is null.  are other places supposed
                // to do this?
                if d.is_null() {
                    Ok(bson::Value::BNull)
                } else {
                    let n = 
                        match d {
                            bson::Value::BDateTime(n) => n,
                            bson::Value::BTimeStamp(n) => {
                                let ms = (n >> 32) * 1000;
                                ms
                            },
                            _ => return Err(Error::MongoCode(16006, format!("datetime or timestamp required, but found {:?}", d))),
                        };
                    let (sec, ms) = misc::fix_ms(n);
                    let ts = time::Timespec::new(sec, (ms * 1000000) as i32);
                    let tm = time::at_utc(ts);
                    let s = try!(mongo_strftime(&format, &tm));
                    Ok(bson::Value::BString(s))
                }
            },
            &Expr::Not(ref v) => {
                let b = try!(Self::eval(ctx, v)).as_expr_bool();
                Ok(bson::Value::BBoolean(!b))
            },
            &Expr::Cond(ref t) => {
                let b = try!(Self::eval(ctx, &t.0)).as_expr_bool();
                if b {
                    Self::eval(ctx, &t.1)
                } else {
                    Self::eval(ctx, &t.2)
                }
            },
            &Expr::Map(ref t) => {
                let name = &t.1;
                if !Self::is_legal_var_name(name) {
                    return Err(Error::MongoCode(16867, format!("illegal variable name{:?}", name)));
                }
                let mut ctx = ctx.clone();
                match try!(Self::eval(&ctx, &t.0)) {
                    bson::Value::BArray(ba) => {
                        let mut a2 = vec![];
                        for v in ba.items {
                            ctx.set(name, v);
                            let v2 = try!(Self::eval(&ctx, &t.2));
                            a2.push(v2);
                        }
                        let a2 = bson::Array {
                            items: a2,
                        };
                        Ok(bson::Value::BArray(a2))
                    },
                    bson::Value::BNull => {
                        Ok(bson::Value::BNull)
                    },
                    v => {
                        Err(Error::MongoCode(16883, format!("$map invalid type {:?}", v)))
                    },
                }
            },
            &Expr::Let(ref vars, ref expr_in) => {
                let mut ctx = ctx.clone();
                for &(ref name, ref e) in vars.iter() {
                    if !Self::is_legal_var_name(name) {
                        return Err(Error::MongoCode(16867, format!("illegal variable name{:?}", name)));
                    }
                    let v = try!(Self::eval(&ctx, e));
                    ctx.set(name, v);
                }
                let v = try!(Self::eval(&ctx, expr_in));
                Ok(v)
            },
            &Expr::SetDifference(_) => {
                Err(Error::Misc(format!("TODO eval {:?}", e)))
            },
            &Expr::SetIsSubset(_) => {
                Err(Error::Misc(format!("TODO eval {:?}", e)))
            },
            &Expr::SetEquals(_) => {
                Err(Error::Misc(format!("TODO eval {:?}", e)))
            },
            &Expr::SetIntersection(_) => {
                Err(Error::Misc(format!("TODO eval {:?}", e)))
            },
            &Expr::SetUnion(_) => {
                Err(Error::Misc(format!("TODO eval {:?}", e)))
            },
        }
    }

    fn parse_accum(v: bson::Value) -> Result<GroupAccum> {
        if !v.is_document() {
            return Err(Error::MongoCode(15950, format!("$group accum invalid: {:?}", v)));
        }
        let mut v = try!(v.into_document());
        if v.pairs.len() != 1 {
            return Err(Error::Misc(format!("$group accum invalid: {:?}", v)));
        }
        let (k,e) = v.pairs.remove(0);
        match k.as_str() {
            "$sum" => Ok(GroupAccum::Sum(try!(Self::parse_expr(e)))),
            "$avg" => Ok(GroupAccum::Avg(try!(Self::parse_expr(e)))),
            "$first" => Ok(GroupAccum::First(try!(Self::parse_expr(e)))),
            "$last" => Ok(GroupAccum::Last(try!(Self::parse_expr(e)))),
            "$max" => Ok(GroupAccum::Max(try!(Self::parse_expr(e)))),
            "$min" => Ok(GroupAccum::Min(try!(Self::parse_expr(e)))),
            "$push" => Ok(GroupAccum::Push(try!(Self::parse_expr(e)))),
            "$addToSet" => Ok(GroupAccum::AddToSet(try!(Self::parse_expr(e)))),
            _ => Err(Error::Misc(format!("$group accum op unknown: {:?}", k)))
        }
    }

    fn parse_agg(a: bson::Array) -> Result<Vec<AggOp>> {
        fn flatten_projection(d: bson::Value) -> Result<Vec<(String, bson::Value)>> {
            fn flatten(a: &mut Vec<(String, bson::Value)>, path: String, d: bson::Value) -> Result<()> {
                match d {
                    bson::Value::BDocument(bd) => {
                        if  bd.pairs.iter().any(|&(ref k, _)| k.starts_with("$")) {
                            if path.as_str() == "" {
                                return Err(Error::MongoCode(16404, String::from("$project key begins with $")))
                            } else {
                                a.push((path, bson::Value::BDocument(bd)));
                            }
                        } else {
                            for (k,v) in bd.pairs {
                                let new_path =
                                    if path.as_str() == "" {
                                        String::from(k)
                                    } else {
                                        format!("{}.{}", path, k)
                                    };
                                try!(flatten(a, new_path, v));
                            }
                        }
                    },
                    _ => {
                        a.push((path, d));
                    },
                }
                Ok(())
            }
            let mut a = vec![];
            try!(flatten(&mut a, String::from(""), d));
            Ok(a)
        }

        a.items.into_iter().map(
            |d| {
                let mut d = try!(d.into_document());
                if d.pairs.len() != 1 {
                    Err(Error::MongoCode(16435, String::from("agg pipeline stage spec must have one item in it")))
                } else {
                    let (k, v) = d.pairs.pop().expect("just checked this");
                    match k.as_str() {
                        "$limit" => {
                            Ok(AggOp::Limit(try!(v.numeric_to_i32())))
                        },
                        "$skip" => {
                            Ok(AggOp::Skip(try!(v.numeric_to_i32())))
                        },
                        "$sort" => {
                            Ok(AggOp::Sort(v))
                        },
                        "$out" => {
                            Ok(AggOp::Out(try!(v.into_string())))
                        },
                        "$unwind" => {
                            Ok(AggOp::Unwind(try!(v.into_string())))
                        },
                        "$match" => {
                            let v = try!(v.into_document());
                            let m = try!(matcher::parse_query(v));
                            // TODO it would seem that mongo expects the following error checks to
                            // be done BEFORE parsing the query, and whether the query can
                            // successfully be parsed or not.  jstests/aggregation/bugs/match.js
                            if matcher::uses_where(&m) {
                                return Err(Error::MongoCode(16395, String::from("$where not allowed in agg match")))
                            }
                            if matcher::uses_near(&m) {
                                return Err(Error::MongoCode(16424, String::from("$near not allowed in agg match")))
                            }
                            Ok(AggOp::Match(m))
                        },
                        "$project" => {
                            // flatten so that:
                            // project b:{a:1} should be an inclusion of b.a, not {a:1} as a doc literal for b
                            let args = try!(flatten_projection(v));
                            // TODO is this $ check needed here again?  It's also done in flatten_projection().
                            if args.iter().any(|&(ref k, _)| k.starts_with("$")) {
                                return Err(Error::MongoCode(16404, String::from("16404 $project key begins with $")))
                            }
                            if args.len() == 0 {
                                return Err(Error::MongoCode(16403, String::from("agg $project must output something")));
                            }
                            let (mut id, not_id): (Vec<_>, Vec<_>) = args.into_iter().partition(|&(ref k, _)| k=="_id");
                            if id.len() > 1 {
                                return Err(Error::Misc(String::from("only one id allowed here")))
                            }
                            let id = id.pop();
                            let id_item =
                                match id {
                                    None => {
                                        // if _id is not explicitly excluded (or reset?) it is included
                                        Some((String::from("_id"), AggProj::Include))
                                    },
                                    Some((_,id)) => {
                                        match id {
                                            bson::Value::BInt32(0) 
                                            | bson::Value::BInt64(0) 
                                            | bson::Value::BDouble(0.0)
                                            | bson::Value::BBoolean(false) => {
                                                // explicitly excluded
                                                None
                                            },
                                            _ => {
                                                // _id is being set to an expression
                                                Some((String::from("_id"), AggProj::Expr(try!(Self::parse_expr(id)))))
                                            },
                                        }
                                    },
                                };
                            //println!("id_item: {:?}", id_item);
                            let expressions =
                                not_id.into_iter().map(
                                    |(k,v)| 
                                    if Self::any_part_starts_with_dollar_sign(&k) {
                                        Err(Error::MongoCode(16410, format!("key starts with dollar sign: {}", k)))
                                    } else {
                                        match v {
                                            bson::Value::BInt32(1) 
                                            | bson::Value::BInt64(1) 
                                            | bson::Value::BDouble(1.0)
                                            | bson::Value::BBoolean(true) => Ok((k, AggProj::Include)),
                                            bson::Value::BInt32(0) 
                                            | bson::Value::BInt64(0) 
                                            | bson::Value::BDouble(0.0)
                                            | bson::Value::BBoolean(false) => Err(Error::MongoCode(16406, String::from("agg $project does not support exclude"))),
                                            _ => Ok((k, AggProj::Expr(try!(Self::parse_expr(v))))),
                                        }
                                    }
                                    ).collect::<Result<Vec<_>>>();
                            let mut expressions = try!(expressions);
                            match id_item {
                                Some(id) => {
                                    expressions.insert(0, id);
                                },
                                None => {
                                },
                            }
                            if expressions.len() == 0 {
                                Err(Error::MongoCode(16403, String::from("agg $project must output something")))
                            } else {
                                Ok(AggOp::Project(expressions))
                            }
                        },
                        "$group" => {
                            let mut d = try!(v.into_document());
                            if d.pairs.len() == 0 {
                                Err(Error::Misc(format!("$group requires args")))
                            } else {
                                let (id_k, id) = d.pairs.remove(0);
                                if id_k != "_id" {
                                    Err(Error::Misc(format!("$group requires _id as first arg")))
                                } else {
                                    let accums = try!(d.pairs.into_iter().map(|(k,op)| {
                                        let a = try!(Self::parse_accum(op));
                                        Ok((k, a))
                                    }).collect::<Result<Vec<_>>>());
                                    if accums.iter().any(|&(ref s,_)| s.find('.').is_some()) {
                                        Err(Error::MongoCode(16414, format!("$group does not allow dot in name")))
                                    } else {
                                        let id = try!(Self::parse_expr(id));
                                        Ok(AggOp::Group(id, accums))
                                    }
                                }
                            }
                        },
                        "$redact" => {
                            let e = try!(Self::parse_expr(v));
                            Ok(AggOp::Redact(e))
                        },
                        "$geoNear" => {
                            Err(Error::Misc(format!("agg pipeline TODO: {}", k)))
                        },
                        _ => Err(Error::MongoCode(16436, format!("invalid agg pipeline stage name: {}", k)))
                    }
                }
            }).collect::<Result<Vec<AggOp>>>()
    }

    fn redact_array(a: bson::Array, e: &Expr) -> Result<bson::Value> {
        let mut a2 = bson::Array::new();
        for v in a.items {
            match v {
                bson::Value::BDocument(bd) => {
                    match try!(Self::redact_document(bd, e)) {
                        Some(v) => {
                            a2.push(v);
                        },
                        None => {
                        },
                    }
                },
                bson::Value::BArray(ba) => {
                    let a3 = try!(Self::redact_array(ba, e));
                    a2.push(a3);
                },
                v => {
                    a2.push(v);
                },
            }
        }
        Ok(a2.into_value())
    }

    fn redact_document(doc: bson::Document, e: &Expr) -> Result<Option<bson::Value>> {
        // TODO the clone() in the following line is sad.  but cases below
        // need the document.  should we get it back from CURRENT?  or make
        // a copy just for the purpose of eval() ?
        let ctx = Self::init_eval_ctx(doc.clone().into_value());
        let v = try!(Self::eval(&ctx, &e));
        match v {
            bson::Value::BString(ref s) => {
                match s.as_str() {
                    "__descend__" => {
                        let mut d2 = bson::Document::new();
                        for (k, v) in doc.pairs.into_iter() {
                            match v {
                                bson::Value::BDocument(bd) => {
                                    match try!(Self::redact_document(bd, &e)) {
                                        Some(q) => {
                                            d2.set(&k, q);
                                        },
                                        None => {
                                        },
                                    }
                                },
                                bson::Value::BArray(ba) => {
                                    d2.set(&k, try!(Self::redact_array(ba, e)));
                                },
                                _ => {
                                    d2.set(&k, v);
                                },
                            }
                        }
                        Ok(Some(d2.into_value()))
                    },
                    "__prune__" => {
                        Ok(None)
                    },
                    "__keep__" => {
                        Ok(Some(doc.into_value()))
                    },
                    v => {
                        Err(Error::MongoCode(17053, format!("invalid result from $redact expression: {}", v)))
                    },
                }
            },
            v => {
                Err(Error::MongoCode(17053, format!("invalid result from $redact expression: {:?}", v)))
            },
        }
    }

    fn agg_redact(seq: Box<Iterator<Item=Result<Row>>>, e: Expr) -> Box<Iterator<Item=Result<Row>>> {
        box seq.filter_map(
            move |rr| {
                match rr {
                    Ok(row) => {
                        // TODO I still wish Row.doc was a document
                        let doc = row.doc.into_document().unwrap();
                        match Self::redact_document(doc, &e) {
                            Ok(Some(v)) => {
                                let r2 = Row {
                                    doc: v,
                                    pos: row.pos,
                                    score: row.score,
                                };
                                Some(Ok(r2))
                            },
                            Ok(None) => {
                                None
                            },
                            Err(e) => {
                                Some(Err(e))
                            },
                        }
                    },
                    Err(e) => {
                        Some(Err(e))
                    },
                }
            }
            )
    }

    fn agg_unwind(seq: Box<Iterator<Item=Result<Row>>>, mut path: String) -> Box<Iterator<Item=Result<Row>>> {
        // TODO verify/strip $ in front of path
        path.remove(0);
        box seq.flat_map(
            move |rr| -> Box<Iterator<Item=Result<Row>>> {
                match rr {
                    Ok(row) => {
                        //println!("unwind: {:?}", row);
                        // TODO is hack_like_find_path() what we want?
                        // do we NEED the synthesized array behavior?
                        match row.doc.walk_path(&path).hack_like_find_path() {
                            bson::Value::BUndefined => box std::iter::empty(),
                            bson::Value::BNull => box std::iter::empty(),
                            bson::Value::BArray(a) => {
                                //println!("unwind: {:?}", a);
                                if a.len() == 0 {
                                    box std::iter::empty()
                                } else {
                                    //let row = row.clone();
                                    let unwind = a.items.into_iter().map(|v| -> Result<Row> {
                                        // TODO clone disaster
                                        let mut d = row.doc.clone();
                                        try!(d.set_path(&path, v.clone()));
                                        let r = Row { 
                                            doc: d,
                                            pos: row.pos,
                                            score: row.score,
                                        };
                                        Ok(r)
                                    }).collect::<Vec<_>>();
                                    // TODO it should be possible to do this without collect().
                                    // problem with lifetime of captured row
                                    //box unwind
                                    box unwind.into_iter()
                                    //box std::iter::empty()
                                }
                            },
                            _ => {
                                box std::iter::once(Err(Error::Misc(format!("$unwind requires an array"))))
                            },
                        }
                    },
                    Err(e) => {
                        box std::iter::once(Err(e))
                    },
                }
            }
            )
    }

    fn init_eval_ctx(d: bson::Value) -> bson::Document {
        let mut ctx = bson::Document::new();
        ctx.set("ROOT", d.clone());
        ctx.set("CURRENT", d);
        // TODO use string constants for the stuff below
        ctx.set("DESCEND", bson::Value::BString(String::from("__descend__")));
        ctx.set("PRUNE", bson::Value::BString(String::from("__prune__")));
        ctx.set("KEEP", bson::Value::BString(String::from("__keep__")));
        ctx
    }

    fn do_group(seq: Box<Iterator<Item=Result<Row>>>, id: Expr, ops: Vec<(String,GroupAccum)>) -> Result<HashMap<bson::Value,bson::Document>> {
        let mut mapa = HashMap::new();
        for rr in seq {
            let row = try!(rr);
            let ctx = Self::init_eval_ctx(row.doc);
            let idval = try!(Self::eval(&ctx, &id));
            // to the extent possible, we normalize numeric values here.
            // it appears that mongo converts everything that fits to i32.
            // server9840 and server5209
            let idval = 
                match idval {
                    bson::Value::BInt32(_) => {
                        idval
                    },
                    bson::Value::BInt64(n) => {
                        if i64_can_be_i32(n) {
                            bson::Value::BInt32(n as i32)
                        } else {
                            idval
                        }
                    },
                    bson::Value::BDouble(f) => {
                        if f64_can_be_i32(f) {
                            bson::Value::BInt32(f as i32)
                        } else {
                            idval
                        }
                    },
                    _ => {
                        idval
                    },
                };
            // TODO avoid clone() in following line
            let acc = match mapa.entry(idval.clone()) {
                std::collections::hash_map::Entry::Vacant(e) => {
                    let mut d = bson::Document::new();
                    d.set("_id", idval);
                    e.insert(d)
                },
                std::collections::hash_map::Entry::Occupied(e) => {
                    e.into_mut()
                },
            };
            for &(ref k, ref op) in ops.iter() {
                //println!("group: k = {}", k);
                //println!("group: op = {:?}", op);
                match op {
                    &GroupAccum::First(ref e) => {
                        let v = try!(Self::eval(&ctx, &e));
                        match try!(acc.entry(k)) {
                            bson::Entry::Found(_) => {
                                // do nothing
                            },
                            bson::Entry::Absent(e) => {
                                try!(e.insert(v));
                            },
                        }
                    },
                    &GroupAccum::Last(ref e) => {
                        let v = try!(Self::eval(&ctx, &e));
                        // TODO shouldn't this be entry?  can k be a path with dots?
                        acc.set(k, v);
                    },
                    &GroupAccum::Max(ref e) => {
                        let v = try!(Self::eval(&ctx, &e));
                        match try!(acc.entry(k)) {
                            bson::Entry::Found(e) => {
                                if Ordering::Greater == matcher::cmp(&v, e.get()) {
                                    e.replace(v);
                                }
                            },
                            bson::Entry::Absent(e) => {
                                try!(e.insert(v));
                            },
                        }
                    },
                    &GroupAccum::Min(ref e) => {
                        let v = try!(Self::eval(&ctx, &e));
                        match try!(acc.entry(k)) {
                            bson::Entry::Found(e) => {
                                if Ordering::Less == matcher::cmp(&v, e.get()) {
                                    e.replace(v);
                                }
                            },
                            bson::Entry::Absent(e) => {
                                try!(e.insert(v));
                            },
                        }
                    },
                    &GroupAccum::Push(ref e) => {
                        let v = try!(Self::eval(&ctx, &e));
                        match try!(acc.entry(k)) {
                            bson::Entry::Found(mut e) => {
                                let mut a = e.get_mut();
                                match a {
                                    &mut bson::Value::BArray(ref mut a) => {
                                        a.items.push(v);
                                    },
                                    _ => {
                                        unreachable!();
                                    },
                                }
                            },
                            bson::Entry::Absent(e) => {
                                let mut a = bson::Array::new();
                                a.items.push(v);
                                try!(e.insert(bson::Value::BArray(a)));
                            },
                        }
                    },
                    &GroupAccum::AddToSet(ref e) => {
                        return Err(Error::Misc(format!("TODO AddToSet: {:?}", e)))
                    },
                    &GroupAccum::Avg(ref e) => {
                        let v = try!(Self::eval(&ctx, &e));
                        match v.numeric_to_f64() {
                            Ok(v) => {
                                match try!(acc.entry(k)) {
                                    bson::Entry::Found(mut e) => {
                                        let mut pair = e.get_mut();
                                        match pair {
                                            &mut bson::Value::BDocument(ref mut pair) => {
                                                let count = pair.get("count").unwrap().i32_or_panic();
                                                pair.set_i32("count", 1 + count);
                                                let sum = pair.get("sum").unwrap().f64_or_panic();
                                                pair.set_f64("sum", v + sum);
                                            },
                                            _ => {
                                                unreachable!();
                                            },
                                        }
                                    },
                                    bson::Entry::Absent(e) => {
                                        let mut pair = bson::Document::new();
                                        pair.set_i32("count", 1);
                                        pair.set_f64("sum", v);
                                        try!(e.insert(bson::Value::BDocument(pair)));
                                    },
                                }
                            },
                            Err(_) => {
                                // ignore this
                            },
                        }
                    },
                    &GroupAccum::Sum(ref e) => {
                        let v = try!(Self::eval(&ctx, &e));
                        // TODO always double?
                        let v = try!(v.numeric_to_f64());
                        match try!(acc.entry(k)) {
                            bson::Entry::Found(e) => {
                                let cur = try!(e.get().numeric_to_f64());
                                e.replace(bson::Value::BDouble(cur + v));
                            },
                            bson::Entry::Absent(e) => {
                                try!(e.insert(bson::Value::BDouble(v)));
                            },
                        }
                    },
                }
            }
        }
        for &(ref k, ref op) in ops.iter() {
            match op {
                &GroupAccum::Avg(_) => {
                    for (_,ref mut acc) in mapa.iter_mut() {
                        let (count,sum) = {
                            let pair = acc.get(k).unwrap().as_document_or_panic();
                            let count = pair.get("count").unwrap().i32_or_panic();
                            let sum = pair.get("sum").unwrap().f64_or_panic();
                            (count,sum)
                            };
                        acc.set_f64(k, sum / (count as f64));
                    }
                },
                _ => {
                    // nothing to do otherwise
                },
            }
        }
        //println!("grouped: {:?}", mapa);
        Ok(mapa)
    }

    fn compare_values_at_path(a: &bson::Value, b: &bson::Value, path: &str, backward: bool) -> Ordering {
        let null = bson::Value::BNull;

        // TODO what is this supposed to do if the path yields multiple values?  error?
        // zip?  what if the two iterators are different lengths?
        // for now, we just call next() on the iterator and use the first value.

        // TODO it is possible for leaves() to result in nothing.  unfortunately.  so
        // for now, we add an extra unwrap_or(&null) after .next()

        // TODO it would be nice to wrap the following long line in a function, but
        // the lifetime of the return value is unknown.  sometimes it returns a reference
        // to our special local 'null'

        let va = a.walk_path(path).leaves().map(|leaf| leaf.v.unwrap_or(&null)).next().unwrap_or(&null);
        let vb = b.walk_path(path).leaves().map(|leaf| leaf.v.unwrap_or(&null)).next().unwrap_or(&null);

        let c = matcher::cmpdir(va, vb, backward);
        c
/*
For server6125 (agg sort), the following code seems a little
more correct than the cmpdir line above.  The agg notion of
sort is apparently different from the orderby with find().
The latter does the "sort arrays by their first element"
trick, but agg sort apparently does not.

Nonetheless, even with the following, server6125 still doesn't
pass because of the DBPointer entry, which is arriving to Elmo
looking EXACTLY like a plain objectid entry.

        let c = matcher::cmp(va, vb);
        if backward {
            c.reverse()
        } else {
            c
        }
*/
    }

    fn do_sort_docs(a: &mut Vec<bson::Value>, orderby: &bson::Value) -> Result<()> {
        let keys =
            match orderby {
                &bson::Value::BDocument(ref bd) => {
                    // TODO it would be nice to do this with map()
                    let mut a = vec![];
                    for &(ref path, ref dir) in &bd.pairs {
                        let n = try!(dir.numeric_to_i32());
                        if n == 0 {
                            return Err(Error::Misc(String::from("sort dir cannot be 0")));
                        }
                        a.push((path, n<0));
                    }
                    a
                },
                _ => {
                    return Err(Error::Misc(String::from("orderby must be a document")));
                },
            };
        a.sort_by(|a,b| -> Ordering {
            for &(ref path, dir) in keys.iter() {
                let c = Self::compare_values_at_path(a, b, path, dir);
                if c != Ordering::Equal {
                    return c;
                }
            }
            Ordering::Equal
        });
        Ok(())
    }

    fn do_sort(a: &mut Vec<Row>, orderby: &bson::Value) -> Result<()> {
        #[derive(Copy,Clone)]
        enum SortType {
            Compare(bool),
            TextScore,
        };

        let keys =
            match orderby {
                &bson::Value::BDocument(ref bd) => {
                    // TODO it would be nice to do this with map()
                    let mut a = vec![];
                    for &(ref path, ref dir) in &bd.pairs {
                        if dir.is_numeric() {
                            let n = try!(dir.numeric_to_i32());
                            if n == 0 {
                                return Err(Error::Misc(String::from("sort dir cannot be 0")));
                            }
                            a.push((path, SortType::Compare(n < 0)));
                        } else if dir.is_document() {
                            let dir = dir.as_document().unwrap();
                            if dir.len() != 1 {
                                return Err(Error::Misc(format!("sort dir invalid: {:?}", dir)));
                            } else if dir.pairs[0].0 != "$meta" {
                                return Err(Error::Misc(format!("sort dir invalid: {:?}", dir)));
                            } else if !dir.pairs[0].1.is_string() {
                                return Err(Error::Misc(format!("sort dir invalid: {:?}", dir)));
                            } else if dir.pairs[0].1.as_str().unwrap() != "textScore" {
                                return Err(Error::Misc(format!("sort dir invalid: {:?}", dir)));
                            } else {
                                a.push((path, SortType::TextScore));
                            }
                        } else {
                            return Err(Error::Misc(format!("sort dir invalid: {:?}", dir)));
                        }
                    }
                    a
                },
                _ => {
                    return Err(Error::Misc(String::from("orderby must be a document")));
                },
            };

        a.sort_by(|a,b| -> Ordering {
            for &(ref path, dir) in keys.iter() {
                match dir {
                    SortType::Compare(backward) => {
                        let c = Self::compare_values_at_path(&a.doc, &b.doc, path, backward);
                        if c != Ordering::Equal {
                            return c;
                        }
                    },
                    SortType::TextScore => {
                        if a.score.is_none() || b.score.is_none() {
                            println!("TODO score is missing");
                        } else {
                            let sa = a.score.unwrap();
                            let sb = b.score.unwrap();
                            if sb < sa {
                                return Ordering::Less;
                            } else if sb > sa {
                                return Ordering::Greater;
                            } else {
                                // Ordering::Equal
                            }
                        }
                    },
                }
            }
            Ordering::Equal
        });
        Ok(())
    }

    fn agg_group(seq: Box<Iterator<Item=Result<Row>>>, id: Expr, ops: Vec<(String,GroupAccum)>) -> Box<Iterator<Item=Result<Row>>> {
        match Self::do_group(seq, id, ops) {
            Ok(mapa) => {
                box mapa.into_iter().map(|(_,v)| {
                    let row = Row {
                        doc: bson::Value::BDocument(v),
                        pos: None,
                        score: None,
                    };
                    Ok(row)
                })
            },
            Err(e) => {
                box std::iter::once(Err(e))
            },
        }
    }

    fn guts_matcher_filter_map(rr: Result<Row>, m: &matcher::QueryDoc) -> Option<Result<Row>> {
                    println!("at {}:{}", file!(), line!());
        match rr {
            Ok(row) => {
                    println!("at {}:{}", file!(), line!());
                //println!("looking at row: {:?}", row);
                //println!("matcher is: {:?}", m);
                let (b, pos) = matcher::match_query(&m, &row.doc);
                    println!("at {}:{}", file!(), line!());
                if b {
                    //println!("    matched");
                    println!("at {}:{}", file!(), line!());
                    let r = Row {
                        doc: row.doc,
                        pos: pos,
                        score: row.score,
                    };
                    println!("at {}:{}", file!(), line!());
                    Some(Ok(r))
                } else {
                    //println!("    no");
                    println!("at {}:{}", file!(), line!());
                    None
                }
            },
            Err(e) => {
                    println!("at {}:{}", file!(), line!());
                Some(Err(e))
            },
        }
    }

    fn seq_project(seq: Box<Iterator<Item=Result<Row>>>, proj: Projection) -> Box<Iterator<Item=Result<Row>>> {
        box seq.map(
            move |rr| {
                match rr {
                    Ok(row) => {
                        proj.project(row)
                    },
                    Err(e) => Err(e),
                }
            }
            )
    }

    fn seq_match(seq: Box<Iterator<Item=Result<Row>>>, m: matcher::QueryDoc) -> Box<Iterator<Item=Result<Row>>> {
        box seq.filter_map(move |r| Self::guts_matcher_filter_map(r, &m))
    }

    fn seq_match_ref<'a>(seq: Box<Iterator<Item=Result<Row>>>, m: &'a matcher::QueryDoc) -> Box<Iterator<Item=Result<Row>> + 'a> {
        box seq.filter_map(move |r| Self::guts_matcher_filter_map(r, m))
    }

    fn agg_project(seq: Box<Iterator<Item=Result<Row>>>, expressions: Vec<(String,AggProj)>) -> Box<Iterator<Item=Result<Row>>> {
        // TODO would it be possible to parse these expressions into a Projection object
        // and re-use the other project code for this case as well?
        box seq.map(
            move |rr| {
                match rr {
                    Ok(mut row) => {
                        let mut d = bson::Document::new();
                        let ctx = Self::init_eval_ctx(row.doc);
                        for &(ref path, ref op) in expressions.iter() {
                            match op {
                                &AggProj::Expr(ref e) => {
                                    //println!("e: {:?}", e);
                                    let v = try!(Self::eval(&ctx, e));
                                    //println!("v: {:?}", v);
                                    match try!(d.entry(path)) {
                                        bson::Entry::Found(_) => {
                                            return Err(Error::Misc(format!("16400 already: {}", path)))
                                        },
                                        bson::Entry::Absent(e) => {
                                            if !v.is_undefined() {
                                                try!(e.insert(v));
                                            }
                                        },
                                    }
                                },
                                &AggProj::Include => {
                                    // TODO this code probably expects that if it tries to project
                                    // something that is already present it will error.  not sure
                                    // walk.project() does that exactly how this code wants it.
                                    let walk = try!(ctx.must_get_document("CURRENT")).walk_path(path);
                                    try!(walk.project(&mut d));
                                },
                            }
                        }
                        row.doc = d.into_value();
                        Ok(row)
                    },
                    Err(e) => Err(e),
                }
            }
            )
    }

    pub fn aggregate(&self,
                db: &str,
                coll: &str,
                pipeline: bson::Array
                ) 
        -> Result<(Option<String>, Box<Iterator<Item=Result<Row>> + 'static>)>
    {
        let ops = try!(Self::parse_agg(pipeline));
        // TODO check for plan
        let plan = None;
        let reader = try!(self.conn.begin_read());
        let mut seq: Box<Iterator<Item=Result<Row>>> = try!(Self::into_collection_reader(reader, db, coll, plan));
        let mut out = None;
        for op in ops {
            match op {
                AggOp::Skip(n) => {
                    seq = box seq.skip(n as usize);
                },
                AggOp::Limit(n) => {
                    seq = box seq.take(n as usize);
                },
                AggOp::Match(m) => {
                    seq = Self::seq_match(seq, m);
                },
                AggOp::Sort(ref orderby) => {
                    let mut a = try!(seq.collect::<Result<Vec<_>>>());
                    try!(Self::do_sort(&mut a, orderby));
                    seq = box a.into_iter().map(|d| Ok(d))
                },
                AggOp::Project(expressions) => {
                    seq = Self::agg_project(seq, expressions);
                },
                AggOp::Group(id, ops) => {
                    seq = Self::agg_group(seq, id, ops);
                },
                AggOp::Unwind(path) => {
                    seq = Self::agg_unwind(seq, path);
                },
                AggOp::Redact(e) => {
                    seq = Self::agg_redact(seq, e);
                },
                AggOp::Out(s) => {
                    out = Some(s);
                },
                AggOp::GeoNear(_) => {
                    return Err(Error::Misc(format!("agg pipeline TODO: {:?}", op)))
                },
            }
        }
        Ok((out, seq))
    }

    pub fn distinct(&self, db: &str, coll: &str, key: &str, query: bson::Document) -> Result<bson::Array> {
        let reader = try!(self.conn.begin_read());
        // TODO dry
        let indexes = try!(reader.list_indexes()).into_iter().filter(
            |ndx| ndx.db == db && ndx.coll == coll
            ).collect::<Vec<_>>();
        //println!("indexes: {:?}", indexes);
        let m = try!(matcher::parse_query(query));
        let plan = try!(Self::choose_index(&indexes, &m, None));
        //println!("plan: {:?}", plan);
        let seq: Box<Iterator<Item=Result<Row>>> = try!(Self::get_collection_reader_r(&*reader, db, coll, plan));
        // TODO we shadow-let here because the type from seq_match_ref() doesn't match the original
        // type because of its explicit lifetime.
        let seq = Self::seq_match_ref(seq, &m);
        let mut results = HashSet::new();
        for rr in seq {
            let row = try!(rr);
            for leaf in row.doc.walk_path(key).leaves() {
                match leaf.v {
                    Some(v) => {
                        results.insert(v.clone());
                    },
                    None => {
                    },
                }
            }
        }
        let mut a = bson::Array::new();
        for v in results {
            a.push(v);
        }
        Ok(a)
    }

    pub fn find(&self,
                db: &str,
                coll: &str,
                query: bson::Document,
                orderby: Option<bson::Value>,
                projection: Option<bson::Document>,
                min: Option<bson::Value>,
                max: Option<bson::Value>,
                hint: Option<bson::Value>,
                // TODO explain is never used in latest wire protocol
                explain: Option<bson::Value>
                ) 
        -> Result<Box<Iterator<Item=Result<Row>> + 'static>>
    {
        let reader = try!(self.conn.begin_read());
        // TODO DRY
        let indexes = try!(reader.list_indexes()).into_iter().filter(
            |ndx| ndx.db == db && ndx.coll == coll
            ).collect::<Vec<_>>();
        // TODO maybe we should get normalized index specs for all the indexes now.
        let m = try!(matcher::parse_query(query));
        fn is_hint_natural(v: &bson::Value) -> bool {
            match v {
                &bson::Value::BDocument(ref bd) => {
                    if bd.pairs.len() == 1 && bd.pairs[0].0 == "$natural" {
                        return true;
                    } else {
                        return false;
                    }
                },
                _ => false,
            }
        }
        let (natural, hint) = 
            match hint {
                Some(ref v) => {
                    if is_hint_natural(v) {
                        (true, None)
                    } else {
                        if let Some(ndx) = Self::try_find_index_by_name_or_spec(&indexes, v) {
                            (false, Some(ndx))
                        } else {
                            return Err(Error::Misc(format!("bad hint: {:?}", v)));
                        }
                    }
                },
                None => (false, None),
            };
        let min = match min {
            Some(v) => {
                let v = try!(v.into_document());
                Some(try!(matcher::parse_query(v)))
            },
            None => {
                None
            },
        };
        let max = match max {
            Some(v) => {
                let v = try!(v.into_document());
                Some(try!(matcher::parse_query(v)))
            },
            None => {
                None
            },
        };
        let mut seq = {
            let plan =
                // unless we're going to add comparisons to the query,
                // the bounds for min/max need to be precise, since the matcher isn't
                // going to help if they're not.  min is inclusive.  max is
                // exclusive.
                match (&min, &max) {
                    (&None, &None) => {
                        if natural {
                            None
                        } else {
                            try!(Self::choose_index(&indexes, &m, hint))
                        }
                    },
                    (min, max) => {
                        // TODO if natural, then fail?
                        fn copy_dirs_from_normspec_to_vals<'a>(normspec: &Vec<(String, IndexType)>, vals: Vec<&'a bson::Value>) -> Vec<(&'a bson::Value, bool)> {
                            // TODO if normspec.len() < vals.len() then panic?
                            // TODO zip?
                            let mut a = Vec::new();
                            for (i,v) in vals.into_iter().enumerate() {
                                let neg = normspec[i].1 == IndexType::Backward;
                                a.push((v, neg));
                            }
                            a
                        }

                        let pair =
                            match (min, max) {
                                (&None, &None) => {
                                    // we handled this case above
                                    unreachable!();
                                },
                                (&Some(ref min), &Some(ref max)) => {
                                    let min = try!(Self::parse_index_min_max(min));
                                    let max = try!(Self::parse_index_min_max(max));
                                    if min.len() != max.len() {
                                        return Err(Error::Misc(String::from("min/max hints must be same length")));
                                    }
                                    let (minkeys, minvals): (Vec<_>, Vec<_>) = min.into_iter().unzip();
                                    let (maxkeys, maxvals): (Vec<_>, Vec<_>) = max.into_iter().unzip();
                                    // TODO minkeys must == maxkeys
                                    match try!(Self::find_index_for_min_max(&indexes, &minkeys)) {
                                        Some(ndx) => {
                                            // TODO the following is way too heavy.  all we need is the index types
                                            // so we can tell if they're supposed to be backwards or not.
                                            let (normspec, _) = try!(get_normalized_spec(ndx));
                                            let minvals = copy_dirs_from_normspec_to_vals(&normspec, minvals);
                                            let maxvals = copy_dirs_from_normspec_to_vals(&normspec, maxvals);
                                            let bounds = QueryBounds::GTE_LT(vec![], minvals, maxvals);
                                            (ndx, bounds)
                                        },
                                        None => {
                                            return Err(Error::Misc(String::from("index not found. TODO should be None?")));
                                        },
                                    }
                                },
                                (&Some(ref min), &None) => {
                                    let min = try!(Self::parse_index_min_max(min));
                                    let (keys, minvals): (Vec<_>, Vec<_>) = min.into_iter().unzip();
                                    match try!(Self::find_index_for_min_max(&indexes, &keys)) {
                                        Some(ndx) => {
                                            // TODO the following is way too heavy.  all we need is the index types
                                            // so we can tell if they're supposed to be backwards or not.
                                            let (normspec, _) = try!(get_normalized_spec(ndx));
                                            let minvals = copy_dirs_from_normspec_to_vals(&normspec, minvals);
                                            let bounds = QueryBounds::GTE(minvals);
                                            (ndx, bounds)
                                        },
                                        None => {
                                            return Err(Error::Misc(String::from("index not found. TODO should be None?")));
                                        },
                                    }
                                },
                                (&None, &Some(ref max)) => {
                                    let max = try!(Self::parse_index_min_max(max));
                                    let (keys, maxvals): (Vec<_>, Vec<_>) = max.into_iter().unzip();
                                    match try!(Self::find_index_for_min_max(&indexes, &keys)) {
                                        Some(ndx) => {
                                            // TODO the following is way too heavy.  all we need is the index types
                                            // so we can tell if they're supposed to be backwards or not.
                                            let (normspec, _) = try!(get_normalized_spec(ndx));
                                            let maxvals = copy_dirs_from_normspec_to_vals(&normspec, maxvals);
                                            let bounds = QueryBounds::LT(maxvals);
                                            (ndx, bounds)
                                        },
                                        None => {
                                            return Err(Error::Misc(String::from("index not found. TODO should be None?")));
                                        },
                                    }
                                },
                            };

                        // TODO tests indicate that if there is a $min and/or $max as well as a $hint,
                        // then we need to error if they don't match each other.

                        let plan = QueryPlan::Regular(&pair.0, pair.1);
                        Some(plan)
                    }
                };

            let seq: Box<Iterator<Item=Result<Row>>> = try!(Self::into_collection_reader(reader, db, coll, plan));
            seq
        };
        seq = Self::seq_match(seq, m);
        match orderby {
            Some(ref orderby) => {
                let mut a = try!(seq.collect::<Result<Vec<_>>>());
                try!(Self::do_sort(&mut a, orderby));
                seq = box a.into_iter().map(|d| Ok(d))
            },
            None => {
            },
        }
        match projection {
            Some(projection) => {
                let projection = try!(Projection::parse(projection));
                seq = Self::seq_project(seq, projection);
            },
            None => {
            },
        }
        Ok(seq)
    }
}

