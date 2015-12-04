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
#![feature(iter_arith)]

use std::collections::BTreeMap;
use std::collections::HashMap;

extern crate lsm;
use lsm::ICursor;
use lsm::IForwardCursor;

extern crate rand;
use rand::Rng;
use rand::SeedableRng;

fn dump_page(name: &str, pgnum: u32) -> Result<(),lsm::Error> {
    let db = try!(lsm::DatabaseFile::new(String::from(name), lsm::DEFAULT_SETTINGS));
    let page = try!(db.get_page(pgnum));
    println!("{:?}", page);
    Ok(())
}

fn show_page(name: &str, pgnum: u32) -> Result<(),lsm::Error> {
    let db = try!(lsm::DatabaseFile::new(String::from(name), lsm::DEFAULT_SETTINGS));
    let cursor = try!(db.open_cursor_on_page(pgnum));
    let pt = cursor.page_type();
    println!("page type: {:?}", pt);
    // TODO
    Ok(())
}

fn show_leaf_page(name: &str, pgnum: u32) -> Result<(),lsm::Error> {
    let db = try!(lsm::DatabaseFile::new(String::from(name), lsm::DEFAULT_SETTINGS));
    let mut cursor = try!(db.open_cursor_on_leaf_page(pgnum));
    try!(cursor.First());
    while cursor.IsValid() {
        {
            let k = try!(cursor.KeyRef());
            println!("k: {:?}", k);
            let v = try!(cursor.ValueRef());
            println!("v: {:?}", v);
            //let q = try!(v.into_boxed_slice());
        }
        try!(cursor.Next());
    }
    Ok(())
}

fn graph_parent_page(name: &str, pgnum: u32, depth: u8) -> Result<(),lsm::Error> {
    let db = try!(lsm::DatabaseFile::new(String::from(name), lsm::DEFAULT_SETTINGS));
    let page = try!(db.read_parent_page(pgnum));
    {
        let it = page.into_node_iter(depth);

        println!("digraph {} {{", pgnum);
        for r in it {
            let nd = try!(r);
            match nd.parent {
                Some(parent) => {
                    println!("{} -> {};", parent, nd.page);
                },
                None => {
                },
            }
        }
        println!("}}");
    }
    Ok(())
}

fn show_parent_page(name: &str, pgnum: u32) -> Result<(),lsm::Error> {
    let db = try!(lsm::DatabaseFile::new(String::from(name), lsm::DEFAULT_SETTINGS));
    let page = try!(db.read_parent_page(pgnum));
    println!("depth: {}", page.depth());
    //println!("count_items: {}", page.count_items());
    //let blocks = try!(page.blocklist_clean());
    //println!("blocks ({} blocks, {} pages): {:?}", blocks.count_blocks(), blocks.count_pages(), blocks);
    //println!("blocks ({} blocks, {} pages)", blocks.count_blocks(), blocks.count_pages());
    //println!("key range: {:?}", try!(page.range()));
    let count = page.count_items();
    //if cfg!(expensive_check) 
    {
        println!("items ({}):", count);
        for i in 0 .. count {
            let p = page.child_pagenum(i);
            println!("    {}", p);
            let child_key = try!(page.child_key(i));
            println!("        {:?}", child_key);
        }
        //try!(page.verify_child_keys());
    }
    //if cfg!(expensive_check) 
    {
        let mut stats = HashMap::new();
        let page = try!(db.read_parent_page(pgnum));
        let mut leaf = page.make_leaf_page();
        let mut parent = page.make_parent_page();
        let it = page.into_node_iter(0);

        #[derive(Debug)]
        struct Stats {
            count_nodes: usize,
            count_items: usize,
            len: usize,
        }

        for r in it {
            let nd = try!(r);
            let (count_items, len) =
                if nd.depth == 0 {
                    try!(leaf.read_page(nd.page));
                    let count_items = leaf.count_keys();
                    let len = leaf.len_on_page();
                    (count_items, len)
                } else {
                    try!(parent.read_page(nd.page));
                    let count_items = parent.count_items();
                    let len = parent.len_on_page();
                    (count_items, len)
                };
            match stats.entry(nd.depth) {
                std::collections::hash_map::Entry::Vacant(e) => {
                    let v = Stats {
                        count_nodes: 1,
                        count_items: count_items,
                        len: len,
                    };
                    e.insert(v);
                },
                std::collections::hash_map::Entry::Occupied(mut e) => {
                    let st = e.get_mut();
                    st.count_nodes += 1;
                    st.count_items += count_items;
                    st.len += len;
                },
            }
        }
        let mut depth = 0;
        loop {
            match stats.get(&depth) {
                Some(stats) => {
                    println!("Depth {}:", depth);
                    println!("    {} nodes", stats.count_nodes);
                    println!("    {} items per node", stats.count_items / stats.count_nodes);
                    println!("    {} len per node", stats.len / stats.count_nodes);
                },
                None => {
                    break;
                },
            }
            depth += 1;
        }
        //println!("stats: {:?}", stats);
    }
    Ok(())
}

fn list_segments(name: &str) -> Result<(),lsm::Error> {
    let db = try!(lsm::DatabaseFile::new(String::from(name), lsm::DEFAULT_SETTINGS));
    let (fresh, young, levels) = try!(db.list_segments());
    println!("fresh ({}): ", fresh.len());

    fn print_seg(s: &lsm::SegmentLocation) {
        println!("    {}, {} pages", s.root_page, 1 + s.blocks.count_pages());
    }

    for s in fresh.iter() {
        //print_seg(s);
        println!("    {:?}", s);
    }
    println!("young ({}): ", young.len());
    for s in young.iter() {
        //print_seg(s);
        println!("    {:?}", s);
    }
    println!("levels ({}): ", levels.len());
    for s in levels.iter() {
        //print_seg(s);
        println!("    {:?}", s);
    }
    Ok(())
}

fn list_free_blocks(name: &str) -> Result<(),lsm::Error> {
    let db = try!(lsm::DatabaseFile::new(String::from(name), lsm::DEFAULT_SETTINGS));
    let blocks = try!(db.list_free_blocks());
    //println!("{:?}", blocks);
    println!("count_blocks: {}", blocks.count_blocks());
    println!("count_pages: {}", blocks.count_pages());
    //println!("pages in largest block: {}", blocks.blocks[0].count_pages());
    Ok(())
}

fn list_keys(name: &str) -> Result<(),lsm::Error> {
    let db = try!(lsm::DatabaseFile::new(String::from(name), lsm::DEFAULT_SETTINGS));
    let mut cursor = try!(db.open_cursor());
    try!(cursor.First());
    while cursor.IsValid() {
        {
            let k = try!(cursor.KeyRef());
            println!("k: {:?}", k);
            let v = try!(cursor.LiveValueRef());
            //println!("v: {:?}", v);
            //let q = try!(v.into_boxed_slice());
        }
        try!(cursor.Next());
    }
    Ok(())
}

fn list_keys_as_strings(name: &str) -> Result<(),lsm::Error> {
    let db = try!(lsm::DatabaseFile::new(String::from(name), lsm::DEFAULT_SETTINGS));
    let mut cursor = try!(db.open_cursor());
    try!(cursor.First());
    while cursor.IsValid() {
        {
            let k = try!(cursor.KeyRef());
            let k = k.into_boxed_slice();
            let s = try!(std::str::from_utf8(&k));
            println!("{}", s);
        }
        try!(cursor.Next());
    }
    Ok(())
}

fn seek_string(name: &str, key: String, sop: String) -> Result<(),lsm::Error> {
    let sop = 
        match sop.as_str() {
            "eq" => lsm::SeekOp::SEEK_EQ,
            "le" => lsm::SeekOp::SEEK_LE,
            "ge" => lsm::SeekOp::SEEK_GE,
            _ => return Err(lsm::Error::Misc(String::from("invalid sop"))),
        };
    let k = key.into_bytes().into_boxed_slice();
    let k = lsm::KeyRef::from_boxed_slice(k);
    let db = try!(lsm::DatabaseFile::new(String::from(name), lsm::DEFAULT_SETTINGS));
    let mut cursor = try!(db.open_cursor());
    let sr = try!(cursor.SeekRef(&k, sop));
    println!("sr: {:?}", sr);
    if cursor.IsValid() {
        {
            let k = try!(cursor.KeyRef());
            println!("k: {:?}", k);
            let v = try!(cursor.LiveValueRef());
            println!("v: {:?}", v);
        }
    }
    Ok(())
}

fn seek_bytes(name: &str, k: Box<[u8]>, sop: String) -> Result<(),lsm::Error> {
    let sop = 
        match sop.as_str() {
            "eq" => lsm::SeekOp::SEEK_EQ,
            "le" => lsm::SeekOp::SEEK_LE,
            "ge" => lsm::SeekOp::SEEK_GE,
            _ => return Err(lsm::Error::Misc(String::from("invalid sop"))),
        };
    let k = lsm::KeyRef::from_boxed_slice(k);
    let db = try!(lsm::DatabaseFile::new(String::from(name), lsm::DEFAULT_SETTINGS));
    let mut cursor = try!(db.open_cursor());
    let sr = try!(cursor.SeekRef(&k, sop));
    println!("RESULT sr: {:?}", sr);
    if cursor.IsValid() {
        {
            let k = try!(cursor.KeyRef());
            println!("k: {:?}", k);
            let v = try!(cursor.LiveValueRef());
            println!("v: {:?}", v);
        }
        for x in 0 .. 20 {
            try!(cursor.Next());
            if cursor.IsValid() {
                let k = try!(cursor.KeyRef());
                println!("    k: {:?}", k);
                let v = try!(cursor.LiveValueRef());
                println!("    v: {:?}", v);
            } else {
                break;
            }
        }
    }
    Ok(())
}

fn add_numbers(name: &str, count: u64, start: u64, step: u64) -> Result<(),lsm::Error> {
    let mut pending = BTreeMap::new();
    for i in 0 .. count {
        let val = start + i * step;
        let k = format!("{:08}", val).into_bytes().into_boxed_slice();
        let v = format!("{}", val).into_bytes().into_boxed_slice();
        pending.insert(k, lsm::Blob::Boxed(v));
    }
    let db = try!(lsm::DatabaseFile::new(String::from(name), lsm::DEFAULT_SETTINGS));
    let seg = try!(db.write_segment(pending).map_err(lsm::wrap_err));
    if let Some(seg) = seg {
        let lck = try!(db.get_write_lock());
        try!(lck.commit_segment(seg).map_err(lsm::wrap_err));
    }
    Ok(())
}

fn add_lines(name: &str, file: String, count_groups: usize, count_per_group: usize) -> Result<(),lsm::Error> {
    use std::io::{self, BufReader};
    use std::io::prelude::*;
    use std::fs::File;

    let db = try!(lsm::DatabaseFile::new(String::from(name), lsm::DEFAULT_SETTINGS));

    let f = try!(File::open(&file));
    let f = BufReader::new(f);

    let mut num_groups_sofar = 0;
    let mut num_in_group = 0;

    let mut pending = BTreeMap::new();
    for line in f.lines() {
        let line = try!(line);
        num_in_group += 1;
        let k = line.into_bytes().into_boxed_slice();
        if k.len() > 0 {
            let v = String::from("").into_bytes().into_boxed_slice();
            pending.insert(k, lsm::Blob::Boxed(v));
        }
        if num_in_group >= count_per_group {
            let seg = try!(db.write_segment(pending).map_err(lsm::wrap_err));
            if let Some(seg) = seg {
                let lck = try!(db.get_write_lock());
                try!(lck.commit_segment(seg).map_err(lsm::wrap_err));
                //println!("commited group");
            }
            pending = BTreeMap::new();
            num_in_group = 0;
            num_groups_sofar += 1;
            if num_groups_sofar == count_groups {
                break;
            }
        }
    }

    match std::sync::Arc::try_unwrap(db) {
        Ok(db) => {
            try!(db.stop());
            Ok(())
        },
        Err(e) => {
            Err(lsm::Error::Misc(String::from("try_unwrap failed")))
        },
    }
}

fn sqlite_lines(name: &str, file: String, count_groups: usize, count_per_group: usize) -> Result<(),lsm::Error> {
    use std::io::{self, BufReader};
    use std::io::prelude::*;
    use std::fs::File;
    extern crate sqlite3;

    let access = sqlite3::access::ByFilename { flags: sqlite3::access::flags::OPEN_READWRITE | sqlite3::access::flags::OPEN_CREATE, filename: name};
    let db = try!(sqlite3::DatabaseConnection::new(access).map_err(lsm::wrap_err));

    try!(db.exec("BEGIN IMMEDIATE TRANSACTION").map_err(lsm::wrap_err));
    // TODO this should use WITHOUT_ROWID
    try!(db.exec("CREATE TABLE lines (s BLOB PRIMARY KEY)").map_err(lsm::wrap_err));
    try!(db.exec("COMMIT TRANSACTION").map_err(lsm::wrap_err));

    let mut stmt = try!(db.prepare("INSERT OR IGNORE INTO lines (s) VALUES (?)").map_err(lsm::wrap_err));

    let f = try!(File::open(&file));
    let f = BufReader::new(f);

    let mut num_groups_sofar = 0;
    let mut num_in_group = 0;

    try!(db.exec("BEGIN IMMEDIATE TRANSACTION").map_err(lsm::wrap_err));
    for line in f.lines() {
        let line = try!(line);
        num_in_group += 1;
        let k = line.into_bytes().into_boxed_slice();
        if k.len() > 0 {
            stmt.clear_bindings();
            try!(stmt.bind_blob(1, &k).map_err(lsm::wrap_err));
            try!(stmt.step().map_err(lsm::wrap_err));
            stmt.reset();
        }
        if num_in_group >= count_per_group {
            try!(db.exec("COMMIT TRANSACTION").map_err(lsm::wrap_err));
            num_groups_sofar += 1;
            num_in_group = 0;
            if num_groups_sofar == count_groups {
                break;
            }
            try!(db.exec("BEGIN IMMEDIATE TRANSACTION").map_err(lsm::wrap_err));
        }
    }
    Ok(())
}

fn add_random(name: &str, seed: usize, count_groups: usize, count_per_group: usize, klen: usize, vlen: usize) -> Result<(),lsm::Error> {
    fn make(rng: &mut rand::StdRng, max_len: usize) -> Box<[u8]> {
        let len = (rng.next_u64() as usize) % max_len + 1;
        let mut k = vec![0u8; len].into_boxed_slice();
        rng.fill_bytes(&mut k);
        k
    }

    let mut rng = rand::StdRng::from_seed(&[seed]);
    let db = try!(lsm::DatabaseFile::new(String::from(name), lsm::DEFAULT_SETTINGS));

    for _ in 0 .. count_groups {
        let mut pending = BTreeMap::new();
        for _ in 0 .. count_per_group {
            let k = make(&mut rng, klen);
            let v = make(&mut rng, vlen);
            pending.insert(k, lsm::Blob::Boxed(v));
        }
        let seg = try!(db.write_segment(pending).map_err(lsm::wrap_err));
        if let Some(seg) = seg {
            let lck = try!(db.get_write_lock());
            try!(lck.commit_segment(seg).map_err(lsm::wrap_err));
        }
    }

    match std::sync::Arc::try_unwrap(db) {
        Ok(db) => {
            try!(db.stop());
            Ok(())
        },
        Err(e) => {
            Err(lsm::Error::Misc(String::from("try_unwrap failed")))
        },
    }
}

fn result_main() -> Result<(),lsm::Error> {
    let args: Vec<_> = std::env::args().collect();
    println!("args: {:?}", args);
    if args.len() < 2 {
        return Err(lsm::Error::Misc(String::from("no filename given")));
    }
    if args.len() < 3 {
        return Err(lsm::Error::Misc(String::from("no command given")));
    }
    let name = args[1].as_str();
    let cmd = args[2].as_str();
    match cmd {
        "add_lines" => {
            println!("usage: add_lines file count_groups count_per_group");
            if args.len() < 6 {
                return Err(lsm::Error::Misc(String::from("too few args")));
            }
            let file = args[3].clone();
            let count_groups = args[4].parse::<usize>().unwrap();
            let count_per_group = args[5].parse::<usize>().unwrap();
            try!(add_lines(name, file, count_groups, count_per_group));
            Ok(())
        },
        "sqlite_lines" => {
            println!("usage: sqlite_lines file count_groups count_per_group");
            if args.len() < 6 {
                return Err(lsm::Error::Misc(String::from("too few args")));
            }
            let file = args[3].clone();
            let count_groups = args[4].parse::<usize>().unwrap();
            let count_per_group = args[5].parse::<usize>().unwrap();
            try!(sqlite_lines(name, file, count_groups, count_per_group));
            Ok(())
        },
        "add_random" => {
            println!("usage: add_random seed count_groups count_per_group klen vlen");
            if args.len() < 8 {
                return Err(lsm::Error::Misc(String::from("too few args")));
            }
            let seed = args[3].parse::<usize>().unwrap();
            let count_groups = args[4].parse::<usize>().unwrap();
            let count_per_group = args[5].parse::<usize>().unwrap();
            let klen = args[6].parse::<usize>().unwrap();
            let vlen = args[7].parse::<usize>().unwrap();
            try!(add_random(name, seed, count_groups, count_per_group, klen, vlen));
            Ok(())
        },
        "add_numbers" => {
            println!("usage: add_numbers count start step");
            if args.len() < 6 {
                return Err(lsm::Error::Misc(String::from("too few args")));
            }
            let count = args[3].parse::<u64>().unwrap();
            let start = args[4].parse::<u64>().unwrap();
            let step = args[5].parse::<u64>().unwrap();
            if step == 0 {
                return Err(lsm::Error::Misc(String::from("step cannot be 0")));
            }
            add_numbers(name, count, start, step)
        },
        "show_page" => {
            println!("usage: show_page pagenum");
            if args.len() < 4 {
                return Err(lsm::Error::Misc(String::from("too few args")));
            }
            let pgnum = args[3].parse::<u32>().unwrap();
            show_page(name, pgnum)
        },
        "show_leaf_page" => {
            println!("usage: show_leaf_page pagenum");
            if args.len() < 4 {
                return Err(lsm::Error::Misc(String::from("too few args")));
            }
            let pgnum = args[3].parse::<u32>().unwrap();
            show_leaf_page(name, pgnum)
        },
        "show_parent_page" => {
            println!("usage: show_parent_page pagenum");
            if args.len() < 4 {
                return Err(lsm::Error::Misc(String::from("too few args")));
            }
            let pgnum = args[3].parse::<u32>().unwrap();
            show_parent_page(name, pgnum)
        },
        "graph_parent_page" => {
            println!("usage: graph_parent_page pagenum depth");
            if args.len() < 5 {
                return Err(lsm::Error::Misc(String::from("too few args")));
            }
            let pgnum = args[3].parse::<u32>().unwrap();
            let depth = args[4].parse::<u8>().unwrap();
            graph_parent_page(name, pgnum, depth)
        },
        "seek_string" => {
            println!("usage: seek_string key sop");
            if args.len() < 5 {
                return Err(lsm::Error::Misc(String::from("too few args")));
            }
            let key = args[3].clone();
            let sop = args[4].clone();
            seek_string(name, key, sop)
        },
        "seek_bytes" => {
            println!("usage: seek_bytes sop numbytes b1 b2 b3 ... ");
            if args.len() < 5 {
                return Err(lsm::Error::Misc(String::from("too few args")));
            }
            let sop = args[3].clone();
            let count = args[4].parse::<usize>().unwrap();
            if count == 0 {
                return Err(lsm::Error::Misc(String::from("count cannot be 0")));
            }
            if args.len() < 5 + count {
                return Err(lsm::Error::Misc(String::from("too few args")));
            }
            let mut k = Vec::with_capacity(count);
            for i in 0 .. count {
                let b = args[5 + i].parse::<u8>().unwrap();
                k.push(b);
            }
            seek_bytes(name, k.into_boxed_slice(), sop)
        },
        "dump_page" => {
            if args.len() < 4 {
                return Err(lsm::Error::Misc(String::from("too few args")));
            }
            let pgnum = args[3].parse::<u32>().unwrap();
            dump_page(name, pgnum)
        },
        "list_keys" => {
            list_keys(name)
        },
        "list_keys_as_strings" => {
            list_keys_as_strings(name)
        },
        "list_segments" => {
            list_segments(name)
        },
        "list_free_blocks" => {
            list_free_blocks(name)
        },
        _ => {
            Err(lsm::Error::Misc(String::from("unknown command")))
        },
    }
}

pub fn main() {
    let r = result_main();
    if r.is_err() {
        println!("{:?}", r);
    }
}

