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

extern crate lsm;

use lsm::ICursor;

fn dump_page(name: &str, pgnum: u32) -> Result<(),lsm::Error> {
    let db = try!(lsm::db::new(String::from(name), lsm::DEFAULT_SETTINGS));
    let page = try!(db.get_page(pgnum));
    println!("{:?}", page);
    Ok(())
}

fn list_segments(name: &str) -> Result<(),lsm::Error> {
    let db = try!(lsm::db::new(String::from(name), lsm::DEFAULT_SETTINGS));
    let (segments, infos) = try!(db.list_segments());
    for s in segments.iter() {
        println!("{}: {:?}", s, infos[s]);
    }
    Ok(())
}

fn list_free_blocks(name: &str) -> Result<(),lsm::Error> {
    let db = try!(lsm::db::new(String::from(name), lsm::DEFAULT_SETTINGS));
    let blocks = try!(db.list_free_blocks());
    println!("{:?}", blocks);
    Ok(())
}

fn list_keys(name: &str) -> Result<(),lsm::Error> {
    let db = try!(lsm::db::new(String::from(name), lsm::DEFAULT_SETTINGS));
    let mut cursor = try!(db.OpenCursor());
    try!(cursor.First());
    while cursor.IsValid() {
        {
            let k = try!(cursor.KeyRef());
            println!("k: {:?}", k);
            let v = try!(cursor.LiveValueRef());
            println!("v: {:?}", v);
            let q = try!(v.into_boxed_slice());
        }
        try!(cursor.Next());
    }
    Ok(())
}

fn merge(name: &str, level: u32, min: usize, max: Option<usize>) -> Result<(),lsm::Error> {
    let db = try!(lsm::db::new(String::from(name), lsm::DEFAULT_SETTINGS));
    match try!(db.merge(level, min, max)) {
        Some(seg) => {
            println!("merged segment: {}", seg);
            let lck = try!(db.GetWriteLock());
            try!(lck.commitMerge(seg));
            Ok(())
        },
        None => {
            println!("no merge needed");
            Ok(())
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
        "merge" => {
            if args.len() < 5 {
                return Err(lsm::Error::Misc(String::from("too few args")));
            }
            let level = args[3].parse::<u32>().unwrap();
            let min = args[4].parse::<usize>().unwrap();
            if args.len() == 5 {
                merge(name, level, min, None)
            } else {
                let max = args[5].parse::<usize>().unwrap();
                merge(name, level, min, Some(max))
            }
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

