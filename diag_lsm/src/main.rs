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

fn list_segments(name: &str) -> Result<(),lsm::Error> {
    let db = try!(lsm::db::new(String::from(name), lsm::DEFAULT_SETTINGS));
    let (segments, infos) = try!(db.list_segments());
    println!("segments: {:?}", segments);
    println!("infos: {:?}", infos);
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
        return Err(lsm::Error::Misc("no command given"));
    }
    let cmd = args[1].as_str();
    if args.len() < 3 {
        return Err(lsm::Error::Misc("no filename given"));
    }
    let name = args[2].as_str();
    match cmd {
        "merge" => {
            if args.len() < 5 {
                return Err(lsm::Error::Misc("too few args"));
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
        "list_segments" => {
            list_segments(name)
        },
        _ => {
            Err(lsm::Error::Misc("unknown command"))
        },
    }
}

pub fn main() {
    let r = result_main();
    if r.is_err() {
        println!("{:?}", r);
    }
}

