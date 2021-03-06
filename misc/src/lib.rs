﻿/*
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

#![feature(associated_consts)]
#![feature(clone_from_slice)]
#![feature(vec_push_all)]

extern crate rand;

use std::collections::HashMap;

pub fn fix_ms(n: i64) -> (i64, i64) {
    if n < 0 {
        let sec = -((-n) / 1000);
        let ms = n % 1000 + 1000;
        (sec, ms)
    } else {
        let sec = n / 1000;
        let ms = n % 1000;
        (sec, ms)
    }
}

pub fn tid() -> String {
    fn to_hex_string(ba: &[u8]) -> String {
        let strs: Vec<String> = ba.iter()
            .map(|b| format!("{:02X}", b))
            .collect();
        strs.join("")
    }

    let ba = rand::random::<[u8; 16]>();
    to_hex_string(&ba)
}

pub fn new_bson_objectid_rand() -> [u8; 12] {
    let ba = rand::random::<[u8; 12]>();
    ba
}

pub fn new_bytes_rand(n: usize) -> Box<[u8]> {
    // TODO slow?
    let mut a = vec![];
    for _ in 0 .. n {
        a.push(rand::random::<u8>());
    }
    a.into_boxed_slice()
}

pub fn tempfile(base: &str) -> String {
    let _ = std::fs::create_dir("tmp");
    let file = "tmp/".to_string() + base + "_" + &tid();
    file
}

pub fn set_vec_len<T: Copy>(v: &mut Vec<T>, val: T, len: usize) {
    v.truncate(len);
    // TODO put val into all the entries that are already there?
    while v.len() < len {
        v.push(val);
    }
}

pub fn insert_vec_into_vec<T>(dest: &mut Vec<T>, ndx: usize, from: Vec<T>) {
    for x in from.into_iter().rev() {
        dest.insert(ndx, x);
    }
}

pub mod endian {
    use std;

#[inline]
pub fn f64_to_bytes_le(i: f64) -> [u8; 8] {
    let mut a: [u8; 8] = unsafe {std::mem::transmute(i)};
    if cfg!(target_endian = "little") {
    } else {
        a.reverse();
    }
    a
}

#[inline]
pub fn f64_to_bytes_be(i: f64) -> [u8; 8] {
    let mut a: [u8; 8] = unsafe {std::mem::transmute(i)};
    if cfg!(target_endian = "little") {
        a.reverse();
    } else {
    }
    a
}

#[inline]
pub fn i64_to_bytes_le(i: i64) -> [u8; 8] {
    let a: [u8; 8] = unsafe {std::mem::transmute(i64::to_le(i))};
    a
}

#[inline]
pub fn i64_to_bytes_be(i: i64) -> [u8; 8] {
    let a: [u8; 8] = unsafe {std::mem::transmute(i64::to_be(i))};
    a
}

#[inline]
pub fn u64_to_bytes_le(i: u64) -> [u8; 8] {
    let a: [u8; 8] = unsafe {std::mem::transmute(u64::to_le(i))};
    a
}

#[inline]
pub fn u64_to_bytes_be(i: u64) -> [u8; 8] {
    let a: [u8; 8] = unsafe {std::mem::transmute(u64::to_be(i))};
    a
}

#[inline]
pub fn i32_to_bytes_le(i: i32) -> [u8; 4] {
    let a: [u8; 4] = unsafe {std::mem::transmute(i32::to_le(i))};
    a
}

#[inline]
pub fn i32_to_bytes_be(i: i32) -> [u8; 4] {
    let a: [u8; 4] = unsafe {std::mem::transmute(i32::to_be(i))};
    a
}

#[inline]
pub fn u32_to_bytes_le(i: u32) -> [u8; 4] {
    let a: [u8; 4] = unsafe {std::mem::transmute(u32::to_le(i))};
    a
}

#[inline]
pub fn u32_to_bytes_be(i: u32) -> [u8; 4] {
    let a: [u8; 4] = unsafe {std::mem::transmute(u32::to_be(i))};
    a
}

#[inline]
pub fn i16_to_bytes_le(i: i16) -> [u8; 2] {
    let a: [u8; 2] = unsafe {std::mem::transmute(i16::to_le(i))};
    a
}

#[inline]
pub fn i16_to_bytes_be(i: i16) -> [u8; 2] {
    let a: [u8; 2] = unsafe {std::mem::transmute(i16::to_be(i))};
    a
}

#[inline]
pub fn u16_to_bytes_le(i: u16) -> [u8; 2] {
    let a: [u8; 2] = unsafe {std::mem::transmute(u16::to_le(i))};
    a
}

#[inline]
pub fn u16_to_bytes_be(i: u16) -> [u8; 2] {
    let a: [u8; 2] = unsafe {std::mem::transmute(u16::to_be(i))};
    a
}

#[inline]
pub fn f64_from_bytes_le(mut a: [u8; 8]) -> f64 {
    if cfg!(target_endian = "little") {
    } else {
        a.reverse();
    }

    let i: f64 = unsafe {std::mem::transmute(a)};
    // TODO we wish we had f64::from_le(i)
    i
}

#[inline]
pub fn f64_from_bytes_be(mut a: [u8; 8]) -> f64 {
    if cfg!(target_endian = "little") {
        a.reverse();
    } else {
    }

    let i: f64 = unsafe {std::mem::transmute(a)};
    // TODO we wish we had f64::from_le(i)
    i
}

#[inline]
pub fn i64_from_bytes_le(a: [u8; 8]) -> i64 {
    let i: i64 = unsafe {std::mem::transmute(a)};
    i64::from_le(i)
}

#[inline]
pub fn i64_from_bytes_be(a: [u8; 8]) -> i64 {
    let i: i64 = unsafe {std::mem::transmute(a)};
    i64::from_be(i)
}

#[inline]
pub fn u64_from_bytes_le(a: [u8; 8]) -> u64 {
    let i: u64 = unsafe {std::mem::transmute(a)};
    u64::from_le(i)
}

#[inline]
pub fn u64_from_bytes_be(a: [u8; 8]) -> u64 {
    let i: u64 = unsafe {std::mem::transmute(a)};
    u64::from_be(i)
}

#[inline]
pub fn i32_from_bytes_le(a: [u8; 4]) -> i32 {
    let i: i32 = unsafe {std::mem::transmute(a)};
    i32::from_le(i)
}

#[inline]
pub fn i32_from_bytes_be(a: [u8; 4]) -> i32 {
    let i: i32 = unsafe {std::mem::transmute(a)};
    i32::from_be(i)
}

#[inline]
pub fn u32_from_bytes_le(a: [u8; 4]) -> u32 {
    let i: u32 = unsafe {std::mem::transmute(a)};
    u32::from_le(i)
}

#[inline]
pub fn u32_from_bytes_be(a: [u8; 4]) -> u32 {
    let i: u32 = unsafe {std::mem::transmute(a)};
    u32::from_be(i)
}

#[inline]
pub fn i16_from_bytes_le(a: [u8; 2]) -> i16 {
    let i: i16 = unsafe {std::mem::transmute(a)};
    i16::from_le(i)
}

#[inline]
pub fn i16_from_bytes_be(a: [u8; 2]) -> i16 {
    let i: i16 = unsafe {std::mem::transmute(a)};
    i16::from_be(i)
}

#[inline]
pub fn u16_from_bytes_le(a: [u8; 2]) -> u16 {
    let i: u16 = unsafe {std::mem::transmute(a)};
    u16::from_le(i)
}

#[inline]
pub fn u16_from_bytes_be(a: [u8; 2]) -> u16 {
    let i: u16 = unsafe {std::mem::transmute(a)};
    u16::from_be(i)
}
}

pub mod bytes {

    #[inline]
    pub fn copy_into(src: &[u8], dst: &mut [u8]) {
        let len = dst.clone_from_slice(src);
        assert_eq!(len, src.len());
    }

    #[inline]
    pub fn extract_2(v: &[u8]) -> [u8; 2]
    {
        let mut a = [0; 2];
        copy_into(v, &mut a);
        a
    }

    #[inline]
    pub fn extract_4(v: &[u8]) -> [u8; 4]
    {
        let mut a = [0; 4];
        copy_into(v, &mut a);
        a
    }

    #[inline]
    pub fn extract_8(v: &[u8]) -> [u8; 8]
    {
        let mut a = [0; 8];
        copy_into(v, &mut a);
        a
    }

}

pub mod bufndx {

    use std;

    #[inline]
    pub fn slurp_8(ba: &[u8], i: &mut usize) -> [u8; 8] {
        let a = super::bytes::extract_8(&ba[*i .. *i + 8]);
        *i = *i + 8;
        a
    }

    #[inline]
    pub fn slurp_4(ba: &[u8], i: &mut usize) -> [u8; 4] {
        let a = super::bytes::extract_4(&ba[*i .. *i + 4]);
        *i = *i + 4;
        a
    }

    #[inline]
    pub fn slurp_i32_le(ba: &[u8], i: &mut usize) -> i32 {
        super::endian::i32_from_bytes_le(slurp_4(ba, i))
    }

    #[inline]
    pub fn slurp_u32_le(ba: &[u8], i: &mut usize) -> u32 {
        super::endian::u32_from_bytes_le(slurp_4(ba, i))
    }

    #[inline]
    pub fn slurp_i64_le(ba: &[u8], i: &mut usize) -> i64 {
        super::endian::i64_from_bytes_le(slurp_8(ba, i))
    }

    #[inline]
    pub fn slurp_f64_le(ba: &[u8], i: &mut usize) -> f64 {
        super::endian::f64_from_bytes_le(slurp_8(ba, i))
    }

    #[inline]
    pub fn slurp_cstring(ba: &[u8], i: &mut usize) -> Result<String,std::str::Utf8Error> {
        let mut len = 0;
        while ba[*i + len] != 0 {
            len = len + 1;
        }
        let s = try!(std::str::from_utf8(&ba[*i .. *i + len]));
        *i = *i + len + 1;
        Ok(String::from(s))
    }

}

pub mod varint {
    // TODO this doesn't need to be usize.  u8 is enough.
    #[inline]
    pub fn space_needed_for(v: u64) -> usize {
        if v<=240 { 1 }
        else if v<=2287 { 2 }
        else if v<=67823 { 3 }
        else if v<=16777215 { 4 }
        else if v<=4294967295 { 5 }
        else if v<=1099511627775 { 6 }
        else if v<=281474976710655 { 7 }
        else if v<=72057594037927935 { 8 }
        else { 9 }
    }

    pub fn first_byte_to_len(a0: u8) -> usize {
        if a0 <= 240 { 
            1
        } else if a0 <= 248 {
            2
        } else if a0 == 249 {
            3
        } else if a0 == 250 {
            4
        } else if a0 == 251 {
            5
        } else if a0 == 252 {
            6
        } else if a0 == 253 {
            7
        } else if a0 == 254 {
            8
        } else {
            9
        }
    }

    // TODO stronger inline hint?
    #[inline]
    pub fn read(buf: &[u8], cur: &mut usize) -> u64 {
        let c = *cur;
        let a0 = buf[c] as u64;
        if a0 <= 240u64 { 
            *cur = *cur + 1;
            a0
        } else if a0 <= 248u64 {
            let a1 = buf[c+1] as u64;
            let r = 240u64 + 256u64 * (a0 - 241u64) + a1;
            *cur = *cur + 2;
            r
        } else if a0 == 249u64 {
            let a1 = buf[c+1] as u64;
            let a2 = buf[c+2] as u64;
            let r = 2288u64 + 256u64 * a1 + a2;
            *cur = *cur + 3;
            r
        } else if a0 == 250u64 {
            let a1 = buf[c+1] as u64;
            let a2 = buf[c+2] as u64;
            let a3 = buf[c+3] as u64;
            let r = (a1 << 16) | (a2 << 8) | a3;
            *cur = *cur + 4;
            r
        } else if a0 == 251u64 {
            let a1 = buf[c+1] as u64;
            let a2 = buf[c+2] as u64;
            let a3 = buf[c+3] as u64;
            let a4 = buf[c+4] as u64;
            let r = (a1 << 24) | (a2 << 16) | (a3 << 8) | a4;
            *cur = *cur + 5;
            r
        } else if a0 == 252u64 {
            let a1 = buf[c+1] as u64;
            let a2 = buf[c+2] as u64;
            let a3 = buf[c+3] as u64;
            let a4 = buf[c+4] as u64;
            let a5 = buf[c+5] as u64;
            let r = (a1 << 32) | (a2 << 24) | (a3 << 16) | (a4 << 8) | a5;
            *cur = *cur + 6;
            r
        } else if a0 == 253u64 {
            let a1 = buf[c+1] as u64;
            let a2 = buf[c+2] as u64;
            let a3 = buf[c+3] as u64;
            let a4 = buf[c+4] as u64;
            let a5 = buf[c+5] as u64;
            let a6 = buf[c+6] as u64;
            let r = (a1 << 40) | (a2 << 32) | (a3 << 24) | (a4 << 16) | (a5 << 8) | a6;
            *cur = *cur + 7;
            r
        } else if a0 == 254u64 {
            let a1 = buf[c+1] as u64;
            let a2 = buf[c+2] as u64;
            let a3 = buf[c+3] as u64;
            let a4 = buf[c+4] as u64;
            let a5 = buf[c+5] as u64;
            let a6 = buf[c+6] as u64;
            let a7 = buf[c+7] as u64;
            let r = (a1 << 48) | (a2 << 40) | (a3 << 32) | (a4 << 24) | (a5 << 16) | (a6 << 8) | a7;
            *cur = *cur + 8;
            r
        } else {
            let a1 = buf[c+1] as u64;
            let a2 = buf[c+2] as u64;
            let a3 = buf[c+3] as u64;
            let a4 = buf[c+4] as u64;
            let a5 = buf[c+5] as u64;
            let a6 = buf[c+6] as u64;
            let a7 = buf[c+7] as u64;
            let a8 = buf[c+8] as u64;
            let r = (a1 << 56) | (a2 << 48) | (a3 << 40) | (a4 << 32) | (a5 << 24) | (a6 << 16) | (a7 << 8) | a8;
            *cur = *cur + 9;
            r
        }
    }

    #[inline]
    pub fn write(buf: &mut [u8], cur: &mut usize, v: u64) {
        let c = *cur;
        if v<=240u64 { 
            buf[c] = v as u8;
            *cur = *cur + 1;
        } else if v<=2287u64 { 
            buf[c] = ((v - 240u64) / 256u64 + 241u64) as u8;
            buf[c+1] = ((v - 240u64) % 256u64) as u8;
            *cur = *cur + 2;
        } else if v<=67823u64 { 
            buf[c] = 249u8;
            buf[c+1] = ((v - 2288u64) / 256u64) as u8;
            buf[c+2] = ((v - 2288u64) % 256u64) as u8;
            *cur = *cur + 3;
        } else if v<=16777215u64 { 
            buf[c] = 250u8;
            buf[c+1] = (v >> 16) as u8;
            buf[c+2] = (v >>  8) as u8;
            buf[c+3] = (v >>  0) as u8;
            *cur = *cur + 4;
        } else if v<=4294967295u64 { 
            buf[c] = 251u8;
            buf[c+1] = (v >> 24) as u8;
            buf[c+2] = (v >> 16) as u8;
            buf[c+3] = (v >>  8) as u8;
            buf[c+4] = (v >>  0) as u8;
            *cur = *cur + 5;
        } else if v<=1099511627775u64 { 
            buf[c] = 252u8;
            buf[c+1] = (v >> 32) as u8;
            buf[c+2] = (v >> 24) as u8;
            buf[c+3] = (v >> 16) as u8;
            buf[c+4] = (v >>  8) as u8;
            buf[c+5] = (v >>  0) as u8;
            *cur = *cur + 6;
        } else if v<=281474976710655u64 { 
            buf[c] = 253u8;
            buf[c+1] = (v >> 40) as u8;
            buf[c+2] = (v >> 32) as u8;
            buf[c+3] = (v >> 24) as u8;
            buf[c+4] = (v >> 16) as u8;
            buf[c+5] = (v >>  8) as u8;
            buf[c+6] = (v >>  0) as u8;
            *cur = *cur + 7;
        } else if v<=72057594037927935u64 { 
            buf[c] = 254u8;
            buf[c+1] = (v >> 48) as u8;
            buf[c+2] = (v >> 40) as u8;
            buf[c+3] = (v >> 32) as u8;
            buf[c+4] = (v >> 24) as u8;
            buf[c+5] = (v >> 16) as u8;
            buf[c+6] = (v >>  8) as u8;
            buf[c+7] = (v >>  0) as u8;
            *cur = *cur + 8;
        } else {
            buf[c] = 255u8;
            buf[c+1] = (v >> 56) as u8;
            buf[c+2] = (v >> 48) as u8;
            buf[c+3] = (v >> 40) as u8;
            buf[c+4] = (v >> 32) as u8;
            buf[c+5] = (v >> 24) as u8;
            buf[c+6] = (v >> 16) as u8;
            buf[c+7] = (v >>  8) as u8;
            buf[c+8] = (v >>  0) as u8;
            *cur = *cur + 9;
        }
    }
}

pub struct ByteSliceRead<'a> {
    buf: &'a [u8],
    cur: usize,
}

impl<'a> ByteSliceRead<'a> {
    pub fn new(buf: &'a [u8]) -> Self {
        ByteSliceRead {
            buf: buf,
            cur: 0,
        }
    }
}

impl<'a> std::io::Read for ByteSliceRead<'a> {
    #[inline]
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        let amt = std::cmp::min(buf.len(), self.buf.len() - self.cur);
        buf.clone_from_slice(&self.buf[self.cur .. self.cur + amt]);
        self.cur += amt;
        Ok(amt)
    }

}

pub struct ByteBufRead {
    buf: Box<[u8]>,
    cur: usize,
}

impl ByteBufRead {
    pub fn new(buf: Box<[u8]>) -> Self {
        ByteBufRead {
            buf: buf,
            cur: 0,
        }
    }
}

impl std::io::Read for ByteBufRead {
    #[inline]
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        let amt = std::cmp::min(buf.len(), self.buf.len() - self.cur);
        buf.clone_from_slice(&self.buf[self.cur .. self.cur + amt]);
        self.cur += amt;
        Ok(amt)
    }

}

pub mod io {
    use std::io;
    use std::io::Read;
    use std::io::Write;
    use super::endian;

    pub fn write_fully<W: Write>(strm: &mut W, buf: &[u8]) -> io::Result<usize> {
        let mut sofar = 0;
        let len = buf.len();
        loop {
            let cur = &buf[sofar..len];
            let n = try!(strm.write(cur));
            if n == 0 {
                break;
            }
            sofar += n;
            if sofar == len {
                break;
            }
        }
        Ok(sofar)
    }

    pub fn read_fully<R: Read>(strm: &mut R, buf: &mut [u8]) -> io::Result<usize> {
        let mut sofar = 0;
        let len = buf.len();
        loop {
            let cur = &mut buf[sofar..len];
            let n = try!(strm.read(cur));
            if n == 0 {
                break;
            }
            sofar += n;
            if sofar == len {
                break;
            }
        }
        Ok(sofar)
    }

    pub fn read_4<R: Read>(strm: &mut R) -> io::Result<[u8; 4]> {
        let mut a = [0; 4];
        let got = try!(read_fully(strm, &mut a));
        // TODO if got == 0 this is just normal end of file
        if got != 4 {
            return Err(io::Error::new(io::ErrorKind::InvalidInput, "failed to read 4 bytes"));
        }
        Ok(a)
    }

    pub fn read_u32_le<R: Read>(strm: &mut R) -> io::Result<u32> {
        let ba = try!(read_4(strm));
        Ok(endian::u32_from_bytes_le(ba))
    }

    pub fn read_i32_le<R: Read>(strm: &mut R) -> io::Result<i32> {
        let ba = try!(read_4(strm));
        Ok(endian::i32_from_bytes_le(ba))
    }

}

pub struct Sqlite4Num {
    neg: bool,
    approx: bool,
    e: i16,
    m: u64,
}

impl Sqlite4Num {
    const SQLITE4_MX_EXP: i16 = 999;
    const SQLITE4_NAN_EXP: i16 = 2000;

    const NAN: Sqlite4Num =
        Sqlite4Num
        {
            neg: false,
            approx: true,
            e: Sqlite4Num::SQLITE4_NAN_EXP,
            m: 0,
        };
    const POS_INF: Sqlite4Num = Sqlite4Num {m: 1, .. Sqlite4Num::NAN};
    const NEG_INF: Sqlite4Num = Sqlite4Num {neg: true, .. Sqlite4Num::POS_INF};
    const ZERO: Sqlite4Num =
        Sqlite4Num
        {
            neg: false,
            approx: false,
            e: 0,
            m: 0,
        };

    pub fn from_f64(d: f64) -> Sqlite4Num {
        // TODO probably this function should be done by decoding the bits
        if d.is_nan() {
            Sqlite4Num::NAN
        } else if d.is_sign_positive() && d.is_infinite() {
            Sqlite4Num::POS_INF
        } else if d.is_sign_negative() && d.is_infinite() {
            Sqlite4Num::NEG_INF
        } else if d==0.0 {
            Sqlite4Num::ZERO
        } else {
            let large = u64::max_value() as f64;
            let large10 = (u64::max_value() / 10) as f64;
            let neg = d < 0.0;
            let mut d = if neg { -d } else { d };
            let mut e = 0;
            while d>large || (d>1.0 && d==((d as i64) as f64)) {
                d = d / 10.0;
                e = e + 1;
            }
            while d<large10 && d != ((d as i64) as f64) {
                d = d * 10.0;
                e = e - 1;
            }
            Sqlite4Num
            {
                neg: neg,
                approx: true,
                e: e as i16,
                m: d as u64,
            }
        }
    }

    fn is_inf(&self) -> bool {
        (self.e > Sqlite4Num::SQLITE4_MX_EXP) && (self.m != 0)
    }

    fn is_nan(&self) -> bool{
        (self.e > Sqlite4Num::SQLITE4_MX_EXP) && (self.m == 0)
    }

    pub fn from_i64(n: i64) -> Sqlite4Num {
        Sqlite4Num
        {
            neg: n<0,
            approx: false,
            m: if n>=0 { (n as u64) } else if n != i64::min_value() { ((-n) as u64) } else { 1 + (i64::max_value() as u64) },
            e: 0,
        }
    }

    fn normalize(&self) -> Sqlite4Num {
        let mut m = self.m;
        let mut e = self.e;

        while (m % 10) == 0 {
            e = e + 1;
            m = m / 10;
        }

        Sqlite4Num {m: m, e: e, .. *self}
    }

    pub fn encode_for_index(&self, w: &mut Vec<u8>) {
        // TODO in sqlite4, the first byte of this encoding 
        // is designed to mesh with the
        // overall type order byte.

        if self.m == 0 {
            if self.is_nan() {
                w.push(0x06u8);
            } else {
                w.push(0x15u8);
            }
        } else if self.is_inf() {
            if self.neg {
                w.push(0x07u8);
            } else {
                w.push(0x23u8);
            }
        } else {
            let num = self.normalize();
            let mut m = num.m;
            let mut e = num.e;
            let mut i_digit;
            let mut a_digit = [0; 12];

            if (num.e%2) != 0 {
                a_digit[0] = (10 * (m % 10)) as u8;
                m = m / 10;
                e = e - 1;
                i_digit = 1;
            } else {
                i_digit = 0;
            }

            while m != 0 {
                a_digit[i_digit] = (m % 100) as u8;
                i_digit = i_digit + 1;
                m = m / 100;
            }

            e = (i_digit as i16) + (e/2);

            fn push_u16_be(w: &mut Vec<u8>, e: u16) {
                w.push(((e>>8) & 0xff_u16) as u8);
                w.push(((e>>0) & 0xff_u16) as u8);
            }

            if e>= 11 {
                if ! num.neg {
                    w.push(0x22u8);
                    push_u16_be(w, e as u16);
                } else {
                    w.push(0x08u8);
                    push_u16_be(w, !e as u16);
                }
            } else if e>=0 {
                if ! num.neg {
                    w.push(0x17u8+(e as u8));
                } else {
                    w.push(0x13u8-(e as u8));
                }
            } else {
                if ! num.neg {
                    w.push(0x16u8);
                    push_u16_be(w, !((-e) as u16));
                } else {
                    w.push(0x14u8);
                    push_u16_be(w, (-e) as u16);
                }
            }

            while i_digit>0 {
                i_digit = i_digit - 1;
                let mut d = a_digit[i_digit] * 2u8;
                if i_digit != 0 { d = d | 0x01u8; }
                if num.neg { d = !d; }
                w.push(d)
            }
        }
    }

}

// TODO in cases where we collect() an iterator and then immediately call this func,
// it would be better to do the result unwrap during the collect, while building the
// first vec, instead of building a vec and then rebuilding it.
// let preds = try!(other.into_iter().map(|(k,v)| parse_pred(&k,v)).collect::<Result<Vec<_>>>());
#[cfg(remove_me)]
pub fn unwrap_vec_of_results<T,E>(v: Vec<std::result::Result<T,E>>) -> std::result::Result<Vec<T>,E> {
    let mut r = Vec::new();
    for t in v {
        let q = try!(t);
        r.push(q);
    }
    Ok(r)
}

pub fn group_by_key<TK : Eq + std::hash::Hash,TV>(pairs: Vec<(TK,TV)>) -> HashMap<TK,Vec<TV>> {
    let mut mc = HashMap::new();
    for (k,v) in pairs {
        let a = match mc.entry(k) {
            std::collections::hash_map::Entry::Vacant(e) => {
                e.insert(vec![])
            },
            std::collections::hash_map::Entry::Occupied(e) => {
                e.into_mut()
            },
        };
        a.push(v);
    }
    mc
}

pub fn remove_first_if_exists<T>(v: &mut Vec<T>) -> Option<T> {
    //gt.reverse();
    //gt.pop()
    if v.len() == 0 {
        None
    } else {
        Some(v.remove(0))
    }
}

pub fn push_varint(v: &mut Vec<u8>, n: u64) {
    let mut buf = [0; 9];
    let mut cur = 0;
    varint::write(&mut buf, &mut cur, n);
    v.push_all(&buf[0 .. cur]);
}

pub struct Lend<T> {
    value: Option<T>,
    done: Box<Fn(T) -> ()>,
}

impl<T> Lend<T> {
    pub fn new(value: T, done: Box<Fn(T) -> ()>) -> Lend<T> {
        Lend {
            value: Some(value),
            done: done,
        }
    }

    pub fn detach(mut self) -> T {
        let value = self.value.take().unwrap();
        value
    }
}

impl<T> AsRef<T> for Lend<T> {
    fn as_ref(&self) -> &T {
        match self.value.as_ref() {
            Some(v) => v,
            None => panic!("smartpointer missing its value.")
        }
    }
}

impl<T> AsMut<T> for Lend<T> {
    fn as_mut(&mut self) -> &mut T {
        match self.value.as_mut() {
            Some(v) => v,
            None => panic!("smartpointer missing its value.")
        }
    }
}

impl<T> std::ops::Deref for Lend<T> {
    type Target = T;

    fn deref<'a>(&'a self) -> &'a T {
        self.as_ref()
    }

}

impl<T> std::ops::DerefMut for Lend<T> {
    fn deref_mut<'a>(&'a mut self) -> &'a mut T {
        self.as_mut()
    }

}

impl<T> Drop for Lend<T> {
    fn drop(&mut self) {
        let value = self.value.take().unwrap();
        (*self.done)(value);
    }
}


pub mod buf_advance {

    use super::endian;
    use super::bytes;

    #[inline]
    pub fn get_byte(buf: &[u8], cur: &mut usize) -> u8 {
        let r = buf[*cur];
        *cur = *cur + 1;
        r
    }

    #[inline]
    pub fn get_u32(buf: &[u8], cur: &mut usize) -> u32 {
        let at = *cur;
        // TODO just buf?  instead of making 4-byte slice.
        let a = bytes::extract_4(&buf[at .. at + 4]);
        *cur = *cur + 4;
        endian::u32_from_bytes_be(a)
    }

    #[inline]
    pub fn get_u16(buf: &[u8], cur: &mut usize) -> u16 {
        let at = *cur;
        // TODO just buf?  instead of making 2-byte slice.
        let a = bytes::extract_2(&buf[at .. at + 2]);
        let r = endian::u16_from_bytes_be(a);
        *cur = *cur + 2;
        r
    }
}

// TODO this is probably in std somewhere
pub fn inside_out<T,E>(v: Option<Result<T,E>>) -> Result<Option<T>,E> {
    match v {
        Some(v) => {
            let v = try!(v);
            Ok(Some(v))
        },
        None => {
            Ok(None)
        },
    }
}

