(*
    Copyright 2015 Zumero, LLC

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
*)

namespace Zumero

open System
open System.IO

type BinReader (ub:byte[], start:int, len:int) =
    // TODO use len
    let mutable i = start
    let ba = ub

    let rec readBsonValue(valType) =
        match valType with
        | 1uy -> readFloat() |> BsonValue.BDouble
        | 2uy -> readBsonString() |> BsonValue.BString
        | 3uy -> readDocument()
        | 4uy -> readArray()
        | 5uy -> readBinary()
        | 6uy -> BsonValue.BUndefined
        | 7uy -> readObjectID() |> BsonValue.BObjectID
        | 8uy -> readBoolean() |> BsonValue.BBoolean
        | 9uy -> readInt64() |> BsonValue.BDateTime
        | 10uy -> BsonValue.BNull
        | 11uy -> readRegex()
        | 12uy -> read12()
        | 13uy -> readJavaScript()
        | 15uy -> readJavaScriptWithScope()
        | 16uy -> readInt32() |> BsonValue.BInt32
        | 17uy -> readInt64() |> BsonValue.BTimeStamp
        | 18uy -> readInt64() |> BsonValue.BInt64
        | 127uy -> BsonValue.BMaxKey
        | 255uy -> BsonValue.BMinKey // -1
        | _ -> failwith (sprintf "Invalid BSON value type: %d" (int valType))

    and read12() =
        // TODO deprecated
        let s = readBsonString()
        readObjectID() |> BObjectID

    and readRegex() =
        let expr = readCString()
        let options = readCString()
        BsonValue.BRegex (expr,options)

    and readBinary() =
        let len = readInt32()
        let subtype = ba.[i]
        i <- i + 1
        let b:byte[] = Array.zeroCreate len
        Array.Copy(ba, i, b, 0, len)
        i <- i + len
        BsonValue.BBinary (subtype,b)

    and readJavaScript() =
        let a = readBsonString()
        BsonValue.BJSCode a

    and readJavaScriptWithScope() =
        let len = readInt32()
        let a = readBsonString()
        let scope = readDocument()
        BsonValue.BJSCodeWithScope a

    and readFloat() =
        let ms = new MemoryStream(ba, i, 8)
        let br = new BinaryReader(ms)
        let f = br.ReadDouble()
        i <- i + 8
        f

    and readObjectID() =
        let b:byte[] = Array.zeroCreate 12
        Array.Copy(ba, i, b, 0, 12)
        i <- i + 12
        b

    and readBoolean() =
        let b = ba.[i]
        i <- i + 1
        if b=0uy then false else true

    and readInt32() =
        let a1 = ba.[i+0] |> uint64
        let a2 = ba.[i+1] |> uint64
        let a3 = ba.[i+2] |> uint64
        let a4 = ba.[i+3] |> uint64
        i <- i + 4
        (a4<<<24) ||| (a3<<<16) ||| (a2<<<8) ||| (a1) |> int32

    and readInt64() =
        let a1 = ba.[i+0] |> uint64
        let a2 = ba.[i+1] |> uint64
        let a3 = ba.[i+2] |> uint64
        let a4 = ba.[i+3] |> uint64
        let a5 = ba.[i+4] |> uint64
        let a6 = ba.[i+5] |> uint64
        let a7 = ba.[i+6] |> uint64
        let a8 = ba.[i+7] |> uint64
        i <- i + 8
        (a8<<<56) ||| (a7<<<48) ||| (a6<<<40) ||| (a5<<<32) ||| (a4<<<24) ||| (a3<<<16) ||| (a2<<<8) ||| (a1) |> int64

    and readCString() =
        let mutable len = 0
        while ba.[i + len] <> 0uy do
            len <- len + 1
        //printfn "cstring len: %d" len
        let s = System.Text.Encoding.UTF8.GetString(ba, i, len)
        //printfn "cstring: %s" s
        i <- i + len + 1
        s

    and readRawDocument() =
        let len = readInt32()
        //printfn "document len: %d" len
        let pairs = ResizeArray<_>()
        while ba.[i] <> 0uy do
            let valType = ba.[i]
            //printfn "valType: %d" (int valType)
            i <- i + 1
            let k = readCString()
            //printfn "k: %s" k
            let v = readBsonValue(valType)
            //printfn "v: %A" v
            let pair = (k,v)
            pairs.Add(pair)
        if ba.[i] <> 0uy then failwith "should be zero"
        i <- i + 1
        // TODO verify len
        pairs

    and readDocument() =
        let pairs = readRawDocument()
        BsonValue.BDocument (pairs.ToArray())

    and readArray() =
        let pairs = readRawDocument()
        // TODO should perhaps verify that all the keys are correct
        let a = pairs.ToArray()
        let a2 = Array.map (fun (k,v) -> v) a
        BsonValue.BArray a2

    and readBsonString() =
        let len = readInt32()
        //printfn "string len: %d" len
        let s = System.Text.Encoding.UTF8.GetString(ba, i, len - 1)
        i <- i + len
        //printfn "string: %s" s
        s

    member this.Position = i
    member this.ReadInt32() = readInt32()
    member this.ReadInt64() = readInt64()
    member this.ReadCString() = readCString()
    member this.ReadDocument() = readDocument()

    static member ReadDocument(ba:byte[]) =
        let br = BinReader(ba, 0, ba.Length)
        br.ReadDocument()

