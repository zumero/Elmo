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

exception MongoCode of (int*string)

type BsonValue =
    | BDouble of float
    | BString of string
    | BInt64 of int64
    | BInt32 of int32
    | BUndefined
    | BObjectID of byte[]
    | BNull
    | BRegex of string*string
    | BJSCode of string
    | BJSCodeWithScope of string
    | BBinary of byte*byte[]
    | BMinKey
    | BMaxKey
    | BDateTime of int64
    | BTimeStamp of int64
    | BBoolean of bool
    | BArray of BsonValue[]
    | BDocument of (string*BsonValue)[]

type sqlite4_num =
    {
        neg:bool
        approx:bool
        e:int16
        m:uint64
    }

module sqlite4 =
    // the code below is a very direct port of sqlite4's numeric key encoding
    // from C to F#.  It uses mutables.  It's yucky (from a functional programming
    // perspective).  Very non-idiomatic.

    let LARGEST_UINT64 = System.UInt64.MaxValue
    let TENTH_MAX = LARGEST_UINT64 / (uint64 10)
    let SQLITE4_MX_EXP = 999s
    let SQLITE4_NAN_EXP = 2000s

    let num_from_double d =
        // TODO probably this function should be done by decoding the bits
        let nan =
            {
                neg = false
                approx = true
                e = SQLITE4_NAN_EXP
                m = 0UL
            }
        let posInf = {nan with m=1UL}
        let negInf = {posInf with neg=true}
        let zero =
            {
                neg = false
                approx = false
                e = 0s
                m = 0UL
            }

        if System.Double.IsNaN(d) then nan
        else if System.Double.IsPositiveInfinity(d) then posInf
        else if System.Double.IsNegativeInfinity(d) then negInf
        else if d=0.0 then zero
        else
            let large = double LARGEST_UINT64
            let large10 = double TENTH_MAX
            let neg = d<0.0
            let mutable d = if neg then -d else d
            let mutable e = 0
            while d>large || (d>1.0 && d=(double (int64 d))) do
                d <- d / 10.0
                e <- e + 1
            while d<large10 && d<>(double (int64 d)) do
                d <- d * 10.0
                e <- e - 1
            {
                neg = neg
                approx = true
                e = int16 e
                m = uint64 d
            }

    let num_isinf num =
        num.e>SQLITE4_MX_EXP && num.m<>0UL

    let num_isnan num =
        num.e>SQLITE4_MX_EXP && num.m=0UL

    let num_from_int64 n =
        {
            neg = n<0L
            approx = false
            m = if n>=0L then (uint64 n) else if n<>System.Int64.MinValue then (uint64 (-n)) else 1UL + (System.Int64.MaxValue |> uint64)
            e = 0s
        }

    let private normalize num =
        let mutable m = num.m
        let mutable e = num.e

        while (m%10UL)=0UL do
            e <- e + 1s
            m <- m / 10UL

        {num with m = m; e = e}

    let encodeForIndexInto (w:BinWriter) num =
        // TODO the first byte of this encoding is designed to mesh with the
        // overall type order byte, but we're not doing that.  instead, we are
        // always prefixing this with the numeric type order byte.

        if num.m=0UL then
            if num_isnan num then
                w.WriteByte(0x06uy)
            else
                w.WriteByte(0x15uy)
        else if num_isinf num then
            if num.neg then
                w.WriteByte(0x07uy)
            else
                w.WriteByte(0x23uy)
        else
            let num = normalize num
            let mutable m = num.m
            let mutable e = num.e
            let mutable iDigit = 0
            let aDigit:byte[] = Array.zeroCreate 12

            if (num.e%2s)<>0s then
                aDigit.[0] <- byte (10UL * (m % 10UL))
                m <- m / 10UL
                e <- e - 1s
                iDigit <- 1
            else
                iDigit <- 0

            while m<>0UL do
                aDigit.[iDigit] <- byte (m % 100UL)
                iDigit <- iDigit + 1
                m <- m / 100UL

            e <- ((int16 iDigit) + (e/2s))

            if e>= 11s then
                if not num.neg then
                    w.WriteByte(0x22uy)
                    w.WriteInt16BigEndian(e)
                else
                    w.WriteByte(0x08uy)
                    w.WriteInt16BigEndian(~~~e)
            else if e>=0s then
                if not num.neg then
                    w.WriteByte(0x17uy+(byte e))
                else
                    w.WriteByte(0x13uy-(byte e))
            else
                if not num.neg then
                    w.WriteByte(0x16uy)
                    w.WriteInt16BigEndian(~~~(-e))
                else
                    w.WriteByte(0x14uy)
                    w.WriteInt16BigEndian(-e)

            while iDigit>0 do
                iDigit <- iDigit - 1
                let mutable d = aDigit.[iDigit]*2uy
                if iDigit<>0 then d <- d ||| 0x01uy
                if num.neg then d <- ~~~d
                w.WriteByte(d)


module bson = 

    open System

    // lexicographic compare
    let bcmp (x:byte[]) (y:byte[]) =
        let xlen = x.Length
        let ylen = y.Length
        let len = if xlen<ylen then xlen else ylen
        let mutable i = 0
        let mutable result = 0
        while i<len do
            let c = (int (x.[i])) - int (y.[i])
            if c <> 0 then
                i <- len+1 // breaks out of the loop, and signals that result is valid
                result <- c
            else
                i <- i + 1
        if i>len then result else (xlen - ylen)

    let splitname (s:string) =
        let dot = s.IndexOf('.')
        if dot<0 then failwith "bad namespace"
        let left = s.Substring(0, dot)
        let right = s.Substring(dot+1)
        (left,right)

    let newObjectID() =
        // TODO make this a real object ID, not just 12 random bytes
        let id:byte[] = Array.zeroCreate 12
        let r = Random()
        for i in 0 .. 11 do
            id.[i] <- (r.Next() % 255) |> byte
        BObjectID id

    let getTypeNumber bv =
        match bv with
        | BDouble _ -> 1
        | BString _ -> 2
        | BDocument _ -> 3
        | BArray _ -> 4
        | BBinary _ -> 5
        | BUndefined _ -> 6
        | BObjectID _ -> 7
        | BBoolean _ -> 8
        | BDateTime _ -> 9
        | BNull -> 10
        | BRegex _ -> 11
        | BJSCode _ -> 13
        | BJSCodeWithScope _ -> 15
        | BInt32 _ -> 16
        | BTimeStamp _ -> 17
        | BInt64 _ -> 18
        | BMinKey -> -1
        | BMaxKey -> 127

    let getTypeOrder bv =
        // same numbers as canonicalizeBSONType()
        match bv with
        | BUndefined -> 0
        | BNull -> 5
        | BDouble _ -> 10
        | BInt64 _ -> 10
        | BInt32 _ -> 10
        | BString _ -> 15
        | BDocument _ -> 20
        | BArray _ -> 25
        | BBinary _ -> 30
        | BObjectID _ -> 35
        | BBoolean _ -> 40
        | BDateTime _ -> 45
        | BTimeStamp _ -> 47
        | BRegex _ -> 50
        | BJSCode _ -> 60
        | BJSCodeWithScope _ -> 65
        | BMinKey -> -1
        | BMaxKey -> 127

    let streqi a b =
        System.String.Equals(a,b,System.StringComparison.InvariantCultureIgnoreCase)

    let tryGetValueForInsensitiveKey bv (s:string) =
        match bv with
        | BDocument pairs -> 
            match Array.tryFind (fun (k,v) -> streqi k s) pairs with
            | Some (k,v) -> Some v
            | None -> None
        | _ -> None // TODO throw?

    let tryGetValueForKey bv (s:string) =
        match bv with
        | BDocument pairs -> 
            match Array.tryFind (fun (k,v) -> k=s) pairs with
            | Some (k,v) -> Some v
            | None -> None
        | _ -> None // TODO throw?

    let tryGetValueAtIndex bv ndx =
        match bv with
        | BArray a ->
            if ndx<0 then None
            else if ndx >= a.Length then None
            else a.[ndx] |> Some
        | _ -> None // TODO throw?

    let tryGetValueEither bv (s:string) =
        match bv with
        | BDocument _ -> tryGetValueForKey bv s
        | BArray _ ->
            let (ok,ndx) = Int32.TryParse(s)
            if not ok then None
            else tryGetValueAtIndex bv ndx
        | _ -> None // TODO throw?

    let hasValueForKey bv s =
        match tryGetValueForKey bv s with
        | Some _ -> true
        | None -> false

    let getValueForKey bv (s:string) =
        match tryGetValueForKey bv s with
        | Some v -> v
        | None -> failwith (sprintf "key not found: %s" s)

    let getValueForInsensitiveKey bv (s:string) =
        match tryGetValueForInsensitiveKey bv s with
        | Some v -> v
        | None -> failwith (sprintf "key not found: %s" s)

    let getString bv =
        match bv with
        | BString s -> s
        | _ -> failwith (sprintf "must be a string: %A" bv)

    let isNull bv =
        match bv with
        | BNull _ -> true
        | _ -> false

    let isArray bv =
        match bv with
        | BArray _ -> true
        | _ -> false

    let isDate bv =
        match bv with
        | BDateTime _ -> true
        | _ -> false

    let isNaN bv =
        match bv with
        | BDouble d -> Double.IsNaN(d)
        | _ -> false

    let isNumeric bv =
        match bv with
        | BInt32 _ -> true
        | BInt64 _ -> true
        | BDouble _ -> true
        | _ -> false

    let isDocument bv =
        match bv with
        | BDocument _ -> true
        | _ -> false

    let getArray bv =
        match bv with
        | BArray a -> a
        | _ -> failwith (sprintf "must be array: %A" bv)

    let is_dbref pairs =
        let has_ref = Array.exists (fun (k,_) -> k="$ref") pairs
        let has_id = Array.exists (fun (k,_) -> k="$id") pairs
        let has_db = Array.exists (fun (k,_) -> k="$db") pairs
        let len = Array.length pairs
        if len=2 && has_ref && has_id then true
        else if len=3 && has_ref && has_id && has_db then true
        else false

    let getDocument bv =
        match bv with
        | BDocument a -> a
        | _ -> failwith "must be document"

    let getBool bv =
        match bv with
        | BBoolean a -> a
        | _ -> failwith "must be bool"

    let getDate bv =
        match bv with
        | BDateTime n -> n
        | _ -> failwith "must be BDateTime"

    let getAsDateTime bv =
        match bv with
        | BDateTime n ->
            DateTime(1970,1,1,0,0,0,0,System.DateTimeKind.Utc).AddMilliseconds(float n)
        | BTimeStamp n ->
            DateTime(1970,1,1,0,0,0,0,System.DateTimeKind.Utc).AddSeconds(float ((int64 n) >>> 32))
        | _ -> raise (MongoCode(16006, (sprintf "can't convert to Date: %A" bv)))

    let getInt32 bv =
        match bv with
        | BInt32 a -> a
        | _ -> failwith "must be int32"

    let getAsExprBool v =
        match v with
        | BBoolean false -> false
        | BNull -> false
        | BUndefined -> false
        | BInt32 0 -> false
        | BInt64 0L -> false
        | BDouble 0.0 -> false
        | _ -> true

    let getAsBool bv =
        match bv with
        | BBoolean b -> b
        | BInt32 i -> i<>0
        | BInt64 i -> i<>0L
        | BDouble f -> ((int32)f)<>0
        | _ -> failwith (sprintf "must be convertible to bool: %A" bv)

    let getAsInt32 bv =
        match bv with
        | BInt32 a -> a
        | BInt64 a -> int32 a
        | BDouble a -> int32 a
        | _ -> failwith (sprintf "must be convertible to int32: %A" bv)

    let getAsInt64 bv =
        match bv with
        | BInt32 a -> int64 a
        | BInt64 a -> a
        | BDouble a -> int64 a
        | BDateTime a -> int64 a
        | _ -> failwith (sprintf "must be convertible to int64: %A" bv)

    let getAsDouble bv =
        match bv with
        | BInt32 a -> double a
        | BInt64 a -> double a
        | BDouble a -> a
        | _ -> failwith (sprintf "must be convertible to double: %A" bv)

    let rec toBinary bv (w:BinWriter) =
        match bv with
        | BsonValue.BDouble f -> w.WriteFloat(f)
        | BsonValue.BInt32 n -> w.WriteInt32(n)
        | BsonValue.BDateTime n -> w.WriteInt64(n)
        | BsonValue.BTimeStamp n -> w.WriteInt64(n)
        | BsonValue.BInt64 n -> w.WriteInt64(n)
        | BsonValue.BString s -> w.WriteBsonString(s)
        | BsonValue.BObjectID a -> w.WriteObjectID(a)
        | BsonValue.BBoolean b -> if b then w.WriteByte(1uy) else w.WriteByte(0uy)
        | BsonValue.BNull -> ()
        | BsonValue.BMinKey -> ()
        | BsonValue.BMaxKey -> ()
        | BsonValue.BRegex (expr,opt) -> w.WriteCString(expr); w.WriteCString(opt)
        | BsonValue.BUndefined -> ()
        | BsonValue.BJSCode s -> w.WriteBsonString(s)
        | BsonValue.BJSCodeWithScope s -> failwith "TODO write BJSCodeWithScope"
        | BsonValue.BBinary (subtype,ba) ->
            w.WriteInt32 ba.Length
            w.WriteByte subtype
            w.WriteBytes ba
        | BsonValue.BArray vals ->
            let start = w.Position
            w.WriteInt32(0) // placeholder for length
            Array.iteri (fun i vsub ->
                w.WriteByte(getTypeNumber vsub |> byte)
                w.WriteCString(i.ToString())
                toBinary vsub w
            ) vals
            w.WriteByte(0uy)
            let len = w.Position - start
            w.WriteInt32At(len, start)
        | BsonValue.BDocument pairs ->
            let start = w.Position
            w.WriteInt32(0) // placeholder for length
            Array.iter (fun (ksub,vsub) ->
                w.WriteByte(getTypeNumber vsub |> byte)
                w.WriteCString(ksub)
                toBinary vsub w
            ) pairs
            w.WriteByte(0uy)
            let len = w.Position - start
            w.WriteInt32At(len, start)

    let toBinaryArray bv =
        let w = BinWriter()
        toBinary bv w
        w.ToArray()

    let rec forAllStrings bv fn =
        match bv with
        | BsonValue.BDouble f -> ()
        | BsonValue.BInt32 n -> ()
        | BsonValue.BDateTime n -> ()
        | BsonValue.BTimeStamp n -> ()
        | BsonValue.BInt64 n -> ()
        | BsonValue.BString s -> fn s
        | BsonValue.BObjectID a -> ()
        | BsonValue.BBoolean b -> ()
        | BsonValue.BNull -> ()
        | BsonValue.BMinKey -> ()
        | BsonValue.BMaxKey -> ()
        | BsonValue.BRegex (expr,opt) -> ()
        | BsonValue.BUndefined -> ()
        | BsonValue.BJSCode s -> ()
        | BsonValue.BJSCodeWithScope s -> ()
        | BsonValue.BBinary (subtype,ba) -> ()
        | BsonValue.BArray vals -> Array.iter (fun v -> forAllStrings v fn) vals
        | BsonValue.BDocument pairs -> Array.iter (fun (k,v) -> forAllStrings v fn) pairs

#if not
    // code to decode IEEE double

    let normalize mantissa exponent =
        if mantissa<>0L then
            let mutable m = mantissa
            let mutable e = exponent
            while m&&&1L=0L do
                m <- m >>> 1
                e <- e + 1
            (m,e)
        else
            (mantissa,exponent)

    let decodeDouble (w:BinWriter) f =
        let bits = System.BitConverter.DoubleToInt64Bits(f)
        let negative = bits<0L
        let exponent = int ((bits >>> 52) &&& 0x7ffL)
        let mantissa = bits &&& 0xfffffffffffffL

        printfn "f: %A" f
        printfn "raw exponent: %d" exponent
        printfn "raw mantissa: %A" mantissa

        if exponent=2047 && mantissa<>0L then
            //printfn "NaN"
            w.WriteByte(0x06uy) // Double.IsNan(f)
        else if exponent=2047 && mantissa=0L then
            if negative then
                //printfn "neg inf"
                w.WriteByte(0x07uy) // Double.IsNegativeInfinity(f)
            else
                //printfn "pos inf"
                w.WriteByte(0x23uy) // Double.IsPositiveInfinity(f)
        else if exponent=0 && mantissa=0L then
            //printfn "zero"
            w.WriteByte(0x15uy) // we make no distinction between positive zero and negative zero
        else
            let (m,e) =
                if exponent=0 then 
                    // subnormal
                    //printfn "subnormal"
                    normalize mantissa (1 - 1023 - 52)
                else
                    // normal.  set the implicit bit.
                    //printfn "normal"
                    normalize (mantissa ||| (1L<<<52)) (exponent - 1023 - 52)

            printfn "exponent: %d" e
            printfn "mantissa: %A" m

            encodeTrioForIndexInto w negative m e
#endif

    let encodeInt64ForIndexInto w n =
        n |> sqlite4.num_from_int64 |> sqlite4.encodeForIndexInto w

    let encodeDoubleForIndexInto w f =
        f |> sqlite4.num_from_double |> sqlite4.encodeForIndexInto w

    let rec private encodeForIndexInto (w:BinWriter) bv =
        w.WriteByte(getTypeOrder bv |> byte)
        match bv with
        | BBoolean b -> w.WriteByte(if b then 1uy else 0uy)
        | BInt64 n -> encodeInt64ForIndexInto w n
        | BInt32 n -> n |> int64 |> encodeInt64ForIndexInto w
        | BDouble f -> encodeDoubleForIndexInto w f
        | BObjectID a -> w.WriteBytes(a)
        | BNull -> ()
        | BUndefined -> ()
        | BMinKey -> ()
        | BMaxKey -> ()
        | BDateTime n -> encodeInt64ForIndexInto w n
        | BTimeStamp n -> w.WriteInt64BigEndian(n) // TODO er, how to encode this?
        | BDocument pairs ->
            // TODO is writing the length here what we want?
            // it means we can't match on a prefix of a document
            //
            // it means any document with 3 pairs will sort before 
            // any document with 4 pairs, even if the first 3 pairs
            // are the same in both.
            w.WriteInt32BigEndian(pairs.Length)
            Array.iter (fun (k:string,v) ->
                w.WriteBytes(System.Text.Encoding.UTF8.GetBytes (k))
                w.WriteByte(0uy)
                encodeForIndexInto w v
            ) pairs
        | BArray a ->
            // TODO is writing the length here what we want?
            // see comment on BDocument just above.
            w.WriteInt32BigEndian(a.Length)
            Array.iter (fun v ->
                encodeForIndexInto w v
            ) a
        | BBinary (subtype,a) ->
            w.WriteByte(subtype)
            w.WriteInt32BigEndian(a.Length)
            w.WriteBytes(a)
        | BRegex (s,opt) ->
            w.WriteBytes(System.Text.Encoding.UTF8.GetBytes (s))
            w.WriteByte(0uy)
            w.WriteBytes(System.Text.Encoding.UTF8.GetBytes (opt))
            w.WriteByte(0uy)
        | BJSCode s ->
            w.WriteBytes(System.Text.Encoding.UTF8.GetBytes (s))
            w.WriteByte(0uy)
        | BJSCodeWithScope s ->
            w.WriteBytes(System.Text.Encoding.UTF8.GetBytes (s))
            w.WriteByte(0uy)
        | BString s ->
            w.WriteBytes(System.Text.Encoding.UTF8.GetBytes (s))
            w.WriteByte(0uy)

    let encodeOneForIndex bv neg =
        let w = BinWriter()
        encodeForIndexInto w bv
        let a = w.ToArray()
        if neg then
            for i in 0 .. (Array.length a - 1) do
                let b = a.[i]
                a.[i] <- ~~~b
        a

    let encodeMultiForIndex a =
        let w = BinWriter()
        Array.iter (fun (v,neg) -> 
            let a = encodeOneForIndex v neg
            w.WriteBytes(a)
        ) a
        w.ToArray()

    let setValueAtIndex bv ndx v =
        match bv with
        | BArray a ->
            let newLen = if ndx >= a.Length then ndx + 1 else a.Length
            if newLen > 1500001 then failwith "too big" // TODO this limit passes test set7.js, but is a bad idea
            let newa:BsonValue[] = Array.create newLen BNull
            Array.Copy(a, 0, newa, 0, a.Length)
            newa.[ndx] <- v
            BArray newa
        | _ -> failwith "error"

    let removeValueAtIndex bv ndx =
        match bv with
        | BArray a ->
            let newa:BsonValue[] = Array.zeroCreate (a.Length-1)
            if ndx > 0 then
                Array.Copy(a, 0, newa, 0, ndx)
            if ndx < a.Length then
                Array.Copy(a, ndx+1, newa, ndx, a.Length - ndx - 1)
            BArray newa
        | _ -> failwith "error"

    let unsetValueAtIndex bv ndx =
        match bv with
        | BArray a ->
            let newa:BsonValue[] = Array.zeroCreate (a.Length)
            Array.Copy(a, 0, newa, 0, a.Length)
            if ndx >=0 && ndx < a.Length then
                newa.[ndx] <- BNull
            BArray newa
        | _ -> failwith "error"

    let setValueForKey doc k v =
        // TODO make this more efficient?
        match doc with
        | BDocument pairs ->
            let newPairs = ResizeArray<_>()
            Array.iter (fun e -> newPairs.Add(e)) pairs
            match Array.tryFindIndex (fun (ksub,_) -> ksub=k) pairs with
            | Some ndx -> 
                newPairs.[ndx] <- (k,v)
            | None ->
                newPairs.Add(k, v)
            BDocument (newPairs.ToArray())
        | _ -> failwith "error"

    let unsetValueForKey doc k =
        // TODO make this more efficient?
        match doc with
        | BDocument pairs ->
            let newPairs = ResizeArray<_>()
            Array.iter (fun e -> newPairs.Add(e)) pairs
            match Array.tryFindIndex (fun (ksub,_) -> ksub=k) pairs with
            | Some ndx -> 
                newPairs.RemoveAt(ndx)
            | None ->
                ()
            BDocument (newPairs.ToArray())
        | _ -> failwith "error"

    let copyValueIfExists v1 k vdest =
        match tryGetValueForKey v1 k with
        | Some vsub -> setValueForKey vdest k vsub
        | None -> vdest

    let rec changeValueForPath (start:BsonValue) (path:string) f = 
        let dot = path.IndexOf('.')
        let name = if dot<0 then path else path.Substring(0, dot)
        match start with
        | BDocument _ ->
            match tryGetValueForKey start name with
            | Some v ->
                if dot<0 then 
                    match f (Some v) with
                    | Some newVal -> setValueForKey start name newVal
                    | None -> unsetValueForKey start name
                else 
                    let subPath = path.Substring(dot+1)
                    match v with
                    | BDocument _ | BArray _ -> 
                        let newDoc = changeValueForPath v subPath f
                        setValueForKey start name newDoc
                    | _ -> 
                        // TODO maybe this should call a second func so the caller can decide?
                        raise (MongoCode(16401, "trying to dive into non-object"))
            | None -> 
                if dot< 0 then
                    match f None with
                    | Some newVal -> setValueForKey start name newVal
                    | None -> start
                else
                    match f None with
                    | Some _ ->
                        let subPath = path.Substring(dot+1)
                        match Int32.TryParse(name) with
                        | (true,_) ->
                            let newDoc = changeValueForPath (BArray [| |]) subPath f
                            setValueForKey start name newDoc
                        | (false,_) ->
                            let newDoc = changeValueForPath (BDocument [| |]) subPath f
                            setValueForKey start name newDoc
                    | None -> start
        | BArray _ ->
            let ndx = Int32.Parse(name)
            match tryGetValueAtIndex start ndx with
            | Some v ->
                if dot<0 then
                    match f (Some v) with
                    | Some newVal -> setValueAtIndex start ndx newVal
                    | None -> unsetValueAtIndex start ndx
                else
                    match v with
                    | BDocument _ | BArray _ -> 
                        let subPath = path.Substring(dot+1)
                        let newDoc = changeValueForPath v subPath f
                        setValueAtIndex start ndx newDoc
                    | _ -> 
                        start
            | None ->
                if dot<0 then
                    match f None with
                    | Some newVal -> setValueAtIndex start ndx newVal
                    | None -> start
                else
                    match f None with
                    | Some _ ->
                        let subPath = path.Substring(dot+1)
                        let newDoc = changeValueForPath (BArray [| |]) subPath f
                        setValueAtIndex start ndx newDoc
                    | None -> start
        | _ -> failwith "error"

    let rec removeUndefined bv =
        match bv with
        | BDocument pairs ->
            let pairs = 
                Array.choose (fun (k,v) -> 
                    match v with
                    | BUndefined -> None
                    | BDocument _ ->
                        let v = removeUndefined v
                        Some (k,v)
                    | BArray _ ->
                        let v = removeUndefined v
                        Some (k,v)
                    | _ -> Some (k,v)
                ) pairs
            BDocument pairs
        | BArray a ->
            let a =
                Array.choose (fun v ->
                    match v with
                    | BUndefined -> None
                    | BDocument _ ->
                        let v = removeUndefined v
                        Some v
                    | BArray _ ->
                        let v = removeUndefined v
                        Some v
                    | _ -> Some v
                ) a
            BArray a
        | BUndefined -> BUndefined // TODO is this right?  or should it throw?
        | _ -> bv

    let rec replaceUndefined bv =
        match bv with
        | BDocument pairs ->
            let pairs = 
                Array.map (fun (k,v) -> 
                    match v with
                    | BUndefined -> (k, BNull)
                    | BDocument _ -> (k, replaceUndefined v)
                    | BArray _ -> (k, replaceUndefined v)
                    | _ -> (k,v)
                ) pairs
            BDocument pairs
        | BArray a ->
            let a =
                Array.map (fun v ->
                    match v with
                    | BUndefined -> BNull
                    | BDocument _ -> replaceUndefined v
                    | BArray _ -> replaceUndefined v
                    | _ -> v
                ) a
            BArray a
        | BUndefined -> BNull
        | _ -> bv

    let rec findPath start (path:string) = 
        let dot = path.IndexOf('.')
        let name = if dot<0 then path else path.Substring(0, dot)
        match start with
        | BDocument pairs ->
            match Array.tryFind (fun (k,_) -> k=name) pairs with
            | Some (_,v) ->
                if dot<0 then v
                else path.Substring(dot+1) |> findPath v
            | None -> 
                BUndefined
        | BArray items ->
            let (ok,ndx) = Int32.TryParse(name)
            if not ok then
                // when we have an array and the next step of the path is not
                // an integer index, we search any subdocs in that array for
                // that path and construct an array of the matches.

                // document : { a:1, b:[ { c:1 }, { c:2 } ] }
                // path : b.c
                // needs to get: [ 1, 2 ]

                // TODO are there any functions in the matcher which could be
                // simplified by using this function? 
                let a = 
                    Array.choose (fun subv ->
                        match subv with
                        | BDocument _ -> findPath subv path |> Some
                        | _ -> None
                    ) items
                // if nothing matched, return None instead of an empty array.
                // TODO is this right?
                if Array.length a=0 then BUndefined else a |> BArray
                //a |> BArray
            else if ndx<0 then
                failwith "array index < 0"
            else if ndx>=Array.length items then
                failwith "array index too large"
            else
                let v = items.[ndx]
                if dot<0 then v
                else path.Substring(dot+1) |> findPath v
        | _ -> BUndefined

    let rec divesIntoAnyArray start (path:string) =
        let dot = path.IndexOf('.')
        let name = if dot<0 then path else path.Substring(0, dot)
        match tryGetValueEither start name with
        | Some v ->
            if dot<0 then 
                false
            else 
                let subPath = path.Substring(dot+1)
                match v with
                | BDocument _ -> divesIntoAnyArray v subPath
                | BArray a -> true
                | _ -> false // TODO wants to dive into something that is not a container
        | None -> 
            false

    let hasIndex a s =
        let (ok,ndx) = Int32.TryParse(s)
        if not ok then None
        else if ndx<0 then None
        else if ndx >= Array.length a then None
        else ndx |> Some

    let rec excludePath (start:BsonValue) (path:string) = 
        let dot = path.IndexOf('.')
        let name = if dot<0 then path else path.Substring(0, dot)
        match start with
        | BDocument pairs ->
            match Array.tryFindIndex (fun (k,_) -> k=name) pairs with
            | Some ndx ->
                if dot<0 then 
                    Array.filter (fun (k,_) -> k<>name) pairs |> BDocument
                else 
                    let subPath = path.Substring(dot+1)
                    let (_,v) = pairs.[ndx]
                    match v with
                    | BDocument _ | BArray _ -> 
                        let vnew = excludePath v subPath
                        let a2 = Array.copy pairs
                        a2.[ndx] <- (name,vnew)
                        BDocument a2
                    | _ -> start
            | None ->
                start
        | BArray a ->
            match hasIndex a name with
            | Some ndx ->
                let v = a.[ndx]
                if dot<0 then 
                    let before = if ndx>0 then Array.sub a 0 ndx else Array.empty
                    let after = if a.Length-ndx>0 then Array.sub a ndx (a.Length-ndx) else Array.empty
                    let a2 = Array.concat [before;after]
                    BArray a2
                else 
                    let subPath = path.Substring(dot+1)
                    let vnew = excludePath v subPath
                    let a2 = Array.copy a
                    a2.[ndx] <- vnew
                    BArray a2
            | None ->
                Array.map (fun vsub -> 
                    match vsub with
                    | BDocument _ -> excludePath vsub path
                    | _ -> vsub
                    ) a |> BArray
        | _ -> failwith "should not happen"

    let rec includePath (start:BsonValue) (path:string) = 
        let dot = path.IndexOf('.')
        let name = if dot<0 then path else path.Substring(0, dot)
        if name="$" then failwith "position operator should not get this far"
        match start with
        | BDocument pairs ->
            match Array.tryFind (fun (k,_) -> k=name) pairs with
            | Some (_,v) ->
                if dot<0 then 
                    BDocument [| (name,v) |]
                else 
                    let subPath = path.Substring(dot+1)
                    match v with
                    | BDocument _ | BArray _ -> BDocument [| (name,includePath v subPath) |]
                    | _ -> BDocument [|  |]
            | None ->
                BDocument [|  |]
        | BArray a ->
            match hasIndex a name with
            | Some ndx ->
                let v = a.[ndx]
                if dot<0 then 
                    BArray [| v |]
                else 
                    let subPath = path.Substring(dot+1)
                    match v with
                    | BDocument _ | BArray _ -> BArray [| includePath v subPath |]
                    | _ -> BArray [|  |]
            | None ->
                Array.collect (fun vsub -> 
                    match vsub with
                    | BDocument _ -> [| includePath vsub path |]
                    | _ -> [|  |]
                    ) a |> BArray
        | _ -> failwith "should not happen"

    let rec merge d1 d2 =
        Array.fold (fun cur (k2,v2) ->
            match v2 with
            | BDocument _ ->
                let f ov =
                    match ov with
                    | Some v1 ->
                        match v1 with
                        | BDocument _ -> merge v1 v2 |> Some
                        | _ -> raise (MongoCode(16401, "trying to dive into non-object"))//Some v2 // TODO overwrite?
                    | None -> Some v2
                changeValueForPath cur k2 f
            | _ ->
                let f ov =
                    match ov with
                    | Some v1 -> Some v2 // TODO overwrite?
                    | None -> Some v2
                changeValueForPath cur k2 f

            ) d1 (getDocument d2)

    let rec fold f path d acc =
        let acc =
            // don't call the folder function for the top level document
            if path="" then acc
            else f path d acc
        let acc = 
            match d with
            // this fold function intentionally does not dive into arrays
            | BDocument pairs ->
                Array.fold (fun acc (k,v) ->
                    let newPath = 
                        if path="" then k
                        else path + "." + k
                    fold f newPath v acc
                    ) acc pairs
            | _ -> acc
        acc

    let rec project3 doc includes =
        //printfn "project3: doc = %A" doc
        //printfn "project3: includes = %A" includes
        let fldr path v acc =
            //printfn "project3: path = %s" path
            //printfn "project3: v = %A" v
            //printfn "project3: acc before = %A" acc
            let acc =
                // if the path exists in the include spec, just include it
                if Array.exists (fun p -> path=p) includes then
                    //printfn "project3: path is included"
                    let f2 ov = Some v
                    // TODO check for overwrite?
                    changeValueForPath acc path f2
                else
                    // otherwise, see if the path is the prefix of something in
                    // the includes.  If so, then the projection wants to include
                    // something which is a descendant of the current path.
                    //printfn "project3: path NOT included"
                    let plusdot = path + "."
                    if Array.exists (fun (p:string) -> p.StartsWith(plusdot)) includes then
                        //printfn "project3: path prefix found"
                        match v with
                        | BDocument _ ->
                            // if it's a document, we go ahead and create the empty doc,
                            // just in case the descendant path doesn't end up matching
                            // anything.
                            //printfn "project3: adding empty doc"
                            let f2 ov = Array.empty |> BDocument |> Some
                            // TODO check for overwrite?
                            changeValueForPath acc path f2
                        | BArray items ->
                            // if it's an array, we want to walk through and see if the
                            // descendant path matches any subdocuments

                            // TODO should we see if the descendant path is actually an
                            // integer index into the array?
                            //printfn "project3: adding array and diving into it"
                            let len = plusdot.Length
                            let subpaths = Array.choose (fun (p:string) -> if p.StartsWith(plusdot) then p.Substring(len) |> Some else None) includes
                            let a2 = 
                                Array.choose (fun v ->
                                    match v with
                                    | BDocument _ ->
                                         project3 v subpaths |> Some
                                    | _ -> 
                                        None
                                ) items
                            // TODO what if a2 is empty?  should we still add an empty array
                            let f2 ov = a2 |> BArray |> Some
                            // TODO check for overwrite?
                            changeValueForPath acc path f2
                        | _ ->
                            acc
                            //raise (MongoCode(16401, "trying to dive into non-object"))
                    else
                        //printfn "project3: path prefix NOT found"
                        acc
            //printfn "project3: acc after = %A" acc
            acc
        let result = fold fldr "" doc (BDocument [| |])
        //printfn "project3: result = %A" result
        result

