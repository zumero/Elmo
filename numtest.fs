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

module test = 

    open System

    // lexicographic compare
    // TODO move this somewhere else
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

    let numtest() =
        let sortByNumber t1 t2 =
            let f1 = fst t1
            let f2 = fst t2
            Matcher.cmp f1 f2

        let sortByEncoding t1 t2 =
            let f1 = snd t1
            let f2 = snd t2
            bcmp f1 f2

        let r = Random(42)
        let frand() =
            match r.Next()%9 with
            | 0 ->
                let v = r.NextDouble() * float (r.Next(1000))
                let neg = (r.Next() % 2)=0
                let v = if neg then -v else v
                BDouble v 
            | 1 ->
                let v = r.Next()
                let neg = (r.Next() % 2)=0
                let v = if neg then -v else v
                BInt32 v
            | 2 ->
                let v = (r.Next() |> int64) * (r.Next() |> int64)
                let neg = (r.Next() % 2)=0
                let v = if neg then -v else v
                BInt64 v
            | 3 ->
                let v = r.NextDouble()
                let neg = (r.Next() % 2)=0
                let v = if neg then -v else v
                BDouble v 
            | 4 ->
                let v = r.Next(1000)
                let neg = (r.Next() % 2)=0
                let v = if neg then -v else v
                BInt32 v
            | 5 ->
                let v = r.NextDouble() * float (r.Next(10))
                let neg = (r.Next() % 2)=0
                let v = if neg then -v else v
                BDouble v 
            | 6 ->
                BInt32 0
            | 7 ->
                Double.PositiveInfinity |> BDouble
            | 8 ->
                Double.NegativeInfinity |> BDouble
            // TODO NaN would be nice here too, but of course it causes the match comparison to fail.  :-)

        let a:BsonValue[] = Array.zeroCreate 500 |> Array.map (fun _ -> frand())
        let b = Array.map (fun f -> (f,bson.encodeOneForIndex f bson.IndexType.Forward)) a
        let s1 = b |> Array.copy
        Array.sortInPlaceWith sortByNumber s1
        let s2 = b |> Array.copy 
        Array.sortInPlaceWith sortByEncoding s2
        printfn "%A" s1
        printfn "%A" s2
        if s1=s2 then printfn "MATCH" else printfn "NOT"

    let num (s:string) =
        let f = double s
        let x = bson.encodeOneForIndex (f |> BDouble) bson.IndexType.Forward
        printfn "%A" x

