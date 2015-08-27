(*
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
*)

namespace Zumero

module test = 

    open System

    let numtest() =
        let sortByNumber t1 t2 =
            let f1 = fst t1
            let f2 = fst t2
            Matcher.cmp f1 f2

        let sortByEncoding t1 t2 =
            let f1 = snd t1
            let f2 = snd t2
            bson.bcmp f1 f2

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
        let b = Array.map (fun f -> (f,bson.encodeOneForIndex f false)) a
        let s1 = b |> Array.copy
        Array.sortInPlaceWith sortByNumber s1
        let s2 = b |> Array.copy 
        Array.sortInPlaceWith sortByEncoding s2
        printfn "%A" s1
        printfn "%A" s2
        if s1=s2 then printfn "MATCH" else printfn "NOT"

    let num (s:string) =
        let f = double s
        let x = bson.encodeOneForIndex (f |> BDouble) false
        printfn "%A" x

