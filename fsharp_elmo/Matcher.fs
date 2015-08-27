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

type QueryDoc = 
    | QueryDoc of items:QueryItem[]
and QueryItem =
    | Compare of path:string*preds:(Pred[])
    | AND of docs:QueryDoc[]
    | OR of docs:QueryDoc[]
    | NOR of docs:QueryDoc[]
    | Where of BsonValue
    | Text of string
and Pred =
    | Exists of bool
    | Size of int
    | Type of int
    | Mod of div:int64*rem:int64 // mongo apparently forces these values to integers
    | ElemMatchObjects of QueryDoc
    | ElemMatchPreds of Pred[]
    | Not of Pred[]
    | In of BsonValue[]
    | Nin of BsonValue[]
    | All of BsonValue[]
    | AllElemMatchObjects of QueryDoc[]
    | EQ of BsonValue
    | NE of BsonValue
    | GT of BsonValue
    | LT of BsonValue
    | GTE of BsonValue
    | LTE of BsonValue
    | REGEX of System.Text.RegularExpressions.Regex
    | Near of BsonValue
    | NearSphere of BsonValue
    | GeoWithin of BsonValue
    | GeoIntersects of BsonValue

module Matcher = 

    open System

    let rec cmp d lit =
        //printfn "compare: %A  %A" d lit
        match d,lit with
        | BObjectID m, BObjectID litv -> 
            // TODO er, what does F# < do for a byte[] ?
            if m=litv then 0
            else if m<litv then -1
            else 1
        | BInt32 m, BInt32 litv -> 
            if m=litv then 0
            else if m<litv then -1
            else 1
        | BInt64 m, BInt64 litv ->
            if m=litv then 0
            else if m<litv then -1
            else 1
        | BDateTime m, BDateTime litv ->
            if m=litv then 0
            else if m<litv then -1
            else 1
        | BTimeStamp m, BTimeStamp litv ->
            if m=litv then 0
            else if m<litv then -1
            else 1
        | BDouble m, BDouble litv ->
            let result = 
                if m=litv then 0
                else if Double.IsNaN(m) && Double.IsNaN(litv) then 0
                else if Double.IsNaN(m) then -1
                else if Double.IsNaN(litv) then 1
                else if m<litv then -1
                else 1
            //printfn "cmp: %A  vs  %A = %d" m litv result
            result
        | BString m, BString litv ->
            if m=litv then 0
            else if m<litv then -1
            else 1
        | BBoolean m, BBoolean litv ->
            if m=litv then 0
            else if m then 1
            else -1
        | BInt32 m, BInt64 litv -> 
            let m = int64 m
            if m=litv then 0
            else if m<litv then -1
            else 1
        | BInt32 m, BDouble litv ->
            let m = float m
            if m=litv then 0
            else if Double.IsNaN(litv) then 1
            else if m<litv then -1
            else 1
        | BInt64 m, BInt32 litv ->
            let litv = int64 litv
            if m=litv then 0
            else if m<litv then -1
            else 1
        | BInt64 m, BDouble litv ->
            // TODO this can overflow
            let m = float m
            if m=litv then 0
            else if Double.IsNaN(litv) then 1
            else if m<litv then -1
            else 1
        | BDouble m, BInt32 litv ->
            // when comparing double and int, cast the int to double, regardless of ordering
            let litv = float litv
            if m=litv then 0
            else if Double.IsNaN(m) then -1
            else if m<litv then -1
            else 1
        | BDouble m, BInt64 litv ->
            // when comparing double and int, cast the int to double, regardless of ordering
            // TODO this can overflow
            let litv = float litv
            if m=litv then 0
            else if Double.IsNaN(m) then -1
            else if m<litv then -1
            else 1
        | BNull , BNull -> 0
        | BUndefined , BUndefined -> 0
        | BArray m, BArray litv ->
            let lenm = m.Length
            let lenlitv = litv.Length
            let rec loop i =
                if i=lenm && i=lenlitv then 0
                else if i=lenm then -1
                else if i=lenlitv then 1
                else
                    let e = cmp (m.[i]) (litv.[i])
                    if e=0 then loop (i+1)
                    else e
            loop 0
        | BDocument m, BDocument litv ->
            let lenm = m.Length
            let lenlitv = litv.Length
            let rec loop i =
                if i=lenm && i=lenlitv then 0
                else if i=lenm then -1
                else if i=lenlitv then 1
                else
                    let (km,vm) = m.[i]
                    let (klitv,vlitv) = litv.[i]
                    if km < klitv then -1
                    else if km > klitv then 1
                    else
                        let e = cmp vm vlitv
                        if e=0 then loop (i+1)
                        else e
            loop 0
        | _ ->
            let torder_d = bson.getTypeOrder d
            let torder_lit = bson.getTypeOrder lit
            if torder_d = torder_lit then
                failwith (sprintf "should have been handled above: d = %A  lit = %A" d lit)
            else if torder_d < torder_lit then
                -1
            else
                1

    let arrayMin a =
        Array.fold (fun cur v ->
            match cur with
            | Some win ->
                let c = cmp v win
                if c<0 then Some v else cur
            | None ->
                Some v
            ) None a

    let arrayMax a =
        Array.fold (fun cur v ->
            match cur with
            | Some win ->
                let c = cmp v win
                if c>0 then Some v else cur
            | None ->
                Some v
            ) None a

    let cmpdir d lit dir =
        // when comparing an array against something else during sort:
        // if two arrays, compare element by element.
        // if array vs. not-array, find the min or max (depending on the
        // sort direction) of the array and compare against that.
        let c =
            match d,lit with
            | BArray _, BArray _ -> cmp d lit
            | BArray a, _ ->
                let om = 
                    if dir < 0 then
                        arrayMax a
                    else
                        arrayMin a
                match om with
                | Some m -> cmp m lit
                | None -> cmp d lit // TODO right behavior for empty array?
            | _, BArray a ->
                let om = 
                    if dir < 0 then
                        arrayMax a
                    else
                        arrayMin a
                match om with
                | Some m -> cmp d m
                | None -> cmp d lit // TODO right behavior for empty array?
            | _ -> cmp d lit
        dir * c

    let cmpEQ (d:BsonValue) (lit:BsonValue) =
        let torder_d = bson.getTypeOrder d
        let torder_lit = bson.getTypeOrder lit
        if torder_d = torder_lit then
            let c = cmp d lit
            0 = c
        else
            false

    let private cmpIn d lit =
        match lit with
        | BRegex (expr,options) ->
            // TODO constructing the regex object here is inefficient
            // TODO options
            let r = System.Text.RegularExpressions.Regex(expr)
            match d with
            | BString s ->
                let m = r.Match(s)
                m.Success
            | _ ->
                false
        | _ -> cmpEQ d lit

    let private cmpLT (d:BsonValue) (lit:BsonValue) =
        let dnan = bson.isNaN d
        let litnan = bson.isNaN lit
        if dnan || litnan then
            false
        else
            let torder_d = bson.getTypeOrder d
            let torder_lit = bson.getTypeOrder lit
            if torder_d = torder_lit then
                let c = cmp d lit
                -1 = c
            else
                false

    let private cmpGT (d:BsonValue) (lit:BsonValue) =
        let dnan = bson.isNaN d
        let litnan = bson.isNaN lit
        if dnan || litnan then
            false
        else
            let torder_d = bson.getTypeOrder d
            let torder_lit = bson.getTypeOrder lit
            if torder_d = torder_lit then
                let c = cmp d lit
                1 = c
            else
                false

    let private cmpLTE (d:BsonValue) (lit:BsonValue) =
        let dnan = bson.isNaN d
        let litnan = bson.isNaN lit
        if dnan || litnan then
            dnan && litnan
        else
            let torder_d = bson.getTypeOrder d
            let torder_lit = bson.getTypeOrder lit
            if torder_d = torder_lit then
                let c = cmp d lit
                if c=0 then
                    true
                else
                    c<0
            else
                false

    let private cmpGTE (d:BsonValue) (lit:BsonValue) =
        let dnan = bson.isNaN d
        let litnan = bson.isNaN lit
        if dnan || litnan then
            dnan && litnan
        else
            let torder_d = bson.getTypeOrder d
            let torder_lit = bson.getTypeOrder lit
            if torder_d = torder_lit then
                let c = cmp d lit
                if c=0 then
                    true
                else
                    c>0
            else
                false

    let rec doElemMatchObjects doc d cbArrayPos =
        // TODO call cbArrayPos here?
        match d with
        | BArray a ->
            Array.exists (fun (vsub:BsonValue) ->
                match vsub with
                | BDocument _ | BArray _ -> matchQueryDoc doc vsub cbArrayPos
                | _ -> false
                ) a
        | _ -> false

    and private matchPredicate pred d cbArrayPos =
        //printfn "matchPredicate: pred = %A" pred
        //printfn "matchPredicate:    d = %A" d
        match pred with
        | Exists b -> failwith (sprintf "should not happen: %A" pred)
        | Not preds -> 
            let anyMatches = Array.exists (fun p -> matchPredicate p d cbArrayPos) preds
            not anyMatches
        | NE lit -> 
            let b = cmpEQ d lit
            not b
        | ElemMatchObjects doc -> // TODO call the func above
            match d with
            | BArray a ->
                let found =
                    Array.tryFindIndex (fun (vsub:BsonValue) ->
                        match vsub with
                        | BDocument _ | BArray _ -> matchQueryDoc doc vsub cbArrayPos
                        | _ -> false
                        ) a
                match found with
                | Some n -> 
                    cbArrayPos "TODO" n
                    true
                | None -> 
                    false
            | _ -> false
        | ElemMatchPreds preds ->
            match d with
            | BArray a ->
                let found =
                    Array.tryFindIndex (fun (v:BsonValue) ->
                        let anyMisses = Array.exists (fun (p:Pred) -> matchPredicate p v cbArrayPos |> not) preds
                        not anyMisses
                        ) a
                match found with
                | Some n -> 
                    cbArrayPos "TODO" n
                    true
                | None -> 
                    false
            | _ -> false
        | AllElemMatchObjects docs ->
            Array.exists (fun doc ->
                // for each elemMatch doc in the $all array, run it against
                // the candidate array.  if any elemMatch doc fails, false.
                doElemMatchObjects doc d cbArrayPos |> not
                ) docs |> not
        | All lits ->
            // TODO does this ever happen, now that it is handled earlier?
            if lits.Length=0 then
                false
            else
                Array.exists (fun lit ->
                    let b =
                        if cmpEQ d lit then
                            true
                        else
                            match d with
                            | BArray a ->
                                Array.exists (fun v -> cmpEQ v lit) a
                            | _ -> false
                    not b
                    ) lits |> not
        | Size n -> 
            match d with 
            | BArray a -> a.Length = n
            | _ -> false
        | Type n -> n = bson.getTypeNumber d
        | Mod (div,rem) -> 
            match d with
            | BInt32 n -> (int64 n % div) = rem
            | BInt64 n -> (n % div) = rem
            | BDouble n -> (int64 n % div) = rem
            | _ -> false
        | In lits -> Array.exists (fun v -> cmpIn d v) lits
        | Nin lits -> Array.exists (fun v -> cmpIn d v) lits |> not
        | EQ lit -> cmpEQ d lit
        | GT lit -> cmpGT d lit
        | LT lit -> cmpLT d lit
        | GTE lit -> cmpGTE d lit
        | LTE lit -> cmpLTE d lit
        | REGEX r ->
            match d with
            | BString s ->
                let m = r.Match(s)
                m.Success
            | _ ->
                false
        | Near _ -> failwith "not implemented yet"
        | NearSphere _ -> failwith "not implemented yet"
        | GeoWithin _ -> failwith "not implemented yet"
        | GeoIntersects _ -> failwith "not implemented yet"

    and private matchPair_exists pred (path:string) (start:BsonValue) =
        // TODO pred argument is unused
        //printfn "Match: path=%s  start=%A" path start
        let dot = path.IndexOf('.')
        let name = if dot<0 then path else path.Substring(0, dot)
        match bson.tryGetValueEither start name with
        | Some v ->
            if dot<0 then 
                true
            else 
                let subPath = path.Substring(dot+1)
                match v with
                | BDocument _ ->
                    matchPair_exists pred subPath v
                | BArray a ->
                    let b = matchPair_exists pred subPath v
                    if b then 
                        true
                    else
                        let f vsub =
                            match vsub with
                            | BDocument _ -> matchPair_exists pred subPath vsub
                            | _ -> false
                        Array.exists f a
                | _ -> false
        | None -> false

    and private matchPair_other pred (path:string) start arr cbArrayPos = // TODO arr is ugly
        //printfn "Match: path=%s  start=%A  pred=%A" path start pred
        let dot = path.IndexOf('.')
        let name = if dot<0 then path else path.Substring(0, dot)
        match bson.tryGetValueEither start name with
        | Some v ->
            if dot<0 then
                let b = matchPredicate pred v cbArrayPos
                if b then
                    true
                else if not arr then
                    match pred with
                    | Size _ -> false
                    | All _ -> false
                    | ElemMatchPreds _ -> false
                    | _ ->
                        match v with
                        | BArray a -> 
                            match Array.tryFindIndex (fun (vsub:BsonValue) -> matchPredicate pred vsub cbArrayPos) a with
                            | Some ndx ->
                                cbArrayPos name ndx
                                true
                            | None -> false
                        | _ -> false
                else
                    false
            else 
                let subPath = path.Substring(dot+1)
                match v with
                | BDocument _ ->
                    matchPair_other pred subPath v false cbArrayPos
                | BArray a ->
                    let b = matchPair_other pred subPath v true cbArrayPos
                    if b then 
                        true
                    else
                        let f vsub =
                            match vsub with
                            | BDocument _ -> matchPair_other pred subPath vsub false cbArrayPos
                            | _ -> false
                        match Array.tryFindIndex f a with
                        | Some ndx ->
                            cbArrayPos name ndx
                            true
                        | None -> false
                | _ -> 
                    match pred with
                    | Type n -> false
                    | _ -> matchPredicate pred (BsonValue.BNull) cbArrayPos
        | None -> 
            if arr then 
                false
            else 
                match pred with
                | Type n -> false
                | _ -> matchPredicate pred (BsonValue.BNull) cbArrayPos

    and private matchPair pred path start cbArrayPos =
        // not all predicates do their path searching in the same way
        // TODO consider a reusable function which generates all possible paths
        match pred with
        | All a ->
            if a.Length=0 then
                false
            else
                let anyMisses = 
                    Array.exists (fun lit ->
                        let subst = EQ lit
                        matchPair subst path start cbArrayPos |> not
                        ) a
                not anyMisses
        // TODO do we need AllElemMatchObjects here?
        | Exists b -> 
            b = matchPair_exists pred path start
        | Not a ->
            let anyMatches = Array.exists (fun (p:Pred) -> matchPair p path start cbArrayPos |> not) a
            anyMatches
        | NE a ->
            // TODO since this is implemented in matchPredicate, it seems like we should
            // be able to remove this implementation.  but if we do, some tests fail.
            // figure out exactly why.
            let subst = EQ a
            let b = matchPair subst path start cbArrayPos
            not b
        | Nin a ->
            // TODO since this is implemented in matchPredicate, it seems like we should
            // be able to remove this implementation.  but if we do, some tests fail.
            // figure out exactly why.
            let subst = In a
            let b = matchPair subst path start cbArrayPos
            not b
        | _ -> 
            matchPair_other pred path start false cbArrayPos

    and private matchQueryItem qit d cbArrayPos =
        match qit with
        | Compare (path,preds) ->
            let anyMisses = Array.exists (fun psub -> matchPair psub path d cbArrayPos |> not) preds
            not anyMisses
        | AND docs ->
            let anyMisses = Array.exists (fun psub -> matchQueryDoc psub d cbArrayPos |> not) docs
            not anyMisses
        | OR docs ->
            let anyMatches = Array.exists (fun psub -> matchQueryDoc psub d cbArrayPos) docs
            anyMatches
        | NOR docs ->
            let anyMatches = Array.exists (fun psub -> matchQueryDoc psub d cbArrayPos) docs
            not anyMatches
        | Text s ->
            true // TODO is there more work to do here?  or does the index code deal with it all now?
        | Where _ ->
            failwith "$where is not supported" //16395 in agg

    and matchQueryDoc q d cbArrayPos =
        let (QueryDoc items) = q
        // AND
        let anyMisses = Array.exists (fun qit -> matchQueryItem qit d cbArrayPos |> not) items
        not anyMisses

    let isValidWithinAll v =
        match v with
        | BDocument pairs -> 
            not (Array.exists (fun (k:string,v) -> k.StartsWith("$")) pairs)
        | _ -> 
            true

    let isValidWithinIn v =
        match v with
        | BDocument pairs -> 
            not (Array.exists (fun (k:string,v) -> k.StartsWith("$")) pairs)
        | _ -> 
            true

    // used for checking projection pos op against query
    let getPaths q =
        let a = ResizeArray<_>()

        let rec f q =
            let (QueryDoc items) = q
            Array.iter (fun qit ->
                match qit with
                | Compare (path, preds) ->
                    a.Add(path)
                | AND docs ->
                    Array.iter (fun d ->
                        f d
                        ) docs
                | _ -> ()
                ) items

        f q
        a.ToArray() |> Set.ofArray |> Set.toArray

    // used for upsert
    let getEqs q =
        let a = ResizeArray<_>()

        let rec f q =
            let (QueryDoc items) = q
            Array.iter (fun qit ->
                match qit with
                | Compare (path, preds) ->
                    Array.iter (fun psub ->
                        match psub with
                        | EQ v ->
                            a.Add(path, v)
                        | _ -> ()
                        ) preds
                | AND docs ->
                    Array.iter (fun d ->
                        f d
                        ) docs
                | _ -> ()
                ) items

        f q
        let result = a.ToArray()
        let keys = Array.map (fun (k,_) -> k) result |> Set.ofArray
        if Set.count keys <> Array.length result then failwith "duplicates found"
        result

    let makeRegex expr (options:string) =
        // TODO look at .NET Ecmascript compat mode for regex
        let opt = System.Text.RegularExpressions.RegexOptions.None
        let opt = if options.Contains("i") then opt ||| System.Text.RegularExpressions.RegexOptions.IgnoreCase else opt
        let opt = if options.Contains("s") then opt ||| System.Text.RegularExpressions.RegexOptions.Singleline else opt
        let opt = if options.Contains("m") then opt ||| System.Text.RegularExpressions.RegexOptions.Multiline else opt
        let r = System.Text.RegularExpressions.Regex(expr, opt) // TODO options, compatibility
        r

    let isQueryDoc v =
        let pairs = bson.getDocument v
        let hasPath = Array.exists (fun (k:string,v) -> k.StartsWith("$") |> not) pairs
        let hasAnd = Array.exists (fun (k:string,v) -> k="$and") pairs
        let hasOr = Array.exists (fun (k:string,v) -> k="$or") pairs
        let hasNor = Array.exists (fun (k:string,v) -> k="$nor") pairs
        hasPath || hasAnd || hasOr || hasNor

    let rec private parseQueryDoc d =
        let pairs = bson.getDocument d
        let result = ResizeArray<_>()
        Array.iter (fun (k,v) -> 
            let do_andor v f =
                let a = bson.getArray v
                if a.Length=0 then failwith "array for $and $or $nor cannot be empty"
                if a.Length=1 then
                    let subpairs = parseQueryDoc (a.[0])
                    Array.iter (fun it -> result.Add(it)) subpairs
                else
                    result.Add(f (Array.map (fun d -> parseQueryDoc d |> QueryDoc) a))
            match k with
            | "$comment" -> ()
            | "$atomic" -> ()
            | "$where" -> result.Add(QueryItem.Where v)
            | "$and" -> do_andor v QueryItem.AND
            | "$or" -> do_andor v QueryItem.OR
            | "$text" -> 
                match v with
                | BDocument pairs ->
                    // TODO there's a language tag in here as well
                    match Array.tryFind (fun (k,v) -> k="$search") pairs with
                    | Some (_,BString s) -> result.Add(QueryItem.Text s)
                    | _ -> failwith "invalid $text"
            | "$nor" -> 
                let a = bson.getArray v
                if a.Length=0 then failwith "array for $and $or $nor cannot be empty"
                // TODO what if just one?  canonicalize?
                let b = Array.map (fun d -> parseQueryDoc d |> QueryDoc) a
                result.Add(QueryItem.NOR (b))
            | _ -> result.Add(parseCompare k v)
        ) pairs
        result.ToArray()

    and private parsePred k v =
        let not_regex v =
            match v with
            | BRegex _ -> failwith "regex not allowed here"
            | _ -> v

        let not_empty a =
            if Array.length a=0 then failwith "empty not allowed"
            else a

        match k with
        | "$eq" -> Pred.EQ v
        | "$ne" -> Pred.NE (not_regex v)
        | "$gt" -> Pred.GT (not_regex v)
        | "$lt" -> Pred.LT (not_regex v)
        | "$gte" -> Pred.GTE (not_regex v)
        | "$lte" -> Pred.LTE (not_regex v)
        | "$regex" -> 
            // TODO can this regex have options?
            let expr = bson.getString v
            System.Text.RegularExpressions.Regex(expr) |> Pred.REGEX
        | "$exists" -> bson.getAsBool v |> Pred.Exists
        | "$type" -> bson.getAsInt32 v |> Pred.Type
        | "$size" ->
            match v with
            | BInt32 n -> n |> Pred.Size
            | BInt64 n ->
                // protect from overflow issues converting really large negative int64
                // to int32.  if it started out negative, just leave it negative.
                // mongo jira SERVER-11952
                // TODO what about large positive?
                let n2 = if n<0L then -1 else n |> int32
                n2 |> Pred.Size
            | BString _ -> 0 |> Pred.Size
            | BDouble f -> 
                // accept a double only if it's really an integer
                let n = int32 f
                let f2 = float n
                let arg = if f2=f then n else -1
                arg |> Pred.Size 
            | _ -> failwith "bad arg to $size" // TODO is this the right behavior?
        | "$all" -> 
            let a = bson.getArray v
            if Array.exists (fun bv ->
                // TODO make sure ALL of the items are elemMatch
                match bv with
                | BDocument pairs ->
                    if pairs.Length=1 then
                        let (k,_) = pairs.[0]
                        k="$elemMatch"
                    else
                        false
                | _ -> false
            ) a then
                let a2 = 
                    Array.map (fun bv -> 
                        let pairs = bson.getDocument bv
                        let (k,v) = pairs.[0]
                        // TODO assert k = $elemMatch
                        parseQueryDoc v |> QueryDoc
                        ) a
                Pred.AllElemMatchObjects a2
            else
                // TODO these all have to be plain literals
                if Array.exists (fun v -> isValidWithinAll v |> not) a then failwith "literals only"
                Pred.All a
        | "$in" -> 
            let a = bson.getArray v
            if Array.exists (fun v -> isValidWithinIn v |> not) a then failwith "literals only"
            Pred.In a
        | "$nin" -> 
            let a = bson.getArray v
            if Array.exists (fun v -> isValidWithinIn v |> not) a then failwith "literals only"
            Pred.Nin a
        | "$not" -> 
            match v with
            | BDocument pairs -> pairs |> not_empty |> parsePredList |> Pred.Not
            | BRegex (expr,options) -> [| makeRegex expr options |> Pred.REGEX |] |> Pred.Not
            | _ -> failwith "invalid for $not"
        | "$mod" -> 
            let a = bson.getArray v
            // TODO a.length must be 2
            let div = a.[0] |> bson.getAsInt64
            let rem = a.[1] |> bson.getAsInt64
            if div=0L then raise (MongoCode(16810, "divide by 0"))
            Pred.Mod (div, rem)
        | "$elemMatch" ->
            if isQueryDoc v then
                v |> parseQueryDoc |> QueryDoc |> ElemMatchObjects
            else
                v |> bson.getDocument |> parsePredList |> ElemMatchPreds
        | "$near" -> Pred.Near v // TODO might want to parse this further now
        | "$nearSphere" -> Pred.NearSphere v // TODO might want to parse this further now
        | "$geoWithin" -> Pred.GeoWithin v // TODO might want to parse this further now
        | "$geoIntersects" -> Pred.GeoIntersects v // TODO might want to parse this further now
        | _ -> failwith (sprintf "bad key in pred: %s" k)

    and parsePredList pairs =
        let (reg,other) = Array.partition (fun (k,_) -> k="$regex" || k="$options") pairs
        let a = Array.map (fun (ksub,vsub) -> parsePred ksub vsub) other
        let r = Array.tryFind (fun (k,_) -> k="$regex") reg
        let o = Array.tryFind (fun (k,_) -> k="$options") reg
        // TODO this might be a problem with getting the pairs out of order
        let p =
            match (r,o) with
            | Some (_,BString expr),None ->
                makeRegex expr "" |> Pred.REGEX |> Some
            | Some (_,BRegex (expr,options)),None ->
                makeRegex expr options |> Pred.REGEX |> Some
            | Some (_,BString expr),Some (_,BString options) ->
                makeRegex expr options |> Pred.REGEX |> Some
            | None,Some _ -> failwith "no options without regex"
            | None,None -> None
        match p with
        | Some p -> [| [| p |]; a |] |> Array.concat
        | None -> a

    and private parseCompare (k:string) v =
        if k.StartsWith("$") then failwith (sprintf "parseCompare with key: %s" k)
        match v with
        | BsonValue.BDocument pairs ->
            if bson.is_dbref pairs then
                Compare (k,[| Pred.EQ v |])
            else if Array.exists (fun (k:string,v) -> k.StartsWith("$")) pairs then
                let predList = pairs |> parsePredList
                Compare (k,predList)
            else
                Compare (k,[| Pred.EQ v |])
        | BsonValue.BRegex (expr,options) ->
            let r = makeRegex expr options
            Compare (k,[| Pred.REGEX r |])
        | _ -> 
            Compare (k,[| Pred.EQ v |])

    let parseQuery d = parseQueryDoc d |> QueryDoc

    let matchPredList preds v =
        let ndx = ref None
        let cbArrayPos name i =
            // TODO use name?
            match !ndx with
            | Some _ -> ()
            | None -> ndx := Some i

        let b = 
            let anyMisses = Array.exists (fun (p:Pred) -> matchPredicate p v cbArrayPos |> not) preds
            not anyMisses

        (b, !ndx)

    let matchQuery m d = 
        // TODO use of a callback and a ref cell to keep track of the
        // ndx of an array match feels like a hack
        let ndx = ref None
        let cbArrayPos name i =
            // TODO use name?
            match !ndx with
            | Some _ -> ndx := Some i // overwrite ()
            | None -> ndx := Some i

        let b = matchQueryDoc m d cbArrayPos
        (b, !ndx)

    let usesWhere m =
        match m with
        | QueryDoc items ->
            Array.exists (fun it ->
                match it with
                | Where _ -> true
                | _ -> false
            ) items

    let usesNear m =
        match m with
        | QueryDoc items ->
            Array.exists (fun it ->
                match it with
                | Compare (path,preds) ->
                    Array.exists (fun p ->
                        match p with
                        | Near _ -> true
                        | _ -> false
                    ) preds
                | _ -> false
            ) items

