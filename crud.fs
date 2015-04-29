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

module crud = 

    open System
    open System.IO

    type opIneq =
        | LT
        | GT
        | LTE
        | GTE

    type opL =
        | LT
        | LTE

    type opG =
        | GT
        | GTE

    let private validateKeys doc =
        let rec f doc depth =
            match doc with
            | BDocument pairs ->
                if depth>0 && bson.is_dbref pairs then
                    false
                else
                    Array.exists (fun (k:string,v) ->
                        if k.StartsWith("$") then
                            true
                        else if k.Contains(".") then
                            true
                        else
                            match v with
                            | BDocument _ -> f v (1+depth)
                            | BArray _ -> f v (1+depth)
                            | _ -> false
                        ) pairs
            | BArray items ->
                Array.exists (fun v ->
                    match v with
                    | BDocument _ -> f v (1+depth)
                    | BArray _ -> f v (1+depth)
                    | _ -> false
                    ) items
            | _ -> false

        match doc with
        | BDocument pairs ->
            match Array.tryFindIndex (fun (k,v) -> k="_id") pairs with
            | Some ndx ->
                match pairs.[ndx] |> snd with
                | BArray _ -> failwith "_id cannot be an array"
                | BUndefined -> failwith "_id cannot be a Undefined"
                | _ -> ()

                if ndx > 0 then
                    // when the _id is not the first thing in the document, we must
                    // move it to the front.  it is important that we do this by
                    // shifting everything else forward, not by swapping the _id
                    // with whatever was first.

                    // TODO mutable.  ugly.  don't modify the pairs array in place.
                    let before = if ndx>0 then Array.sub pairs 0 ndx else [| |]
                    let after = if ndx=Array.length pairs - 1 then [| |] else Array.sub pairs (ndx+1) (Array.length pairs - (ndx+1))
                    let first = Array.concat [ [| pairs.[ndx] |] ; before ; after ]
                    Array.Copy(first, 0, pairs, 0, pairs.Length)
            | None ->
                failwith "document has no _id"
        | _ -> 
            failwith "top-level must be a document"

        if f doc 0 then failwith (sprintf "can't have a key that starts with a dollar sign: %A" doc)
        let rec validateDepth doc depth =
            if depth > 100 then failwith "too much nesting"
            match doc with
            | BDocument pairs ->
                Array.iter (fun (k,v) -> validateDepth v (depth+1)) pairs
            | BArray items ->
                Array.iter (fun v -> validateDepth v (depth+1)) items
            | _ -> ()
        validateDepth doc 1
        bson.getValueForKey doc "_id"


    let private basicInsert w newDoc = 
        //printfn "basicInsert: %A" newDoc
        validateKeys newDoc |> ignore
        w.insert newDoc

    let private basicUpdate w newDoc =
        validateKeys newDoc |> ignore
        w.update newDoc

    let private basicDelete w newDoc =
        w.delete newDoc

    let insert dbName collName docs =
        // TODO and if autoIndexId was false?
        let docs = 
            Seq.map (fun doc ->
                match bson.tryGetValueForKey doc "_id" with
                | Some _ -> doc
                | None -> bson.setValueForKey doc "_id" (bson.newObjectID())
                ) docs
        let conn = kv.connect()
        try
            let w = conn.beginWrite dbName collName
            try
                let results = 
                    Seq.map (fun doc -> 
                        try 
                            basicInsert w doc
                            (doc, None)
                        with e -> (doc,Some (e.ToString()))
                    ) docs |> Seq.toArray
                w.commit()
                results
            with
            | _ ->
                w.rollback()
                reraise()
        finally
            conn.close()

    let private seqMatch m s =
        s 
        |> Seq.choose (fun st ->
                let (ok,ndx) = Matcher.matchQuery m st.doc
                if ok then Some {st with pos=ndx}
                else None
              )

    let private tryFitIndexToQuery ndx comps_eq comps_ineq textQuery =
        let (scalar_keys,weights) = kv.getNormalizedSpec ndx
        match (weights,textQuery) with
        | (None,Some _) -> 
            // if there is a textQuery but this is not a text index, give up now
            None
        | _ ->
            // TODO this code assumes that everything is either scalar or text, which
            // will be wrong when geo comes along.
            let num_scalar_keys = Array.length scalar_keys
            if num_scalar_keys=0 then
                match weights with
                | Some _ ->
                    // just a text index
                    match textQuery with
                    | None ->
                        // if there is no textQuery, give up
                        None
                    | Some tq ->
                        (ndx, plan.bounds.Text (Array.empty,tq)) |> Some
                | None ->
                    // er, why are we here?
                    failwith "index with no keys?"
            else
                // we have some scalar keys, and maybe a text index after it.
                // for every scalar key, find comparisons from the query.
                let matching_ineqs = 
                    Array.map (fun (k,_) -> 
                        match Map.tryFind k comps_ineq with
                        | Some a -> a
                        | None -> (None,None)
                    ) scalar_keys
                let matching_eqs = 
                    // TODO now we convert this back to where each element is
                    // either an array of one item or an empty array.  this is
                    // dorky.
                    Array.map (fun (k,_) -> 
                        match Map.tryFind k comps_eq with
                        | Some a -> [| a |]
                        | None -> Array.empty
                    ) scalar_keys
                let first_no_eqs = Array.tryFindIndex (fun acomps -> 0 = Array.length acomps) matching_eqs

                // chop matching_eqs down to the stuff that actually matched, with only one item each
                let matching_eqs = 
                    match first_no_eqs with
                    | Some n ->
                        let a = Array.sub matching_eqs 0 n
                        Array.map (fun acomps -> Array.get acomps 0) a
                    | None ->
                        Array.map (fun acomps -> Array.get acomps 0) matching_eqs

                match textQuery with
                | Some tq ->
                    match first_no_eqs with
                    | Some _ ->
                        // if there is a text index, we need an EQ for every scalar key.
                        // so this won't work.
                        None
                    | None ->
                        // we have an EQ for every key.  this index will work.
                        (ndx, plan.bounds.Text (matching_eqs, tq)) |> Some
                | None ->
                    // there is no text query.  note that this might still be a text index,
                    // but at this point we don't care.  we are considering whether we can
                    // use the scalar keys to the left of the text index.
                    match first_no_eqs with
                    | None -> 
                        if Array.length matching_eqs > 0 then
                            (ndx, plan.bounds.EQ matching_eqs) |> Some
                        else
                            // we can't use this index at all.
                            None
                    | Some num_eq ->
                        let ineq = matching_ineqs.[num_eq]
                        match ineq with
                        | (None,None) ->
                            if num_eq>0 then
                                (ndx, plan.bounds.EQ matching_eqs) |> Some
                            else
                                // we can't use this index at all.
                                None
                        | (Some min,None) ->
                            let (op,v) = min
                            let vals = Array.append matching_eqs [| v |]
                            match op with
                            | opG.GT ->  (ndx, plan.bounds.GT vals) |> Some
                            | opG.GTE -> (ndx, plan.bounds.GTE vals) |> Some
                        | (None,Some max) ->
                            let (op,v) = max
                            let vals = Array.append matching_eqs [| v |]
                            match op with
                            | opL.LT  -> (ndx, plan.bounds.LT vals) |> Some
                            | opL.LTE -> (ndx, plan.bounds.LTE vals) |> Some
                        | (Some min, Some max) ->
                            // this can probably only happen when the comps came
                            // from an elemMatch
                            let (gtop,vmin) = min
                            let (ltop,vmax) = max

                            let minvals = Array.append matching_eqs [| vmin |]
                            let maxvals = Array.append matching_eqs [| vmax |]
                            match (gtop,ltop) with
                            | opG.GT, opL.LT -> (ndx, plan.bounds.GT_LT (minvals,maxvals)) |> Some
                            | opG.GT, opL.LTE -> (ndx, plan.bounds.GT_LTE (minvals,maxvals)) |> Some
                            | opG.GTE, opL.LT -> (ndx, plan.bounds.GTE_LT (minvals,maxvals)) |> Some
                            | opG.GTE, opL.LTE -> (ndx, plan.bounds.GTE_LTE (minvals,maxvals)) |> Some

    let private findIndexForMinMax indexes a =
        //printfn "indexes: %A" indexes
        //printfn "keys: %A" a
        Array.tryFind (fun ndx ->
            let (normspec,weights) = kv.getNormalizedSpec ndx
            let keys = Array.map (fun (k,v) -> k) normspec
            keys = a
        ) indexes

    let private findTextQuery m =
        let a =
            match m with
            | QueryDoc a ->
                // TODO only in the top level of the query?
                // TODO dive into AND?
                // TODO dive into OR?  the docs say this is allowed under certain conditions
                Array.choose (fun it ->
                    match it with
                    | QueryItem.Text s -> Some s
                    | _ -> None
                ) a
        if Array.length a = 0 then None
        else if Array.length a > 1 then failwith "only one $text in a query"
        else a.[0] |> Some

    let private findComparesEQ m =
        let rec find m =
            match m with
            | QueryDoc a ->
                Array.collect (fun it ->
                    match it with
                    | Compare (k, a) -> 
                        Array.choose (fun p ->
                            match p with
                            | Pred.EQ v -> Some (k,v)
                            | _ -> None
                        ) a
                    | AND docs ->
                        Array.collect (fun d -> find d) docs
                    | _ -> Array.empty
                ) a

        let comps = find m
        let mc = 
            Array.fold (fun cur (k,v) ->
                match Map.tryFind k cur with
                | Some a ->
                    let a = v :: a
                    Map.add k a cur
                | None ->
                    Map.add k [v] cur
            ) Map.empty comps
        // query for x=3 && x=4 is legit in mongo.
        // it can match a doc where x is an array that contains both 3 and 4
        // {x:[1,2,3,4,5]}
        // in terms of choosing an index to use, we can pick either one.
        // the index will give us, for example, "all documents where x is 3",
        // which will include the one above, and the matcher will then also
        // make sure that the 4 is there as well.
        let mc =
            Map.fold (fun mc k a ->
                match a with
                | [] -> failwith "should never happen"
                | x :: xs ->
                    if List.isEmpty xs then
                        Map.add k x mc
                    else
                        let distinct = a |> Set.ofList |> Set.toArray
                        if Array.length distinct > 1 then
                            //failwith "conflicting $eq"
                            Map.add k x mc
                        else
                            Map.add k x mc
            ) Map.empty mc
        //printfn "map: %A" mc
        mc

    let private findComparesIneq m =
        let rec find m =
            match m with
            | QueryDoc a ->
                Array.collect (fun it ->
                    match it with
                    | Compare (k, a) -> 
                        Array.choose (fun p ->
                            match p with
                            | Pred.LT v -> Some (k,opIneq.LT,v)
                            | Pred.GT v -> Some (k,opIneq.GT,v)
                            | Pred.LTE v -> Some (k,opIneq.LTE,v)
                            | Pred.GTE v -> Some (k,opIneq.GTE,v)
                            | _ -> None
                        ) a
                    | AND docs ->
                        Array.collect (fun d -> find d) docs
                    | _ -> Array.empty
                ) a

        let comps = find m
        let mc = 
            Array.fold (fun cur (k,op,v) ->
                match Map.tryFind k cur with
                | Some a ->
                    let a = (op,v) :: a
                    Map.add k a cur
                | None ->
                    Map.add k [op,v] cur
            ) Map.empty comps
        let mc =
            let gtSort (op1,v1) (op2,v2) =
                let c = Matcher.cmp v1 v2
                if c<0 then c
                else if c>0 then c
                else 
                    match (op1,op2) with
                    | opG.GT,opG.GT -> 0
                    | opG.GTE,opG.GTE -> 0
                    | opG.GT,opG.GTE -> -1
                    | opG.GTE,opG.GT -> 1

            let ltSort (op1,v1) (op2,v2) =
                let c = Matcher.cmp v1 v2
                if c<0 then c
                else if c>0 then c
                else 
                    match (op1,op2) with
                    | opL.LT,opL.LT -> 0
                    | opL.LTE,opL.LTE -> 0
                    | opL.LT,opL.LTE -> -1
                    | opL.LTE,opL.LT -> 1

            let gtFix op =
                match op with
                | opIneq.GT -> opG.GT
                | opIneq.GTE -> opG.GTE
                | _ -> failwith "never"

            let ltFix op =
                match op with
                | opIneq.LT -> opL.LT
                | opIneq.LTE -> opL.LTE
                | _ -> failwith "never"

            Map.fold (fun mc k a ->
                let gt = List.filter (fun (op,v) -> op=opIneq.GT || op=opIneq.GTE) a
                let gt = List.map (fun (op,v) -> (gtFix op,v)) gt
                let gt = List.sortWith gtSort gt |> List.rev
                let gt = if List.isEmpty gt then None else gt |> List.head |> Some

                let lt = List.filter (fun (op,v) -> op=opIneq.LT || op=opIneq.LTE) a
                let lt = List.map (fun (op,v) -> (ltFix op,v)) lt
                let lt = List.sortWith ltSort lt
                let lt = if List.isEmpty lt then None else lt |> List.head |> Some

#if not // mongo actually WANTS to allow this.  test find8.js
                match (gt,lt) with
                | (Some (gtop,gtv), Some (ltop,ltv)) ->
                    let c = Matcher.cmp gtv ltv
                    if c>0 then failwith "cannot be >x and <y when x>y"
                    else if c<0 then ()
                    else if gtop=opG.GT && ltop=opL.LT then failwith "cannot be > and < the same value"
                    else ()
                | _ ->
                    ()
#endif

#if not // TODO dive into elemMatch
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
                Map.add k (gt,lt) mc
#else
                let comp = 
                    match gt with
                    | Some _ -> (gt,None)
                    | None -> (None,lt)
                Map.add k comp mc
#endif
            ) Map.empty mc
        //printfn "map: %A" mc
        mc

    // TODO so the following function is very non-idiomatic from a functional programming
    // perspective.  yucky.
    let parseTextQuery s =
        let is_delim c =
            match c with
            | ' ' -> true
            | ',' -> true
            | ';' -> true
            | '.' -> true
            | _ -> false
        let i = ref 0
        let len = String.length s
        let skip_delim() =
            while !i<len && is_delim s.[!i] do
                i := !i + 1
        let a = ResizeArray<_>()
        let get_token() =
            //printfn "get_token: %s" (s.Substring(!i))
            skip_delim()
            //printfn "after skip_delim: %s" (s.Substring(!i))
            if !i>=len then false
            else
                let neg =
                    if '-'=s.[!i] then
                        i := !i + 1
                        true
                    else
                        false

                // TODO do we allow space between the - and the word or phrase?

                if !i>=len then failwith "negate of nothing"


                if '"'=s.[!i] then
                    let tokStart = !i + 1
                    //printfn "in phrase"
                    i := !i + 1
                    while !i<len && s.[!i]<>'"' do
                        i := !i + 1
                    //printfn "after look for other quote: %s" (s.Substring(!i))
                    let tokLen = 
                        if !i<len then !i-tokStart
                        else failwith "unmatched phrase quote"
                    //printfn "phrase tokLen: %d" tokLen
                    i := !i + 1
                    // TODO need to get the individual words out of the phrase here?
                    // TODO what if the phrase is an empty string?  error?
                    if tokLen>0 then
                        let term = plan.Phrase(neg, s.Substring(tokStart,tokLen))
                        a.Add(term)
                        true
                    else
                        false // TODO isn't this always an error?
                else
                    let tokStart = !i
                    while !i<len && not (is_delim s.[!i]) do
                        i := !i + 1
                    let tokLen = !i - tokStart
                    if tokLen>0 then
                        let term = plan.Word(neg, s.Substring(tokStart,tokLen))
                        a.Add(term)
                        true
                    else
                        false // TODO isn't this always an error?
        while get_token() do
            ()
        let terms = a.ToArray()
        terms |> Set.ofArray |> Set.toArray

    let private findFitIndexes indexes m =
        let textQuery = 
            match findTextQuery m with
            | Some s -> s |> parseTextQuery |> Some
            | None -> None
        let comps_eq = findComparesEQ m
        let comps_ineq = findComparesIneq m
        let fits = Array.choose (fun ndx -> tryFitIndexToQuery ndx comps_eq comps_ineq textQuery) indexes
        (fits,textQuery)

    let private chooseFromPossibles possibles =
        if Array.isEmpty possibles then 
            None
        else
            // prefer the _id index if we can use it
            match Array.tryFind (fun (ndx,fit) -> ndx.ndx="_id_") possibles with
            | Some r -> r |> plan.q.Plan |> Some
            | None ->
                // TODO otherwise prefer any unique index
                // TODO otherwise prefer any EQ index
                // TODO or any index which has both min_max bounds
                // otherwise any index at all.  just take the first one.
                possibles.[0] |> plan.q.Plan |> Some

    let private chooseIndex indexes m hint =
        let (fits,textQuery) = findFitIndexes indexes m

        match textQuery with
        | Some _ ->
            // TODO if there is a $text query, disallow hint
            match fits with
            | [|   |]  -> failwith "$text without index"
            | [| r |] -> plan.q.Plan r |> Some
            | _ -> failwith "should not happen"
        | None ->
            match hint with
            | Some ndxHint ->
                match Array.tryFind (fun (ndx,fit) -> ndx.spec=ndxHint.spec) fits with
                | Some r -> r |> plan.q.Plan |> Some
                | None -> chooseFromPossibles fits
            | None -> chooseFromPossibles fits

    let private getOneMatch w m =
        let indexes = w.getIndexes()
        let plan = chooseIndex indexes m None
        let {docs=s;funk=funk} = w.getSelect plan
        try
            let a = s |> seqMatch m |> Seq.truncate 1 |> Seq.toList
            let d = 
                if List.isEmpty a then None
                else List.head a |> Some
            d
        finally
            funk()

    let private sortFunc ord f =
        match ord with
        | BDocument keys ->
            let rec mycmp cur ta tb =
                let (k,dir) = keys.[cur]
                let dir1 = match dir with
                           | BInt32 a -> a
                           | BInt64 a -> int32 a
                           | BDouble a -> int32 a
                           | BDocument [| ("$meta",BString "textScore") |] -> 1 // TODO fake textScore
                           | _ -> failwith (sprintf "invalid sort: %A" dir)
                if dir1=0 then failwith "sort dir cannot be 0"
                let dir = if dir1 < 0 then -1 else 1
                let a = f ta
                let b = f tb
                // note that, apparently, mongo always treats undefined as null for sorting purposes
                let va = bson.findPath a k |> bson.replaceUndefined
                let vb = bson.findPath b k |> bson.replaceUndefined
                let c = Matcher.cmpdir va vb dir
                if c<>0 then
                    c
                else
                    if cur+1 < keys.Length then
                        mycmp (cur+1) ta tb
                    else
                        0
            mycmp 0
        | BInt32 dir -> failwith "TODO" // TODO this will end up being allowed for orderby
        | _ -> failwith "orderby needs a document or an int"

    let private sortDocumentsBy docs ord f =
        let a2 = Array.copy docs
        let fsort = sortFunc ord f
        Array.sortInPlaceWith fsort a2
        a2

    let private tryFindIndexByNameOrSpec dbName collName indexes desc =
        let a = 
            match desc with
            | BString name -> Array.filter (fun info -> info.db=dbName && info.coll=collName && info.ndx=name) indexes
            | BDocument _ -> Array.filter (fun info -> info.db=dbName && info.coll=collName && info.spec=desc) indexes
            | _ -> failwith "must be name or index doc"
        if Array.isEmpty a then None
        else if Array.length a > 1 then failwith "should never happen"
        else a.[0] |> Some

    let deleteIndexes db coll index =
        let conn = kv.connect()
        try
            // TODO it would be nice to have a tx around this
            let indexes = conn.listIndexes() |> Array.filter (fun info -> info.db=db && info.coll=coll)
            let count_before = Array.length indexes
            let indexes = 
                match index with
                | BString "*" ->
                    Array.filter (fun info -> info.ndx<>"_id_") indexes    
                | _ ->
                    // TODO we're supposed to disallow delete of _id_, right?
                    match tryFindIndexByNameOrSpec db coll indexes index with
                    | Some info -> [| info |]
                    | None -> Array.empty
            //printfn "deleting: %A" indexes
            let count_deleted = 
                Array.sumBy (fun info ->
                    let deleted = conn.dropIndex info.db info.coll info.ndx
                    if deleted then 1 else 0
                ) indexes
            (count_before,count_deleted)
        finally
            conn.close()

    let createIndexes dbName collName indexes =
        let a = 
            Array.map (fun d -> 
                let ndxKey = bson.getValueForKey d "key"
                let ndxName = bson.getValueForKey d "name" |> bson.getString
                let options = BDocument Array.empty
                let options = 
                    match bson.tryGetValueForKey d "unique" with
                    | Some v -> 
                        match v with
                        | BBoolean b ->
                            let f ov = Some v
                            bson.changeValueForPath options "unique" f
                        | _ -> failwith "illegal value for unique"
                    | None -> options
                let options = 
                    // TODO note that if a key appears in weights but not
                    // in the key itself, it is indexed anyway
                    match bson.tryGetValueForKey d "weights" with
                    | Some v -> 
                        match v with
                        | BDocument _ ->
                            let f ov = Some v
                            bson.changeValueForPath options "weights" f
                        | _ -> failwith "illegal value for weights"
                    | None -> options
                // TODO what other options might exist here?
                {
                    db=dbName
                    coll=collName
                    ndx=ndxName
                    spec=ndxKey
                    options=options
                }
                ) indexes
        let conn = kv.connect()
        try
            conn.createIndexes a
        finally
            conn.close()

    let createCollection dbName collName options =
        let conn = kv.connect()
        try
            conn.createCollection dbName collName options
        finally
            conn.close()

    let listCollections (ofDb:string option) =
        let a = 
            let conn = kv.connect()
            try
                conn.listCollections()
            finally
                conn.close()

        match ofDb with
        | Some s -> Array.filter (fun (db,_,_) -> db=s) a
        | None -> a

    let private listAllIndexes() =
        let conn = kv.connect()
        try
            conn.listIndexes()
        finally
            conn.close()

    let private listIndexesForCollection db coll =
        listAllIndexes() |> Array.filter (fun info -> info.db=db && info.coll=coll)

    let private listIndexesForDatabase db =
        listAllIndexes() |> Array.filter (fun info -> info.db=db)

    let listIndexes (dbName:string option) (collName:string option) =
        match dbName,collName with
        | Some nsDb,Some nsColl ->
            let result = listIndexesForCollection nsDb nsColl
            if Array.isEmpty result then
                if listCollections None |> Array.filter (fun (db,coll,_) -> db=nsDb && coll=nsColl) |> Array.isEmpty then
                    failwith "collection does not exist"
                else
                    result
            else
                result
        | Some nsDb,None ->
            listIndexesForDatabase nsDb
            // TODO gripe if db does not exist?
        | None, Some _ ->
            failwith "should not happen"
        | None,None ->
            listAllIndexes()

    let clearCollection dbName collName =
        let conn = kv.connect()
        try
            conn.clearCollection dbName collName
        finally
            conn.close()

    let dropCollection dbName collName =
        let conn = kv.connect()
        try
            conn.dropCollection dbName collName
        finally
            conn.close()

    let dropDatabase (dbName:string) =
        let conn = kv.connect()
        try
            conn.dropDatabase dbName
        finally
            conn.close()

    let private myMin va vb =
        let c = Matcher.cmp va vb
        if c<0 then va else vb

    let private myMax va vb =
        let c = Matcher.cmp va vb
        if c>0 then va else vb

    let private add va vb =
        match va with
        | BInt32 a -> BInt32 (a + bson.getAsInt32 vb) // TODO int64 and what else?
        | BDouble a -> BDouble (a + bson.getAsDouble vb)
        | _ -> failwith "can't add"

    let private mul va vb =
        match va with
        | BInt32 a -> BInt32 (a * bson.getAsInt32 vb) // TODO int64 and what else?
        | BDouble a -> BDouble (a * bson.getAsDouble vb)
        | _ -> failwith "can't add"
        
    let private getDate() =
        let epoch = DateTime(1970,1,1)
        let since = DateTime.Now - epoch
        let ms = since.TotalMilliseconds
        let i = int64 ms
        BDateTime i

    let tscount = ref 0 // TODO eek a global!
    let private getTimeStamp() =
        let epoch = DateTime(1970,1,1)
        let since = DateTime.Now - epoch
        let s = since.TotalSeconds
        let c = !tscount
        tscount := c + 1
        let i = ((int64 s) <<< 32) ||| (int64 c)
        BTimeStamp i

    type private UpdateOp =
        | UpdateMin of string*BsonValue
        | UpdateMax of string*BsonValue
        | UpdateInc of string*BsonValue
        | UpdateMul of string*BsonValue
        | UpdateBitAnd of string*int64
        | UpdateBitOr of string*int64
        | UpdateBitXor of string*int64
        | UpdateSet of string*BsonValue
        | UpdateUnset of string
        | UpdateDate of string
        | UpdateRename of string*string
        | UpdateTimeStamp of string
        | UpdateSetOnInsert of string*BsonValue
        | UpdateAddToSet of string*BsonValue[]
        | UpdatePush of path:string*each:BsonValue[]*slice:int option*sort:BsonValue option*position:int option
        | UpdatePullValue of string*BsonValue
        | UpdatePullQuery of string*QueryDoc
        | UpdatePullPredicates of string*Pred[]
        | UpdatePullAll of string*BsonValue[]
        | UpdatePop of string*int

    // this function is used to check two paths to see if one of them
    // is a prefix of the other, which, for example, in the case of two
    // update operators, is a conflict.
    //
    // the check cannot be done correctly with simple string.StartsWith()
    // calls, because x.fu is not actually a prefix of x.fubar, since x
    // can happily have both fu and fubar as a key.
    let private checkPrefix (a:string) (b:string) =
        let aparts = a.Split('.')
        let bparts = b.Split('.')
        let alen = Array.length aparts
        let blen = Array.length bparts
        let len = min alen blen
        // TODO actually constructing the two subarrays here is not the
        // most efficient way to do this.
        let asub = Array.sub aparts 0 len
        let bsub = Array.sub bparts 0 len
        asub = bsub

    let private anyPrefix (a:ResizeArray<string>) (s:string) =
        Seq.exists (fun q -> checkPrefix q s) a

    let private checkUpdateDocForConflicts ops =
        let a = ResizeArray<_>()

        let add p =
            if anyPrefix a p then failwith "conflict"
            a.Add(p)

        Array.iter (fun op ->
            match op with
            | UpdateMin (path,_) -> add path
            | UpdateMax (path,_) -> add path
            | UpdateInc (path,_) -> add path
            | UpdateMul (path,_) -> add path
            | UpdateSet (path,_) -> add path
            | UpdateUnset (path) -> add path
            | UpdateBitAnd (path,_) -> add path
            | UpdateBitOr (path,_) -> add path
            | UpdateBitXor (path,_) -> add path
            | UpdateDate (path) -> add path
            | UpdateTimeStamp (path) -> add path
            | UpdatePush (path,_,_,_,_) -> add path
            | UpdatePullValue (path,_) -> add path
            | UpdatePullQuery (path,_) -> add path
            | UpdatePullPredicates (path,_) -> add path
            | UpdatePullAll (path,_) -> add path
            | UpdatePop (path,_) -> add path
            | UpdateSetOnInsert (path,_) -> add path
            | UpdateAddToSet (path,_) -> add path
            | UpdateRename (path1,path2) -> 
                add path1
                add path2
            ) ops

    let rec private anyPartStartsWithDollarSign (s:string) =
        let dot = s.IndexOf('.')
        let name = if dot<0 then s else s.Substring(0, dot)
        if name.StartsWith("$") then true
        else if dot>0 then
            let subPath = s.Substring(dot+1)
            anyPartStartsWithDollarSign subPath
        else false

    let private parseUpdateDoc d =
        let pairs = bson.getDocument d
        let result = ResizeArray<_>()
        Array.iter (fun (k,v) ->
            match k with
            | "$min" -> bson.getDocument v |> Array.iter (fun (path,v) -> result.Add(UpdateMin(path,v)))
            | "$max" -> bson.getDocument v |> Array.iter (fun (path,v) -> result.Add(UpdateMax(path,v)))
            | "$inc" -> bson.getDocument v |> Array.iter (fun (path,v) -> result.Add(UpdateInc(path,v)))
            | "$mul" -> bson.getDocument v |> Array.iter (fun (path,v) -> result.Add(UpdateMul(path,v)))
            | "$set" -> bson.getDocument v |> Array.iter (fun (path,v) -> result.Add(UpdateSet(path,v)))
            | "$unset" -> bson.getDocument v |> Array.iter (fun (path,_) -> result.Add(UpdateUnset(path)))
            | "$setOnInsert" -> bson.getDocument v |> Array.iter (fun (path,v) -> result.Add(UpdateSetOnInsert(path,v)))
            | "$pop" -> bson.getDocument v |> Array.iter (fun (path,v) -> result.Add(UpdatePop(path,(v|>bson.getAsInt32))))
            | "$pushAll" -> 
                bson.getDocument v 
                |> Array.iter (fun (path,vsub) -> 
                    let items = 
                                match vsub with
                                | BArray a -> a
                                | _ -> failwith "$pushAll needs an array"
                    result.Add(UpdatePush(path,items,None,None,None))
                    )
            | "$push" -> 
                bson.getDocument v 
                |> Array.iter (fun (path,vsub) -> 
                    let (each,eachItems) =
                        match vsub with
                        | BDocument pairs ->
                            match Array.tryFind (fun (k,_) -> k="$each") pairs with
                            | Some (_,BArray h) -> (true,h)
                            | Some (_,_) -> failwith "$each needs an array"
                            | None -> (false,[| vsub |])
                        | _ -> (false,[| vsub |])
                    let slice =
                        if not each then None else
                            match vsub with
                            | BDocument pairs ->
                                match Array.tryFind (fun (k,_) -> k="$slice") pairs with
                                | Some (_,BInt32 n) -> n |> Some
                                | Some (_,BInt64 n) -> n |> int32 |> Some
                                | Some (_,BDouble n) -> n |> int32 |> Some
                                | Some (_,_) -> failwith "$slice needs a number"
                                | None -> None
                            | _ -> None
                    let sort =
                        if not each then None else
                            match vsub with
                            | BDocument pairs ->
                                match Array.tryFind (fun (k,_) -> k="$sort") pairs with
                                | Some (_,BInt32 n) -> n |> BInt32 |> Some
                                | Some (_,BInt64 n) -> n |> int32 |> BInt32 |> Some
                                | Some (_,BDouble n) -> n |> int32 |> BInt32 |> Some
                                | Some (_,BDocument d) -> d |> BDocument |> Some
                                | Some (_,_) -> failwith "$sort needs a number or a document"
                                | None -> None
                            | _ -> None
                    let position =
                        if not each then None else
                            match vsub with
                            | BDocument pairs ->
                                match Array.tryFind (fun (k,_) -> k="$position") pairs with
                                | Some (_,BInt32 n) -> n |> Some
                                | Some (_,BInt64 n) -> n |> int32 |> Some
                                | Some (_,BDouble n) -> n |> int32 |> Some
                                | Some (_,_) -> failwith "$position needs a number"
                                | None -> None
                            | _ -> None
                    result.Add(UpdatePush(path,eachItems,slice,sort,position))
                    )
            | "$pull" ->
                bson.getDocument v
                |> Array.iter (fun (path,v) ->
                    match v with
                    | BDocument pairs -> 
                        if Matcher.isQueryDoc v then
                            let qd = Matcher.parseQuery v
                            result.Add(UpdatePullQuery(path, qd))
                        else
                            let q= Matcher.parsePredList pairs
                            result.Add(UpdatePullPredicates(path,q))
                    | _ -> result.Add(UpdatePullValue(path,v))
                    )
            | "$pullAll" ->
                //printfn "pullAll: %A" v
                bson.getDocument v
                |> Array.iter (fun (path,v) ->
                    match v with
                    | BArray a -> result.Add(UpdatePullAll(path,a))
                    | _ -> failwith "$pullAll needs an array"
                    )
            | "$rename" ->
                bson.getDocument v
                |> Array.iter (fun (path,v) ->
                    match v with
                    | BString newPath ->
                        // TODO even mongo has problems in this area.  it seems to have
                        // different rules for key/path names in its rename code than in
                        // other places.
                        if path="" then failwith "empty key cannot be renamed" // TODO why not?
                        if newPath="" then failwith "cannot rename to empty key" // TODO why not?
                        if path="_id" then failwith "_id cannot be renamed"
                        // TODO what about rename something to _id ?
                        if path.StartsWith(".") then failwith "bad path"
                        if newPath.StartsWith(".") then failwith "bad path"
                        if path.EndsWith(".") then failwith "bad path"
                        if newPath.EndsWith(".") then failwith "bad path"
                        if path=newPath then failwith "cannot rename to same path"
                        if path.StartsWith(newPath) then failwith "overlap rename path" // TODO use correct prefix func
                        if newPath.StartsWith(path) then failwith "overlap rename path" // TODO use correct prefix func
                        if anyPartStartsWithDollarSign path then failwith "key starts with dollar sign"
                        if anyPartStartsWithDollarSign newPath then failwith "key starts with dollar sign"
                        result.Add(UpdateRename(path,newPath))
                    | _ -> failwith "rename needs a path"
                    )
            | "$bit" -> 
                bson.getDocument v
                |> Array.iter (fun (path,v) ->
                    match v with
                    | BDocument pairs ->
                        if pairs.Length <> 1 then failwith "$bit invalid"
                        let (kb,vb) = pairs.[0]
                        let num =
                            match vb with
                            | BInt32 n -> int64 n
                            | BInt64 n -> n
                            | _ -> failwith "$bit invalid"
                        match kb with
                        | "and" -> result.Add(UpdateBitAnd(path,num))
                        | "or" -> result.Add(UpdateBitOr(path,num))
                        | "xor" -> result.Add(UpdateBitXor(path,num))
                        | _ -> failwith "$bit invalid"
                    | _ -> failwith "$bit invalid"
                    )
            | "$currentDate" -> 
                bson.getDocument v
                |> Array.iter (fun (path,v) ->
                    match v with
                    | BBoolean b ->
                        if b then result.Add(UpdateDate(path))
                        else failwith "currentDate:false is invalid"
                    | BDocument pairs ->
                        if pairs.Length <> 1 then failwith "currentDate invalid"
                        let (kt,vt) = pairs.[0]
                        if kt <> "$type" then failwith "currentDate invalid"
                        match vt with
                        | BString s ->
                            match s with
                            | "date" -> result.Add(UpdateDate(path))
                            | "timestamp" -> result.Add(UpdateTimeStamp(path))
                            | _ -> failwith "currentDate invalid"
                        | _ -> failwith "currentDate invalid"
                    | _ -> failwith "currentDate invalid"
                    )
            | "$addToSet" ->
                bson.getDocument v
                |> Array.iter (fun (path,vsub) ->
                    let eachItems =
                        match vsub with
                        | BDocument pairs ->
                            if pairs.Length=1 then
                                let (k3,v3) = pairs.[0]
                                if k3="$each" then
                                    match v3 with
                                    | BArray h -> h
                                    | _ -> failwith "$each needs an array"
                                else [| vsub |]
                            else [| vsub |]
                        | _ -> [| vsub |]
                    result.Add(UpdateAddToSet(path,eachItems))
                    )
            | _ -> failwith (sprintf "unknown update operator: %s" k)
            ) pairs
        let ops = result.ToArray()
        checkUpdateDocForConflicts ops
        ops

    let private arrayInsert a b pos =
        if pos<0 then failwith "position negative"
        if pos=0 then Array.concat [b;a]
        else if pos >= Array.length a then Array.concat [a;b]
        else
            let before = Array.sub a 0 pos
            let after = Array.sub a pos (Array.length a - pos)
            Array.concat [before;b;after]
            
    let private fixPositional (s:string) ndx =
        // must match the dot before because $ is legal in the middle of a key.
        // matching 2 doesn't work because the $ can be at the end of the path.
        // TODO maybe split the string, match the parts whole, and re-join
        match ndx with
        | Some i -> s.Replace(".$", (sprintf ".%d" i))
        | None -> s

    let private applyUpdateOps doc ops isUpsert ndx =
        Array.fold (fun cur2 op ->
            match op with
            | UpdateMin (ksub,vsub) ->
                let f ov =
                    match ov with
                    | Some v -> myMin v vsub |> Some
                    | None -> vsub |> Some // when the key isn't found, $min works like set
                let ksub = fixPositional ksub ndx
                bson.changeValueForPath cur2 ksub f
            | UpdateMax (ksub,vsub) ->
                let f ov =
                    match ov with
                    | Some v -> myMax v vsub |> Some
                    | None -> vsub |> Some // when the key isn't found, $max works like set
                let ksub = fixPositional ksub ndx
                bson.changeValueForPath cur2 ksub f
            | UpdateInc (ksub,vsub) ->
                let f ov =
                    match ov with
                    | Some v -> add v vsub |> Some
                    | None -> vsub |> Some // when the key isn't found, $inc works like set
                let ksub = fixPositional ksub ndx
                bson.changeValueForPath cur2 ksub f
            | UpdateMul (ksub,vsub) ->
                let f ov =
                    match ov with
                    | Some v -> mul v vsub |> Some
                    | None -> vsub |> Some // when the key isn't found, $mul works like set ?  TODO right?
                let ksub = fixPositional ksub ndx
                bson.changeValueForPath cur2 ksub f
            | UpdateRename (path1,path2) ->
                if bson.divesIntoAnyArray cur2 path1 then failwith "path1 can't be an array element"
                if bson.divesIntoAnyArray cur2 path2 then failwith "path2 can't be an array element"
                let oldValue = ref None
                let f1 ov1 = 
                    match ov1 with
                    | Some _ -> oldValue := ov1
                    | None -> ()
                    None
                let path1 = fixPositional path1 ndx
                let unset = bson.changeValueForPath cur2 path1 f1
                match !oldValue with
                | Some d ->
                    let f2 ov2 = Some d // TODO check ov2 here for overwrite?
                    let path2 = fixPositional path2 ndx
                    bson.changeValueForPath unset path2 f2
                | None -> cur2
            | UpdateSet (ksub,vsub) ->
                let f ov = Some vsub
                let ksub = fixPositional ksub ndx
                bson.changeValueForPath cur2 ksub f
            | UpdateUnset ksub ->
                let f ov = None
                let ksub = fixPositional ksub ndx
                bson.changeValueForPath cur2 ksub f
            | UpdateBitAnd (ksub,num) ->
                let f ov =
                    match ov with
                    | Some v -> 
                        match v with
                        | BInt32 vn -> (int64 vn) &&& num |> BInt64 |> Some
                        | BInt64 vn -> (int64 vn) &&& num |> BInt64 |> Some
                        | _ -> failwith "$bit invalid"
                    | None -> failwith "$bit invalid" // when the key isn't found, TODO
                let ksub = fixPositional ksub ndx
                bson.changeValueForPath cur2 ksub f
            | UpdateBitOr (ksub,num) ->
                let f ov =
                    match ov with
                    | Some v -> 
                        match v with
                        | BInt32 vn -> (int64 vn) ||| num |> BInt64 |> Some
                        | BInt64 vn -> (int64 vn) ||| num |> BInt64 |> Some
                        | _ -> failwith "$bit invalid"
                    | None -> failwith "$bit invalid" // when the key isn't found, TODO
                let ksub = fixPositional ksub ndx
                bson.changeValueForPath cur2 ksub f
            | UpdateBitXor (ksub,num) ->
                let f ov =
                    match ov with
                    | Some v -> 
                        match v with
                        | BInt32 vn -> (int64 vn) ^^^ num |> BInt64 |> Some
                        | BInt64 vn -> (int64 vn) ^^^ num |> BInt64 |> Some
                        | _ -> failwith "$bit invalid"
                    | None -> failwith "$bit invalid" // when the key isn't found, TODO
                let ksub = fixPositional ksub ndx
                bson.changeValueForPath cur2 ksub f
            | UpdateDate ksub ->
                let dval = getDate()
                let f ov = Some dval
                let ksub = fixPositional ksub ndx
                bson.changeValueForPath cur2 ksub f
            | UpdateTimeStamp ksub ->
                let dval = getTimeStamp()
                let f ov = Some dval
                let ksub = fixPositional ksub ndx
                bson.changeValueForPath cur2 ksub f
            | UpdateSetOnInsert (ksub,vsub) ->
                if isUpsert then
                    let f ov = Some vsub
                    let ksub = fixPositional ksub ndx
                    bson.changeValueForPath cur2 ksub f
                else
                    cur2
            | UpdatePullValue (ksub,v) ->
                //printfn "pullValue: cur2 = %A" cur2
                //printfn "pullValue: ksub = %A" ksub
                //printfn "pullValue:  val = %A" v
                let f ov =
                    match ov with
                    | Some (BArray a) ->
                        let a2 = Array.filter (fun v2 -> v <> v2) a
                        BArray a2 |> Some
                    | _ -> 
                        failwith (sprintf "$pull not array: %A" ov)
                let ksub = fixPositional ksub ndx
                let r = bson.changeValueForPath cur2 ksub f
                //printfn "pullValue: result = %A" r
                r
            | UpdatePullQuery (ksub,q) ->
                let f ov =
                    match ov with
                    | Some (BArray a) ->
                        let a2 = Array.filter (fun v2 -> Matcher.matchQuery q v2 |> fst |> not) a
                        BArray a2 |> Some
                    | _ -> 
                        failwith (sprintf "$pull not array: %A" ov)
                let ksub = fixPositional ksub ndx
                bson.changeValueForPath cur2 ksub f
            | UpdatePullPredicates (ksub,pa) ->
                let f ov =
                    match ov with
                    | Some (BArray a) ->
                        let a2 = Array.filter (fun v2 -> Matcher.matchPredList pa v2 |> fst |> not) a
                        BArray a2 |> Some
                    | _ -> 
                        failwith (sprintf "$pull not array: %A" ov)
                let ksub = fixPositional ksub ndx
                bson.changeValueForPath cur2 ksub f
            | UpdatePop (ksub,which) ->
                let f ov =
                    match ov with
                    | Some (BArray a) ->
                        if a.Length=1 then
                            BArray [| |] |> Some
                        else if a.Length = 0 then
                            ov // failwith "pop empty array"
                        else
                            let a2:BsonValue[] = Array.zeroCreate (a.Length-1)
                            if which > 0 then
                                Array.Copy(a, 0, a2, 0, a.Length-1)
                            else
                                Array.Copy(a, 1, a2, 0, a.Length-1)
                            BArray a2 |> Some
                    | None -> ov
                    | _ -> 
                        failwith (sprintf "pop not array: %A" ov)
                let ksub = fixPositional ksub ndx
                bson.changeValueForPath cur2 ksub f
            | UpdatePush (ksub,each,slice,sort,position) ->
                let f ov =
                    match ov with
                    | Some (BArray a) -> 
                        let pos =
                            match position with
                            | Some n -> n
                            | None -> Array.length a
                        let step1 = arrayInsert a each pos
                        let step2 =
                            match sort with
                            | Some v -> sortDocumentsBy step1 v (fun x -> x)
                            | None -> step1
                        let step3 =
                            match slice with
                            | Some n ->
                                let len = Array.length step2
                                if n=0 then [| |]
                                else if n > 0 then
                                    let n = min n len
                                    Array.sub step2 0 n
                                else
                                    let n = -n
                                    let n = min n len
                                    Array.sub step2 (len-n) n
                            | None -> step2
                        step3 |> BArray |> Some
                    | Some (_) -> ov // TODO shouldn't this fail?
                    | None -> BArray each |> Some
                let ksub = fixPositional ksub ndx
                bson.changeValueForPath cur2 ksub f
            | UpdatePullAll (ksub,va) ->
                Array.fold (fun cur3 vsub ->
                    let f ov =
                        match ov with
                        | Some (BArray a) ->
                            let a2 = Array.filter (fun v2 -> vsub <> v2) a
                            BArray a2 |> Some
                        | _ -> failwith (sprintf "$pull not array: %A" ov)
                    // TODO shouldn't fixPositional be done outside this fold?
                    let ksub = fixPositional ksub ndx
                    let r = bson.changeValueForPath cur3 ksub f
                    r
                    ) cur2 va
            | UpdateAddToSet (ksub,va) ->
                Array.fold (fun cur3 vsub ->
                    let f ov =
                        match ov with
                        | Some v ->
                            match v with
                            | BArray items ->
                                if not (Array.exists (fun x -> x=vsub) items) then
                                    Array.append items [| vsub |] |> BArray |> Some
                                else
                                    ov
                            | _ ->
                                failwith "must be an array"
                        | None ->
                            BArray [| vsub |] |> Some
                    // TODO shouldn't fixPositional be done outside this fold?
                    let ksub = fixPositional ksub ndx
                    bson.changeValueForPath cur3 ksub f
                    ) cur2 va
            ) doc ops

    let private buildSimpleUpsert q u =
        let (id,newDoc) = 
            match (bson.tryGetValueForKey q "_id", bson.tryGetValueForKey u "_id") with
            | Some idq, Some idu ->
                if idq=idu then (idu,u)
                else failwith "can't change id"
            | Some idq, None ->
                let newDoc = bson.setValueForKey u "_id" idq
                (idq,newDoc)
            | None, Some idu ->
                (idu,u)
            | None, None ->
                let id = bson.newObjectID()
                let newDoc = bson.setValueForKey u "_id" id
                (id,newDoc)
        (id,newDoc)

    let private buildUpsertWithUpdateOperators q u =
        let m = Matcher.parseQuery q
        let a = Matcher.getEqs m
        let d1 = 
            Array.fold (fun cur (k,v) ->
                let f ov =
                    Some v
                bson.changeValueForPath cur k f
                ) (BDocument [| |]) a
        let id1 = bson.tryGetValueForKey d1 "_id"
        let ops = parseUpdateDoc u
        let doc = applyUpdateOps d1 ops true None
        match id1 with
        | Some _ -> 
            let id2 = bson.tryGetValueForKey doc "_id"
            if id1 <> id2 then failwith "_id changed"
        | None -> 
            ()
        match bson.tryGetValueForKey doc "_id" with
        | Some v -> 
            (v,doc)
        | None -> 
            let id = bson.newObjectID()
            let newDoc = bson.setValueForKey doc "_id" id
            (id,newDoc)

    let private idChanged d1 d2 =
        let id1 = bson.getValueForKey d1 "_id"
        let id2 = bson.getValueForKey d2 "_id"
        id1 <> id2

    let private connect2() =
        let conn = kv.connect()
        try
            let rconn = kv.connect()
            (conn,rconn)
        with
        | _ -> 
            conn.close()
            reraise()

    let update dbName collName (updates:BsonValue[]) =
        // TODO $isolated should determine whether there is a tx around the whole operation

        let (conn,rconn) = connect2()

        try
            let w = conn.beginWrite dbName collName

            try
                let oneUpdateOrUpsert upd =
                    //printfn "oneUpdateOrUpsert: %A" upd
                    let q = bson.getValueForKey upd "q"
                    let u = bson.getValueForKey upd "u"
                    let multi = bson.getValueForKey upd "multi" |> bson.getBool
                    let upsert = bson.getValueForKey upd "upsert" |> bson.getBool
                    let m = Matcher.parseQuery q
                    let hasUpdateOperators = Array.exists (fun (k:string,_) -> k.StartsWith("$")) (bson.getDocument u)
                    if hasUpdateOperators then
                        let ops = parseUpdateDoc u
                        let (countMatches,countModified) = 
                            if multi then
                                let indexes = w.getIndexes()
                                let plan = chooseIndex indexes m None
                                let {docs=s;funk=funk} = rconn.beginRead dbName collName plan
                                try
                                    let mods = ref 0
                                    let matches = ref 0
                                    s |> seqMatch m |> 
                                        Seq.iter (fun {doc=doc;pos=ndx} -> 
                                            //printfn "iter, doc = %A" doc
                                            let newDoc = applyUpdateOps doc ops false ndx
                                            if idChanged doc newDoc then failwith "cannot change _id"
                                            //printfn "after updates: %A" newDoc
                                            matches := !matches + 1
                                            if newDoc <> doc then
                                                basicUpdate w newDoc
                                                mods := !mods + 1
                                            )
                                    (!matches, !mods)
                                finally
                                    funk()
                            else
                                match getOneMatch w m with
                                | Some {doc=doc;pos=ndx} ->
                                    let newDoc = applyUpdateOps doc ops false ndx
                                    if idChanged doc newDoc then failwith "cannot change _id"
                                    //printfn "after updates: %A" newDoc
                                    if newDoc <> doc then
                                        basicUpdate w newDoc
                                        (1,1)
                                    else
                                        (1,0)
                                | None -> (0,0)
                        if countMatches=0 then
                            if upsert then
                                let (id,newDoc) = buildUpsertWithUpdateOperators q u
                                basicInsert w newDoc
                                (countMatches, countModified, Some id, None)
                            else
                                (countMatches, countModified, None, None)
                        else
                            (countMatches, countModified, None, None)
                    else
                        // TODO what happens if the update document has no update operators
                        // but it has keys which are dotted?
                        if multi then failwith "multi update requires $ update operators"
                        match getOneMatch w m with
                        | Some {doc=found} ->
                            let id1 = bson.getValueForKey found "_id"
                            let newDoc =
                                match bson.tryGetValueForKey u "_id" with
                                | Some id2 ->
                                    if id1=id2 then u
                                    else failwith  "cannot change _id"
                                | None ->
                                    bson.setValueForKey u "_id" id1
                            basicUpdate w newDoc
                            (1,1,None, None)
                        | None ->
                            if upsert then
                                let (id,newDoc) = buildSimpleUpsert q u
                                basicInsert w newDoc
                                (0,0,Some id, None)
                            else
                                (0,0,None, None)

                let results = 
                    Array.map (fun upd ->
                        try oneUpdateOrUpsert upd
                        with e -> (0,0,None,Some (e.ToString()))
                        ) updates
                w.commit()
                results
            with
            | _ ->
                w.rollback()
                reraise()
        finally
            conn.close()
            rconn.close()

    let delete dbName collName (deletes:BsonValue[]) =
        let conn = kv.connect()
        try
            let w = conn.beginWrite dbName collName
            try
                let count = ref 0
                Array.iter (fun upd ->
                    let q = bson.getValueForKey upd "q"
                    let limit = bson.tryGetValueForKey upd "limit"
                    let m = Matcher.parseQuery q
                    // TODO is this safe?  or do we need two-conn isolation like update?
                    let indexes = w.getIndexes()
                    let plan = chooseIndex indexes m None
                    let {docs=s;funk=funk} = w.getSelect plan
                    try
                        s |> seqMatch m |> 
                            Seq.iter (fun {doc=doc} -> 
                                // TODO is it possible to delete from an autoIndexId=false collection?
                                let id = bson.getValueForKey doc "_id"
                                if basicDelete w id then
                                    count := !count + 1
                                )
                    finally
                        funk()
                ) deletes
                w.commit()
                !count
            with
            | _ ->
                w.rollback()
                reraise()
        finally
            conn.close()

    let renameCollection oldName newName dropTarget =
        let conn = kv.connect()
        try
            conn.renameCollection oldName newName dropTarget
        finally
            conn.close()

    let private dofam_upsert w query update gnew fields =
        let hasUpdateOperators = Array.exists (fun (k:string,_) -> k.StartsWith("$")) (bson.getDocument update)
        let q =
            match query with
            | Some q -> q
            | None -> BDocument [| |]
        let (id,newDoc) =
            if hasUpdateOperators then
                buildUpsertWithUpdateOperators q update
            else
                buildSimpleUpsert q update
        basicInsert w newDoc
        if gnew then (None,true,Some id,Some newDoc) else (None,true,Some id,None)

    let private dofam_remove w doc =
        // TODO is it possible to delete from an autoIndexId=false collection?
        let id = bson.getValueForKey doc "_id"
        let removed  = basicDelete w id
        (None,removed,None,Some doc)

    let private dofam_update w st query update gnew fields =
        let doc = st.doc
        let ndx = st.pos
        let hasUpdateOperators = Array.exists (fun (k:string,_) -> k.StartsWith("$")) (bson.getDocument update)
        let (updated,result) =
            if hasUpdateOperators then
                let ops = parseUpdateDoc update
                let newDoc = applyUpdateOps doc ops false ndx
                if idChanged doc newDoc then failwith "cannot change _id"
                //printfn "after updates: %A" newDoc
                let updated = 
                    if newDoc <> doc then 
                        basicUpdate w newDoc
                        true
                    else
                        false
                let result = if gnew then Some newDoc else Some doc
                (updated,result)
            else
                let id1 = bson.getValueForKey doc "_id"
                let newDoc =
                    match bson.tryGetValueForKey update "_id" with
                    | Some id2 ->
                        if id1=id2 then update
                        else failwith  "cannot change _id"
                    | None ->
                        bson.setValueForKey update "_id" id1
                let updated =
                    if newDoc <> doc then 
                        basicUpdate w newDoc
                        true
                    else
                        false
                let result = if gnew then Some newDoc else Some doc
                (updated,result)
        (None,updated,None,result)

    let private seqSort ord s =
        let a1 = s |> Seq.toArray
        let fsort = sortFunc ord (fun st -> st.doc)
        Array.sortInPlaceWith fsort a1
        Array.toSeq a1

    let private getFirstMatch w m ord =
        // TODO collecting all the results and sorting and taking the first one.
        // would probably be faster to just iterate over all and keep track of what
        // the first one would be.
        let indexes = w.getIndexes()
        let plan = chooseIndex indexes m None
        let {docs=s;funk=funk} = w.getSelect plan
        try
            let a = s |> seqMatch m |> seqSort ord |> Seq.truncate 1 |> Seq.toList
            // TODO list match
            let d = 
                if List.isEmpty a then None
                else List.head a |> Some
            d
        finally
            funk()

    let private doProjectionOperator cur k (projOp:(string*BsonValue)[]) =
        // TODO is it really true that the projection op document can only have one thing in it?
        if projOp.Length <> 1 then failwith (sprintf "projOp: %A" projOp)
        let (op,arg) = projOp.[0]
        match op with
        | "$meta" ->
            let f ov =
                match ov with
                | Some v -> Some v // TODO overwrite?
                | None -> 1.0 |> BDouble |> Some // TODO fake textScore
            bson.changeValueForPath cur k f
        | "$elemMatch" ->
            let f ov =
                match ov with
                | None -> None
                | Some (BArray items) ->
                    //let len = items.Length
                    match arg with
                    | BDocument argPairs ->
                        if Matcher.isQueryDoc arg then
                            let m = arg |> Matcher.parseQuery
                            match Array.tryFind (fun v2 -> Matcher.matchQuery m v2 |> fst) items with
                            | Some v -> [| v |] |> BArray |> Some
                            | None -> [| |] |> BArray |> Some
                        else
                            let preds = argPairs |> Matcher.parsePredList
                            match Array.tryFind (fun v2 -> Matcher.matchPredList preds v2 |> fst) items with
                            | Some v -> [| v |] |> BArray |> Some
                            | None -> [| |] |> BArray |> Some
                    | _ -> failwith "arg to $elemMatch must be a document"
                | _ -> ov // TODO is this right?  when $elemMatch gets a non-array, do nothing?
            bson.changeValueForPath cur k f
        | "$slice" ->
            //printfn "projOp: %A" projOp
            let f ov =
                match ov with
                | None -> None
                | Some (BArray items) ->
                    let len = items.Length
                    match arg with
                    | BInt32 _ | BInt64 _ | BDouble _ ->
                        let n = bson.getAsInt32 arg
                        if n > 0 then
                            let n = min n len
                            Array.sub items 0 n |> BArray |> Some
                        else
                            let n = -n
                            let n = min n len
                            Array.sub items (len-n) n |> BArray |> Some
                    | BArray argPair ->
                        if argPair.Length<>2 then failwith "skip,limit array wrong length"
                        let skip = argPair.[0] |> bson.getAsInt32
                        let limit = argPair.[1] |> bson.getAsInt32
                        if skip >= 0 then
                            let skip = min skip len
                            let remaining = len - skip
                            let limit = min limit remaining
                            Array.sub items skip limit |> BArray |> Some
                        else
                            let skip = -skip
                            let skip = min skip len
                            let limit = min limit skip
                            Array.sub items (len-skip) limit |> BArray |> Some
                    | _ -> failwith "arg to $slice must be a number or a 2-number array"
                | _ -> ov // TODO is this right?  when $slice gets a non-array, do nothing?
            bson.changeValueForPath cur k f
        | _ -> failwith (sprintf "unsupported projection operator: %A" projOp)

    let private projOps doc pairs ndx =
        Array.fold (fun cur (k:string,inc) ->
            let k = k.Replace(".$", "") // TODO proper fix for positional here is to remove it? 
            match inc with
            | BDocument projOp -> doProjectionOperator cur k projOp
            | _ -> failwith "not here"
            ) doc pairs

    let private projExclude doc paths =
        Array.fold (fun cur k ->
            bson.excludePath cur k
            ) doc paths

    let private projInclude doc paths ndx =
        //printfn "projInclude doc=%A" doc
        //printfn "projInclude paths=%A" paths
        Array.fold (fun cur k ->
            let k = fixPositional k ndx
            bson.includePath doc k |> bson.merge cur
            ) (BDocument [| |]) paths

    let private projIncludeOps orig doc pairs ndx =
        Array.fold (fun cur (k,_) ->
            let k = fixPositional k ndx
            match bson.findPath orig k with
            | BUndefined -> cur
            | v ->
                let f ov = 
                    match ov with
                    | Some _ -> ov
                    | None -> Some v
                bson.changeValueForPath cur k f
            ) doc pairs

    let private isExplicitInclude v =
        match v with
        | BBoolean b -> b
        | BInt32 i -> i<>0
        | BInt64 i -> i<>0L
        | BDouble f -> ((int32)f)<>0
        | _ -> false

    let private isExplicitExclude v =
        // return true if this is booleable and false
        match v with
        | BBoolean b -> not b
        | BInt32 i -> i=0
        | BInt64 i -> i=0L
        | BDouble f -> ((int32)f)=0
        | _ -> false

    let private positionOperatorInPath (s:string) =
        //s.EndsWith(".$")
        let parts = s.Split('.')
        match Array.tryFindIndex (fun p -> p="$") parts with
        | Some ndx ->
            if ndx = parts.Length-1 then true
            else failwith "projection position operator only allowed at end of path"
        | None -> false

    // TODO seems weird that the server needs access to the stuff below
    type Projection =
        {
            excludes:string[]
            includes:string[]
            excludeMode:bool
            ops:(string*BsonValue)[]
            id:(string*BsonValue) option
        }

    // TODO seems weird that the server needs access to the stuff below
    let verifyProjection proj q =
        match proj with
        | BDocument pairs ->
            // TODO special case when pairs is empty
            let excludes = pairs |> Array.filter (fun (k,v) -> k<>"_id" && (isExplicitExclude v)) |> Array.map (fun (k,_) -> k)
            let includes = pairs |> Array.filter (fun (k,v) -> k<>"_id" && (isExplicitInclude v)) |> Array.map (fun (k,_) -> k)
            let ops = Array.filter (fun (k,v) -> bson.isDocument v) pairs // TODO should check for $slice, etc
            let id = Array.tryFind (fun (k,v) -> k="_id") pairs

            // TODO somewhere in here we need to deal with $meta

            if excludes.Length>0 && includes.Length>0 then failwith (sprintf "cannot have both: %A" pairs)

            let excludeMode =
                if excludes.Length>0 then 
                    true
                else if includes.Length>0 then
                    false
                else 
                    // mongo's rules for deciding whether to use exclude mode or include mode seem
                    // inconsistent for cases where there are no explicit includes or excludes.
                    // elemMatchProjection.js has one test where a projection has only a $slice,
                    // and another test where the projection has only an $elemMatch, and these
                    // two cases end up in different modes.  So...

                    let hasMeta = 
                        Array.exists (fun (_,v) ->
                            match v with
                            | BDocument pairs -> Array.exists (fun (k,v) -> k="$meta") pairs
                            | _ -> false
                            ) ops
                    let hasSlice = 
                        Array.exists (fun (_,v) ->
                            match v with
                            | BDocument pairs -> Array.exists (fun (k,v) -> k="$slice") pairs
                            | _ -> false
                            ) ops
                    let hasElemMatch = 
                        Array.exists (fun (_,v) ->
                            match v with
                            | BDocument pairs -> Array.exists (fun (k,v) -> k="$elemMatch") pairs
                            | _ -> false
                            ) ops
                    if hasSlice then true
                    else if hasElemMatch then false
                    else if hasMeta then false
                    else
                        match id with
                        | Some (_,v) -> 
                            let b = bson.getAsBool v
                            not b
                        | None -> failwith "cannot have nothing"

            if Array.exists positionOperatorInPath excludes then failwith "position operator not allowed with exclude"
            let posopIncludes = Array.filter positionOperatorInPath includes
            let posopOps = Array.filter (fun (k,_) -> positionOperatorInPath k) ops
            if  Array.length posopIncludes + Array.length posopOps > 1 then failwith "more than one position operator"

            let posopPath =
                if Array.length posopIncludes = 1 then
                    posopIncludes.[0] |> Some
                else if Array.length posopOps = 1 then
                    posopOps.[0] |> fst |> Some
                else
                    None

            // TODO in the following check, we ask the matcher for a list of all paths
            // used in the query so we can check the path of the pos op against the list.
            // It would seem nicer if the ndx from the matcher simply contained the path
            // of the array to which the ndx corresponds.
            match (posopPath, q) with
            | (Some path, Some m) ->
                let apath = path.Replace(".$", "")
                let qpaths = Matcher.getPaths m
                // TODO the following checkPrefix should probably check in only one direction
                let found = Array.exists (fun p -> checkPrefix p apath) qpaths
                if not found then failwith (sprintf "query doesn't contain path: %s" apath)
            // TODO other combinations? what if we have posop but no query?  or vice versa?
            | _ -> ()

            {
                excludes=excludes
                includes=includes
                ops=ops
                id=id
                excludeMode=excludeMode
            }

        | _ -> failwith "projection must be a document"

    // TODO seems weird that the server needs access to the stuff below
    let projectDocument d ndx proj =
        //printfn "d = %A" d

        // in excludeMode, everything starts out IN and has to get explicitly kicked out.
        // otherwise, everything starts out OUT and has to be explicitly included.

        let step1 =
            if proj.excludeMode then
                projExclude d proj.excludes
            else
                projInclude d proj.includes ndx

        //printfn "step1: %A" step1

        let step2 =
            if proj.excludeMode then
                step1
            else
                projIncludeOps d step1 proj.ops ndx

        //printfn "step2: %A" step2

        let step3 =
            projOps step2 proj.ops ndx

        //printfn "step3: %A" step3

        let step4 =
            match proj.id with
            | Some (_,idv) ->
                let bId = bson.getAsBool idv
                if proj.excludeMode then
                    if bId then
                        step3
                    else
                        bson.changeValueForPath step3 "_id" (fun _ -> None)
                else
                    if bId then
                        let id = bson.getValueForKey d "_id"
                        let tmp = bson.setValueForKey step3 "_id" id
                        validateKeys tmp |> ignore
                        tmp
                    else
                        step3
            | None ->
                if proj.excludeMode then
                    step3
                else
                    let id = bson.getValueForKey d "_id"
                    let tmp = bson.setValueForKey step3 "_id" id
                    validateKeys tmp |> ignore
                    tmp

        //printfn "step4: %A" step4

        step4

    let private parseIndexMinMax v =
        let m = Matcher.parseQuery v
        match m with
        | QueryDoc a ->
            Array.choose (fun it ->
                match it with
                | Compare (k,[| EQ v |]) ->
                    Some (k,v)
                | _ -> 
                    failwith "wrong format for $min/$max"
            ) a

    let seqSkip n s =
        s
        |> Seq.mapi (fun i elem -> i, elem)
        |> Seq.choose (fun (i, elem) -> if i >= n then Some(elem) else None)

    let private seqLimit n s =
        Seq.truncate n s

    let private seqProject proj m s =
        let prep = verifyProjection proj m
        Seq.map (fun st -> 
            let newDoc = projectDocument st.doc st.pos prep
            // preserve other parts of the state
            {st with doc=newDoc}
            ) s

    let seqOnlyDoc s =
        Seq.map (fun st -> st.doc) s

    let private addCloseToKillFunc conn rdr =
        let funk2() =
            rdr.funk()
            conn.close()
        {rdr with funk=funk2}

    let private getSelectWithClose dbName collName plan = 
        let conn = kv.connect()
        conn.beginRead dbName collName plan |> addCloseToKillFunc conn

    type query_modifiers = 
        {
            orderby:BsonValue option
            projection:BsonValue option
            min:BsonValue option
            max:BsonValue option
            hint:BsonValue option
            explain:BsonValue option // TODO wire version 2?
        }

    let noQueryModifiers = 
        {
            orderby=None
            projection=None
            min=None
            max=None
            hint=None
            explain=None
        }

    let find dbName collName q mods =
        // TODO need a list of indexes, but the conn isn't open yet
        let indexes = listIndexesForCollection dbName collName
        //printfn "in find: indexes = %A" indexes
        let m = Matcher.parseQuery q

        // TODO tests indicate that if there is a $min and/or $max as well as a $hint,
        // then we need to error if they don't match each other.

        let hint = 
            match mods.hint with
            | Some desc -> tryFindIndexByNameOrSpec dbName collName indexes desc
            | None -> None

        let plan = 
            // unless we're going to add comparisons to the query,
            // the bounds for min/max need to be precise, since the matcher isn't
            // going to help if they're not.  min is inclusive.  max is
            // exclusive.
            match (mods.min,mods.max) with
            | Some vmin, Some vmax -> 
                let amin = parseIndexMinMax vmin
                let amax = parseIndexMinMax vmax
                if Array.length amin <> Array.length amax then failwith "different"
                let keys = Array.map (fun (k,v) -> k) amin
                if Array.map (fun (k,v) -> k) amax <> keys then failwith "different"
                let minvals = Array.map (fun (k,v) -> v) amin
                let maxvals = Array.map (fun (k,v) -> v) amax
                match findIndexForMinMax indexes keys with
                | Some ndx -> (ndx,plan.bounds.GTE_LT(minvals,maxvals)) |> plan.q.Plan |> Some
                | None -> failwith "index not found" // TODO or None
            | Some vmin, None ->
                let amin = parseIndexMinMax vmin
                let keys = Array.map (fun (k,v) -> k) amin
                let minvals = Array.map (fun (k,v) -> v) amin
                match findIndexForMinMax indexes keys with
                | Some ndx -> (ndx,plan.bounds.GTE(minvals)) |> plan.q.Plan |> Some
                | None -> failwith "index not found" // TODO or None
            | None, Some vmax ->
                let amax = parseIndexMinMax vmax
                let keys = Array.map (fun (k,v) -> k) amax
                let maxvals = Array.map (fun (k,v) -> v) amax
                match findIndexForMinMax indexes keys with
                | Some ndx -> (ndx,plan.bounds.LT(maxvals)) |> plan.q.Plan |> Some
                | None -> failwith "index not found" // TODO or None
            | None,None -> 
                chooseIndex indexes m hint
                // None

        let rdr = getSelectWithClose dbName collName plan
        try
            let s = rdr.docs
            let s = seqMatch m s
            let s =
                match mods.orderby with
                | Some ord -> seqSort ord s
                | None -> s
            let s = 
                match mods.projection with
                | Some proj -> seqProject proj (Some m) s
                | None -> s
            {rdr with docs=s}
        with
        | _ ->
            rdr.funk()
            reraise()

    let count dbName collName q =
        // TODO should this support query modifiers $min and $max ?
        let rdr = find dbName collName q noQueryModifiers
        try
            Seq.length rdr.docs
        finally
            rdr.funk()

    let findandmodify dbName collName query sort remove update gnew fields upsert =
        let m = 
            match query with
            | Some q -> Matcher.parseQuery q
            | None -> [| |] |> BDocument |> Matcher.parseQuery
        let conn = kv.connect()
        try
            let w = conn.beginWrite dbName collName
            try
                let found = 
                    match sort with
                    | Some s -> getFirstMatch w m s
                    | None -> getOneMatch w m
                //printfn "found: %A" found
                // TODO a 4-tuple is kinda big
                try
                    let (err,changed,upserted,result) =
                        // TODO only the catch case returns an err, so don't put None
                        // at the front of every tuple below.
                        match update,remove with
                        | Some _, Some _ -> failwith "don't specify both update and remove"
                        | None, None -> failwith "must specify either update or remove"
                        | Some u, None -> 
                            match found with
                            | Some st ->
                                dofam_update w st query u gnew fields
                            | None ->
                                if upsert then
                                    dofam_upsert w query u gnew fields
                                else
                                    (None,false,None,None)
                        | None, Some r -> 
                            if upsert then failwith "no upsert with remove"
                            match found with
                            | Some st ->
                                dofam_remove w st.doc
                            | None ->
                                (None,false,None,None)
                    w.commit()
                    (found,err,changed,upserted,result)
                with
                | e ->
                    w.rollback()
                    (found,Some (e.ToString()),false,None,None)
            with
            | e ->
                w.rollback()
                (None,Some (e.ToString()),false,None,None)
        finally
            conn.close()

    let distinct dbName collName key query =
        let m = 
            match query with
            | Some q -> Matcher.parseQuery q
            | None -> [| |] |> BDocument |> Matcher.parseQuery
        // TODO need a list of indexes, but the conn isn't open yet
        let indexes = listIndexesForCollection dbName collName
        let plan = chooseIndex indexes m None

        // TODO do we need special handling here for the case where the collection
        // does not exist?
        let {docs=s;funk=funk} = getSelectWithClose dbName collName plan
        try
            // TODO shouldn't this be a fold?
            let results = ref Set.empty
            s |> seqMatch m |>
                Seq.iter (fun {doc=doc} -> 
                    match bson.findPath doc key with
                    | BUndefined -> ()
                    | v -> results := Set.add v !results
                    )
            Set.toArray !results
        finally
            funk()

    type private Expr =
        | Expr_var of string
        | Expr_literal of BsonValue

        | Expr_allElementsTrue of Expr
        | Expr_anyElementTrue of Expr
        | Expr_dayOfMonth of Expr
        | Expr_dayOfWeek of Expr
        | Expr_dayOfYear of Expr
        | Expr_hour of Expr
        | Expr_millisecond of Expr
        | Expr_minute of Expr
        | Expr_month of Expr
        | Expr_not of Expr
        | Expr_second of Expr
        | Expr_size of Expr
        | Expr_toLower of Expr
        | Expr_toUpper of Expr
        | Expr_week of Expr
        | Expr_year of Expr

        | Expr_cmp of Expr*Expr
        | Expr_eq of Expr*Expr
        | Expr_ne of Expr*Expr
        | Expr_gt of Expr*Expr
        | Expr_lt of Expr*Expr
        | Expr_gte of Expr*Expr
        | Expr_lte of Expr*Expr
        | Expr_subtract of Expr*Expr
        | Expr_divide of Expr*Expr
        | Expr_mod of Expr*Expr
        | Expr_ifNull of Expr*Expr
        | Expr_setDifference of Expr*Expr
        | Expr_setIsSubset of Expr*Expr
        | Expr_strcasecmp of Expr*Expr

        | Expr_substr of Expr*Expr*Expr
        | Expr_cond of Expr*Expr*Expr

        | Expr_and of Expr[]
        | Expr_or of Expr[]
        | Expr_add of Expr[]
        | Expr_multiply of Expr[]
        | Expr_concat of Expr[]
        | Expr_setEquals of Expr[]
        | Expr_setIntersection of Expr[]
        | Expr_setUnion of Expr[]

        | Expr_let of (string*Expr)[]*Expr
        | Expr_map of Expr*string*Expr
        | Expr_dateToString of string*Expr

        // TODO | Expr_meta

    let rec private parseExpr v =
        let getOneArg v =
            match v with
            | BArray a ->
                if Array.length a <> 1 then raise (MongoCode(16020,"wrong number of arguments"))
                a.[0] |> parseExpr
            | _ -> v |> parseExpr

        let getTwoArgs v =
            match v with
            | BArray a ->
                if Array.length a <> 2 then raise (MongoCode(16020,"wrong number of arguments"))
                let v1 = a.[0]
                let v2 = a.[1]
                (parseExpr v1, parseExpr v2)
            | _ -> 
                raise (MongoCode(16020,"wrong number of arguments")) // TODO or perhaps invalid type?

        match v with
        | BDocument [| ("$literal", v) |] -> v |> Expr_literal
        | BString s ->
            if s.StartsWith("$$") then
                s.Substring(2) |> Expr_var
            else if s.StartsWith("$") then
                ("CURRENT." + s.Substring(1)) |> Expr_var
            else
                s |> BString |> Expr_literal

        | BDocument [| ("$allElementsTrue", v) |] -> v |> getOneArg |> Expr_allElementsTrue
        | BDocument [| ("$anyElementTrue", v) |] -> v |> getOneArg |> Expr_anyElementTrue
        | BDocument [| ("$dayOfMonth", v) |] -> v |> getOneArg |> Expr_dayOfMonth
        | BDocument [| ("$dayOfWeek", v) |] -> v |> getOneArg |> Expr_dayOfWeek
        | BDocument [| ("$dayOfYear", v) |] -> v |> getOneArg |> Expr_dayOfYear
        | BDocument [| ("$hour", v) |] -> v |> getOneArg |> Expr_hour
        | BDocument [| ("$millisecond", v) |] -> v |> getOneArg |> Expr_millisecond
        | BDocument [| ("$minute", v) |] -> v |> getOneArg |> Expr_minute
        | BDocument [| ("$month", v) |] -> v |> getOneArg |> Expr_month
        | BDocument [| ("$not", v) |] -> v |> getOneArg |> Expr_not
        | BDocument [| ("$second", v) |] -> v |> getOneArg |> Expr_second
        | BDocument [| ("$size", v) |] -> v |> getOneArg |> Expr_size
        | BDocument [| ("$toLower", v) |] -> v |> getOneArg |> Expr_toLower
        | BDocument [| ("$toUpper", v) |] -> v |> getOneArg |> Expr_toUpper
        | BDocument [| ("$week", v) |] -> v |> getOneArg |> Expr_week
        | BDocument [| ("$year", v) |] -> v |> getOneArg |> Expr_year

        | BDocument [| ("$cmp", v) |] -> v |> getTwoArgs |> Expr_cmp
        | BDocument [| ("$eq", v) |] -> v |> getTwoArgs |> Expr_eq
        | BDocument [| ("$ne", v) |] -> v |> getTwoArgs |> Expr_ne
        | BDocument [| ("$gt", v) |] -> v |> getTwoArgs |> Expr_gt
        | BDocument [| ("$lt", v) |] -> v |> getTwoArgs |> Expr_lt
        | BDocument [| ("$gte", v) |] -> v |> getTwoArgs |> Expr_gte
        | BDocument [| ("$lte", v) |] -> v |> getTwoArgs |> Expr_lte
        | BDocument [| ("$subtract", v) |] -> v |> getTwoArgs |> Expr_subtract
        | BDocument [| ("$divide", v) |] -> v |> getTwoArgs |> Expr_divide
        | BDocument [| ("$mod", v) |] -> v |> getTwoArgs |> Expr_mod
        | BDocument [| ("$ifNull", v) |] -> v |> getTwoArgs |> Expr_ifNull
        | BDocument [| ("$setDifference", v) |] -> v |> getTwoArgs |> Expr_setDifference
        | BDocument [| ("$setIsSubset", v) |] -> v |> getTwoArgs |> Expr_setIsSubset
        | BDocument [| ("$strcasecmp", v) |] -> v |> getTwoArgs |> Expr_strcasecmp

        | BDocument [| ("$substr", BArray [| v1; v2; v3 |]) |] -> (parseExpr v1, parseExpr v2, parseExpr v3) |> Expr_substr
        | BDocument [| ("$cond", BArray [| v1; v2; v3 |]) |] -> (parseExpr v1, parseExpr v2, parseExpr v3) |> Expr_cond
        | BDocument [| ("$cond", BArray a) |] when 3 <> Array.length a  -> raise (MongoCode(16020,"wrong number of arguments"))
        | BDocument [| ("$cond", BDocument args) |] ->
             if Array.exists (fun (k,_) -> k<>"if" && k<>"then" && k<>"else") args then raise (MongoCode(17083,"cond unrecognized arg"))
             let argIf = 
                 match Array.tryFind (fun (k,v) -> k="if") args with
                 | Some (_,v) -> v
                 | None -> raise (MongoCode(17080,"cond missing if"))
             let argThen = 
                 match Array.tryFind (fun (k,v) -> k="then") args with
                 | Some (_,v) -> v
                 | None -> raise (MongoCode(17081,"cond missing then"))
             let argElse = 
                 match Array.tryFind (fun (k,v) -> k="else") args with
                 | Some (_,v) -> v
                 | None -> raise (MongoCode(17082,"cond missing else"))
             (parseExpr argIf, parseExpr argThen, parseExpr argElse) |> Expr_cond

        | BDocument [| ("$and", BArray a) |] -> a |> Array.map (fun v -> parseExpr v) |> Expr_and
        | BDocument [| ("$or", BArray a) |] -> a |> Array.map (fun v -> parseExpr v) |> Expr_or
        | BDocument [| ("$add", BArray a) |] -> a |> Array.map (fun v -> parseExpr v) |> Expr_add
        | BDocument [| ("$multiply", BArray a) |] -> a |> Array.map (fun v -> parseExpr v) |> Expr_multiply
        | BDocument [| ("$concat", BArray a) |] -> a |> Array.map (fun v -> parseExpr v) |> Expr_concat
        | BDocument [| ("$setEquals", BArray a) |] -> a |> Array.map (fun v -> parseExpr v) |> Expr_setEquals
        | BDocument [| ("$setIntersection", BArray a) |] -> a |> Array.map (fun v -> parseExpr v) |> Expr_setIntersection
        | BDocument [| ("$setUnion", BArray a) |] -> a |> Array.map (fun v -> parseExpr v) |> Expr_setUnion

        | BDocument [| ("$let", BDocument args) |] ->
             if Array.exists (fun (k,_) -> k<>"vars" && k<>"in") args then raise (MongoCode(16875,"map unrecognized arg"))
             let argVars = 
                 match Array.tryFind (fun (k,v) -> k="vars") args with
                 | Some (_,BDocument pairs) -> pairs
                 | Some (_,_) -> raise (MongoCode(16876,"$let vars must be a document"))
                 | None -> raise (MongoCode(16876,"$let missing vars"))
             let argIn = 
                 match Array.tryFind (fun (k,v) -> k="in") args with
                 | Some (_,v) -> v
                 | None -> raise (MongoCode(16877,"$let missing in"))
             let vars = Array.map (fun (k,v) -> (k,parseExpr v)) argVars
             let ein = parseExpr argIn
             (vars,ein) |> Expr_let    
        | BDocument [| ("$let", _) |] -> raise (MongoCode(16874,"$let requires an object as its argument"))

        | BDocument [| ("$map", BDocument args) |] ->
             if Array.exists (fun (k,_) -> k<>"input" && k<>"as" && k<>"in") args then raise (MongoCode(16879,"map unrecognized arg"))
             let argInput = 
                 match Array.tryFind (fun (k,v) -> k="input") args with
                 | Some (_,v) -> v
                 | None -> raise (MongoCode(16880,"cond missing input"))
             let argAs = 
                 match Array.tryFind (fun (k,v) -> k="as") args with
                 | Some (_,v) -> v
                 | None -> raise (MongoCode(16881,"cond missing as"))
             let argIn = 
                 match Array.tryFind (fun (k,v) -> k="in") args with
                 | Some (_,v) -> v
                 | None -> raise (MongoCode(16882,"cond missing in"))
             (parseExpr argInput, bson.getString argAs, parseExpr argIn) |> Expr_map
        | BDocument [| ("$dateToString", v) |] ->
            match v with
            | BDocument pairs ->
                let date = 
                    match Array.tryFind (fun (k,_) -> k="date") pairs with
                    | Some (_,v2) -> v2
                    | None -> raise (MongoCode(18628,"$dateToString requires date"))
                let fmt = 
                    match Array.tryFind (fun (k,_) -> k="format") pairs with
                    | Some (_,BString s) -> s
                    | Some _ -> raise (MongoCode(18533,"$dateToString format must be a string"))
                    | None -> raise (MongoCode(18627,"$dateToString requires format"))
                if Array.length pairs > 2 then raise (MongoCode(18534,"$dateToString extra stuff"))
                (fmt,parseExpr date) |> Expr_dateToString
            | _ -> raise (MongoCode(18629,"$dateToString needs an object"))
                 
        | BDocument [| (op, _) |] when op.StartsWith("$") -> raise (MongoCode(15999,"invalid operator"))

        // TODO should we have explicit rules for all the literals?
        | BBoolean _ -> v |> Expr_literal

        // TODO is everything just a literal if it doesn't match anything above?
        // Is {$cond:3} a literal or an error?

        // TODO in a document literal, disallow $keys
        | _ -> v |> Expr_literal
        //| _ -> failwith (sprintf "cannot parse expression: %A" v)

    let private coerceToString v =
        // TODO what are the rules for how/when string coercion happens?
        // this function was written simply because the string expression
        // functions in the aggregation pipeline are documented to require
        // strings but their test suite has a number of cases that verify
        // that coercion to string happens for certain types.  but I can't
        // find a spec which explains which types get coerced and which ones
        // do not.
        match v with
        | BDateTime _ -> 
            let dt = v |> bson.getAsDateTime
            dt.ToString("yyyy-MM-ddTHH:mm:ss", System.Globalization.CultureInfo.InvariantCulture) // TODO this is the wrong format
        | BInt32 n -> string n
        | BInt64 n -> string n
        | BDouble n -> string n
        | BString s -> s
        | BNull -> ""
        | _ -> failwith (sprintf "coerceToString invalid type: %A" v) // TODO raise

    let private initEval d =
        BDocument [| ("CURRENT", d); ("ROOT", d); ("DESCEND", BString "__descend__"); ("PRUNE", BString "__prune__"); ("KEEP", BString "__keep__") |]

    let private legalVarName s =
        s="CURRENT" || Char.IsLower(s.[0])

    let private floatCanBeInt32 f =
        let n = int32 f
        let f2 = float n
        f = f2

    let private floatCanBeInt64 f =
        let n = int64 f
        let f2 = float n
        f = f2

    let private weekOfYear dt =
        let cal = System.Globalization.GregorianCalendar()
        let week = cal.GetWeekOfYear(dt, System.Globalization.CalendarWeekRule.FirstFullWeek, DayOfWeek.Sunday)
        let month = dt.Month
        let week = if month=1 && week>6 then 0 else week
        week

    let rec private formatDate (dt:DateTime) s cur =
        let len = String.length s // have to calc this every time because it changes
        if cur >= len then
            s
        else
            let n = s.IndexOf("%", cur)
            if n<0 then 
                s
            else
                if n+1 >= len then raise (MongoCode(18535,"odd %"))
                let repl = 
                    match s.[n+1] with
                    | 'Y' -> dt.Year.ToString("0000")
                    | 'm' -> dt.Month.ToString("00")
                    | 'd' -> dt.Day.ToString("00")
                    | 'H' -> dt.Hour.ToString("00")
                    | 'M' -> dt.Minute.ToString("00")
                    | 'S' -> dt.Second.ToString("00")
                    | 'L' -> dt.Millisecond.ToString("000")
                    | 'j' -> dt.DayOfYear.ToString("000")
                    | 'w' -> ((dt.DayOfWeek |> int)+1).ToString("0")
                    | 'U' -> (weekOfYear dt).ToString("00")
                    | '%' -> "%"
                    | _ -> raise (MongoCode(18536,(sprintf "invalid modifier: %s" (s.Substring(n)))))
                let before = if n > 0 then s.Substring(0,n) else ""
                let after = if n+2 < len then s.Substring(n+2) else ""
                let s2 = before + repl + after
                formatDate dt s2 (n + repl.Length)

    let rec private eval ctx e =
        match e with
        | Expr_literal lit -> lit
        | Expr_allElementsTrue a ->
            let v = eval ctx a
            let items = bson.getArray v
            let b = Array.forall (fun v -> bson.getAsExprBool v) items
            BBoolean b
        | Expr_anyElementTrue a ->
            let v = eval ctx a
            let items = bson.getArray v
            let b = Array.exists (fun v -> bson.getAsExprBool v) items
            BBoolean b
        | Expr_cmp (e1,e2) -> 
            let v1 = eval ctx e1
            let v2 = eval ctx e2
            Matcher.cmp v1 v2 |> BInt32
        // all of the operators below use simplistic implementations which
        // are different from, for example, Matcher.cmpLTE.  so the implementation
        // of $lte in the agg pipeline is different from the one in the query matcher.
        // this is apparently what mongo does as well.
        | Expr_eq (e1,e2) -> 
            let v1 = eval ctx e1
            let v2 = eval ctx e2
            Matcher.cmp v1 v2 = 0 |> BBoolean
        | Expr_ne (e1,e2) -> 
            let v1 = eval ctx e1
            let v2 = eval ctx e2
            Matcher.cmp v1 v2 <> 0 |> BBoolean
        | Expr_gt (e1,e2) -> 
            let v1 = eval ctx e1
            let v2 = eval ctx e2
            Matcher.cmp v1 v2 > 0 |> BBoolean
        | Expr_lt (e1,e2) -> 
            let v1 = eval ctx e1
            let v2 = eval ctx e2
            Matcher.cmp v1 v2 < 0 |> BBoolean
        | Expr_gte (e1,e2) -> 
            let v1 = eval ctx e1
            let v2 = eval ctx e2
            Matcher.cmp v1 v2 >= 0 |> BBoolean
        | Expr_lte (e1,e2) -> 
            let v1 = eval ctx e1
            let v2 = eval ctx e2
            Matcher.cmp v1 v2 <= 0 |> BBoolean
        | Expr_and a ->
            Array.forall (fun e -> e |> eval ctx |> bson.getAsExprBool) a |> BBoolean
        | Expr_or a ->
            Array.exists (fun e -> e |> eval ctx |> bson.getAsExprBool) a |> BBoolean
        | Expr_not e ->
            e |> eval ctx |> bson.getAsExprBool |> not |> BBoolean
        | Expr_subtract (e1,e2) ->
            let v1 = eval ctx e1
            let v2 = eval ctx e2
            match (v1,v2) with
            | BInt32 n1, BInt32 n2 -> (n1 - n2) |> BInt32
            | BInt64 n1, BInt64 n2 -> (n1 - n2) |> BInt64
            | BDouble n1, BDouble n2 -> (n1 - n2) |> BDouble

            | BInt32 n1, BInt64 n2 -> ((int64 n1) - n2) |> BInt64
            | BInt32 n1, BDouble n2 -> ((float n1) - n2) |> BDouble

            | BInt64 n1, BInt32 n2 -> (n1 - (int64 n2)) |> BInt64
            | BInt64 n1, BDouble n2 -> ((float n1) - n2) |> BDouble

            | BDouble n1, BInt32 n2 -> (n1 - (float n2)) |> BDouble
            | BDouble n1, BInt64 n2 -> (n1 - (float n2)) |> BDouble

            | BDateTime n1, BDateTime n2 -> (n1 - n2) |> BInt64
            | BDateTime n1, BInt32 n2 -> (n1 - (int64 n2)) |> BDateTime
            | BDateTime n1, BInt64 n2 -> (n1 - (int64 n2)) |> BDateTime
            | BDateTime n1, BDouble n2 -> (n1 - (int64 n2)) |> BDateTime

            | _ -> raise (MongoCode(16556, "invalid types for $subtract"))
        | Expr_divide (e1,e2) ->
            let v1 = eval ctx e1
            let v2 = eval ctx e2
            if (v1 |> bson.isNumeric |> not) || (v2 |> bson.isNumeric |> not) then 
                raise (MongoCode(16609, "numeric types only"))
            match v2 with
            | BInt32 0 | BInt64 0L | BDouble 0.0 -> raise (MongoCode(16608, "divide by 0"))
            | _ -> ()

            // TODO assume always doubles here for division?
            ((bson.getAsDouble v1) / (bson.getAsDouble v2)) |> BDouble
        | Expr_mod (e1,e2) ->
            let v1 = eval ctx e1
            let v2 = eval ctx e2
            if (v1 |> bson.isNumeric |> not) || (v2 |> bson.isNumeric |> not) then 
                raise (MongoCode(16611, "numeric types only"))
            match v2 with
            | BInt32 0 | BInt64 0L | BDouble 0.0 -> raise (MongoCode(16610, "mod by 0"))
            | _ -> ()

            match (v1,v2) with
            | BInt32 n1, BInt32 n2 -> (n1 % n2) |> BInt32
            | BInt64 n1, BInt64 n2 -> (n1 % n2) |> BInt64
            | BDouble n1, BDouble n2 -> (n1 % n2) |> BDouble

            | BInt64 n1, BInt32 n2 -> (n1 % (int64 n2)) |> BInt64
            | BInt32 n1, BInt64 n2 -> ((int64 n1) % n2) |> BInt64

            | BDouble n1, BInt32 n2 when floatCanBeInt32 n1 -> ((int32 n1) % n2) |> BInt32
            | BDouble n1, BInt64 n2 when floatCanBeInt64 n1 -> ((int64 n1) % n2) |> BInt64
            | BInt32 n1, BDouble n2 when floatCanBeInt32 n2 -> (n1 % (int32 n2)) |> BInt32
            | BInt64 n1, BDouble n2 when floatCanBeInt64 n2 -> (n1 % (int64 n2)) |> BInt64

            | BDouble n1, BInt32 n2 -> (n1 % (float n2)) |> BDouble
            | BDouble n1, BInt64 n2 -> (n1 % (float n2)) |> BDouble
            | BInt32 n1, BDouble n2 -> ((float n1) % n2) |> BDouble
            | BInt64 n1, BDouble n2 -> ((float n1) % n2) |> BDouble
        | Expr_add a ->
            let vals = Array.map (fun e -> eval ctx e) a
            let countDates = vals |> Array.filter (fun e -> bson.isDate e) |> Array.length
            if countDates>1 then raise (MongoCode(16612, "only one date allowed"))
            if vals |> Array.exists (fun e -> not ((bson.isDate e) || (bson.isNumeric e))) then
                raise (MongoCode(16554, "$add supports numeric or date"))
            if countDates=0 then
                // TODO preserve ints if all ints ?
                let sum = Array.fold (fun sum v -> sum + bson.getAsDouble v) 0.0 vals
                BDouble sum
            else
                let ms = Array.fold (fun sum v -> sum + bson.getAsInt64 v) 0L vals
                BDateTime ms
        | Expr_multiply a ->
            let vals = Array.map (fun e -> eval ctx e) a
            if vals |> Array.exists (fun e -> not (bson.isNumeric e)) then 
                raise (MongoCode(16555, "numeric types only"))
            let result = Array.fold (fun sum v -> sum * bson.getAsDouble v) 1.0 vals
            // TODO preserve ints if all ints
            BDouble result
        | Expr_size e ->
            match eval ctx e with
            | BArray a -> a.Length |> BInt32
            | _ -> raise (MongoCode(17124, "$size requires array"))
        | Expr_cond (eb,et,ef) ->
            if eval ctx eb |> bson.getAsExprBool then eval ctx et
            else eval ctx ef
        | Expr_toLower e ->
            let s = eval ctx e |> coerceToString
            s.ToLower() |> BString
        | Expr_toUpper e ->
            let s = eval ctx e |> coerceToString
            s.ToUpper() |> BString
        | Expr_concat a ->
            Array.fold (fun cur e ->
                match cur,eval ctx e with
                | BNull,_ -> BNull
                | BUndefined,_ -> BNull
                | BString scur,BString s -> scur + s |> BString
                | BString _,BNull -> BNull
                | BString _,BUndefined -> BNull
                | _ -> raise (MongoCode(16702, "$concat needs a string"))
                ) (BString "") a
        | Expr_substr (e1,e2,e3) ->
            let s = eval ctx e1 |> coerceToString
            let slen = s.Length
            let start = eval ctx e2 |> bson.getAsInt32
            if start<0 then
                BString ""
            else if start>=slen then
                BString ""
            else
                let len = eval ctx e3 |> bson.getAsInt32
                if len<0 then
                    s.Substring(start) |> BString
                else if (start+len)>=slen then
                    s.Substring(start) |> BString
                else
                    s.Substring(start,len) |> BString
        | Expr_strcasecmp (e1,e2) ->
            let s1 = eval ctx e1 |> coerceToString
            let s2 = eval ctx e2 |> coerceToString
            String.Compare(s1, s2, StringComparison.OrdinalIgnoreCase) |> BInt32
        | Expr_var s ->
            // if the var contains an object followed by a dotted path,
            // we need to dive into that path.
            let dot = s.IndexOf('.')
            let name = if dot<0 then s else s.Substring(0, dot)
            let v = bson.getValueForKey ctx name
            if dot<0 then
                v
            else
                let subPath = s.Substring(dot+1)
                if subPath.IndexOf(Convert.ToChar(0))>=0 then raise (MongoCode(16419,"field path cannot contain NUL char"))
                match bson.findPath v subPath with
                | BUndefined -> BUndefined // TODO is this right?  or should it just throw?
                | v -> v |> bson.removeUndefined
        | Expr_let (newVars,inExpr) ->
            let ctx =
                // we're supposed to do eager evaluation here, not lazy, right? 
                Array.fold (fun cur (k,e) ->
                    if legalVarName k |> not then raise (MongoCode(16867,"invalid variable name"))
                    let v = eval ctx e
                    bson.setValueForKey cur k v
                    ) ctx newVars
            eval ctx inExpr
        | Expr_map (eInput, name, eIn) ->
            if legalVarName name |> not then raise (MongoCode(16867,"invalid variable name"))
            match eval ctx eInput with
            | BArray a ->
                Array.map (fun v ->
                    let ctx = bson.setValueForKey ctx name v
                    eval ctx eIn
                    ) a |> BArray
            | BNull ->
                BNull
            | _ -> raise (MongoCode(16883,"invalid type"))
        | Expr_ifNull (e1,e2) ->
            let v1 = eval ctx e1
            match v1 with
            | BNull | BUndefined -> eval ctx e2
            | _ -> v1
        | Expr_dateToString (fmt,e) ->
            let v = eval ctx e
            if bson.isNull v then
                BNull
            else
                let dt = v |> bson.getAsDateTime
                // TODO keep this UTC ?
                formatDate dt fmt 0 |> BString
        | Expr_dayOfYear e ->
            let v = eval ctx e
            let dt = v |> bson.getAsDateTime
            // TODO keep this UTC ?
            dt.DayOfYear |> BInt32
        | Expr_dayOfWeek e ->
            let v = eval ctx e
            let dt = v |> bson.getAsDateTime
            // TODO keep this UTC ?
            ((dt.DayOfWeek |> int)+1) |> BInt32
        | Expr_dayOfMonth e ->
            let v = eval ctx e
            let dt = v |> bson.getAsDateTime
            // TODO keep this UTC ?
            dt.Day |> BInt32
        | Expr_hour e ->
            let v = eval ctx e
            let dt = v |> bson.getAsDateTime
            // TODO keep this UTC ?
            dt.Hour |> BInt32
        | Expr_minute e ->
            let v = eval ctx e
            let dt = v |> bson.getAsDateTime
            // TODO keep this UTC ?
            dt.Minute |> BInt32
        | Expr_week e ->
            let v = eval ctx e
            let dt = v |> bson.getAsDateTime
            // TODO keep this UTC ?
            weekOfYear dt |> BInt32
        | Expr_second e ->
            let v = eval ctx e
            let dt = v |> bson.getAsDateTime
            // TODO keep this UTC ?
            dt.Second |> BInt32
        | Expr_millisecond e ->
            let v = eval ctx e
            let dt = v |> bson.getAsDateTime
            // TODO keep this UTC ?
            dt.Millisecond |> BInt32
        | Expr_year e ->
            let v = eval ctx e
            let dt = v |> bson.getAsDateTime
            // TODO keep this UTC ?
            dt.Year |> BInt32
        | Expr_month e ->
            let v = eval ctx e
            let dt = v |> bson.getAsDateTime
            // TODO keep this UTC ?
            dt.Month |> BInt32
        | Expr_setDifference (e1,e2) ->
            let v1 = eval ctx e1 |> bson.getArray |> Set.ofArray
            let v2 = eval ctx e2 |> bson.getArray |> Set.ofArray
            let v3 = Set.difference v1 v2
            v3 |> Set.toArray |> BArray
        | Expr_setEquals a ->
            let len = a.Length
            if len<2 then failwith "must have at least 2"
            let a = Array.map (fun x -> eval ctx x |> bson.getArray |> Set.ofArray) a
            let first = a.[0]
            let b = Array.forall (fun s -> first=s) (Array.sub a 1 (len-1))
            BBoolean b
        | Expr_setIntersection a ->
            let a = Array.map (fun x -> eval ctx x |> bson.getArray |> Set.ofArray) a
            a |> Array.toSeq |> Set.intersectMany |> Set.toArray |> BArray
        | Expr_setIsSubset (e1,e2) ->
            let v1 = eval ctx e1 |> bson.getArray |> Set.ofArray
            let v2 = eval ctx e2 |> bson.getArray |> Set.ofArray
            Set.isSubset v1 v2 |> BBoolean
        | Expr_setUnion a ->
            let len = a.Length
            if len<2 then failwith "must have at least 2"
            let a = Array.map (fun x -> eval ctx x |> bson.getArray |> Set.ofArray) a
            a |> Array.toSeq |> Set.unionMany |> Set.toArray |> BArray

    type private GroupAccum =
        | Accum_sum of Expr
        | Accum_avg of Expr
        | Accum_first of Expr
        | Accum_last of Expr
        | Accum_max of Expr
        | Accum_min of Expr
        | Accum_push of Expr
        | Accum_addToSet of Expr

    let private parseAccum v =
        match v with
        | BDocument [| ("$sum", ev) |] ->
            let e = parseExpr ev
            Accum_sum e
        | BDocument [| ("$avg", ev) |] ->
            let e = parseExpr ev
            Accum_avg e
        | BDocument [| ("$first", ev) |] ->
            let e = parseExpr ev
            Accum_first e
        | BDocument [| ("$last", ev) |] ->
            let e = parseExpr ev
            Accum_last e
        | BDocument [| ("$max", ev) |] ->
            let e = parseExpr ev
            Accum_max e
        | BDocument [| ("$min", ev) |] ->
            let e = parseExpr ev
            Accum_min e
        | BDocument [| ("$push", ev) |] ->
            let e = parseExpr ev
            Accum_push e
        | BDocument [| ("$addToSet", ev) |] ->
            let e = parseExpr ev
            Accum_addToSet e
        | _ -> failwith (sprintf "cannot parse $group accum: %A" v)


    // TODO this type was created so that all the projection operations
    // could be done in the order they appeared, which we are not really
    // doing.  So now the parser is constructing these values and then
    // we unconstruct them later.  Messy.
    type private AggProj =
        | AggProjInclude
        | AggProjExpr of Expr

    type private AggOp =
        | AggSkip of int
        | AggLimit of int
        | AggSort of BsonValue
        | AggOut of string
        | AggUnwind of string
        | AggMatch of QueryDoc
        | AggProject of (string*AggProj)[]
        | AggGroup of BsonValue*(string*GroupAccum)[]
        | AggGeoNear of BsonValue
        | AggRedact of Expr

    let private flattenProjection d =
        let rec flatten f path d =
            match d with
            | BDocument pairs ->
                if Array.exists (fun (k:string,_) -> k.StartsWith("$")) pairs then
                    if path="" then
                        raise (MongoCode(16404, "$project key begins with $"))
                    else
                        f path d
                else
                    Array.iter (fun (k,v) ->
                        let newPath = 
                            if path="" then k
                            else path + "." + k
                        flatten f newPath v
                    ) pairs
            | _ -> f path d

        let a = ResizeArray<_>()
        let f path d = a.Add(path,d)
        flatten f "" d
        a.ToArray()

    let private parseAgg items =
        Array.map (fun d ->
            match d with
            // TODO is multiple patterns the best way to deal with these?
            | BDocument [| ("$limit", BInt32 n) |] -> n |> AggLimit
            | BDocument [| ("$limit", BDouble n) |] -> n|> int32 |> AggLimit
            | BDocument [| ("$limit", BInt64 n) |] -> n |> int32 |> AggLimit

            | BDocument [| ("$skip", BInt32 n) |] -> n |> AggSkip
            | BDocument [| ("$skip", BDouble n) |] -> n |> int32 |> AggSkip
            | BDocument [| ("$skip", BInt64 n) |] -> n |> int32 |> AggSkip

            | BDocument [| ("$sort", BDocument keys) |] -> AggSort (BDocument keys)
            | BDocument [| ("$out", BString s) |] -> AggOut s
            | BDocument [| ("$unwind", BString s) |] -> AggUnwind s
            | BDocument [| ("$match", q) |] -> 
                let m = q |> Matcher.parseQuery
                if Matcher.usesWhere m then raise (MongoCode(16395, "$where not allowed in agg match"))
                if Matcher.usesNear m then raise (MongoCode(16424, "$near not allowed in agg match"))
                m |> AggMatch
            | BDocument [| ("$project", BDocument args) |] -> 
                // flatten so that:
                // project b:{a:1} should be an inclusion of b.a, not {a:1} as a doc literal for b
                let args = args |> BDocument |> flattenProjection
                //printfn "args: %A" args
                if Array.exists (fun (k:string,_) -> k.StartsWith("$")) args then
                    raise (MongoCode(16404, "$project key begins with $"))
                let (id,notid) = Array.partition (fun (k,v) -> k="_id") args
                if Array.length id > 1 then failwith "only one id"
                let idItem =
                    if Array.length id=0 then
                        Some ("_id",AggProjInclude)
                    else
                        let v = id.[0] |> snd
                        match v with
                        | BInt32 0 | BInt64 0L | BDouble 0.0 | BBoolean false -> None
                        | _ -> Some ("_id", parseExpr v |> AggProjExpr)
                let expressions =
                    Array.map (fun (k,v) ->
                        match v with
                        | BInt32 1 | BInt64 1L | BDouble 1.0 | BBoolean true ->
                            (k,AggProjInclude)
                        | _ ->
                            (k,parseExpr v |> AggProjExpr)
                    ) notid
                match idItem with
                | Some ida ->
                    let e2 = [| [| ida |]; expressions |] |> Array.concat
                    AggProject e2
                | None ->
                    AggProject expressions
            | BDocument [| ("$group", BDocument args) |] -> 
                let len = Array.length args
                if len<1 then failwith "$group requires args"
                if args.[0] |> fst <> "_id" then failwith "$group requires _id first"
                let id = args.[0] |> snd
                let accums = Array.sub args 1 (len-1) |> Array.map (fun (k,op) -> (k, parseAccum op))
                if Array.exists (fun (k:string,_) -> k.IndexOf('.')>=0) accums then raise (MongoCode(16414,"$group field name cannot contain '.'"))
                //printfn "parsed accums: %A" accums
                AggGroup (id, accums)
            | BDocument [| ("$redact", v) |] -> 
                let e = parseExpr v
                e |> AggRedact
            | BDocument [| ("$geoNear", BDocument args) |] -> args |> BDocument |> AggGeoNear
            | BDocument [|  |] -> raise (MongoCode(16435, "agg pipeline stage spec must have one thing in it"))
            | BDocument [| (_,_) |] -> raise (MongoCode(16436, "invalid agg pipeline stage spec"))
            | _ -> raise (MongoCode(16435, "invalid pipeline spec"))
            ) items

    let private seqRedact e s =
        Seq.choose (fun st -> 
            let rec f doc =
                match eval (initEval doc) e with
                | BString "__descend__" ->
                    let pairs = bson.getDocument doc
                    let newDoc =
                        Array.fold (fun cur (k,v) ->
                            match v with
                            | BArray a ->
                                let rec fa a =
                                    let a2 = 
                                        Array.choose (fun v ->
                                            match v with
                                            | BDocument _ -> f v 
                                            | BArray a3 -> Some (fa a3)
                                            | _ -> Some v
                                        ) a
                                    BArray a2
                                bson.setValueForKey cur k (fa a)
                            | BDocument _ ->
                                match f v  with
                                | Some d -> bson.setValueForKey cur k d
                                | None -> cur
                            | _ ->
                                bson.setValueForKey cur k v
                        ) (BDocument Array.empty) pairs
                    Some newDoc
                | BString "__prune__" -> 
                    None
                | BString "__keep__" -> 
                    Some doc
                | _ -> raise (MongoCode(17053, "invalid result from redact expression"))
            // preserve other parts of the state
            match f st.doc with
            | Some d -> Some {st with doc=d}
            | None -> None
            ) s

    let private seqAggProject expressions s =
        //printfn "expressions: %A" expressions
        Seq.map (fun st ->
            let d = st.doc
            //printfn "projecting from: %A" d
            let d0 = BDocument [| |]
            let includes = 
                Array.choose (fun (k,op) ->
                    match op with
                    | AggProjInclude -> Some k
                    | AggProjExpr _ -> None
                ) expressions
            // TODO to pass 6177 we cannot do all the inclusions and then do all the expressions.
            //
            // but 6184 requires that we process inclusions in the order they appear in the document, not in the order they appear in the projection
            let exes = 
                Array.choose (fun (k,op) ->
                    match op with
                    | AggProjInclude -> None
                    | AggProjExpr e -> Some (k,e)
                ) expressions
            // TODO exes and includes could have been a partition?
            let d0 = bson.project3 d includes
            let d3 =
                Array.fold (fun cur (k,e) ->
                    //printfn "path: %s" k
                    //printfn "op: %A" op
                    #if not
                    match op with
                    | AggProjInclude ->
                        // TODO this needs to fail when it tries to set x.b while x is already an int, for example
                        let copied = bson.includePath d k
                        //printfn "copied: %A" copied
                        //printfn "cur: %A" cur
                        let cur = copied |> bson.merge cur
                        //printfn "new cur: %A" cur
                        cur
                    | AggProjExpr e ->
                    #endif
                        //printfn "e: %A" e
                        let v = eval (initEval d) e
                        //printfn "v: %A" v
                        let f ov = 
                            //printfn "ov: %A" ov
                            match ov with
                            | Some existing -> 
                                //printfn "ov is %A" existing
                                raise (MongoCode(16400, "already"))
                            | None -> 
                                //printfn "ov is None"
                                match v with
                                | BUndefined -> None
                                | _ -> Some v
                        //printfn "cur: %A" cur
                        let cur = bson.changeValueForPath cur k f
                        //printfn "new cur: %A" cur
                        cur
                    ) d0 exes
            //printfn "projection result: %A" d3
            let d = st.doc
            {st with doc=d3}
            ) s

    let private seqUnwind (path:string) s =
        // TODO strip the $ in front.  verify it?
        let path = path.Substring(1)
        Seq.collect (fun st ->
            match bson.findPath st.doc path with
            | BUndefined -> Seq.empty
            | BNull -> Seq.empty
            | BArray a ->
                if Array.length a=0 then
                    Seq.empty
                else
                    seq { 
                        for i in 0..a.Length-1 do 
                            let v=a.[i] 
                            let f ov = Some v
                            // TODO no positional operator here?
                            let d2 = bson.changeValueForPath st.doc path f
                            //printfn "unwound: %A" d2
                            // TODO should we preserve score and pos here?
                            yield {st with doc=d2}
                    }
            | _ -> raise (MongoCode(15978, "$unwind needs array"))
            ) s

    let private seqGroup id ops s =
        let exprId = parseExpr id
        // this function discards score and pos from the states
        let mapa =
            Seq.fold (fun cur {doc=doc} ->
                let idval = eval (initEval doc) exprId
                let accums = 
                    match Map.tryFind idval cur with
                    | Some found -> found
                    | None -> BDocument [| ("_id",idval) |]
                let accums =
                    Array.fold (fun cur (k:string,op) ->
                        //printfn "in accums fold: k = %s" k
                        //printfn "in accums fold: cur = %A" cur
                        //printfn "in accums fold: op = %A" op
                        match op with
                        | Accum_first e ->
                            match bson.tryGetValueForKey cur k with
                            | Some _ ->
                                cur
                            | None ->
                                let v = eval (initEval doc) e
                                bson.setValueForKey cur k v
                        | Accum_last e ->
                            let v = eval (initEval doc) e
                            bson.setValueForKey cur k v
                        | Accum_max e ->
                            let v = eval (initEval doc) e
                            match bson.tryGetValueForKey cur k with
                            | Some curv ->
                                let c = Matcher.cmp v curv
                                if c > 0 then
                                    bson.setValueForKey cur k v
                                else
                                    cur
                            | None ->
                                cur
                        | Accum_min e ->
                            let v = eval (initEval doc) e
                            match bson.tryGetValueForKey cur k with
                            | Some curv ->
                                let c = Matcher.cmp v curv
                                if c < 0 then
                                    bson.setValueForKey cur k v
                                else
                                    cur
                            | None ->
                                cur
                        | Accum_push e ->
                            let v = eval (initEval doc) e
                            match bson.tryGetValueForKey cur k with
                            | Some (BArray a) -> 
                                bson.setValueForKey cur k (BArray (Array.append a [| v |]))
                            | Some x -> failwith (sprintf "should not: %A" x)
                            | None -> BArray [| v |]
                        | Accum_addToSet e ->
                            let v = eval (initEval doc) e
                            match bson.tryGetValueForKey cur k with
                            | Some (BArray a) -> 
                                let s = Set.ofArray a
                                let s = Set.add v s
                                let a = Set.toArray s
                                bson.setValueForKey cur k (BArray a)
                            | Some x -> failwith (sprintf "should not: %A" x)
                            | None -> BArray [| v |]
                        | Accum_sum e ->
                            let v = eval (initEval doc) e |> bson.getAsDouble // TODO always double?
                            let prevSum =
                                match bson.tryGetValueForKey cur k with
                                | Some curv -> bson.getAsDouble curv
                                | None -> 0.0
                            bson.setValueForKey cur k (BDouble (v + prevSum))
                        | Accum_avg e ->
                            let v = eval (initEval doc) e
                            // only certain types become part of the average.  others are ignored.
                            let v = 
                                match v with
                                | BInt32 n -> n |> float |> Some
                                | BInt64 n -> n |> float |> Some
                                | BDouble n -> n |> float |> Some
                                | _ -> None
                            match v with
                            | Some f ->
                                // add to the average

                                // see if the count/sum pair subdoc exists yet
                                let (count,sum) =
                                    match bson.tryGetValueForKey cur k with
                                    | Some (BDocument [| ("count",BInt32 count);("sum",BDouble sum) |]) -> (count,sum)
                                    | Some x -> failwith (sprintf "should not: %A" x)
                                    | None -> (0,0.0)
                                let newPair = BDocument [| ("count",BInt32 (count+1));("sum",BDouble (sum+f)) |]
                                bson.setValueForKey cur k newPair
                            | None ->
                                // ignore
                                cur
                    ) accums ops
                //printfn "after accum: %A" accums
                Map.add idval accums cur
                ) Map.empty s
        // avg needs to get fixed up now, since we store it along the way as a running count and sum.
        // replace that with the sum divided by the count.
        let mapa = 
            Map.map (fun _ accums ->
                let accums =
                    Array.fold (fun cur (k,op) ->
                        match op with
                        | Accum_avg _ ->
                            match bson.tryGetValueForKey cur k with
                            | Some (BDocument [| ("count",BInt32 count);("sum",BDouble sum) |]) ->
                                // TODO what if count is 0 ?
                                bson.setValueForKey cur k (BDouble (sum / (float count)))
                            | None ->
                                // TODO this should maybe be an error.  if a value for this avg accumulator
                                // exists, then it darn well oughta be the count/sum pair we put there.
                                cur
                        | _ ->
                            cur
                    ) accums ops
                accums
                ) mapa
        //printfn "last step: %A" mapa
        // this function discards score and pos from the states
        mapa |> Map.toSeq |> Seq.map (fun (_,d) -> {doc=d;score=None;pos=None} )

    let aggregate dbName collName pipeline =
        let ops = parseAgg pipeline

        // check to see if the first pipeline stage is match.  if so,
        // check for an index we can use.

        let plan =
            if Array.length ops = 0 then
                None
            else
                match Array.get ops 0 with
                | AggMatch m ->
                    // TODO need a list of indexes, but the conn isn't open yet
                    let indexes = listIndexesForCollection dbName collName
                    chooseIndex indexes m None
                | _ ->
                    None

        let {docs=s;funk=funk} = getSelectWithClose dbName collName plan

        try
            let (out,ops) =
                let len = Array.length ops
                if len=0 then
                    (None,ops)
                else
                    match ops.[len-1] with
                    | AggOut s -> (Some s, Array.sub ops 0 (len-1))
                    | _ -> (None,ops)

            let s = 
                Array.fold (fun cur op ->
                    match op with
                    | AggSkip n -> seqSkip n cur
                    | AggLimit n -> seqLimit n cur
                    | AggSort keys -> cur |> seqSort keys
                    | AggMatch m -> seqMatch m cur
                    | AggProject expressions -> seqAggProject expressions cur
                    | AggOut s -> failwith "$out can only appear at the end of the pipeline"
                    | AggUnwind s -> seqUnwind s cur
                    | AggGroup (id,ops) -> seqGroup id ops cur
                    | AggGeoNear _ -> failwith "not implemented" // TODO only as first stage
                    | AggRedact e -> seqRedact e cur
                    ) s ops

            let s = seqOnlyDoc s

            (out,s,funk)
        with
        | _ ->
            funk()
            reraise()

    let private seqMatchOnlyDoc m s =
        s 
        |> Seq.choose (fun doc ->
                let (ok,_) = Matcher.matchQuery m doc
                if ok then Some doc
                else None
              )

    let doFilter a q =
        let m = Matcher.parseQuery q
        a |> Seq.ofArray |> seqMatchOnlyDoc m |> Seq.toArray

