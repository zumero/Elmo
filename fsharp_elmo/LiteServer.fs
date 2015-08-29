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

// This server exists so that we can run the jstests suite (from the MongoDB
// source repo on GitHub) against Elmo.  It is *not* expected that an actual
// server listening on a socket would be useful for the common use cases on 
// a mobile device.

module LiteServer = 

    open System
    open System.IO
    open System.Net
    open System.Net.Sockets
    open System.Threading

    let cursors = System.Collections.Generic.Dictionary<int64,string*seq<BsonValue>*(unit->unit)>()
    let mutable cursorNum = 0L

    // TODO mongo has a way of automatically killing a cursor after 10 minutes idle

    let storeCursor coll s funk =
        //printfn "storeCursor: %s" coll
        cursorNum <- cursorNum + 1L
        cursors.[cursorNum] <- (coll,s,funk)
        cursorNum

    let fetchCursor cursorID =
        let (found,result) = cursors.TryGetValue(cursorID)
        if found then
            cursors.Remove(cursorID) |> ignore
            Some result
        else
            None

    let killCursorIfExists cursorID =
        match fetchCursor cursorID with
        | Some (_,_,funk) -> funk()
        | None -> ()

    let removeCursorsForCollection coll =
        //printfn "removeCursorsForCollection: %s" coll
        let a = ResizeArray<_>()
        for pair in cursors do
            let (c,_,_) = pair.Value
            //printfn "in removeCursorsForCollection, seeing %s" c
            if c = coll then
                //printfn "    which will be removed"
                a.Add(pair.Key)
        for cursorID in a do
            killCursorIfExists cursorID

    let createReply reqID docs crsrID =
        let msg = 
            {
            r_requestID = 0
            r_responseTo = reqID
            r_responseFlags = 0
            r_cursorID = crsrID
            r_startingFrom = 0 // TODO
            r_documents = docs
            }
        msg

    let private reply_whatsmyuri clientMsg =
        let pairs = ResizeArray<_>()
        pairs.Add("you", BString "127.0.0.1:65460") // TODO wrong
        pairs.Add("ok", BDouble 1.0)
        let doc = BDocument (pairs.ToArray())
        createReply clientMsg.q_requestID [| doc |] 0L

    let private reply_renameCollection clientMsg =
        let q = clientMsg.q_query
        let oldName = bson.getValueForKey q "renameCollection" |> bson.getString
        let newName = bson.getValueForKey q "to" |> bson.getString
        let dropTarget = 
            match bson.tryGetValueForKey q "dropTarget" with
            | Some v ->
                match v with
                | BBoolean b -> b
                | _ -> false
            | None -> false
        crud.renameCollection oldName newName dropTarget
        let pairs = ResizeArray<_>()
        // TODO
        pairs.Add("ok", BDouble 1.0)
        let doc = BDocument (pairs.ToArray())
        createReply clientMsg.q_requestID [| doc |] 0L

    let private reply_replSetGetStatus clientMsg =
        let pairs = ResizeArray<_>()
        pairs.Add("_id", BInt32 0)
        pairs.Add("name", BString "whatever") // TODO
        pairs.Add("state", BInt32 1)
        pairs.Add("health", BDouble 1.0)
        pairs.Add("stateStr", BString "PRIMARY")
        pairs.Add("uptime", BInt32 0) // TODO
        pairs.Add("optime", BTimeStamp 0L) // TODO
        pairs.Add("optimeDate", BDateTime 0L) // TODO
        pairs.Add("electionTime", BTimeStamp 0L) // TODO
        pairs.Add("electionDate", BDateTime 0L) // TODO
        pairs.Add("self", BBoolean true)
        let mine = BDocument (pairs.ToArray())

        let pairs = ResizeArray<_>()
        pairs.Add("set", BString "foo")
        pairs.Add("date", BDateTime 0L) // TODO
        pairs.Add("myState", BInt32 1)
        pairs.Add("members", BArray [| mine |])
        pairs.Add("ok", BDouble 1.0)
        let doc = BDocument (pairs.ToArray())
        createReply clientMsg.q_requestID [| doc |] 0L

    let private reply_isMaster clientMsg =
        let pairs = ResizeArray<_>()
        pairs.Add("setName", BString "foo") // TODO
        pairs.Add("setVersion", BInt32 1)
        pairs.Add("ismaster", BBoolean true)
        pairs.Add("secondary", BBoolean false)
        pairs.Add("maxWireVersion", BInt32 3)
        // ver >= 2:  we don't support the older fire-and-forget write operations. 
        // ver >= 3:  we don't support the older form of explain
        // TODO if we set minWireVersion to 3, which is what we want to do, so
        // that we can tell the client that we don't support the older form of
        // explain, what happens is that we start getting the old fire-and-forget
        // write operations instead of the write commands that we want.
        pairs.Add("minWireVersion", BInt32 2) 
        // TODO
        pairs.Add("ok", BDouble 1.0)
        let doc = BDocument (pairs.ToArray())
        createReply clientMsg.q_requestID [| doc |] 0L

    let private reply_getLog_startupWarnings clientMsg = 
        let pairs = ResizeArray<_>()
        pairs.Add("totalLinesWritten", BInt32 0)
        pairs.Add("log", BArray [| |])
        pairs.Add("ok", BDouble 1.0)
        let doc = BDocument (pairs.ToArray())
        createReply clientMsg.q_requestID [| doc |] 0L

    let private reply_AdminCmd clientMsg =
        match clientMsg.q_query with
        | BsonValue.BDocument pairs ->
            match pairs.[0] with
            // TODO probably don't need to match on the other half of the pair?
            | ("whatsmyuri", BsonValue.BInt32 1) -> reply_whatsmyuri clientMsg
            | ("renameCollection", BString whatever) -> reply_renameCollection clientMsg
            | ("getLog", BsonValue.BString "startupWarnings") -> reply_getLog_startupWarnings clientMsg
            | ("replSetGetStatus", BsonValue.BDouble 1.0) -> reply_replSetGetStatus clientMsg
            | ("isMaster", BsonValue.BDouble 1.0) -> reply_isMaster clientMsg
            | _ -> failwith (sprintf "unknown admin.$cmd : %A" pairs.[0])
        | _ -> failwith "how could this not be a document?"

    let grab (num: int) (source: seq<'a>) : array<'a>*seq<'a> =
        let e = source.GetEnumerator()
        let idx = ref 0
        let loop = ref true
        let a = ResizeArray<_>()
        while !idx < num && !loop do
            if e.MoveNext() then
                a.Add(e.Current)
            else
                loop := false
            idx := !idx + 1
        let r1 = a.ToArray()
        // now construct a seq for the leftovers, using the same
        // enumerator.
        let r2 = seq {
            // TODO once again we have an enumerator here which doesn't get
            // freed unless the seq gets fully consumed.
            while e.MoveNext() do
                yield e.Current
            e.Dispose()
            }
        (r1,r2)

    let private reply_code requestID code errmsg =
        let pairs = ResizeArray<_>()
        // TODO stack trace was nice here
        pairs.Add("errmsg", BString ("exception: " + errmsg))
        pairs.Add("code", BInt32 code)
        pairs.Add("ok", BInt32 0)
        let doc = BDocument (pairs.ToArray())
        createReply requestID [| doc |] 0L

    let private reply_with_cursor ns s funk cursorOptions defaultBatchSize =
        let numberToReturn =
            match cursorOptions with
            | Some (BDocument pairs) ->
                if Array.exists (fun (k,v) -> k<>"batchSize") pairs then failwith "nope"
                let pair = Array.tryFind
                match Array.tryFind (fun (k,_) -> k="batchSize") pairs with
                | Some (_,BInt32 n) -> if n<0 then failwith "nope" else n
                | Some (_,BDouble f) -> if f<0.0 then failwith "nope" else f |> int32
                | Some (_,BInt64 n) -> if n<0L then failwith "nope" else n |> int32
                | Some _ -> failwith "nope"
                | None -> defaultBatchSize
            | Some _ -> failwith "nope"
            | None -> 
                // TODO in the case where the cursor is not requested, how
                // many should we return?  For now we return all of them,
                // which for now we flag by setting numberToReturn to a negative
                // number, which is handled as a special case below.
                -1

        let (docs,cursorID) = 
            if numberToReturn<0 then
                let docs = Seq.toArray s
                funk()
                (docs, 0L)
            else if numberToReturn=0 then
                // if 0, return nothing but keep the cursor open.
                // but we need to eval the first item in the seq,
                // to make sure that an error gets found now.
                // but we can't consume that first item and let it
                // get lost.  so we grab a batch but then put it back.

                let (one,s2) = grab defaultBatchSize s
                if Array.length one = 0 then
                    // batch contained nothing.  kill the cursor.
                    funk()
                    [| |],0L
                else
                    // put the batch back
                    let s3a = Array.toSeq one
                    let cursorID =
                        if Array.length one=defaultBatchSize then
                            let s3 = [| s3a; s2|] |> Array.toSeq |> Seq.concat
                            storeCursor ns s3 funk
                        else
                            // the first batch consumed the cursor
                            funk()
                            storeCursor ns s3a (fun () -> ())
                    [| |],cursorID
            else
                let (docs,s2) = grab numberToReturn s
                if Array.length docs=numberToReturn then
                    // if we grabbed the same number we asked for, we assume the
                    // sequence has more, so we store the cursor and return it.
                    let cursorID = storeCursor ns s2 funk
                    (docs, cursorID)
                else
                    // but if we got less than we asked for, we assume we have
                    // consumed the whole sequence.
                    funk()
                    (docs, 0L)

        let doc = 
            match cursorOptions with
            | Some _ ->
                BDocument [| ("cursor",BDocument [| ("id",BInt64 cursorID);("ns",BString ns);("firstBatch",BArray docs) |]);("ok",BInt32 1) |]
            | None ->
                BDocument [| ("result",BArray docs) ;("ok",BInt32 1) |]
        doc

    let doInsert db coll s =
        let results = crud.insert db coll s
        let writeErrors =
            results
            |> Array.filter (fun (_,err) ->
                match err with
                | Some _ -> true
                | None -> false
                )
            |> Array.mapi (fun i (_,err) ->
                // TODO use of Option.get is bad, but we just filtered all the Some values above
                BDocument [| ("index",BInt32 i); ("errmsg",Option.get err |> BString) |]
                )
        (results,writeErrors)

    let private reply_aggregate clientMsg db = 
        let q = clientMsg.q_query
        let coll = bson.getValueForKey q "aggregate" |> bson.getString
        let pipeline = bson.getValueForKey q "pipeline" |> bson.getArray
        let cursorOptions = bson.tryGetValueForKey q "cursor"
        match cursorOptions with
        | Some (BDocument _) -> ()
        | Some _ -> failwith "nope"
        | None -> ()
        try
            let (out,s,funk) = crud.aggregate db coll pipeline
            try
                match out with
                | Some newCollName ->
                    if newCollName.StartsWith("system.") then raise (MongoCode(17385, "no $out into system collection"))
                    match db |> Some |> crud.listCollections |> Array.tryFind (fun (dbName,collName,options) -> collName=newCollName) with
                    | Some (dbName,collName,options) ->
                        match bson.tryGetValueForKey options "capped" with
                        | Some _ -> raise (MongoCode(17152, "no $out into capped collection"))
                        | _ -> ()
                    | None -> ()
                    let fullColl = sprintf "%s.%s" db newCollName
                    removeCursorsForCollection fullColl
                    crud.clearCollection db newCollName
                    let (results,writeErrors) = doInsert db newCollName s
                    funk()
                    let doc = reply_with_cursor (db+"."+coll) (Seq.empty) (fun ()->()) (Some (BDocument Array.empty)) 100
                    createReply clientMsg.q_requestID [| doc |] 0L
                | None ->
                    let defaultBatchSize = 100 // TODO
                    let doc = reply_with_cursor (db+"."+coll) s funk cursorOptions defaultBatchSize
                    createReply clientMsg.q_requestID [| doc |] 0L
            with
            | _ ->
                funk()
                reraise()
        with
        | MongoCode(code,errmsg) -> reply_code clientMsg.q_requestID code errmsg

    let private reply_Insert clientMsg db = 
        let q = clientMsg.q_query
        let coll = bson.getValueForKey q "insert" |> bson.getString
        let docs = bson.getValueForKey q "documents" |> bson.getArray
        // TODO ordered
        let (results,writeErrors) = doInsert db coll (Seq.ofArray docs)
        let pairs = ResizeArray<_>()
        pairs.Add("n", BInt32 (results.Length - writeErrors.Length))
        //pairs.Add("lastOp", BTimeStamp 0L) // TODO
        if writeErrors.Length > 0 then
            pairs.Add("writeErrors", BArray writeErrors)
        // TODO electionId?
        pairs.Add("ok", BDouble 1.0)
        let doc = BDocument (pairs.ToArray())
        createReply clientMsg.q_requestID [| doc |] 0L

    let private reply_DropCollection clientMsg db = 
        let q = clientMsg.q_query
        let coll = bson.getValueForKey q "drop" |> bson.getString
        let fullColl = sprintf "%s.%s" db coll
        removeCursorsForCollection fullColl
        let bDeleted = crud.dropCollection db coll
        let pairs = ResizeArray<_>()
        //pairs.Add("lastOp", BTimeStamp 0L) // TODO
        // TODO electionId?
        pairs.Add("ok", (if bDeleted then 1 else 0) |> BInt32)
        if not bDeleted then
            pairs.Add("errmsg", BString "ns not found") // mongo shell apparently cares about this exact error message string
        let doc = BDocument (pairs.ToArray())
        createReply clientMsg.q_requestID [| doc |] 0L

    let private reply_DropDatabase clientMsg db = 
        let q = clientMsg.q_query
        //let whatever = bson.getValueForKey q "dropDatabase"
        crud.dropDatabase db
        let pairs = ResizeArray<_>()
        pairs.Add("ok", BDouble 1.0)
        let doc = BDocument (pairs.ToArray())
        createReply clientMsg.q_requestID [| doc |] 0L

    let private reply_CreateCollection clientMsg db = 
        let q = clientMsg.q_query
        let coll = bson.getValueForKey q "create" |> bson.getString
        let options = BDocument Array.empty
        // TODO maybe just pass everything through instead of looking for specific options
        let options =
            match bson.tryGetValueForKey q "autoIndexId" with
            | Some (BBoolean b) -> bson.setValueForKey options "autoIndexId" (BBoolean b)
            | _ -> options
        let options =
            match bson.tryGetValueForKey q "temp" with
            | Some (BBoolean b) -> bson.setValueForKey options "temp" (BBoolean b)
            | _ -> options
        let options =
            match bson.tryGetValueForKey q "capped" with
            | Some (BBoolean b) -> bson.setValueForKey options "capped" (BBoolean b)
            | _ -> options
        let options =
            match bson.tryGetValueForKey q "size" with
            | Some (BInt32 n) -> bson.setValueForKey options "size" (n |> int64 |> BInt64)
            | Some (BInt64 n) -> bson.setValueForKey options "size" (n |> int64 |> BInt64)
            | Some (BDouble n) -> bson.setValueForKey options "size" (n |> int64 |> BInt64)
            | _ -> options
        let options =
            match bson.tryGetValueForKey q "max" with
            | Some (BInt32 n) -> bson.setValueForKey options "max" (n |> int64 |> BInt64)
            | Some (BInt64 n) -> bson.setValueForKey options "max" (n |> int64 |> BInt64)
            | Some (BDouble n) -> bson.setValueForKey options "max" (n |> int64 |> BInt64)
            | _ -> options
        let ids = crud.createCollection db coll options
        let pairs = ResizeArray<_>()
        pairs.Add("ok", BDouble 1.0)
        let doc = BDocument (pairs.ToArray())
        createReply clientMsg.q_requestID [| doc |] 0L

    let private reply_Delete clientMsg db = 
        let q = clientMsg.q_query
        let coll = bson.getValueForKey q "delete" |> bson.getString
        let deletes = bson.getValueForKey q "deletes" |> bson.getArray
        // TODO limit
        // TODO ordered
        let results = crud.delete db coll deletes
        let pairs = ResizeArray<_>()
        pairs.Add("n", BInt32 results)
        //pairs.Add("lastOp", BTimeStamp 0L) // TODO
        // TODO electionId?
        pairs.Add("ok", BDouble 1.0)
        let doc = BDocument (pairs.ToArray())
        createReply clientMsg.q_requestID [| doc |] 0L

    let private reply_FindAndModify clientMsg db = 
        let q = clientMsg.q_query
        let coll = bson.getValueForInsensitiveKey q "findandmodify" |> bson.getString
        let query = bson.tryGetValueForKey q "query"
        let sort = bson.tryGetValueForKey q "sort"
        let remove = bson.tryGetValueForKey q "remove"
        let update = bson.tryGetValueForKey q "update"
        let gnew = 
            match bson.tryGetValueForKey q "new" with
            | Some (BBoolean b) -> b
            | _ -> false
        let fields = bson.tryGetValueForKey q "fields"
        let upsert = 
            match bson.tryGetValueForKey q "upsert" with
            | Some (BBoolean b) -> b
            | _ -> false

        // TODO remove needs to return number removed?  or is it always 1 or 0?
        let (found,err,changed,upserted,result) = crud.findandmodify db coll query sort remove update gnew upsert

        let lastErrorObject = ResizeArray<_>()
        let pairs = ResizeArray<_>()

        // TODO docs say: The updatedExisting field only appears if the command specifies an update or an update 
        // with upsert: true; i.e. the field does not appear for a remove.

        lastErrorObject.Add("n", BInt32 (if changed then 1 else 0)) // TODO always 1 ?  appears for every op?

        match upserted with
        | Some id -> lastErrorObject.Add("upserted", id)
        | _ -> ()

        match update,found,upsert with
        | Some _,None,_ -> lastErrorObject.Add("updatedExisting", BBoolean false)
        | Some _,Some _,false -> lastErrorObject.Add("updatedExisting", BBoolean changed)
        | _ -> lastErrorObject.Add("updatedExisting", BBoolean changed)

        // TODO docs say: if not found, for update or remove (but not upsert), then
        // lastErrorObject does not appear in the return document and the value field holds a null.

        // TODO docs say: for update with upsert: true operation that results in an insertion, if the command 
        // also specifies new is false and specifies a sort, the return document has a lastErrorObject, value, 
        // and ok fields, but the value field holds an empty document {}.

        // TODO docs say: for update with upsert: true operation that results in an insertion, if the command 
        // also specifies new is false but does not specify a sort, the return document has a lastErrorObject, value, 
        // and ok fields, but the value field holds a null.

        match err with
        | Some s -> 
            lastErrorObject.Add("errmsg", BString s) // TODO is this right?  docs don't say this.
            pairs.Add("ok", BDouble 0.0)
        | None ->
            pairs.Add("ok", BDouble 1.0)

        match result with
        | Some v -> 
            match fields with
            | Some proj ->
                // TODO calling stuff below that seems like it should be private to the crud module
                let prep = crud.verifyProjection proj None // TODO projection position op allowed here?
                pairs.Add("value", crud.projectDocument {doc=v;score=None;pos=None} prep) // TODO projection position op allowed here?
            | None ->
                pairs.Add("value", v)
        | None -> pairs.Add("value", BNull)

        pairs.Add("lastErrorObject", BDocument (lastErrorObject.ToArray()))
        let doc = BDocument (pairs.ToArray())
        createReply clientMsg.q_requestID [| doc |] 0L

    let private reply_distinct clientMsg db =
        let q = clientMsg.q_query
        let coll = bson.getValueForKey q "distinct" |> bson.getString
        let key = 
            match bson.getValueForKey q "key" with
            | BString s -> s
            | _ -> raise (MongoCode(18510, "invalid type for distinct"))
        let qry = 
            let qv = bson.tryGetValueForKey q "query" 
            match qv with
            | Some (BDocument s) -> qv
            | _ -> raise (MongoCode(18511, "invalid type for distinct"))
        let values = crud.distinct db coll key qry
        let pairs = ResizeArray<_>()
        pairs.Add("values", BArray values)
        pairs.Add("ok", BDouble 1.0)
        let doc = BDocument (pairs.ToArray())
        createReply clientMsg.q_requestID [| doc |] 0L

    let private reply_Update clientMsg db = 
        let q = clientMsg.q_query
        let coll = bson.getValueForKey q "update" |> bson.getString
        let updates = bson.getValueForKey q "updates" |> bson.getArray
        // TODO ordered
        let results = crud.update db coll updates
        //printfn "results: %A" results
        let matches = Array.sumBy (fun (matches,_,_,_) -> matches) results
        let mods = Array.sumBy (fun (_,mods,_,_) -> mods) results
        let upserted =
            results
            |> Array.filter (fun (_,_,up,_) ->
                match up with
                | Some _ -> true
                | None -> false
                )
            |> Array.mapi (fun i (_,_,up,_) -> 
                BDocument [| ("index",BInt32 i); ("_id",Option.get up) |]
                )
        let writeErrors =
            results
            |> Array.filter (fun (_,_,_,err) ->
                match err with
                | Some _ -> true
                | None -> false
                )
            |> Array.mapi (fun i (_,_,_,err) ->
                BDocument [| ("index",BInt32 i); ("errmsg",Option.get err |> BString) |]
                )

        let pairs = ResizeArray<_>()
        pairs.Add("n", BInt32 (matches + upserted.Length))
        pairs.Add("nModified", BInt32 (mods))
        if upserted.Length > 0 then
            pairs.Add("upserted", BArray upserted)
        if writeErrors.Length > 0 then
            pairs.Add("writeErrors", BArray writeErrors)
        //pairs.Add("lastOp", BTimeStamp 0L) // TODO probably not
        // TODO electionId? probably not
        pairs.Add("ok", BDouble 1.0)
        let doc = BDocument (pairs.ToArray())
        createReply clientMsg.q_requestID [| doc |] 0L


    let private reply_Count clientMsg db = 
        let q = clientMsg.q_query
        let coll = bson.getValueForKey q "count" |> bson.getString
        // TODO fields
        let query = bson.tryGetValueForKey q "query"
        let query =
            match query with
            | Some q -> q
            | None -> BDocument [| |]
        let mods = 
            {
                crud.orderby = None
                crud.projection = None
                crud.min = None
                crud.max = None
                crud.hint = bson.tryGetValueForKey q "hint"
                crud.explain = None
            }
        let count = crud.count db coll query mods
        // TODO it's a little weird to do skip/limit here instead of
        // the way it's done for find.
        let skip = bson.tryGetValueForKey q "skip"
        let count =
            match skip with
            | Some v -> 
                let n = bson.getAsInt32 v
                if n < 0 then failwith "negative skip"
                if count >= n then count - n else 0
            | None -> count
        let limit = bson.tryGetValueForKey q "limit"
        let count =
            match limit with
            | Some v -> 
                let n = bson.getAsInt32 v
                let n = if n<0 then -n else n // TODO hard limit vs soft limit
                // TODO limit of 0 is no limit
                if n > 0 && count > n then n else count
            | None -> count
        let pairs = ResizeArray<_>()
        pairs.Add("n", BInt32 (count))
        //pairs.Add("lastOp", BTimeStamp 0L) // TODO
        // TODO electionId?
        pairs.Add("ok", BDouble 1.0)
        let doc = BDocument (pairs.ToArray())
        createReply clientMsg.q_requestID [| doc |] 0L

    let private reply_Validate clientMsg db = 
        let q = clientMsg.q_query
        let coll = bson.getValueForKey q "validate" |> bson.getString
        // TODO ordered
        let pairs = ResizeArray<_>()
        //pairs.Add("n", BInt32 (0)) // TODO
        pairs.Add("valid", BBoolean true) // TODO
        // TODO electionId?
        pairs.Add("ok", BDouble 1.0)
        let doc = BDocument (pairs.ToArray())
        createReply clientMsg.q_requestID [| doc |] 0L

    let private reply_createIndexes clientMsg db = 
        let q = clientMsg.q_query
        let coll = bson.getValueForKey q "createIndexes" |> bson.getString
        let indexes = bson.getValueForKey q "indexes" |> bson.getArray
        let result = crud.createIndexes db coll indexes
        // TODO createdCollectionAutomatically
        // TODO numIndexesBefore
        // TODO numIndexesAfter
        let pairs = ResizeArray<_>()
        pairs.Add("ok", BDouble 1.0)
        let doc = BDocument (pairs.ToArray())
        createReply clientMsg.q_requestID [| doc |] 0L

    let private reply_deleteIndexes clientMsg db = 
        //printfn "%A" clientMsg
        let q = clientMsg.q_query
        let coll = bson.getValueForKey q "deleteIndexes" |> bson.getString
        let index = bson.getValueForKey q "index"
        let fullColl = sprintf "%s.%s" db coll
        removeCursorsForCollection fullColl
        let (count_indexes_before, num_indexes_deleted) = crud.deleteIndexes db coll index
        // TODO nIndexesWas
        let pairs = ResizeArray<_>()
        pairs.Add("ok", BDouble 1.0)
        let doc = BDocument (pairs.ToArray())
        createReply clientMsg.q_requestID [| doc |] 0L

    let private reply_features clientMsg db = 
        let q = clientMsg.q_query
        //let coll = bson.getValueForKey q "createIndexes" |> bson.getString
        //let indexes = bson.getValueForKey q "indexes" |> bson.getArray
        // TODO return oidMachine
        let pairs = ResizeArray<_>()
        pairs.Add("ok", BDouble 1.0)
        let doc = BDocument (pairs.ToArray())
        createReply clientMsg.q_requestID [| doc |] 0L

    let private reply_listCollections clientMsg (db:string) =
        let q = clientMsg.q_query
        let result = crud.listCollections (Some db)
        let result = Array.map (fun (dbName,collName,options) -> BDocument [| ("name", BString collName);("options", options) |]) result
        let result = 
            match bson.tryGetValueForKey q "filter" with
            // TODO calling stuff below that seems like it should be private to the crud module
            | Some d -> crud.doFilter result d
            | None -> result
        let s = Seq.ofArray result
        let funk() = ()
        let defaultBatchSize = 100
        let cursorOptions = bson.tryGetValueForKey q "cursor"
        let cursorOptions =
            match cursorOptions with
            | Some (BDocument _) -> cursorOptions
            | Some _ -> failwith (sprintf "invalid cursor options: %A" cursorOptions)
            | None -> Array.empty |> BDocument |> Some
        let doc = reply_with_cursor (db+"."+"$cmd.listCollections") s funk cursorOptions defaultBatchSize
        createReply clientMsg.q_requestID [| doc |] 0L

    let private reply_listIndexes clientMsg (db:string) =
        let q = clientMsg.q_query
        let coll = 
            match bson.getValueForKey q "listIndexes" with
            | BString "" -> failwith "empty string not allowed here"
            | BString s -> s
            | _ -> failwith "must be a string"
        let result = crud.listIndexes (Some db) (Some coll)
        let result = 
            Array.map (fun (ndxInfo:index_info) -> 
                let unique = 
                    match bson.tryGetValueForKey ndxInfo.options "unique" with
                    | Some (BBoolean true) -> true
                    | _ -> false
                let pairs = ResizeArray<_>()
                pairs.Add("name", BString ndxInfo.ndx)
                pairs.Add("ns", BString (sprintf "%s.%s" ndxInfo.db ndxInfo.coll))
                pairs.Add("key", ndxInfo.spec)
                // TODO it seems the automatic index on _id is NOT supposed to be marked unique
                if unique && ndxInfo.ndx<>"_id_" then pairs.Add("unique", BBoolean unique)
                pairs.ToArray() |> BDocument
                ) result
        let s = Seq.ofArray result
        let funk() = ()
        let defaultBatchSize = 100
        let cursorOptions = bson.tryGetValueForKey q "cursor"
        let cursorOptions =
            match cursorOptions with
            | Some (BDocument _) -> cursorOptions
            | Some _ -> failwith "nope"
            | None -> Array.empty |> BDocument |> Some
        let doc = reply_with_cursor (db+"."+"$cmd.listIndexes") s funk cursorOptions defaultBatchSize
        createReply clientMsg.q_requestID [| doc |] 0L

    let tryGetKeyWithOrWithoutDollarSignPrefix v k =
        match bson.tryGetValueForKey v ("$"+k) with
        | Some r -> Some r
        | None ->
            // now without the dollar sign
            match bson.tryGetValueForKey v k with
            | Some r -> Some r
            | None -> None

    let private reply_err clientMsg (e:Exception) =
        let pairs = ResizeArray<_>()
        pairs.Add("$err", BString (e.ToString()))
        let doc = BDocument (pairs.ToArray())
        let r = createReply clientMsg.q_requestID [| doc |] 0L
        {r with r_responseFlags=2}

    let reply_explain clientMsg db = 
        let q_query = clientMsg.q_query
        let explain = bson.getValueForKey q_query "explain"
        let verbosity = bson.getValueForKey q_query "verbosity" |> bson.getString
        let coll = bson.getValueForKey explain "find" |> bson.getString
        let filter = bson.getValueForKey explain "filter"
        let options = bson.getValueForKey explain "options"
        let orderby = tryGetKeyWithOrWithoutDollarSignPrefix options "orderby"
        let ndxMin = tryGetKeyWithOrWithoutDollarSignPrefix options "min"
        let ndxMax = tryGetKeyWithOrWithoutDollarSignPrefix options "max"
        let ndxHint = tryGetKeyWithOrWithoutDollarSignPrefix options "hint"
        let projection = clientMsg.q_returnFieldsSelector

        let mods = 
            {
                crud.orderby = orderby
                crud.projection = projection
                crud.min = ndxMin
                crud.max = ndxMax
                crud.hint = ndxHint
                crud.explain = None // TODO what to do with this?
            }

        let rdr = crud.find db coll filter mods

        try
            let num =
                let s = rdr.docs
                let s = 
                    if clientMsg.q_numberToSkip > 0 then
                        // TODO do we want seqSkip to be public?
                        crud.seqSkip (clientMsg.q_numberToSkip) s
                    else if clientMsg.q_numberToSkip < 0 then
                        failwith "negative skip"
                    else
                        s

                #if not // apparently explain is supposed to ignore hard limits
                let numberToReturn = clientMsg.q_numberToReturn
                if numberToReturn < 0 || numberToReturn = 1 then
                    // hard limit, would not return a cursor
                    let n = if numberToReturn < 0 then -numberToReturn else numberToReturn
                    if n <0 then failwith "overflow"
                    let num = Seq.truncate n s |> Seq.length
                    rdr.funk()
                    num
                else
                #endif

                // would return everything
                let num = s |> Seq.length
                rdr.funk()
                num

            let set d k v =
                let f ov = Some v
                bson.changeValueForPath d k f

            let queryPlanner = BDocument Array.empty
            let queryPlanner = sprintf "%s.%s" db coll |> BString |> set queryPlanner "namespace" 
            let queryPlanner = false |> BBoolean |> set queryPlanner "indexFilterSet" 
            // TODO parsedQuery
            // TODO winningPlan

            (*

                "queryPlanner" : {
                    "plannerVersion" : 1,
                    "namespace" : "test.foo",
                    "indexFilterSet" : false,
                    "parsedQuery" : {
                        "a" : {
                            "$eq" : 1
                        }
                    },
                    "winningPlan" : {
                        "stage" : "FETCH",
                        "inputStage" : {
                            "stage" : "IXSCAN",
                            "keyPattern" : {
                                "a" : 1
                            },
                            "indexName" : "a_1",
                            "isMultiKey" : true,
                            "direction" : "forward",
                            "indexBounds" : {
                                "a" : [
                                    "[1.0, 1.0]"
                                ]
                            }
                        }
                    },
                    "rejectedPlans" : [ ]
                },
                "serverInfo" : {
                    "host" : "erics-air-2.ad.sourcegear.com",
                    "port" : 27017,
                    "version" : "3.0.1",
                    "gitVersion" : "534b5a3f9d10f00cd27737fbcd951032248b5952"
                },

            *)

            let serverInfo = BDocument Array.empty
            let serverInfo = "Elmo" |> BString |> set queryPlanner "software" // TODO not really present from Mongo
            let serverInfo = "TODO" |> BString |> set queryPlanner "version"
            let serverInfo = "TODO" |> BString |> set queryPlanner "host" 
            let serverInfo = 27017 |> BInt32 |> set queryPlanner "port"  // TODO

            let doc = BDocument Array.empty
            let doc = set doc "queryPlanner" queryPlanner
            let doc = set doc "serverInfo" serverInfo

            let doc = 
                match verbosity with
                | "executionStats"
                | "allPlansExecution" ->
                    let stats = BDocument Array.empty
                    let stats = num |> BInt32 |> set stats "nReturned"
                    let stats = rdr.totalKeysExamined() |> BInt32 |> set stats "totalKeysExamined"
                    let stats = rdr.totalDocsExamined() |> BInt32 |> set stats "totalDocsExamined"
                    // TODO
                    set doc "executionStats" stats
                | _ -> doc

            let doc = set doc "ok" (BDouble 1.0)
            createReply clientMsg.q_requestID [| doc |] 0L
        with
            | e -> 
                //printfn "%A" e
                rdr.funk()
                reply_err clientMsg e


    let private reply_cmd clientMsg (db:string) =
        // this code assumes that the first key is always the command
        let cmd = 
            match clientMsg.q_query with
            | BDocument pairs ->
                if Array.isEmpty pairs then failwith "empty query"
                let (k,v) = pairs.[0]
                k
            | _ -> failwith "query must be a document"
        let cmd = cmd.ToLower()
        match cmd with
        | "explain" -> reply_explain clientMsg db
        | "aggregate" -> reply_aggregate clientMsg db
        | "insert" -> reply_Insert clientMsg db
        | "delete" -> reply_Delete clientMsg db
        | "distinct" -> reply_distinct clientMsg db
        | "update" -> reply_Update clientMsg db
        | "findandmodify" -> reply_FindAndModify clientMsg db
        | "count" -> reply_Count clientMsg db
        | "validate" -> reply_Validate clientMsg db
        | "createindexes" -> reply_createIndexes clientMsg db
        | "deleteindexes" -> reply_deleteIndexes clientMsg db
        | "drop" -> reply_DropCollection clientMsg db
        | "dropdatabase" -> reply_DropDatabase clientMsg db
        | "listcollections" -> reply_listCollections clientMsg db
        | "listindexes" -> reply_listIndexes clientMsg db
        | "create" -> reply_CreateCollection clientMsg db
        | "features" -> reply_features clientMsg db
        | _ -> failwith (sprintf "unknown foo.$cmd : %A" cmd)
     
    let private reply_cmd_sys_inprog clientMsg (db:string) =
        let pairs = ResizeArray<_>()
        pairs.Add("inprog", BArray [| |]) // TODO
        pairs.Add("ok", BDouble 1.0)
        let doc = BDocument (pairs.ToArray())
        createReply clientMsg.q_requestID [| doc |] 0L

    let private reply_system_indexes clientMsg (db:string) =
        let q = clientMsg.q_query
        let dbName,collName = 
            match bson.tryGetValueForKey q "ns" with
            | Some (BString ns) -> 
                let a,b = bson.splitname ns
                (Some a, Some b)
            | _ -> 
                None,None
        let result = crud.listIndexes dbName collName
        let result = result |> Array.map (fun ndxInfo -> BDocument [| "name", BString ndxInfo.ndx |])
        createReply clientMsg.q_requestID result 0L

    let private reply_system_namespaces clientMsg (db:string) =
        let result = None |> crud.listCollections |> Array.map (fun (dbName,collName,options) -> BDocument [| "name", BString (sprintf "%s.%s" dbName collName) |])
        createReply clientMsg.q_requestID result 0L

    let doLimit coll numberToReturn s kill =
        if numberToReturn < 0 || numberToReturn = 1 then
            // hard limit, do not return a cursor
            let n = if numberToReturn < 0 then -numberToReturn else numberToReturn
            if n <0 then failwith "overflow"
            let docs = Seq.truncate n s |> Seq.toArray
            kill()
            (docs, 0L)
        else if numberToReturn=0 then
            // return whatever the default size is
            // TODO for now, just return them all and close the cursor
            let docs = Seq.toArray s
            kill()
            (docs, 0L)
        else
            // soft limit.  keep cursor open.
            let (docs,s2) = grab numberToReturn s
            if docs.Length > 0 then
                let cursorID = storeCursor coll s2 kill
                (docs, cursorID)
            else
                kill()
                (docs, 0L)

    let private reply_Query clientMsg = 
        let fullCollectionName = clientMsg.q_fullCollectionName
        let (db,coll) = bson.splitname fullCollectionName
        let bvQuery = clientMsg.q_query

        // TODO what if somebody queries on a field named query?  ambiguous.

        // This *might* just have the query in it.  OR it might have the 
        // query in a key called query, which might also be called $query,
        // along with other stuff (like orderby) as well.
        // This other stuff is called query modifiers.  
        // Sigh.

        let (actualQuery, queryFormat2) = 
            match tryGetKeyWithOrWithoutDollarSignPrefix bvQuery "query" with
            | Some q -> (q,true)
            | None -> (bvQuery,false)

        let orderby = 
            if queryFormat2 then
                tryGetKeyWithOrWithoutDollarSignPrefix bvQuery "orderby"
            else
                // TODO orderby in the legacy format?
                None

        let ndxMin = 
            if queryFormat2 then
                tryGetKeyWithOrWithoutDollarSignPrefix bvQuery "min"
            else
                None

        let ndxMax = 
            if queryFormat2 then
                tryGetKeyWithOrWithoutDollarSignPrefix bvQuery "max"
            else
                None

        let ndxHint = 
            if queryFormat2 then
                tryGetKeyWithOrWithoutDollarSignPrefix bvQuery "hint"
            else
                None

        let explain = 
            if queryFormat2 then
                tryGetKeyWithOrWithoutDollarSignPrefix bvQuery "explain"
            else
                None

        let projection = clientMsg.q_returnFieldsSelector

        let mods = 
            {
                crud.orderby = orderby
                crud.projection = projection
                crud.min = ndxMin
                crud.max = ndxMax
                crud.hint = ndxHint
                crud.explain = explain
            }

        //printfn "actualQuery: %A" actualQuery
        let {docs=s;funk=kill} = crud.find db coll actualQuery mods

        let s = crud.seqOnlyDoc s

        try
            let s = 
                if clientMsg.q_numberToSkip > 0 then
                    // TODO do we want seqSkip to be public?
                    crud.seqSkip (clientMsg.q_numberToSkip) s
                else if clientMsg.q_numberToSkip < 0 then
                    failwith "negative skip"
                else
                    s

            let (docs,cursorID) = doLimit fullCollectionName clientMsg.q_numberToReturn s kill

            createReply clientMsg.q_requestID docs cursorID
        with
            | e -> 
                kill()
                reply_err clientMsg e

    let private reply_errmsg clientMsg (e:Exception) =
        let pairs = ResizeArray<_>()
        pairs.Add("errmsg", BString (e.ToString()))
        pairs.Add("ok", BInt32 0)
        let doc = BDocument (pairs.ToArray())
        createReply clientMsg.q_requestID [| doc |] 0L

    let reply2004 clientMsg =
        let pair = clientMsg.q_fullCollectionName.Split('.')
        if pair.Length < 2 then failwith (sprintf "bad collection name: %s" (clientMsg.q_fullCollectionName))
        let db = pair.[0]
        let coll = pair.[1]
        if db = "admin" then
            if coll = "$cmd" then
                reply_AdminCmd clientMsg
            else
                failwith "not implemented"
        else
            if coll = "$cmd" then
                if pair.Length = 4 && pair.[2]="sys" && pair.[3]="inprog" then
                    reply_cmd_sys_inprog clientMsg db
                else
                    reply_cmd clientMsg db
            else if pair.Length=3 && pair.[1]="system" && pair.[2]="indexes" then
                reply_system_indexes clientMsg db
            else if pair.Length=3 && pair.[1]="system" && pair.[2]="namespaces" then
                reply_system_namespaces clientMsg db
            else
                try
                    reply_Query clientMsg
                with
                    | e -> reply_err clientMsg e

    let reply2005 clientMsg =
        let cursorID = clientMsg.m_cursorID
        match fetchCursor cursorID with
        | Some (coll,s,funk) ->
            let (docs,cursorID) = doLimit coll clientMsg.m_numberToReturn s funk
            createReply clientMsg.m_requestID docs cursorID
        | None ->
            let r = createReply clientMsg.m_requestID [| |] 0L
            {r with r_responseFlags=1}

    type Socket with
        member socket.AsyncAccept() = Async.FromBeginEnd(socket.BeginAccept, socket.EndAccept)

    type Server() =
        static member Start(hostname:string, ?port) =
            let ipAddress = Dns.GetHostEntry(hostname).AddressList.[0]
            Server.Start(ipAddress, ?port = port)

        static member Start(?ipAddress, ?port, ?verbose) =
            let ipAddress = defaultArg ipAddress IPAddress.Any
            let port = defaultArg port 80
            let verbose = defaultArg verbose true
            let endpoint = IPEndPoint(ipAddress, port)
            let cts = new CancellationTokenSource()
            let listener = new Socket(AddressFamily.InterNetwork, SocketType.Stream, ProtocolType.Tcp)
            listener.Bind(endpoint)
            listener.Listen(int SocketOptionName.MaxConnections)
            printfn "Started listening on port %d" port
        
            let serviceClient clientSocket = async {
                let clientStream = new NetworkStream(clientSocket, false) 

                try
                    try
                        while true do
                            let! msg = protocol.readMessage clientStream
                            if verbose then
                                printfn "----------------------------------------------------------------"
                                printfn "Received %d bytes from client" (msg.Length)
                            if msg.Length > 0 then
                                let m = protocol.parseMessageFromClient msg
                                if verbose then printfn "%A" m
                                //m.CompareTo(msg)

                                match m with
                                | BsonMsgKillCursors km ->
                                    // as far as I can tell, even in the new version of the mongo
                                    // wire protocol, killCursors does not have a way to reply to
                                    // to the client.
                                    for cursorID in km.k_cursorIDs do
                                        killCursorIfExists cursorID
                                | _ ->
                                    let resp = 
                                        match m with
                                        | BsonMsgQuery qm ->
                                            try 
                                                reply2004 qm
                                            with
                                                | MongoCode(code,errmsg) -> reply_code qm.q_requestID code errmsg
                                                | e -> reply_errmsg qm e
                                        | BsonMsgGetMore gm -> 
                                            try
                                                reply2005 gm  
                                            with
                                                | MongoCode(code,errmsg) -> reply_code gm.m_requestID code errmsg
                                        | BsonMsgKillCursors km -> 
                                            failwith "should not happen"  
                                    if verbose then printfn "%A" resp
                                    let ra = protocol.encodeReply resp
                                    do! clientStream.AsyncWrite(ra, 0, ra.Length)
                    with :? System.IO.EndOfStreamException -> ()
                finally
                    clientStream.Close()
                    //clientSocket.Shutdown(SocketShutdown.Both)
                    clientSocket.Close()
            }

            let rec loop() = async {
                printfn "Waiting for request ..."
                let! socket = listener.AsyncAccept()
                printfn "Received connection"
                do! serviceClient socket
                return! loop() }

            Async.Start(loop(), cancellationToken = cts.Token)
            { new IDisposable with member x.Dispose() = cts.Cancel(); listener.Close() }

    let runServer port verbose =
        use s = Server.Start(port = port, verbose=verbose)
        System.Console.ReadLine() |> ignore
        printfn "bye!"


