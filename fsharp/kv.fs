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

type index_info =
    {
        db:string
        coll:string
        ndx:string // TODO should be called name
        spec:BsonValue
        options:BsonValue
    }

module plan =
    type TextQueryTerm =
        | Word of bool*string
        | Phrase of bool*string

    type bounds = 
        | EQ of BsonValue[]
        | Text of BsonValue[]*TextQueryTerm[]
        | GT of BsonValue[]
        | GTE of BsonValue[]
        | LT of BsonValue[]
        | LTE of BsonValue[]
        | GT_LT of BsonValue[]*BsonValue[]
        | GT_LTE of BsonValue[]*BsonValue[]
        | GTE_LT of BsonValue[]*BsonValue[]
        | GTE_LTE of BsonValue[]*BsonValue[]

    type q =
        | Plan of index_info*bounds

type state =
    {
        doc:BsonValue
        score:float option
        pos:int option
    }

type reader = 
    {
        docs:seq<state>
        totalKeysExamined:unit->int
        totalDocsExamined:unit->int
        funk:unit->unit
        // TODO need a method here to get the number of docs scanned
    }

type tx_write =
    {
        database:string
        collection:string
        insert:BsonValue->unit
        update:BsonValue->unit
        delete:BsonValue->bool
        getSelect:(plan.q option)->reader
        getIndexes:unit->index_info[]
        commit:unit->unit
        rollback:unit->unit
    }

type conn_methods =
    {
        // TODO filename:string

        listCollections:unit->(string*string*BsonValue)[]
        listIndexes:unit->index_info[]

        createCollection:string->string->BsonValue->bool
        dropCollection:string->string->bool
        renameCollection:string->string->bool->bool
        clearCollection:string->string->bool

        createIndexes:index_info[]->bool[]
        dropIndex:string->string->string->bool

        dropDatabase:string->bool

        beginWrite:string->string->tx_write
        beginRead:string->string->(plan.q option)->reader

        close:unit->unit
    }

module kv =
    open SQLitePCL
    open SQLitePCL.Ugly

    // TODO I'm not sure this type is worth the trouble anymore.
    // maybe we should go back to just keeping a bool that specifies
    // whether we need to negate or not.
    type IndexType =
        | Forward
        | Backward
        | Geo2d

    let private decodeIndexType v =
        match v with
        | BInt32 n -> if n<0 then IndexType.Backward else IndexType.Forward
        | BInt64 n -> if n<0L then IndexType.Backward else IndexType.Forward
        | BDouble n -> if n<0.0 then IndexType.Backward else IndexType.Forward
        | BString "2d" -> IndexType.Geo2d
        | _ -> failwith (sprintf "decodeIndexType: %A" v)

    // this function gets the index spec (its keys) into a form that
    // is simplified and cleaned up.
    //
    // if there are text indexes in index.spec, they are removed
    //
    // all text indexes, including any that were in index.spec, and
    // anything implied by options.weights, are stored in a new Map<string,int>
    // called weights.
    //
    // any non-text indexes that appeared in spec AFTER any text
    // indexes are discarded.  I *think* Mongo keeps these, but only
    // for the purpose of grabbing their data later when used as a covering
    // index, which we're ignoring.
    //
    let getNormalizedSpec info =
        //printfn "info: %A" info
        let keys = bson.getDocument info.spec
        let first_text = 
            Array.tryFindIndex (fun (k,typ) -> 
                match typ with
                | BString "text" -> true
                | _ -> false
            ) keys
        let weights = bson.tryGetValueForKey info.options "weights"
        match (first_text, weights) with
        | None, None ->
            let decoded = Array.map (fun (k,v) -> (k, decodeIndexType v)) keys
            //printfn "no text index: %A" decoded
            (decoded, None)
        | _ ->
            let (scalar_keys,text_keys) = 
                match first_text with
                | Some i -> 
                    let scalar_keys = Array.sub keys 0 i
                    // note that any non-text index after the first text index is getting discarded
                    let text_keys = 
                        Array.choose (fun (k,typ) ->
                            match typ with
                            | BString "text" -> Some k
                            | _ -> None
                        ) keys
                    (scalar_keys, text_keys)
                | None -> (keys, Array.empty)
            let weights =
                match weights with
                | Some (BDocument a) -> a
                | Some _ -> failwith "weights must be a document"
                | None -> Array.empty
            let weights =
                Array.fold (fun cur (k,v) ->
                    let n = 
                        match v with
                        | BInt32 n -> n
                        | BInt64 n -> int32 n
                        | BDouble n -> int32 n
                        | _ -> failwith "weight must be numeric"
                    Map.add k n cur
                ) Map.empty weights
            let weights =
                Array.fold (fun cur k ->
                    if Map.containsKey k cur then cur
                    else Map.add k 1 cur
                ) weights text_keys
            // TODO if the wildcard is present, remove everything else?
            let decoded = Array.map (fun (k,v) -> (k, decodeIndexType v)) scalar_keys
            let r = (decoded, Some weights)
            //printfn "%A" r
            r

    let replaceArrayElement vals i v =
        let a = Array.copy vals
        a.[i] <- v
        a

    let private getIndexEntries newDoc normspec weights options f =
        //printfn "getIndexEntries: options = %A" options
        let sparse =
            match bson.tryGetValueForKey options "sparse" with
            | Some (BBoolean b) -> b
            | _ -> false
        let findIndexEntryVals normspec doc =
            //printfn "spec: %A" spec
            //printfn "doc: %A" doc
            Array.choose (fun (k,typ) ->
                //printfn "k : %s" k
                let v = bson.findPath doc k
                //printfn "findPath: k = %A" k
                //printfn "findPath: v = %A" v

                // now we replace any BUndefined with BNull.  this seems, well,
                // kinda wrong, as it effectively encodes the index entries to
                // contain information that is slightly incorrect, since BNull
                // means "it was present and explicitly null", whereas BUndefined
                // means "it was absent".  Still, this appears to be the exact
                // behavior of Mongo.  Note that this only affects index entries.
                // The matcher can and must still distinguish between null and
                // undefined.

                let keep = 
                    if sparse then
                        match v with
                        | BUndefined -> false
                        | _ -> true
                    else
                        true

                if keep then
                    //printfn "keep index entry"
                    let v = bson.replaceUndefined v
                    let neg = IndexType.Backward=typ
                    Some (v,neg)
                else
                    //printfn "no index entry"
                    None
            ) normspec

        let q vals w (s:string) =
            let a = s.Split(' ') // TODO tokenize properly
            let a = a |> Set.ofArray |> Set.toArray
            Array.iter (fun s ->
                let v = BArray [| (BString s); (BInt32 w) |]
                let vals = Array.append vals [| (v,false) |]
                vals |> f
            ) a

        let maybeText vals newDoc weights f =
            match weights with
            | Some weights ->
                Map.iter (fun k w ->
                    // TODO what if k is a wildcard?
                    if k="$**" then 
                        bson.forAllStrings newDoc (fun s -> q vals w s)
                    else
                        match bson.findPath newDoc k with
                        | BUndefined -> ()
                        | v ->
                            match v with
                            | BString s -> q vals w s
                            | BArray a ->
                                let a = a |> Set.ofArray |> Set.toArray
                                Array.iter (fun v ->
                                    match v with
                                    | BString s -> q vals w s
                                    | _ -> () // no index entry unless it's a string 
                                ) a
                            | _ -> () // no index entry unless it's a string 
                ) weights
            | None ->
                //printfn "maybeText: %A" vals
                vals |> f

        let rec maybeArray newDoc vals weights f =
            // first do the index entries for the document without considering arrays
            maybeText vals newDoc weights f 

            // now, if any of the vals in the key are an array, we need
            // to generate more index entries for this document, one
            // for each item in the array.  Mongo calls this a
            // multikey index.

            Array.iteri (fun i (v,typ) ->
                match v with
                | BArray a ->
                    let a = a |> Set.ofArray |> Set.toArray
                    Array.iter (fun av ->
                        let replaced = replaceArrayElement vals i (av,typ)
                        maybeArray newDoc replaced weights f 
                    ) a
                | _ -> ()
            ) vals

        let vals = findIndexEntryVals normspec newDoc
        maybeArray newDoc vals weights f


    // TODO special type for the pair db and coll

    // TODO consider having two forms of this connect() method.  one returns a read-only conn.
    let connect() =
        // TODO allow a different filename to be specified
        let conn = ugly.``open``("elmodata.db")
        conn.exec("PRAGMA journal_mode=WAL")
        conn.exec("PRAGMA foreign_keys=ON")
        conn.exec("CREATE TABLE IF NOT EXISTS \"collections\" (dbName TEXT NOT NULL, collName TEXT NOT NULL, options BLOB NOT NULL, PRIMARY KEY (dbName,collName))")
        conn.exec("CREATE TABLE IF NOT EXISTS \"indexes\" (dbName TEXT NOT NULL, collName TEXT NOT NULL, ndxName TEXT NOT NULL, spec BLOB NOT NULL, options BLOB NOT NULL, PRIMARY KEY (dbName, collName, ndxName), FOREIGN KEY (dbName,collName) REFERENCES \"collections\" ON DELETE CASCADE ON UPDATE CASCADE, UNIQUE (spec,dbName,collName))")

        let getCollectionOptions db coll =
            use stmt = conn.prepare("SELECT options FROM \"collections\" WHERE dbName=? AND collName=?")
            stmt.bind_text(1,db)
            stmt.bind_text(2,coll)
            if raw.SQLITE_ROW=stmt.step() then
                stmt.column_blob(0) |> BinReader.ReadDocument |> Some
            else
                None

        let sqlSelectIndexes = "SELECT ndxName, spec, options, dbName, collName FROM \"indexes\""

        let getIndexFromRow (stmt:sqlite3_stmt) =
            let ndx = stmt.column_text(0)
            let spec = stmt.column_blob(1) |> BinReader.ReadDocument
            let options = stmt.column_blob(2) |> BinReader.ReadDocument
            let db = stmt.column_text(3)
            let coll = stmt.column_text(4)
            {db=db;coll=coll;ndx=ndx;spec=spec;options=options}

        let getIndexInfo db coll ndx =
            use stmt = conn.prepare(sqlSelectIndexes + " WHERE dbName=? AND collName=? AND ndxName=?")
            stmt.bind_text(1,db)
            stmt.bind_text(2,coll)
            stmt.bind_text(3,ndx)
            if raw.SQLITE_ROW=stmt.step() then
                getIndexFromRow(stmt) |> Some
            else
                None

        let getTableNameForCollection db coll = sprintf "docs.%s.%s" db coll // TODO cleanse?

        let getTableNameForIndex db coll ndx = sprintf "ndx.%s.%s.%s" db coll ndx // TODO cleanse?

        let prepareIndexInsert tbl =
            conn.prepare(sprintf "INSERT INTO \"%s\" (k,doc_rowid) VALUES (?,?)" tbl)

        let indexInsertStep (stmt_insert:sqlite3_stmt) k doc_rowid = 
            //printfn "    index key: %A" k
            stmt_insert.clear_bindings()
            stmt_insert.bind_blob(1, k)
            stmt_insert.bind_int64(2, doc_rowid)
            stmt_insert.step_done()
            if conn.changes()<>1 then failwith "index entry insert failed"
            stmt_insert.reset()

        let getStmtSequence (stmt:sqlite3_stmt) count =
            seq {
                while raw.SQLITE_ROW = stmt.step() do
                    let doc = stmt.column_blob(0) |> BinReader.ReadDocument
                    count := !count + 1
                    printfn "got_SQLITE_ROW"
                    yield {doc=doc;score=None;pos=None}
            }

        let rec createIndex info =
            let createdColl = createCollection info.db info.coll (BDocument Array.empty)
            ignore createdColl // TODO are we supposed to tell the caller we created the collection?
            //printfn "createIndex: %A" info
            
#if not
// TODO for now we decide to leave the spec as it was provided to us.
            let weights = bson.tryGetValueForKey info.options "weights"

            // if weights mention keys not in spec, add them to the spec
            let spec = 
                match weights with
                | Some (BDocument weights) ->
                    Array.fold (fun cur (k,_) ->
                        let f ov = 
                            match ov with
                            | Some _ -> ov
                            | None -> "text" |> BString |> Some
                        bson.changeValueForPath cur k f
                    ) info.spec weights
                | Some _ -> failwith "invalid weights"
                | None ->
                    info.spec
#endif

            match getIndexInfo info.db info.coll info.ndx with
            | Some already ->
                //printfn "it already exists: %A" already
                if already.spec<>info.spec then
                    // note that we do not compare the options.
                    // I think mongo does it this way too.
                    failwith "index already exists with different keys"
                false
            | None ->
                //printfn "did not exist, creating it"
                // TODO if we already have a text index (where any of its spec keys are text)
                // then fail.
                let baSpec = bson.toBinaryArray info.spec
                let baOptions = bson.toBinaryArray info.options
                use stmt = conn.prepare("INSERT INTO \"indexes\" (dbName,collName,ndxName,spec,options) VALUES (?,?,?,?,?)")
                stmt.bind_text(1,info.db)
                stmt.bind_text(2,info.coll)
                stmt.bind_text(3,info.ndx)
                stmt.bind_blob(4,baSpec)
                stmt.bind_blob(5,baOptions)
                stmt.step_done()
                let collTable = getTableNameForCollection info.db info.coll
                let ndxTable = getTableNameForIndex info.db info.coll info.ndx
                // TODO WITHOUT ROWID ?
                match bson.tryGetValueForKey info.options "unique" with
                | Some (BBoolean true) ->
                    conn.exec(sprintf "CREATE TABLE \"%s\" (k BLOB NOT NULL, doc_rowid int NOT NULL REFERENCES \"%s\"(did) ON DELETE CASCADE, PRIMARY KEY (k))" ndxTable collTable)
                | _ ->
                    conn.exec(sprintf "CREATE TABLE \"%s\" (k BLOB NOT NULL, doc_rowid int NOT NULL REFERENCES \"%s\"(did) ON DELETE CASCADE, PRIMARY KEY (k,doc_rowid))" ndxTable collTable)
                conn.exec(sprintf "CREATE INDEX \"childndx_%s\" ON \"%s\" (doc_rowid)" ndxTable ndxTable)
                // now insert index entries for every doc that already exists
                let (normspec,weights) = getNormalizedSpec info
                //printfn "normspec in createIndex: %A" normspec
                //printfn "weights in createIndex: %A" weights
                use stmt2 = conn.prepare(sprintf "SELECT did,bson FROM \"%s\"" collTable)
                use stmt_insert = prepareIndexInsert ndxTable
                while raw.SQLITE_ROW = stmt2.step() do
                    let doc_rowid = stmt2.column_int64(0)
                    let newDoc = stmt2.column_blob(1) |> BinReader.ReadDocument

                    let entries = ResizeArray<_>()
                    let f vals = entries.Add(vals)

                    getIndexEntries newDoc normspec weights info.options f

                    let entries = entries.ToArray() |> Set.ofArray |> Set.toArray
                    //printfn "entries for index: %A" entries
                    Array.iter (fun vals ->
                        //printfn "for index: %A" vals
                        let k = bson.encodeMultiForIndex vals
                        indexInsertStep stmt_insert k doc_rowid
                    ) entries
                true

        and createCollection db coll options =
            //printfn "createCollection: %s.%s" db coll
            match getCollectionOptions db coll with
            | Some _ ->
                //printfn "collection %s.%s already exists" db coll
                false
            | None ->
                //printfn "collection %s.%s did not exist, creating it" db coll
                let baOptions = bson.toBinaryArray options
                use stmt = conn.prepare("INSERT INTO \"collections\" (dbName,collName,options) VALUES (?,?,?)", db, coll, baOptions)
                stmt.step_done()
                let collTable = getTableNameForCollection db coll
                conn.exec(sprintf "CREATE TABLE \"%s\" (did INTEGER PRIMARY KEY, bson BLOB NOT NULL)" collTable)
                match bson.tryGetValueForKey options "autoIndexId" with
                | Some (BBoolean false) ->
                    ()
                | _ ->
                    let info = 
                        {
                            db = db
                            coll = coll
                            ndx = "_id_"
                            spec = BDocument [| ("_id",BInt32 1) |]
                            options = BDocument [| ("unique",BBoolean true) |]
                        }
                    let created = createIndex info
                    ignore created
                true

        let listCollections() =
            use stmt = conn.prepare("SELECT dbName, collName, options FROM \"collections\" ORDER BY collName ASC")
            let results = ResizeArray<_>()
            while raw.SQLITE_ROW = stmt.step() do
                let dbName = stmt.column_text(0)
                let collName = stmt.column_text(1)
                let options = stmt.column_blob(2) |> BinReader.ReadDocument
                results.Add(dbName,collName,options)
            results.ToArray()

        let listIndexes() =
            use stmt = conn.prepare(sqlSelectIndexes)
            let results = ResizeArray<_>()
            while raw.SQLITE_ROW = stmt.step() do
                results.Add(getIndexFromRow stmt)
            results.ToArray()

        let dropIndex db coll ndxName =
            //printfn "dropping index: %s.%s.%s" db coll ndxName
            match getIndexInfo db coll ndxName with
            | Some _ ->
                //printfn "and yes, it did exist"
                use stmt_ndx = conn.prepare("DELETE FROM \"indexes\" WHERE dbName=? AND collName=? AND ndxName=?")
                stmt_ndx.bind_text(1,db)
                stmt_ndx.bind_text(2,coll)
                stmt_ndx.bind_text(3,ndxName)
                stmt_ndx.step_done()
                let deleted = conn.changes()>0
                // TODO assert deleted is true?
                let ndxTable = getTableNameForIndex db coll ndxName
                conn.exec(sprintf "DROP TABLE \"%s\"" ndxTable)
                deleted
            | None ->
                //printfn "it did not exist"
                false

        let dropCollection db coll =
            //printfn "dropping collection: %s.%s" db coll
            match getCollectionOptions db coll with
            | Some _ ->
                //printfn "it exists, dropping it"
                let indexes = listIndexes() |> Array.filter (fun ndxInfo -> db=ndxInfo.db && coll=ndxInfo.coll)
                Array.iter (fun info ->
                    let deleted = dropIndex info.db info.coll info.ndx
                    ignore deleted
                ) indexes
                let collTable = getTableNameForCollection db coll
                conn.exec(sprintf "DROP TABLE \"%s\"" collTable)
                use stmt=conn.prepare("DELETE FROM \"collections\" WHERE dbName=? AND collName=?")
                stmt.bind_text(1,db)
                stmt.bind_text(2,coll)
                stmt.step_done()
                let deleted = conn.changes()>0
                // TODO assert deleted is true?
                deleted
            | None ->
                //printfn "but it did not exist"
                false

        let renameCollection oldName newName dropTarget =
            let (oldDb,oldColl) = bson.splitname oldName
            let (newDb,newColl) = bson.splitname newName

            // jstests/core/rename8.js seems to think that renaming to/from a system collection is illegal unless
            // that collection is system.users, which is "whitelisted".  for now, we emulate this behavior, even
            // though system.users isn't supported.
            if oldColl<>"system.users" && oldColl.StartsWith("system.") then failwith "renameCollection with a system collection not allowed."
            if newColl<>"system.users" && newColl.StartsWith("system.") then failwith "renameCollection with a system collection not allowed."

            if dropTarget then 
                let deleted = dropCollection newDb newColl
                ignore deleted

            match getCollectionOptions oldDb oldColl with
            | Some _ -> 
                let indexes = listIndexes() |> Array.filter (fun ndxInfo -> oldDb=ndxInfo.db && oldColl=ndxInfo.coll)
                let oldTable = getTableNameForCollection oldDb oldColl
                let newTable = getTableNameForCollection newDb newColl
                let f which =
                    use stmt = conn.prepare(sprintf "UPDATE \"%s\" SET dbName=?, collName=? WHERE dbName=? AND collName=?" which)
                    stmt.bind_text(1, newDb)
                    stmt.bind_text(2, newColl)
                    stmt.bind_text(3, oldDb)
                    stmt.bind_text(4, oldColl)
                    stmt.step_done()
                // f "indexes" // ON UPDATE CASCADE does this
                f "collections"
                conn.exec(sprintf "ALTER TABLE \"%s\" RENAME TO \"%s\"" oldTable newTable)
                Array.iter (fun ndxInfo ->
                    let oldName = getTableNameForIndex oldDb oldColl ndxInfo.ndx
                    let newName = getTableNameForIndex newDb newColl ndxInfo.ndx
                    conn.exec(sprintf "ALTER TABLE \"%s\" RENAME TO \"%s\"" oldName newName)
                ) indexes
                false
            | None -> 
                createCollection newDb newColl (BDocument Array.empty)

        //let fn_close() = conn.close()

        let fn_close() = 
            try
                conn.close()
            with
            | _ ->
                let mutable cur = conn.next_stmt(null)
                while cur<>null do
                    printfn "%s" (cur.sql())
                    cur <- conn.next_stmt(cur)
                reraise()

        let getDirs normspec vals =
            //printfn "normspec: %A" normspec
            //printfn "vals: %A" vals
            let len = Array.length vals
            let pairs = Array.sub normspec 0 len
            let dirs = Array.map (fun (_,v) -> IndexType.Backward=v) pairs
            Array.zip vals dirs

        let add_one ba =
            let rec f (a:byte[]) ndx =
                let b = a.[ndx]
                if b < 255uy then
                    a.[ndx] <- b + 1uy
                else
                    a.[ndx] <- 0uy
                    if ndx>0 then f a (ndx-1)
            let ba = Array.copy ba
            f ba (ba.Length - 1)
            ba

        let getStmtForIndex ndx b =
            //printfn "ndx: %A" ndx
            //printfn "bounds: %A" b

            let tblColl = getTableNameForCollection ndx.db ndx.coll
            let tblIndex = getTableNameForIndex ndx.db ndx.coll ndx.ndx
            let (normspec,weights) = getNormalizedSpec ndx

            // note that one of the reasons we need to do DISTINCT here is because a
            // single index in a single document can produce multiple index entries,
            // because, for example, when a value is an array, we don't just index
            // the array as a value, but we also index each of its elements.
            //
            // TODO it would be nice if the DISTINCT here was happening on the rowids, not on the blobs

            let f_two kmin kmax op1 op2 =
                printfn "INDEX_SCAN_BOTH: %s %s" op1 op2
                let sql = sprintf "SELECT DISTINCT d.bson FROM \"%s\" d INNER JOIN \"%s\" i ON (d.did = i.doc_rowid) WHERE k %s ? AND k %s ?" tblColl tblIndex op1 op2
                let stmt = conn.prepare(sql)
                stmt.bind_blob(1, kmin)
                stmt.bind_blob(2, kmax)
                stmt
 
            let f_one op k = 
                printfn "INDEX_SCAN_ONE: %s" op
                let sql = sprintf "SELECT DISTINCT d.bson FROM \"%s\" d INNER JOIN \"%s\" i ON (d.did = i.doc_rowid) WHERE k %s ?" tblColl tblIndex op
                let stmt = conn.prepare(sql)
                stmt.bind_blob(1, k)
                stmt

            let f_gt_lt (kmin,kmax) = f_two kmin kmax ">" "<"
            let f_gt_lte (kmin,kmax) = f_two kmin kmax ">" "<="
            let f_gte_lt (kmin,kmax) = f_two kmin kmax ">=" "<"
            let f_gte_lte (kmin,kmax) = f_two kmin kmax ">=" "<="

            match b with
            | plan.bounds.Text (eq,search) -> failwith "this case is handled separately"
            | plan.bounds.GT vals ->
                vals |> getDirs normspec |> bson.encodeMultiForIndex |> f_one ">"
            | plan.bounds.GTE vals ->
                vals |> getDirs normspec |> bson.encodeMultiForIndex |> f_one ">="
            | plan.bounds.LT vals ->
                vals |> getDirs normspec |> bson.encodeMultiForIndex |> f_one "<"
            | plan.bounds.LTE vals ->
                vals |> getDirs normspec |> bson.encodeMultiForIndex |> f_one "<="
            | plan.bounds.EQ vals ->
                let kmin = vals |> getDirs normspec |> bson.encodeMultiForIndex
                let kmax = add_one kmin
                (kmin,kmax) |> f_gte_lt
            | plan.bounds.GT_LT (minvals,maxvals) ->
                let kmin = minvals |> getDirs normspec |> bson.encodeMultiForIndex
                let kmax = maxvals |> getDirs normspec |> bson.encodeMultiForIndex
                (kmin,kmax) |> f_gt_lt
            | plan.bounds.GT_LTE (minvals,maxvals) ->
                let kmin = minvals |> getDirs normspec |> bson.encodeMultiForIndex
                let kmax = maxvals |> getDirs normspec |> bson.encodeMultiForIndex
                (kmin,kmax) |> f_gt_lte
            | plan.bounds.GTE_LT (minvals,maxvals) ->
                let kmin = minvals |> getDirs normspec |> bson.encodeMultiForIndex
                let kmax = maxvals |> getDirs normspec |> bson.encodeMultiForIndex
                (kmin,kmax) |> f_gte_lt
            | plan.bounds.GTE_LTE (minvals,maxvals) ->
                let kmin = minvals |> getDirs normspec |> bson.encodeMultiForIndex
                let kmax = maxvals |> getDirs normspec |> bson.encodeMultiForIndex
                (kmin,kmax) |> f_gte_lte

        let getTableScanReader tx db coll =
            printfn "TABLE_SCAN"
            let stmt =
                let collTable = getTableNameForCollection db coll
                conn.prepare(sprintf "SELECT bson FROM \"%s\"" collTable)

            let count = ref 0
            let s = getStmtSequence stmt count

            let killFunc() =
                if tx then conn.exec("COMMIT TRANSACTION")
                stmt.sqlite3_finalize()

            {
                docs=s
                totalKeysExamined=fun () -> 0
                totalDocsExamined=fun () -> !count
                funk=killFunc
            }

        let getTextIndexReader tx ndx eq terms =
            let tblColl = getTableNameForCollection ndx.db ndx.coll
            let tblIndex = getTableNameForIndex ndx.db ndx.coll ndx.ndx
            let (normspec,weights) = getNormalizedSpec ndx
            let weights = 
                match weights with
                | Some a -> a
                | None -> failwith "must be a text index"

            let sql = sprintf "SELECT k, doc_rowid FROM \"%s\" i WHERE k > ? AND k < ?" tblIndex
            let stmt = conn.prepare(sql)

            let get_weight_from_index_entry k =
                let len = Array.length k
                let n = k |> Array.rev |> Array.findIndex (fun b -> b=0uy)
                let n = len - n
                let ord = 0 |> BInt32 |> bson.getTypeOrder |> byte
                if k.[n] <> ord then failwith "bad type order byte"
                let e = (k.[n+1] |> int) - 23
                // exponent is number of times the mantissa must be multiplied times 100
                // if we assume that all mantissa digits are to the right of the decimal point.
                if e<=0 then failwith "bad e"
                let n = n + 2
                let a = Array.sub k n (len - n)
                // remaining bytes are mantissa, base 100
                // last byte of mantissa is 2*x
                // previous bytes are 2*x+1

                //printfn "mantissa: %A" a
                //printfn "e: %d" e

                // we have an array of centimal digits here, all of
                // which appear to the right of the decimal point.
                //
                // we know from the context that this
                // SHOULD be an integer.

                let len = Array.length a

                // chop off digits that won't matter
                let a =
                    if len > e then
                        Array.sub a 0 e
                    else
                        a

                let len = Array.length a
                // assert len <= e

                let v =
                    Array.fold (fun v d ->
                        let b = d >>> 1 |> int
                        v * 100 + b
                    ) 0 a

                let need = e - len
                let v = 
                    if need <= 0 then v
                    else
                        Seq.fold (fun v _ ->
                            v * 100
                        ) v { 1 .. need }

                //printfn "weight: %d" v
                v

            let lookup word =
                // TODO if we just search for the word without the weight, we could
                // use the add_one trick from EQ.  Probably need key encoding of an array
                // to omit the array length.  See comment there.
                let vmin = BArray [| (BString word); (BInt32 0) |]
                let vmax = BArray [| (BString word); (BInt32 100000) |]
                let vals = getDirs normspec eq
                let kmin = [| (vmin,false) |] |> Array.append vals |> bson.encodeMultiForIndex
                let kmax = [| (vmax,false)|] |> Array.append vals |> bson.encodeMultiForIndex
                let entries = ResizeArray<_>()
                stmt.clear_bindings()
                stmt.bind_blob(1, kmin)
                stmt.bind_blob(2, kmax)
                while raw.SQLITE_ROW = stmt.step() do
                    let k = stmt.column_blob(0)
                    let w = get_weight_from_index_entry k
                    let did = stmt.column_int64(1)
                    entries.Add(did,w)
                stmt.reset()
                entries.ToArray()

            // TODO try/catch to make sure stmt gets finalized

            let found = 
                Array.map (fun term ->
                    match term with
                    | plan.Word (neg,s) ->
                        let entries = lookup s
                        (term,entries)
                    | plan.Phrase (neg,s) ->
                        let words = s.Split(' ') // TODO how to do this properly?  deal with punctuation.
                        let entries = 
                            Array.collect (fun word ->
                                lookup word
                            ) words
                        (term,entries)
                ) terms

            stmt.sqlite3_finalize()

            //printfn "found: %A" found

            let contains_phrase doc (p:string) =
                Map.exists (fun k _ ->
                    match bson.findPath doc k with
                    | BUndefined -> false
                    | v ->
                        match v with
                        | BString s -> s.IndexOf(p) >= 0
                        | _ -> false
                ) weights

            let check_phrase doc =
                Array.forall (fun term ->
                    match term with
                    | plan.Word _ -> true
                    | plan.Phrase (neg,s) ->
                        let has = contains_phrase doc s
                        if neg then not has
                        else has
                ) terms

            let pos_entries = 
                Array.collect (fun (term,entries) ->
                    let neg = 
                        match term with
                        | plan.Word (neg,_) -> neg
                        | plan.Phrase (neg,_) -> neg

                    if neg then
                        Array.empty
                    else
                        entries
                ) found

            let neg_entries = 
                Array.collect (fun (term,entries) ->
                    let neg = 
                        match term with
                        | plan.Word (neg,_) -> neg
                        | plan.Phrase (neg,_) -> false // neg 
                        // TODO probably should not negate a doc just because it contains one of the words in a negated phrase

                    if neg then
                        entries
                    else
                        Array.empty
                ) found

            let remaining =
                let neg_docids = neg_entries |> Array.map (fun (did,w) -> did) |> Set.ofArray
                Array.filter (fun (did,w) ->
                    Set.contains did neg_docids |> not
                ) pos_entries

            let doc_weights =
                Array.fold (fun cur (did,w) ->
                    match Map.tryFind did cur with
                    | Some a ->
                        let a = w :: a
                        Map.add did a cur
                    | None ->
                        Map.add did [w] cur
                ) Map.empty remaining

            let sql = sprintf "SELECT bson FROM \"%s\" WHERE did=?" tblColl
            let stmt = conn.prepare(sql)
            let count = ref 0
            let s = 
                seq {
                    for (did,w) in Map.toSeq doc_weights do
                        stmt.clear_bindings()
                        stmt.bind_int64(1, did)
                        stmt.step_row()
                        let doc = stmt.column_blob(0) |> BinReader.ReadDocument
                        count := !count + 1
                        printfn "got_SQLITE_ROW"
                        stmt.reset()
                        let keep = check_phrase doc
                        if keep then
                            //printfn "weights for this doc: %A" w
                            let score = List.sum w |> float // TODO this is not the way mongo does this calculation
                            yield {doc=doc;score=Some score;pos=None}
                }
            let killFunc() =
                if tx then conn.exec("COMMIT TRANSACTION")
                stmt.sqlite3_finalize()

            {
                docs=s
                totalKeysExamined=fun () -> 0
                totalDocsExamined=fun () -> !count
                funk=killFunc
            }

        let getNonTextIndexReader tx ndx b =
            let stmt = getStmtForIndex ndx b
            let count = ref 0
            let s = getStmtSequence stmt count
            let killFunc() =
                if tx then conn.exec("COMMIT TRANSACTION")
                stmt.sqlite3_finalize()

            {
                docs=s
                totalKeysExamined=fun () -> 0
                totalDocsExamined=fun () -> !count
                funk=killFunc
            }

        let getIndexScanReader tx p =
            let (ndx,b) = 
                match p with
                | plan.q.Plan (ndx,b) -> (ndx,b)

            match b with
            | plan.bounds.Text (eq,search) -> getTextIndexReader tx ndx eq search
            | _ -> getNonTextIndexReader tx ndx b

        let getSeq tx db coll plan =
            match getCollectionOptions db coll with
            | Some _ ->
                if tx then conn.exec("BEGIN TRANSACTION")

                match plan with
                | Some ndxu -> getIndexScanReader tx ndxu
                | None -> getTableScanReader tx db coll
            | None ->
                {
                    docs=Seq.empty
                    totalKeysExamined=fun () -> 0
                    totalDocsExamined=fun () -> 0
                    funk=(fun () -> ())
                }

        let beginWrite db coll = 
            let created = createCollection db coll (BDocument Array.empty)
            ignore created
            let tblCollection = getTableNameForCollection db coll
            let stmt_insert = conn.prepare(sprintf "INSERT INTO \"%s\" (bson) VALUES (?)" tblCollection)
            let stmt_delete = conn.prepare(sprintf "DELETE FROM \"%s\" WHERE rowid=?" tblCollection)
            let stmt_update = conn.prepare(sprintf "UPDATE \"%s\" SET bson=? WHERE rowid=?" tblCollection)
            let indexes = listIndexes() |> Array.filter (fun ndxInfo -> db=ndxInfo.db && coll=ndxInfo.coll)
            let opt_stmt_find_rowid = 
                match Array.tryFind (fun info -> info.ndx="_id_") indexes with
                | Some info ->
                    let tblIndex = getTableNameForIndex db coll "_id_"
                    let stmt_find_rowid = conn.prepare(sprintf "SELECT doc_rowid FROM \"%s\" WHERE k=?" tblIndex)
                    Some stmt_find_rowid
                | None ->
                    None

            let index_stmts = 
                Array.map (fun info->
                    let tbl = getTableNameForIndex db coll info.ndx
                    let stmt_insert = prepareIndexInsert tbl
                    let stmt_delete = conn.prepare(sprintf "DELETE FROM \"%s\" WHERE doc_rowid=?" tbl)
                    (info,stmt_insert,stmt_delete)
                ) indexes

            let find_rowid id =
                match opt_stmt_find_rowid with
                | Some stmt_find_rowid ->
                    let idk = bson.encodeOneForIndex id false
                    stmt_find_rowid.clear_bindings()
                    stmt_find_rowid.bind_blob(1, idk)
                    let rowid = 
                        if raw.SQLITE_ROW=stmt_find_rowid.step() then
                            stmt_find_rowid.column_int64(0) |> Some
                        else
                            None
                    stmt_find_rowid.reset()
                    rowid
                | None ->
                    None

            let update_indexes doc_rowid newDoc =
                Array.iter (fun (info,stmt_insert:sqlite3_stmt,stmt_delete:sqlite3_stmt) ->
                    // so, when we update a very large document that has lots of index
                    // entries, we delete all of them, and then add all new ones.  if
                    // most of the index entries are actually the same, this is sad.

                    stmt_delete.clear_bindings()
                    stmt_delete.bind_int64(1, doc_rowid)
                    stmt_delete.step_done()
                    stmt_delete.reset()

                    let (normspec,weights) = getNormalizedSpec info

                    let entries = ResizeArray<_>()

                    let f vals = entries.Add(vals)

                    getIndexEntries newDoc normspec weights info.options f

                    let entries = entries.ToArray() |> Set.ofArray |> Set.toArray
                    Array.iter (fun vals ->
                        //printfn "for index: %A" vals
                        let k = bson.encodeMultiForIndex vals
                        //printfn "encoded: %A" k
                        indexInsertStep stmt_insert k doc_rowid
                    ) entries

                ) index_stmts

            let to_bson newDoc =
                // TODO validateKeys here?
                let ba = bson.toBinaryArray newDoc
                if ba.Length > 16*1024*1024 then raise (MongoCode(10329, "document more than 16MB"))
                ba

            let fn_getIndexes() = indexes

            let fn_insert newDoc =
                let ba = to_bson newDoc
                stmt_insert.clear_bindings()
                stmt_insert.bind_blob(1, ba)
                stmt_insert.step_done()
                let doc_rowid = conn.last_insert_rowid()
                stmt_insert.reset()
                if conn.changes()<>1 then failwith "insert failed"
                update_indexes doc_rowid newDoc

            let fn_delete id =
                match find_rowid id with
                | Some rowid ->
                    stmt_delete.clear_bindings()
                    stmt_delete.bind_int64(1,rowid)
                    stmt_delete.step_done()
                    stmt_delete.reset()
                    // TODO remove from indexes?
                    true
                | None ->
                    false

            let fn_update newDoc =
                match bson.tryGetValueForKey newDoc "_id" with
                | Some id ->
                    match find_rowid id with
                    | Some rowid ->
                        let ba = to_bson newDoc
                        stmt_update.clear_bindings()
                        stmt_update.bind_blob(1, ba)
                        stmt_update.bind_int64(2, rowid)
                        stmt_update.step_done()
                        stmt_update.reset()
                        if conn.changes()<>1 then failwith "insert failed"
                        update_indexes rowid newDoc
                    | None ->
                        failwith "update, but does not exist"
                | None ->
                    failwith "cannot update without id"

            let finalize_stmts() =
                match opt_stmt_find_rowid with
                | Some stmt_find_rowid -> stmt_find_rowid.sqlite3_finalize()
                | None -> ()
                stmt_insert.sqlite3_finalize()
                stmt_delete.sqlite3_finalize()
                stmt_update.sqlite3_finalize()
                Array.iter (fun (_,stmt_insert:sqlite3_stmt,stmt_delete:sqlite3_stmt) -> 
                    stmt_insert.sqlite3_finalize()
                    stmt_delete.sqlite3_finalize()
                    ) index_stmts

            let fn_rollback() =
                //printfn "rollback"
                conn.exec("ROLLBACK TRANSACTION")
                finalize_stmts()
                
            let fn_commit() =
                //printfn "commit"
                conn.exec("COMMIT TRANSACTION")
                finalize_stmts()
                
            let fn_getSelect plan =
                getSeq false db coll plan

            conn.exec("BEGIN TRANSACTION") // TODO immediate?

            {
                database = db
                collection = db
                insert = fn_insert
                update = fn_update
                delete = fn_delete
                getSelect = fn_getSelect
                getIndexes = fn_getIndexes
                commit = fn_commit
                rollback = fn_rollback
            }

        let fn_beginWrite db coll =
            try
                beginWrite db coll
            with
            | e ->
                printfn "%A" e
                reraise()

        let fn_beginRead db coll plan =
            getSeq true db coll plan

        let fn_listCollections() =
            conn.exec("BEGIN TRANSACTION")
            try
                let a = listCollections()
                conn.exec("COMMIT TRANSACTION")
                a
            with
            | _ ->
                conn.exec("ROLLBACK TRANSACTION")
                reraise()

        let fn_listIndexes() =
            conn.exec("BEGIN TRANSACTION")
            try
                let a = listIndexes()
                conn.exec("COMMIT TRANSACTION")
                a
            with
            | _ ->
                conn.exec("ROLLBACK TRANSACTION")
                reraise()

        let fn_dropIndex db coll ndx =
            conn.exec("BEGIN TRANSACTION")
            try
                let a = dropIndex db coll ndx
                conn.exec("COMMIT TRANSACTION")
                a
            with
            | _ ->
                conn.exec("ROLLBACK TRANSACTION")
                reraise()

        let fn_createCollection db coll =
            conn.exec("BEGIN TRANSACTION")
            try
                let a = createCollection db coll 
                conn.exec("COMMIT TRANSACTION")
                a
            with
            | _ ->
                conn.exec("ROLLBACK TRANSACTION")
                reraise()

        let fn_dropCollection db coll =
            conn.exec("BEGIN TRANSACTION")
            try
                let a = dropCollection db coll 
                conn.exec("COMMIT TRANSACTION")
                a
            with
            | _ ->
                conn.exec("ROLLBACK TRANSACTION")
                reraise()

        let fn_renameCollection oldFullName newFullName dropTarget =
            conn.exec("BEGIN TRANSACTION")
            try
                let a = renameCollection oldFullName newFullName dropTarget
                conn.exec("COMMIT TRANSACTION")
                a
            with
            | _ ->
                conn.exec("ROLLBACK TRANSACTION")
                reraise()

        let fn_clearCollection db coll = 
            conn.exec("BEGIN TRANSACTION")
            try
                let created = 
                    match getCollectionOptions db coll with
                    | Some _ ->
                        let collTable = getTableNameForCollection db coll
                        conn.exec(sprintf "DELETE FROM \"%s\"" collTable)
                        false
                    | None ->
                        createCollection db coll (BDocument Array.empty)
                conn.exec("COMMIT TRANSACTION")
                created
            with
            | _ ->
                conn.exec("ROLLBACK TRANSACTION")
                reraise()

        let fn_dropDatabase db =
            conn.exec("BEGIN TRANSACTION")
            try
                let a = listCollections() |> Array.filter (fun (name,_,_) -> db=name)
                let deleted = Array.isEmpty a |> not
                Array.iter (fun (db,coll,_) ->
                    let deleted = dropCollection db coll
                    ignore deleted
                ) a
                conn.exec("COMMIT TRANSACTION")
                deleted
            with
            | _ ->
                conn.exec("ROLLBACK TRANSACTION")
                reraise()

        let fn_createIndexes a =
            conn.exec("BEGIN TRANSACTION")
            try
                let r =
                    Array.map (fun info ->
                        createIndex info
                    ) a
                conn.exec("COMMIT TRANSACTION")
                r
            with
            | _ ->
                conn.exec("ROLLBACK TRANSACTION")
                reraise()

        // ----------------------------------------------------------------

        {
            close = fn_close
            beginWrite = fn_beginWrite
            listCollections = fn_listCollections
            listIndexes = fn_listIndexes
            beginRead = fn_beginRead
            clearCollection = fn_clearCollection
            dropDatabase = fn_dropDatabase
            createIndexes = fn_createIndexes
            dropIndex = fn_dropIndex
            createCollection = fn_createCollection
            dropCollection = fn_dropCollection
            renameCollection = fn_renameCollection
        }

