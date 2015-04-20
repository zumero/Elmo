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

// chooseIndex should be smart enough to combine expressions to
// use a compound index?
//
// chooseIndex: dive into AND?
//
// chooseIndex: deal with multiple items in a Compare?
//
// use chooseIndex in getOneMatch
//
// use chooseIndex in getFirstMatch
//
// use chooseIndex in agg pipeline
//
// use chooseIndex in update/getSelect
//
// use chooseIndex in delete/getSelect
//
// use chooseIndex in distinct
//
// hint
//
// explain
//
// bson binary subtypes
//
// consider having the LiteServer layer keep the kv.conn open all the time.
//
// funk never gets called when the client abandons a cursor.  time it out.
//
// figure out why none of the parallel shell things work
//
// separate actual networking part of the server from the layer that
// just takes a message and returns a reply message
//
// sort bindata, length, then subtype, then byte by byte
//
// implement actual objectid, first four timestamp
//
// consider implement capped collection.  size may not make sense, but
// max probably does.
//
// tests for accums min, max, push, addToSet
//
// string sort uses strcmpi ?
//
// insert empty timestamp, mongo fills it in, top level only
//
// regex tests
//
// geo
//
// $text ? fts ?
//
// $natural query modifier
//
// consider hacking the tests so I don't have to throw out a long test just
// because mongolite can't pass one little part of it
//
// convert BinReader/BinWriter to closures?
//
// bson writer BsonValue.BJSCodeWithScope
//
// lots of failwiths should be mongocode
//
// maybe use findPath more in Matcher now that it dives into arrays
//
// should find and aggregate share their implementation of projection?
// 
// no test case for $orderby int?  see sortFunc.
//
// should count (and maybe distinct) map onto the agg pipeline?

open System
open System.IO
open System.Diagnostics

let path_mongo_shell = "/Users/eric/Downloads/mongodb-osx-x86_64-3.0.1/bin/mongo"
let path_mongo_src = "/Users/eric/m/mongo"
let tests = [
    "jstests/aggregation/bugs/server11675.js"; // $text fts?
    "jstests/aggregation/bugs/server5209.js"; // group by 24 vs 24L vs 24.0
    "jstests/aggregation/bugs/server6125.js"; // sort.  test case seems wrong.  array containing 1 should sort before 2L.
    "jstests/aggregation/bugs/server6165.js"; // long_dublong case.  mongo results seems wrong.
    "jstests/aggregation/bugs/server6177.js"; // $project:{ 'x':{ $add:[ 1 ] }, 'x.b':1 } } should fail even when doc is {}, broke on fix of 6185
    "jstests/aggregation/bugs/server6192_server6193.js"; // explain
    "jstests/aggregation/bugs/server6238.js"; // error codes on invalid $ in paths, project and group
    "jstests/aggregation/bugs/server6361.js"; // exclusions not allowed
    "jstests/aggregation/bugs/server6529.js"; // {$project:{foo:{$add:[{b:1}]}}} is supposed to complain about field inclusion?!?  16420.
    "jstests/aggregation/bugs/server6530.js"; // no $near in match, but syntax looks wrong anyway?
    "jstests/aggregation/bugs/server6531.js"; // support $within
    "jstests/aggregation/bugs/server7781.js"; // $geoNear
    "jstests/aggregation/bugs/server9840.js"; // $const.  also, japanese variable name seen as invalid.
    "jstests/aggregation/bugs/strcasecmp.js"; // "fails" because unicode support is more complete
    "jstests/aggregation/bugs/substr.js"; // "fails" because unicode support is more complete
    "jstests/aggregation/bugs/upperlower.js"; // "fails" because unicode support is more complete
    "jstests/core/drop.js"; // seems to require listIndexes on a non-existent collection to return empty instead of error
    "jstests/core/updatej.js"; // update validation failure terminates the update without modifying subsequent
    // "jstests/core/elemMatchProjection.js"; // jira server-1013, partial
    // "jstests/core/remove_undefined.js"; // test is broken.  doesn't drop its coll first.
    // "jstests/aggregation/bugs/server5932.js"; // unwind, exceeds message size
    "jstests/core/minmax.js"; // min/max query modifier, 2 Compares
    // "jstests/core/server9547.js"; // comment in test says that mongo SHOULD be giving the result we are giving
    // "jstests/aggregation/bugs/server9444.js"; // huge
    // "jstests/aggregation/bugs/server14969.js"; // outofmemory ?
    // "jstests/aggregation/bugs/server10530.js"; // huge
    // "jstests/aggregation/bugs/server6118.js"; // shard
    // "jstests/aggregation/bugs/server6179.js"; // shard

    "jstests/aggregation/bugs/server6189.js"; // date operators with dates before 1970.  date formatting ?
    "jstests/aggregation/bugs/server11118.js"; // date formatting
    "jstests/aggregation/bugs/match.js"; // invalid matcher syntax mod:[0,0]
    "jstests/aggregation/bugs/server8581.js"; // $redact, matcher problem with $lte undefined vs number
    "jstests/aggregation/bugs/server6335.js"; // no $where in match
    "jstests/core/sort2.js"; // NaN/Infinity issue ?
    "jstests/aggregation/bugs/server3253.js"; // $out
    "jstests/core/list_collections1.js"; // filter, query expression
    "jstests/core/list_indexes1.js"; // listIndexes command not implemented
    "jstests/core/in5.js"; // dropIndex
    "jstests/aggregation/bugs/server7768.js"; // $readPreference
    "jstests/aggregation/bugs/server5782.js"; // mongo reply has 'result' instead of 'cursor'
    "jstests/aggregation/bugs/server6121.js"; // accept timestamp everywhere a date is allowed
    "jstests/aggregation/bugs/server6143.js"; // timestamp ?
    "jstests/aggregation/bugs/server6190.js"; // $week
    "jstests/aggregation/bugs/server6239.js"; // $subtract actually is supposed to support dates
    "jstests/aggregation/bugs/server9289.js"; // $add doesn't actually support dates yet
    "jstests/aggregation/bugs/server6290.js"; // invalid operator, 15999
    "jstests/aggregation/bugs/server6045.js"; // empty pipeline stage
    "jstests/aggregation/bugs/server6861.js"; // agg parsing errors
    "jstests/aggregation/bugs/server6556.js"; // nul char in field path string
    "jstests/aggregation/bugs/server6195.js"; // concat error cases
    "jstests/aggregation/bugs/server6198.js"; // disallow dots in group output field names, 16414
    "jstests/aggregation/bugs/server6275.js"; // $avg
    "jstests/aggregation/bugs/server6468.js"; // nested/dotted projections should be same
    "jstests/aggregation/bugs/server6184.js"; // project b:{a:1} should be an inclusion of b.a, not {a:1} as a doc literal for b
    "jstests/aggregation/bugs/server6181.js"; // expression _id
    "jstests/aggregation/bugs/server6127.js"; // projection issue
    "jstests/aggregation/bugs/server6185.js"; // projecting nonexistent subfield
    "jstests/aggregation/bugs/server6269.js"; // unwind
    "jstests/aggregation/bugs/server6131.js"; // unwind
    "jstests/aggregation/bugs/cond.js";
    "jstests/aggregation/bugs/firstlast.js";
    "jstests/aggregation/bugs/ifnull.js";
    "jstests/aggregation/bugs/server6240.js"; // only one date allowed, 16612
    "jstests/aggregation/bugs/server4899.js"; // $size not array ?
    "jstests/aggregation/bugs/server6570.js"; // should be convertible to double ?
    "jstests/aggregation/bugs/server15810.js";
    "jstests/aggregation/bugs/server13715.js";
    "jstests/aggregation/bugs/server6120.js";
    "jstests/aggregation/bugs/server5012.js";
    "jstests/aggregation/bugs/server5973.js";
    "jstests/aggregation/bugs/server4738.js";
    "jstests/aggregation/bugs/server3832.js";
    "jstests/aggregation/bugs/server4638.js";
    "jstests/aggregation/bugs/server4656.js";
    "jstests/aggregation/bugs/server6147.js";
    "jstests/aggregation/bugs/server6194.js";
    "jstests/aggregation/bugs/server6779.js";
    "jstests/aggregation/bugs/server7900.js";
    "jstests/aggregation/bugs/server9841.js";
    "jstests/aggregation/bugs/server6186.js";
    "jstests/aggregation/bugs/server6232.js";

    "jstests/core/sortd.js"; // batchSize
    "jstests/core/drop3.js"; // batchSize, cursor
    "jstests/core/nan.js"; // cursor
    "jstests/core/or5.js"; // cursor,batchSize
    "jstests/core/or6.js"; // cursor
    "jstests/core/oro.js"; // batchSize, cursor, explain
    // "jstests/core/find9.js"; // huge
    // "jstests/core/or4.js"; // $group
    "jstests/core/cursor1.js";
    "jstests/core/cursor2.js";
    "jstests/core/cursor3.js";
    "jstests/core/cursor4.js";
    "jstests/core/cursor5.js";
    "jstests/core/cursor6.js";
    "jstests/core/cursor7.js";


    "jstests/core/sort8.js"; // Sorting is based on array members, not the array itself
    "jstests/core/update_find_and_modify_id.js"; // an update should fail but doesn't
    "jstests/core/fm3.js"; // mine has a z but not mongo's
    "jstests/core/find_and_modify_server6582.js"; // updatedExisting in result doc
    "jstests/core/find_size.js"; // arg to size, str is 0, double returns nothing
    "jstests/core/find_and_modify_empty_update.js";
    "jstests/core/find_and_modify_server6226.js";
    "jstests/core/find_and_modify_server6254.js";
    "jstests/core/find_and_modify_server6588.js";
    "jstests/core/find_and_modify_server6659.js";
    "jstests/core/find_and_modify_server6909.js";
    "jstests/core/find_and_modify_server6993.js";
    "jstests/core/find_and_modify_server7660.js";
    "jstests/core/server14747.js";
    "jstests/core/server14753.js";
    "jstests/core/server5346.js";
    "jstests/core/server7756.js";
    "jstests/core/server9385.js";
     "jstests/core/server1470.js"; // dbref
    "jstests/core/update_server-12848.js";
    "jstests/core/fm1.js";
    "jstests/core/fm2.js";
    "jstests/core/fm4.js";
    "jstests/core/find_dedup.js";
    "jstests/core/distinct4.js"; // planFailedWithCode ?

    // "jstests/core/or_inexact.js"; // predicates with inexact bounds
    // "jstests/core/mod1.js"; // explain, stats, js
    // "jstests/core/find_and_modify_where.js"; // js
    // "jstests/core/find_and_modify_concurrent_update.js"; // parallel
    // "jstests/core/write_result.js"; // write concern
    // "jstests/core/distinct1.js"; // stats, planSummary
    // "jstests/core/insert_illegal_doc.js"; // parallel indexing of arrays test
    // "jstests/core/remove2.js"; // $atomic
    // "jstests/core/rename6.js"; // rename a coll when one of its indexes will gen a namespace > 120 chars
    // "jstests/core/sortc.js"; // $natural
    // "jstests/core/objid5.js"; // $cmd 'features'
    // "jstests/core/removea.js"; // $atomic
    // "jstests/core/depth_limit.js"; // $where
    
    // "jstests/core/sorta.js"; // fragile test? assumes a certain sort ordering of three equal fields?
    // "jstests/core/rename.js"; // fragile test, stats, capped collection ?
    // "jstests/core/rename7.js"; // capped collection, collStats

    "jstests/core/upsert_shell.js"; // autoIndexId:false, collection without _id
    "jstests/core/rename8.js"; // rename to system collections
    "jstests/core/and2.js" // when moving _id to front, make sure we shift, not swap
    "jstests/core/push_sort.js"; // $slice
    "jstests/core/rename4.js"; // rename a.b to a
    "jstests/core/slice1.js";
    "jstests/core/string_with_nul_bytes.js";
    "jstests/core/update_blank1.js";
    "jstests/core/nin.js";
    "jstests/core/nin2.js";
    "jstests/core/null.js";
    "jstests/core/null2.js";
    "jstests/core/numberint.js";
    "jstests/core/numberlong.js";
    "jstests/core/numberlong2.js";
    "jstests/core/numberlong3.js";
    "jstests/core/numberlong4.js";
    "jstests/core/pull.js";
    "jstests/core/pull2.js";
    "jstests/core/pull_or.js";
    "jstests/core/pull_remove1.js";
    "jstests/core/pullall.js";
    "jstests/core/pullall2.js";
    "jstests/core/push.js";
    "jstests/core/push2.js"; // huge
    "jstests/core/distinct2.js";
    "jstests/core/error2.js";
    "jstests/core/error5.js";
    "jstests/core/insert_id_undefined.js";
    "jstests/core/pushall.js";
    "jstests/core/remove3.js";
    "jstests/core/remove4.js";
    "jstests/core/remove6.js";
    "jstests/core/remove7.js";
    // "jstests/core/remove9.js"; // parallel
    // "jstests/core/removeb.js"; // parallel
    // "jstests/core/removec.js"; // parallel
    "jstests/core/rename2.js";
    "jstests/core/rename3.js";
    "jstests/core/rename5.js";
    "jstests/core/sort1.js";
    "jstests/core/sort3.js";
    "jstests/core/sort4.js";
    "jstests/core/sort5.js";
    "jstests/core/sort6.js";
    "jstests/core/sort7.js";
    "jstests/core/sort9.js";
    "jstests/core/sort10.js";
    // "jstests/core/sortb.js"; // huge
    // "jstests/core/sortf.js"; // huge
    // "jstests/core/sortg.js"; // memory exception for huge sort
    "jstests/core/sorth.js";
    "jstests/core/sorti.js";
    // "jstests/core/sortj.js"; // really long test, huge, crashes
    // "jstests/core/sortk.js"; // stats
    "jstests/core/sort_numeric.js";
    // "jstests/core/distinct3.js"; // parallel
    // "jstests/core/drop2.js"; // parallel
    // "jstests/core/finda.js"; // batch size, covered index
    "jstests/core/query1.js"; // $comment
    "jstests/core/find_and_modify.js";
    "jstests/core/find_and_modify2.js";
    "jstests/core/find_and_modify3.js";
    "jstests/core/find_and_modify4.js";
    "jstests/core/big_object1.js";
    "jstests/core/binData.js";
    "jstests/core/bulk_insert.js";
    "jstests/core/date1.js";
    "jstests/core/date2.js";
    "jstests/core/date3.js";


    "jstests/core/unset.js";
    "jstests/core/unset2.js"; // assert.writeError, tries to set and unset same item to different values

    "jstests/core/nestedarr1.js"; //Exceeded depth limit of 150
    "jstests/core/nestedobj1.js"; //Exceeded depth limit of 150
    "jstests/core/update_min_max_examples.js";
    "jstests/core/update_setOnInsert.js"; // assert.writeError, $setOnInsert _id.a, two notions of _id
    "jstests/core/upsert_and.js"; // assert.writeError, both q and u try to set c to different values
    "jstests/core/update_multi6.js"; // assert.writeError, both q and u contain _id ?
    "jstests/core/set7.js"; // a.9 set doesn't grow array with nulls in between
    "jstests/core/update_multi5.js";
    "jstests/core/update_addToSet.js";
    "jstests/core/update_addToSet3.js";
    "jstests/core/update_bit_examples.js";
    "jstests/core/update_currentdate_examples.js";
    "jstests/core/set1.js";
    "jstests/core/set2.js";
    "jstests/core/set3.js";
    "jstests/core/set4.js";
    "jstests/core/set5.js";
    "jstests/core/set6.js"; // dbref

    "jstests/core/updatel.js"; // dollar operator
    "jstests/core/update_addToSet2.js";
    "jstests/core/update_arrayMatch1.js";
    "jstests/core/update_arrayMatch2.js";
    "jstests/core/update_arrayMatch3.js";
    "jstests/core/update_arrayMatch4.js";
    "jstests/core/update_arrayMatch5.js";
    "jstests/core/update_arrayMatch6.js";
    "jstests/core/update_arrayMatch7.js";
    "jstests/core/update_arrayMatch8.js"; // dbref
    "jstests/core/update_blank1.js";
    "jstests/core/update_invalid1.js";
    "jstests/core/update_mul_examples.js";
    "jstests/core/update_multi3.js";
    "jstests/core/update_multi4.js";
    // "jstests/core/update_replace.js"; // some good validation stuff, but uses a second connection

    "jstests/core/all.js";
    "jstests/core/all2.js";
    "jstests/core/all3.js";
    "jstests/core/all4.js";
    "jstests/core/all5.js";
    "jstests/core/ne1.js";
    "jstests/core/ne3.js";
    "jstests/core/objid1.js";
    "jstests/core/objid2.js";
    "jstests/core/objid3.js"; // _id is supposed to be first key
    "jstests/core/objid4.js";
    "jstests/core/objid6.js";
    "jstests/core/objid7.js";
    "jstests/core/numberlong.js";
    "jstests/core/numberint.js";
    "jstests/core/null_field_name.js";
    "jstests/core/remove.js";
    "jstests/core/or1.js"; // $or should throw if array is empty
    "jstests/core/or7.js";
    "jstests/core/or8.js";
    "jstests/core/or9.js";
    "jstests/core/orb.js";
    "jstests/core/orc.js";
    "jstests/core/ord.js";
    "jstests/core/ore.js";
    "jstests/core/org.js";
    "jstests/core/orh.js";
    "jstests/core/orj.js";
    "jstests/core/ork.js";
    "jstests/core/orp.js";
    "jstests/core/skip1.js";
    "jstests/core/type1.js";
    "jstests/core/type2.js"; // $type:10 should not match missing value
    "jstests/core/type3.js"; // bson type Code
    "jstests/core/not1.js";
    "jstests/core/not2.js"; // $not:{}  and  findOne has more than 1 result
    "jstests/core/not3.js";
    "jstests/core/in.js"; // throws
    "jstests/core/in2.js";
    "jstests/core/in3.js";
    "jstests/core/in4.js";
    "jstests/core/in6.js";
    "jstests/core/in7.js"; // $elemMatch should throw within $in
    "jstests/core/in8.js";
    "jstests/core/inc1.js";
    "jstests/core/inc2.js"; // sort
    "jstests/core/inc3.js";
    "jstests/core/exists.js";
    "jstests/core/exists2.js";
    "jstests/core/exists3.js";
    "jstests/core/exists4.js";
    "jstests/core/exists5.js";
    "jstests/core/exists6.js";
    "jstests/core/exists7.js";
    "jstests/core/exists8.js";
    "jstests/core/exists9.js";
    "jstests/core/existsb.js";
    "jstests/core/find1.js"; // snapshot , $query with dollar sign
    "jstests/core/find2.js";
    "jstests/core/find3.js";
    "jstests/core/find4.js";
    "jstests/core/find5.js";
    "jstests/core/find7.js";
    "jstests/core/find8.js";
    "jstests/core/array1.js";
    "jstests/core/array3.js";
    "jstests/core/array4.js";
    "jstests/core/array_match1.js";
    "jstests/core/array_match2.js";
    "jstests/core/array_match3.js";
    "jstests/core/arrayfind1.js";
    "jstests/core/arrayfind2.js";
    "jstests/core/arrayfind3.js";
    "jstests/core/arrayfind4.js";
    "jstests/core/arrayfind5.js";
    "jstests/core/arrayfind6.js";
    "jstests/core/arrayfind7.js";
    "jstests/core/arrayfind9.js";
    "jstests/core/arrayfinda.js";
    "jstests/core/arrayfindb.js";
    "jstests/core/basic1.js";
    "jstests/core/basic2.js";
    "jstests/core/basic3.js";
    "jstests/core/basic4.js";
    "jstests/core/basic5.js";
    "jstests/core/basic6.js";
    "jstests/core/basic7.js";
    "jstests/core/basic8.js";
    "jstests/core/basic9.js";
    "jstests/core/basica.js";
    "jstests/core/basicb.js";
    "jstests/core/count.js";
    "jstests/core/count2.js";
    "jstests/core/count3.js";
    "jstests/core/count4.js";
    "jstests/core/count5.js";
    "jstests/core/count6.js";
    "jstests/core/count7.js";
    "jstests/core/count9.js";
    // "jstests/core/count10.js"; // parallel
    "jstests/core/count11.js";
    "jstests/core/update2.js";
    "jstests/core/update3.js";
    "jstests/core/update5.js";
    "jstests/core/update6.js";
    "jstests/core/update7.js";
    "jstests/core/update8.js";
    "jstests/core/update9.js";
    "jstests/core/updatea.js";
    "jstests/core/updateb.js";
    "jstests/core/updatec.js";
    "jstests/core/updated.js";
    "jstests/core/updatee.js";
    // "jstests/core/updatef.js"; // parallel
    "jstests/core/updateg.js";
    "jstests/core/updateh.js"; // $id, $db, $ref acceptable in a subdoc.  dbref
    "jstests/core/updatei.js";
    "jstests/core/updatek.js";
    "jstests/core/updatem.js";
    "jstests/core/multi.js";
    "jstests/core/multi2.js";

    // "jstests/core/remove8.js"; // eval js
    //
    // "jstests/core/group1.js"; // js
    // "jstests/core/group2.js"; // js
    // "jstests/core/group3.js"; // js
    // "jstests/core/group4.js"; // js
    // "jstests/core/group5.js"; // js
    // "jstests/core/group6.js"; // js
    // "jstests/core/group7.js"; // js
    // "jstests/core/group8.js"; // js
    
    // "jstests/core/arrayfind8.js"; // unexpected count in unindexed standard query, SERVER-1264, unresolved
    // "jstests/core/existsa.js"; // issue with sparse index
    // "jstests/core/upsert_fields.js"; // also fails in mongo 2.6


    // "jstests/core/or2.js"; // explain, analyze_plan.js
    // "jstests/core/or3.js"; // explain, analyze_plan.js
    // "jstests/core/orf.js"; // explain
    // "jstests/core/ne2.js"; // explain
    // "jstests/core/array_match4.js"; // explain

    // "jstests/core/ora.js"; // js
    // "jstests/core/and3.js" // js
    // "jstests/core/counta.js"; // js
    // "jstests/core/countb.js"; // js
    // "jstests/core/countc.js"; // js
    // "jstests/core/and.js"; // js
    // "jstests/core/find6.js"; // js
    
    "jstests/core/regex.js";
    "jstests/core/regex2.js"; // dot all syntax, Singleline mode
    // "jstests/core/regex3.js"; // stats
    // "jstests/core/regex4.js"; // stats
    // "jstests/core/regex5.js"; // SERVER-505
    // "jstests/core/regex6.js"; // explain, stats
    // "jstests/core/regex7.js";
    "jstests/core/regex8.js";
    "jstests/core/regex9.js"; // must be a string?
    "jstests/core/regexa.js";
    "jstests/core/regexb.js";
    "jstests/core/regexc.js";
    ]

type res =
    {
        name : string
        status : int
        out : string
        err : string
        elapsed : float
    }

let lsof() =
    let ps = ProcessStartInfo()
    ps.CreateNoWindow <- true
    ps.RedirectStandardError <- true
    ps.RedirectStandardOutput <- true
    ps.UseShellExecute <- false
    //ps.WorkingDirectory <- path_mongo_src
    //ps.Arguments <- Path.Combine(path_mongo_src, t)
    ps.FileName <- "/Users/eric/dev/z_mongo/lsof.sh"
    use p = new Process()
    p.StartInfo <- ps
    p.Start() |> ignore // TODO
    let stdout = p.StandardOutput.ReadToEnd()
    printf "%s" stdout
    let stderr = p.StandardError.ReadToEnd()
    //printf "%s" stderr
    p.WaitForExit()

let results =
    List.map (fun t -> 
        //printfn "%s" t
        let t1 = DateTime.Now
        let ps = ProcessStartInfo()
        ps.CreateNoWindow <- true
        ps.RedirectStandardError <- true
        ps.RedirectStandardOutput <- true
        ps.UseShellExecute <- false
        ps.WorkingDirectory <- path_mongo_src
        ps.Arguments <- Path.Combine(path_mongo_src, t)
        ps.FileName <- path_mongo_shell
        use p = new Process()
        p.StartInfo <- ps
        p.Start() |> ignore // TODO
        let stdout = p.StandardOutput.ReadToEnd()
        //printf "%s" stdout
        let stderr = p.StandardError.ReadToEnd()
        //printf "%s" stderr
        p.WaitForExit()
        let t2 = DateTime.Now
        let elapsed = (t2 - t1).TotalMilliseconds
        let status = p.ExitCode
        if status <> 0 then printfn "    failed: %s" t //else printfn "    passed"
        //lsof()
        {
            name = t
            status = status
            out = stdout
            err = stderr
            elapsed = elapsed
        }
        ) tests

let passed = 
    List.filter (fun r -> r.status = 0) results

let failed = 
    List.filter (fun r -> r.status <> 0) results

let passed_names =
    List.map (fun r-> r.name) passed

let failed_names =
    List.map (fun r-> r.name) failed

printfn "Passed (%d): %A" (List.length passed) passed_names

printfn "Failed (%d): %A" (List.length failed) failed_names

