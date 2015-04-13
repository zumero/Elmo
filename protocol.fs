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

type BsonMsgReply =
    {
        r_requestID : int32
        r_responseTo : int32
        r_responseFlags : int32
        r_cursorID : int64
        r_startingFrom : int32
        r_documents : BsonValue[]
    }

type BsonMsgQuery =
    {
        q_requestID : int32
        q_flags : int32
        q_fullCollectionName : string
        q_numberToSkip : int32
        q_numberToReturn : int32
        q_query : BsonValue // always a BsonValue.BDocument
        q_returnFieldsSelector : BsonValue option
    }

type BsonMsgGetMore =
    {
        m_requestID : int32
        m_fullCollectionName : string
        m_numberToReturn : int32
        m_cursorID : int64
    }

type BsonMsgKillCursors =
    {
        k_requestID : int32
        k_cursorIDs : int64[]
    }

type BsonClientMsg =
    | BsonMsgQuery of BsonMsgQuery
    | BsonMsgGetMore of BsonMsgGetMore
    | BsonMsgKillCursors of BsonMsgKillCursors

module protocol = 

    open System
    open System.IO

    let readMessageHeader (br:BinReader) =
        let messageLength = br.ReadInt32()
        let requestID = br.ReadInt32()
        let responseTo = br.ReadInt32()
        let opCode = br.ReadInt32()
        (messageLength,requestID,responseTo,opCode)

    let encodeReplyTo (msg:BsonMsgReply) (w:BinWriter) =
        let start = w.Position
        w.WriteInt32(0) // length placeholder
        w.WriteInt32(msg.r_requestID)
        w.WriteInt32(msg.r_responseTo)
        w.WriteInt32(1) // TODO magic number
        w.WriteInt32(msg.r_responseFlags)
        w.WriteInt64(msg.r_cursorID)
        w.WriteInt32(msg.r_startingFrom)
        w.WriteInt32(msg.r_documents.Length)
        for i in 0 .. msg.r_documents.Length-1 do
            let doc = msg.r_documents.[i]
            bson.toBinary doc w
        let len = w.Position - start
        w.WriteInt32At(len, start)

    let encodeReply msg =
        let w = BinWriter()
        encodeReplyTo msg w
        w.ToArray()

    let debug_VerifyReplyMsg r msg =
        let chk = encodeReply r
        if msg = chk then 
            printfn "MATCH"
        else
            printfn "MISMATCH"
            printfn "msg.Length = %d" (msg.Length)
            printfn "chk.Length = %d" (chk.Length)
            printfn "msg: %A" msg
            printfn "chk: %A" chk
            if msg.Length = chk.Length then
                for i in 0 .. msg.Length-1 do
                    if msg.[i] <> chk.[i] then
                        printfn "byte at %d differs: %d vs %d" i (msg.[i]) (chk.[i])

    let parseMessageFromClient (ba:byte[]) =
        let br = new BinReader(ba, 0, ba.Length)
        let (messageLength,requestID,resonseTo,opCode) = readMessageHeader br
        match opCode with
        | 2004 ->
            let flags = br.ReadInt32()
            let fullCollectionName = br.ReadCString()
            let numberToSkip = br.ReadInt32()
            let numberToReturn = br.ReadInt32()
            let query = br.ReadDocument()
            let returnFieldsSelector = if br.Position < ba.Length then Some (br.ReadDocument()) else None

            let msg = {
                q_requestID = requestID
                q_flags = flags
                q_fullCollectionName = fullCollectionName
                q_numberToSkip = numberToSkip
                q_numberToReturn = numberToReturn
                q_query = query
                q_returnFieldsSelector = returnFieldsSelector
            }
            BsonMsgQuery msg

        | 2005 ->
            let flags = br.ReadInt32()
            let fullCollectionName = br.ReadCString()
            let numberToReturn = br.ReadInt32()
            let cursorID = br.ReadInt64()

            let msg = {
                m_requestID = requestID
                m_fullCollectionName = fullCollectionName
                m_numberToReturn = numberToReturn
                m_cursorID = cursorID
            }
            BsonMsgGetMore msg

        | 2007 ->
            let flags = br.ReadInt32()
            let numberOfCursorIDs = br.ReadInt32()
            let cursorIDs:int64[] = Array.zeroCreate numberOfCursorIDs
            for i in 0 .. numberOfCursorIDs-1 do
                cursorIDs.[i] <- br.ReadInt64()

            let msg = {
                k_requestID = requestID
                k_cursorIDs = cursorIDs
            }
            BsonMsgKillCursors msg

        | _ -> failwith (sprintf "Unknown message opcode: %d" (opCode))

    let readMessage (stream:Stream) = async {
        let! a = stream.AsyncRead(4)
        //printfn "a: %A" a
        let messageLength = BinReader(a, 0, 4).ReadInt32()
        //printfn "messageLength: %d" messageLength
        let msg:byte[] = Array.zeroCreate messageLength
        Array.Copy(a, 0, msg, 0, 4)
        //printfn "messageLength: %d" messageLength
        let sofar = ref 4
        while !sofar < messageLength do
            let! got = stream.AsyncRead(msg, !sofar, messageLength - !sofar)
            //printfn "got: %d" got
            sofar := !sofar + got
        return msg
    }
        

