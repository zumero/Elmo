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

type BinWriter () =
    let mutable i = 0
    let mutable space = 1024
    let mutable ba:byte[] = Array.zeroCreate space

    let ensureSpace more =
        let need = i + more
        if need > space then
            let twice = space * 2
            let newspace = if twice > need then twice else need
            let newa:byte[] = Array.zeroCreate newspace
            Array.Copy(ba, 0, newa, 0, i)
            ba <- newa
            space <- newspace

    let writeInt32At v p =
        ba.[p+0] <- byte (v >>> 0)
        ba.[p+1] <- byte (v >>> 8)
        ba.[p+2] <- byte (v >>> 16)
        ba.[p+3] <- byte (v >>> 24)

    let writeInt32 v =
        ensureSpace 4
        writeInt32At v i
        i <- i + 4

    let writeInt16BigEndian (v:int16) =
        ensureSpace 2
        ba.[i+1] <- byte (v >>> 0)
        ba.[i+0] <- byte (v >>> 8)
        i <- i + 2

    let writeInt32BigEndian v =
        ensureSpace 4
        ba.[i+3] <- byte (v >>> 0)
        ba.[i+2] <- byte (v >>> 8)
        ba.[i+1] <- byte (v >>> 16)
        ba.[i+0] <- byte (v >>> 24)
        i <- i + 4

    let writeInt64BigEndian (v:int64) =
        ensureSpace 8
        ba.[i+7] <- byte (v >>> 0)
        ba.[i+6] <- byte (v >>> 8)
        ba.[i+5] <- byte (v >>> 16)
        ba.[i+4] <- byte (v >>> 24)
        ba.[i+3] <- byte (v >>> 32)
        ba.[i+2] <- byte (v >>> 40)
        ba.[i+1] <- byte (v >>> 48)
        ba.[i+0] <- byte (v >>> 56)
        i <- i + 8

    let writeInt64 (v:int64) =
        ensureSpace 8
        ba.[i+0] <- byte (v >>> 0)
        ba.[i+1] <- byte (v >>> 8)
        ba.[i+2] <- byte (v >>> 16)
        ba.[i+3] <- byte (v >>> 24)
        ba.[i+4] <- byte (v >>> 32)
        ba.[i+5] <- byte (v >>> 40)
        ba.[i+6] <- byte (v >>> 48)
        ba.[i+7] <- byte (v >>> 56)
        i <- i + 8

    let writeByte b =
        ensureSpace 1
        ba.[i] <- b
        i <- i + 1

    let writeCString (s:string) =
        let a = System.Text.Encoding.UTF8.GetBytes (s)
        ensureSpace (a.Length + 1)
        Array.Copy(a, 0, ba, i, a.Length)
        ba.[i+a.Length] <- 0uy
        i <- i + a.Length + 1

    let writeBsonString (s:string) =
        let a = System.Text.Encoding.UTF8.GetBytes (s)
        writeInt32 (a.Length + 1)
        ensureSpace (a.Length + 1)
        Array.Copy(a, 0, ba, i, a.Length)
        ba.[i+a.Length] <- 0uy
        i <- i + a.Length + 1

    let writeBytes (a:byte[]) =
        ensureSpace (a.Length)
        Array.Copy(a, 0, ba, i, a.Length)
        i <- i + a.Length

    let writeFloat (f:float) =
        let a = BitConverter.GetBytes(f)
        if not BitConverter.IsLittleEndian then Array.Reverse a
        writeBytes a

    member this.Position = i
    member this.WriteInt16BigEndian(v) = writeInt16BigEndian v
    member this.WriteInt32BigEndian(v) = writeInt32BigEndian v
    member this.WriteInt64BigEndian(v) = writeInt64BigEndian v
    member this.WriteInt32(v) = writeInt32 v
    member this.WriteInt32At(v,p) = writeInt32At v p
    member this.WriteInt64(v) = writeInt64 v
    member this.WriteCString(s) = writeCString s
    member this.WriteByte(b) = writeByte b
    member this.WriteBsonString(s) = writeBsonString s
    member this.WriteFloat(f) = writeFloat f
    member this.WriteObjectID(a) = writeBytes a
    member this.WriteBytes(a) = writeBytes a
    member this.ToArray() =
        let a:byte[] = Array.zeroCreate i
        Array.Copy(ba, 0, a, 0, i)
        a


