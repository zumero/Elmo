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

module ProxyServer = 

    open System
    open System.IO
    open System.Net
    open System.Net.Sockets
    open System.Threading

    let parseMessageFromServer (ba:byte[]) =
        let br = new BinReader(ba, 0, ba.Length)
        let (messageLen,requestID,responseTo,opCode) = protocol.readMessageHeader br
        match opCode with
        | 1 ->
            let responseFlags = br.ReadInt32()
            let cursorID = br.ReadInt64()
            let startingFrom = br.ReadInt32()
            let numberReturned = br.ReadInt32()
            let msg = {
                r_requestID = requestID
                r_responseTo = responseTo
                r_responseFlags = responseFlags
                r_cursorID = cursorID
                r_startingFrom = startingFrom
                r_documents = Array.zeroCreate numberReturned
            }
            for i in 0 .. numberReturned-1 do
                msg.r_documents.[i] <- br.ReadDocument()
            msg

        | _ -> failwith "Unknown message opcode"

    type Socket with
        member socket.AsyncAccept() = Async.FromBeginEnd(socket.BeginAccept, socket.EndAccept)

    type Server() =
        static member Start(hostname:string, ?port) =
            let ipAddress = Dns.GetHostEntry(hostname).AddressList.[0]
            Server.Start(ipAddress, ?port = port)

        static member Start(?ipAddress, ?port) =
            let ipAddress = defaultArg ipAddress IPAddress.Any
            let port = defaultArg port 80
            let endpoint = IPEndPoint(ipAddress, port)
            let cts = new CancellationTokenSource()
            let listener = new Socket(AddressFamily.InterNetwork, SocketType.Stream, ProtocolType.Tcp)
            listener.Bind(endpoint)
            listener.Listen(int SocketOptionName.MaxConnections)
            printfn "Started listening on port %d" port
        
            let serviceClient clientSocket = async {
                let clientStream = new NetworkStream(clientSocket, false) 

                let serverSocket = new Socket(AddressFamily.InterNetwork, SocketType.Stream, ProtocolType.Tcp)
                serverSocket.Connect(IPAddress.Loopback, 27017)
                let serverStream = new NetworkStream(serverSocket)

                try
                    try
                        while true do
                            let! msg = protocol.readMessage clientStream
                            printfn "----------------------------------------------------------------"
                            printfn "Received %d bytes from client" (msg.Length)
                            if msg.Length > 0 then
                                let m = protocol.parseMessageFromClient msg
                                printfn "%A" m
                                do! serverStream.AsyncWrite(msg, 0, msg.Length)

                            let! msg = protocol.readMessage serverStream
                            printfn "Received %d bytes from server" (msg.Length)
                            if msg.Length > 0 then
                                let m = parseMessageFromServer msg
                                printfn "%A" m
                                do! clientStream.AsyncWrite(msg, 0, msg.Length)
                    with :? System.IO.EndOfStreamException -> ()
                finally
                    clientStream.Close()
                    //clientSocket.Shutdown(SocketShutdown.Both)
                    clientSocket.Close()

                    serverStream.Close()
                    //clientSocket.Shutdown(SocketShutdown.Both)
                    serverSocket.Close()
            }

            let rec loop() = async {
                printfn "Waiting for request ..."
                let! socket = listener.AsyncAccept()
                printfn "Received connection"
                do! serviceClient socket
                return! loop() }

            Async.Start(loop(), cancellationToken = cts.Token)
            { new IDisposable with member x.Dispose() = cts.Cancel(); listener.Close() }

    let runServer port =
        use s = Server.Start(port = port)
        System.Console.ReadLine() |> ignore
        printfn "bye!"


