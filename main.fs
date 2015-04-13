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

module main = 

    open System

    [<EntryPoint>]
    let main argv = 
        match argv.[0] with
        | "proxy" -> ProxyServer.runServer 8090
        | "run" -> LiteServer.runServer 27017 false
        | "runv" -> LiteServer.runServer 27017 true
        | _ -> failwith (sprintf "Invalid command: %s" argv.[0])
        0

