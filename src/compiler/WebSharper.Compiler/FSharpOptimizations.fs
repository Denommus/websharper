// $begin{copyright}
//
// This file is part of WebSharper
//
// Copyright (c) 2008-2016 IntelliFactory
//
// Licensed under the Apache License, Version 2.0 (the "License"); you
// may not use this file except in compliance with the License.  You may
// obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
// implied.  See the License for the specific language governing
// permissions and limitations under the License.
//
// $end{copyright}

module WebSharper.Compiler.FSharpOptimizations

open WebSharper.Core
open WebSharper.Core.AST

module I = IgnoreSourcePos

module Definitions =

    let Operators =
        TypeDefinition {
            Assembly = "FSharp.Core"
            FullName = "Microsoft.FSharp.Core.Operators"
        }

    let WSPervasives =
        TypeDefinition {
            Assembly = "WebSharper.Main"
            FullName = "WebSharper.Pervasives"
        }

let (|LetFunction|_|) x =
    let rec r lets x =
        match IgnoreExprSourcePos x with
        | Lambda ([ v ], res) ->
            let lets b =
                lets |> List.fold (fun body (v, value) ->
                    Let(v, value, body)) b                
            Some <| (lets, v, res)
        | Let (v, value, body) ->
            r ((v, value) :: lets) body
        | _ ->
            None
    r [] x

let (|LetFunction2|_|) x =
    let rec r lets x =
        match IgnoreExprSourcePos x with
        | Lambda ([ v1 ], IgnoreExprSourcePos (Lambda ([ v2 ], res))) ->
            let lets b =
                lets |> List.fold (fun body (v, value) ->
                    Let(v, value, body)) b                
            Some <| (lets, v1, v2, res)
        | Let (v, value, body) ->
            r ((v, value) :: lets) body
        | _ ->
            None
    r [] x

let (|LetFunction3|_|) x =
    let rec r lets x =
        match IgnoreExprSourcePos x with
        | Lambda ([ v1 ], IgnoreExprSourcePos (Lambda ([ v2 ], IgnoreExprSourcePos (Lambda ([ v3 ], res))))) ->
            let lets b =
                lets |> List.fold (fun body (v, value) ->
                    Let(v, value, body)) b                
            Some <| (lets, v1, v2, v3, res)
        | Let (v, value, body) ->
            r ((v, value) :: lets) body
        | _ ->
            None
    r [] x

let OptimizeCalls td (md: Method) args = 
    if td = Definitions.Operators then
        match md.Value.MethodName with
        | "op_PipeRight" ->
            let [x; f] = args
            match f with
            | LetFunction (lets, v, body) ->
                Some <| Let(v, x, lets body)   
            | _ -> None  
        | "op_PipeLeft" ->
            let [f; x] = args
            match f with
            | LetFunction (lets, v, body) ->
                Some <| lets (Let(v, x, body))   
            | _ -> None  
        | "op_PipeRight2" ->
            let [x; y; f] = args
            match f with
            | LetFunction2 (lets, v1, v2, body) ->
                Some <| Let(v1, x, Let(v2, y, lets body))   
            | _ -> None  
        | "op_PipeLeft2" ->
            let [f; x; y] = args
            match f with
            | LetFunction2 (lets, v1, v2, body) ->
                Some <| lets (Let(v1, x, Let(v2, y, body)))   
            | _ -> None  
        | "op_PipeRight3" ->
            let [x; y; z; f] = args
            match f with
            | LetFunction3 (lets, v1, v2, v3, body) ->
                Some <| Let(v1, x, Let(v2, y, Let(v3, z, lets body)))   
            | _ -> None  
        | "op_PipeLeft3" ->
            let [x; y; z; f] = args
            match f with
            | LetFunction3 (lets, v1, v2, v3, body) ->
                Some <| lets (Let(v1, x, Let(v2, y, Let(v3, z, body))))   
            | _ -> None  
        | "op_ComposeRight" ->
            let [f; g] = args
            match f, g with
            | LetFunction (letsf, vf, bodyf), LetFunction (letsg, vg, bodyg) ->
                Some <| letsf(letsg(Lambda([vf], Let (vg, bodyf, bodyg))))
            | _ -> None  
        | "op_ComposeLeft" ->
            let [g; f] = args
            match f, g with
            | LetFunction (letsf, vf, bodyf), LetFunction (letsg, vg, bodyg) ->
                Some <| letsg(letsf(Lambda([vf], Let (vg, bodyf, bodyg))))
            | _ -> None  
        | _ -> None
    elif td = Definitions.WSPervasives then
        match md.Value.MethodName with
        | "op_BarGreaterBang" ->
            let [x; f] = args
            match f with
            | LetFunction (lets, v, body) ->
                Some <| Let(v, x, Sequential [lets body; Var v])   
            | _ -> None  
        | _ -> None
    else None
