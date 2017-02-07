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

module WebSharper.Tests.Optimizations

open WebSharper
open WebSharper.JavaScript
open WebSharper.Testing
module R = WebSharper.Testing.Random

[<JavaScript>]
let GlobalTupled (a, b) =
    a + b 

[<JavaScript>]
let GlobalCurried a b =
    a + b

[<JavaScript>]
let TupledArg f : int =
    f (1, 2)

[<JavaScript>]
let CurriedArg f : int =
    f 1 2

[<JavaScript>]
type TypeWithTupled(f) =
    let g = JavaScript.FuncWithArgs(f)
    member this.Apply() = g.Call(1, 2) : int

[<JavaScript>]
type TypeWithCurried(f) =
    let g = JavaScript.FuncWithArgs(fun (a, b) -> f a b)
    member this.Apply() = g.Call(1, 2) : int

[<JavaScript>]
let Tests =

    let LocalTupled (a, b) =
        a + b 

    let LocalCurried a b =
        a + b

    TestCategory "Optimizations" {
        Test "Tupled function" {
            equal (GlobalTupled (1, 2)) 3
            equal (LocalTupled (1, 2)) 3
        }

        Test "Tupled function argument" {
            equal (TupledArg (fun (a, b) -> a + b)) 3
            equal (TupledArg GlobalTupled) 3
            equal (TupledArg LocalTupled) 3
            equal (TypeWithTupled(fun (a, b) -> a + b).Apply()) 3
        }

        Test "Curried function" {
            equal (GlobalCurried 1 2) 3
            equal (LocalCurried 1 2) 3
        }

        Test "Curried function argument" {
            equal (CurriedArg (fun a b -> a + b)) 3
            equal (CurriedArg GlobalCurried) 3
            equal (CurriedArg LocalCurried) 3
            equal (TypeWithCurried(fun a b -> a + b).Apply()) 3
        }
    }
