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

module WebSharper.Compiler.Closures

open System.Collections.Generic

open WebSharper.Core
open WebSharper.Core.AST

module M = WebSharper.Core.Metadata

type CollectVariables() =
    inherit StatementVisitor()

    let vars = ResizeArray()

    override this.VisitFuncDeclaration(f, _, _) =
        vars.Add f

    override this.VisitVarDeclaration(v, _) =
        vars.Add v

    member private this.Vars = vars :> _ seq

    static member ScopeVars(s: Statement) =
        let c = CollectVariables() 
        c.VisitStatement(s)
        c.Vars

type Scope =
    {
        Vars : HashSet<Id>
        Captured : HashSet<Id>
        CaptureSets : ResizeArray<Set<Id> * option<SourcePos>>
    }

type ExamineClosures (comp: Compilation) =
    inherit TransformerWithSourcePos(comp)

    let mutable outerScope = true
    let mutable scopeChain = []
    let mutable topScopeVars = HashSet()

    member this.EnterScope(args, body) =
        scopeChain <- 
            {
                Vars = HashSet (Seq.append args (CollectVariables.ScopeVars(body)))
                Captured = HashSet()
                CaptureSets = ResizeArray()
            } :: scopeChain

    member this.Warning(pos, msg) =
        match pos with 
        | Some pos ->
            let oneCharPos =                 
                { pos with End = pos.Start }
            comp.AddWarning(Some oneCharPos, SourceWarning msg)
        | _ -> ()
    
    member this.Warning(msg) =
        this.Warning(this.CurrentSourcePos, msg)

    member this.ExitScope() =
        let s = List.head scopeChain
        scopeChain <- List.tail scopeChain
        match scopeChain with
        | c :: _ ->
            if s.Captured.Count = 0 then
                this.Warning("This function captures no variables. Consider moving it to top scope.")
                s.Captured |> Seq.iter (c.Captured.Add >> ignore)
            else
                for cv in s.Captured do
                    if not (c.Vars.Contains cv) then
                        c.Captured.Add cv |> ignore
                if s.Captured |> Seq.forall (c.Vars.Contains >> not) then
                    this.Warning("This function captures no variables from parent scope. Consider moving it to higher scope.")
                else
                    c.CaptureSets.Add(Set s.Captured, this.CurrentSourcePos)
        | _ -> ()
        let retained = s.CaptureSets |> Seq.map fst |> Set.unionMany
        for cs, pos in s.CaptureSets do
            let diff = retained - cs
            if not (Set.isEmpty diff) then
                let names =
                    diff |> Seq.map (fun i -> defaultArg i.Name "_") |> String.concat ", "
                this.Warning(pos, "This function do not use all retained variables through capture: " + names)    

    override this.TransformFuncDeclaration(f, args, body) =
        // top scope is not a named function
        this.EnterScope(args, body)
        let res = base.TransformFuncDeclaration(f, args, body)
        this.ExitScope()
        res

    override this.TransformFunction(args, body) =
        if outerScope then
            outerScope <- false
            CollectVariables.ScopeVars(body) |> Seq.iter (topScopeVars.Add >> ignore)
            let res = base.TransformFunction(args, body)
            outerScope <- true
            res
        else
            this.EnterScope(args, body)
            let res = Function(args, this.TransformStatement body)
            this.ExitScope()
            res

    override this.TransformId(i) =
        match scopeChain with
        | s :: _ ->
            if not (s.Vars.Contains i) && not (topScopeVars.Contains i) then
//                match i.Name with
//                | Some n ->
//                    this.Warning("captured variable: " + n)
//                | _ ->
//                    this.Warning("captured unnamed variable")
                s.Captured.Add i |> ignore   
        | _ -> ()
        i
