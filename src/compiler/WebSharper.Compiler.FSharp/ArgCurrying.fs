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

module WebSharper.Compiler.FSharp.ArgCurrying

open System.Collections.Generic

open WebSharper.Core
open WebSharper.Core.AST
open WebSharper.Core.Metadata
open WebSharper.Compiler
open WebSharper.Compiler.NotResolved
module I = IgnoreSourcePos

type Member =
    | Method of TypeDefinition * Method
    | Constructor of TypeDefinition * Constructor

let minLists a b =
    let rec m acc a b =
        match a, b with
        | ah :: ar, bh :: br ->
            let h = if ah <> bh then 1 else ah
            m (h :: acc) ar br
        | _ -> List.rev acc
    m [] a b

type CurryingVisitor(curriedArgs: (int list)[], margs: Id list, mems) =
    inherit Visitor()

    let cargs =
        (curriedArgs, Array.ofList margs) ||> Seq.map2 (fun c a ->
            if List.isEmpty c then None else Some a
        ) |> Seq.choose id |> HashSet
    let margs = margs |> Seq.mapi (fun i a -> a, i) |> dict

    let appl = curriedArgs |> Array.copy
    let calls = Array.init curriedArgs.Length ResizeArray

    let setAppl i value =
        let i = margs.[i]
        let a = appl.[i]
        if a.Length > value then
            appl.[i] <- a |> List.take value

    member this.Results =
        Array.zip appl calls    

    override this.VisitId i =
        if cargs.Contains i then
//            printfn "Non-application use of curried arg %s of %s" i.Name.Value mems 
            setAppl i 0

    override this.VisitFunction(args, body) =
        this.VisitStatement body

    override this.VisitLet(var, value, body) =
        match value with
        | Hole _ -> this.VisitExpression(body)
        | _ -> base.VisitLet(var, value, body)

    override this.VisitCall(thisOpt, typ, meth, args) =
        thisOpt |> Option.iter this.VisitExpression
        args |> List.iteri (fun i a ->
            match IgnoreExprSourcePos a with
            | Var v ->
                if cargs.Contains v then
                    calls.[margs.[v]].Add(Method (typ.Entity, meth.Entity), i)
            | a -> this.VisitExpression a     
        )

    override this.VisitCtor(typ, ctor, args) =
        args |> List.iteri (fun i a ->
            match IgnoreExprSourcePos a with
            | Var v ->
                if cargs.Contains v then
                    calls.[margs.[v]].Add(Constructor (typ.Entity, ctor), i)
            | a -> this.VisitExpression a     
        )

    override this.VisitCurriedApplication(f, args) =
        match IgnoreExprSourcePos f with
        | Var i ->
            if cargs.Contains i then
                setAppl i (List.length args)
        | f -> this.VisitExpression f
        args |> List.iter this.VisitExpression            

type CurryingTransformer(cargs: IDictionary<Id,int list>) =
    inherit Transformer()

    override this.TransformVar(v) =
        match cargs.TryGetValue v with
        | true, c ->
            CurriedVar(v, c)
        | _ -> Var v
    
    override this.TransformCurriedApplication(func, args: Expression list) =
        match func with
        | I.Var f when cargs.ContainsKey f ->
            let ucArgs = ResizeArray()
            let ca = cargs.[f]
            for (i, t) in ca |> List.indexed do
                if t = 1 then
                    ucArgs.Add(args.[i])           
                else       
                    for j = 0 to t - 1 do
                        ucArgs.Add(args.[i].[Value (Int j)])
            let inner = Application(func, List.ofSeq ucArgs, false, Some ucArgs.Count)
            CodeReader.appplyCurried inner args.[ca.Length .. args.Length - 1]
        | _ ->
            CodeReader.appplyCurried func args
    
type ResolveCurrying(comp: Compilation) =
    let members = Dictionary<Member, NotResolvedMethod * Id list>()
    let resolved = HashSet<Member>()
    let rArgs = Dictionary<Member * int, int list>()
    let callsTo = Dictionary<Member * int, list<Member * int>>()

    let printMem mem = 
        match mem with
        | Method(typ, meth) -> sprintf "method %s.%s" typ.Value.FullName meth.Value.MethodName
        | Constructor(typ, ctor) -> sprintf "constructor %s" typ.Value.FullName

    let getRArgs mi =
        match rArgs.TryGetValue(mi) with
        | true, v -> v
        | _ -> []
         
    let rec setRArgs mi value =
        let mem, i = mi
        match rArgs.TryGetValue(mi) with
        | true, v -> 
            if value <> v then
                printfn "Changing curried optimization %s - %d : %A" (printMem mem) i value
                rArgs.[mi] <- value
                match callsTo.TryGetValue(mi) with
                | true, ct ->
                    for c in ct do
                        setRArgs c value
                | _ -> ()
        | _ ->
            printfn "Setting curried optimization %s - %d : %A" (printMem mem) i value
            rArgs.[mi] <- value
            rArgs.[mi] <- value

    member this.AddMember(mem, nr, args) =
        members.Add(mem, (nr, args)) |> ignore    

    member this.GetCompiled(mem, i) =
        match mem with
        | Method(typ, meth) ->
            comp.TryLookupClassInfo(typ) |> Option.map (fun cls -> cls.Methods.[meth])
        | Constructor(typ, ctor) ->
            comp.TryLookupClassInfo(typ) |> Option.map (fun cls -> cls.Constructors.[ctor])
        |> Option.bind (fun (_, opts, _) ->
            opts.FuncArgs |> Option.map (fun ca -> ca.[i])
        )

    member this.ResolveMember(mem) =
        if resolved.Add(mem) then
            match members.TryGetValue mem with
            | true, (nr, args) -> 
                let nr, args = members.[mem] 
                let cv = CurryingVisitor(nr.FuncArgs.Value, args, printMem mem)
//                printfn "Resolving use of funcion arguments of %s : %s" (printMem mem) (Debug.PrintExpression nr.Body)
                cv.VisitExpression(nr.Body)
                for i, (c, calls) in cv.Results |> Seq.indexed do
                    if not (List.isEmpty c) then
                        calls |> Seq.fold (fun v call -> 
                            match this.GetCompiled(call) with
                            | Some n -> 
                                Dict.addToMulti callsTo call (mem, i)
                                minLists n v
                            | _ -> 
                                this.ResolveMember(fst call)
                                minLists (getRArgs call) v
                        ) c |> setRArgs (mem, i)
                    else
                        setRArgs (mem, i) [] 
            | _ -> ()

    member this.ResolveAll() =
        for mem in members.Keys do
            this.ResolveMember(mem)

        let rArgs =
            rArgs
            |> Seq.map (fun (KeyValue((mem, i), c)) -> mem, (i, c))
            |> Seq.groupBy fst
            |> Seq.map (fun (mem, curr) ->
                let cs = Array.zeroCreate (List.length (snd members.[mem]))
                for _, (i, c) in curr do
                    cs.[i] <- c
                mem, cs
            )
            |> dict
        
        for (KeyValue(mem, (nr, args))) in members do
            let cs = rArgs.[mem]
            nr.FuncArgs <- Some cs
            let tr = 
                (cs, args) ||> Seq.map2 (fun c a ->
                    if List.isEmpty c then None else Some (a, c)           
                ) |> Seq.choose id |> dict |> CurryingTransformer
            nr.Body <- tr.TransformExpression(nr.Body)
