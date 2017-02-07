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

type FuncArgVisitor(opts: FuncArgOptimization list, margs: Id list, mems) =
    inherit Visitor()

    let cargs =
        (opts, margs) ||> Seq.map2 (fun c a ->
            match c with
            | CurriedFuncArg _ 
            | TupledFuncArg _ -> Some a
            | _ -> None
        ) |> Seq.choose id |> HashSet
    let iargs = margs |> Seq.mapi (fun i a -> a, i) |> dict

    let appl =
        opts |> Seq.map (fun c ->
            match c with
            | CurriedFuncArg a -> a
            | TupledFuncArg _ -> 1
            | _ -> 0
        ) |> Array.ofSeq
    let calls = Array.init iargs.Count ResizeArray

    let setAppl i value =
        let i = iargs.[i]
        let a = appl.[i]
        if a > value then
            appl.[i] <- value

    let (|ArgIndex|_|) e =
        match e with
        | Var v ->
            if cargs.Contains v then Some iargs.[v] else None
        | Hole i ->
            if cargs.Contains margs.[i] then Some i else None
        | _ -> None
                
    member this.Results =
        let res =
            (appl, opts) ||> Seq.map2(fun i c -> 
                match c with     
                | CurriedFuncArg _ -> 
                    if i > 1 then CurriedFuncArg i else NotOptimizedFuncArg
                | TupledFuncArg _ ->
                    if i > 0 then c else NotOptimizedFuncArg
                | _ -> c
            ) |> Array.ofSeq
        Array.zip res calls    

    override this.VisitId i =
        if cargs.Contains i then
//            printfn "Non-application use of curried arg %s of %s" i.Name.Value mems 
            setAppl i 0

    override this.VisitHole i =
        this.VisitId(margs.[i])

    override this.VisitFunction(args, body) =
        this.VisitStatement body

    override this.VisitLet(var, value, body) =
        match value with
        | Hole _ when iargs.ContainsKey var -> this.VisitExpression(body)
        | _ -> base.VisitLet(var, value, body)

    override this.VisitCall(thisOpt, typ, meth, args) =
        thisOpt |> Option.iter this.VisitExpression
        args |> List.iteri (fun i a ->
            match IgnoreExprSourcePos a with
            | ArgIndex j ->
                calls.[j].Add(Method (typ.Entity, meth.Entity), i)
            | a -> this.VisitExpression a     
        )

    override this.VisitCtor(typ, ctor, args) =
        args |> List.iteri (fun i a ->
            match IgnoreExprSourcePos a with
            | ArgIndex j ->
                calls.[j].Add(Constructor (typ.Entity, ctor), i)
            | a -> this.VisitExpression a     
        )

//    override this.VisitFieldSet(obj, typ, name, isPrivate, value) =
//        match obj with
//        | Some o -> this.VisitExpression(o)
//        | _ -> ()
//        if isPrivate then
//            match IgnoreExprSourcePos value with
//            | ArgIndex j ->
//                calls.[j].Add(PrivateField name, 0)
//            | a -> this.VisitExpression(value)
//        else
//            this.VisitExpression(value)

    override this.VisitCurriedApplication(f, args) =
        match IgnoreExprSourcePos f with
        | ArgIndex i ->
            setAppl margs.[i] (List.length args)
        | f -> this.VisitExpression f
        args |> List.iter this.VisitExpression            

    override this.VisitApplication(f, args, _, _) =
        match IgnoreExprSourcePos f with
        | ArgIndex i ->
            setAppl margs.[i] 1
        | f -> this.VisitExpression f
        args |> List.iter this.VisitExpression            

type FuncArgTransformer(al: list<Id * FuncArgOptimization>) =
    inherit Transformer()

    let cargs = dict al
         
    override this.TransformVar(v) =
        match cargs.TryGetValue v with
        | true, (CurriedFuncArg _ | TupledFuncArg _ as opt) ->
            OptimizedFSharpArg(Var v, opt)
        | _ -> Var v
    
    override this.TransformHole(i) =
        match al.[i] with
        | _, (CurriedFuncArg _ | TupledFuncArg _ as opt) ->
            OptimizedFSharpArg(Hole i, opt)
        | _ -> Hole i

    override this.TransformCurriedApplication(func, args: Expression list) =
        let normal() =
            CodeReader.applyCurried (this.TransformExpression func)
                (List.map this.TransformExpression args)
        match func with
        | I.Var f ->
            match cargs.TryGetValue f with
            | true, CurriedFuncArg a ->
//                printfn "transforming curried application, length: %d args %d" a args.Length
                let ucArgs, restArgs = args |> List.map this.TransformExpression |> List.splitAt a
                let inner = Application(Var f, ucArgs, false, Some a)
                let res = CodeReader.applyCurried inner restArgs
//                printfn "result: %s" (Debug.PrintExpression res)
                res
            | true, TupledFuncArg a ->
                match args with
                | t :: rArgs ->
                    CodeReader.applyCurried (this.TransformApplication(func, [t], false, Some 1))
                        (List.map this.TransformExpression rArgs)
                | _ -> failwith "tupled func must have arguments"
            | _ -> normal()
        | _ -> normal()

    override this.TransformApplication(func, args, p, l) =
        let normal() =
            Application(this.TransformExpression func, List.map this.TransformExpression args, p, l)
        match func with
        | I.Var f ->
            match cargs.TryGetValue f with
            | true, TupledFuncArg a ->
                match args with
                | [ I.NewArray es ] ->
                    Application(Var f, List.map this.TransformExpression es, p, Some (List.length es))
                | _ ->
                    failwith "tupled function applied with multiple arguments"    
            | _ -> normal()    
        | _ -> normal()
    
type ResolveFuncArgs(comp: Compilation) =
    let members = Dictionary<Member, NotResolvedMethod * Id list>()
    let resolved = HashSet<Member>()
    let rArgs = Dictionary<Member * int, FuncArgOptimization>()
    let callsTo = Dictionary<Member * int, list<Member * int>>()

    let printMem mem = 
        match mem with
        | Method(typ, meth) -> sprintf "method %s.%s" typ.Value.FullName meth.Value.MethodName
        | Constructor(typ, ctor) -> sprintf "constructor %s" typ.Value.FullName

    let getRArgs mi =
        match rArgs.TryGetValue(mi) with
        | true, v -> v
        | _ -> NotOptimizedFuncArg
         
    let rec setRArgs mi value =
        let mem, i = mi
        match rArgs.TryGetValue(mi) with
        | true, v -> 
            if value <> v then
//                printfn "Changing curried optimization %s - %d : %A" (printMem mem) i value
                rArgs.[mi] <- value
                match callsTo.TryGetValue(mi) with
                | true, ct ->
                    for c in ct do
                        setRArgs c value
                | _ -> ()
        | _ ->
//            printfn "Setting curried optimization %s - %d : %A" (printMem mem) i value
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
                let cv = FuncArgVisitor(nr.FuncArgs.Value, args, printMem mem)
//                printfn "Resolving use of funcion arguments of %s : %s" (printMem mem) (Debug.PrintExpression nr.Body)
                cv.VisitExpression(nr.Body)
                for i, (c, calls) in cv.Results |> Seq.indexed do
                    match c with
                    | CurriedFuncArg _ -> 
                        calls |> Seq.fold (fun v call -> 
                            match this.GetCompiled(call) with
                            | Some n -> 
                                Dict.addToMulti callsTo call (mem, i)
                                min n v
                            | _ -> 
                                this.ResolveMember(fst call)
                                min (getRArgs call) v
                        ) c |> setRArgs (mem, i)
                    | TupledFuncArg _ -> 
                        calls |> Seq.fold (fun v call -> 
                            match this.GetCompiled(call) with
                            | Some n -> 
                                Dict.addToMulti callsTo call (mem, i)
                                min n v
                            | _ -> 
                                this.ResolveMember(fst call)
                                min (getRArgs call) v
                        ) c |> setRArgs (mem, i)
                    | _ ->
                        setRArgs (mem, i) c
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
                mem, List.ofArray cs
            )
            |> dict
        
        for (KeyValue(mem, (nr, args))) in members do
            let cs = rArgs.[mem]
            nr.FuncArgs <- Some cs
            let tr = 
                (args, cs) ||> List.zip |> FuncArgTransformer
            nr.Body <- tr.TransformExpression(nr.Body)
