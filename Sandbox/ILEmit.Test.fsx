
#r "./bin/debug/Alpa.Compiler.dll"
open Alpa.Emit
open Alpa.Emit.EmitException
open Alpa.Emit.HashMap
open Alpa.Emit.TypeSpec
open Alpa.Emit.ILEmit

let (!) = TypeVar
let typeSpec n ts = TypeSpec(FullName(n, [], [], None), ts)
let type0 n = typeSpec n []
let type1 n t1 = typeSpec n [t1]
let type2 n (t1, t2) = typeSpec n [t1;t2]

let alias n ps t = n, { aTypeParams = ps; entity = t }

let rec reduce amap visitedNames = function
    | TypeSpec(FullName(n, [], [], None), ts) as t ->
        if List.contains n visitedNames then raiseEmitExn <| RecursiveAlias n

        let mutable v = Unchecked.defaultof<_>
        if tryGet amap n &v then
            let ts = List.map (reduce amap visitedNames) ts
            reduce amap (n::visitedNames) <| applyType n v ts
        else
            t

    | TypeSpec(n, ts) -> TypeSpec(n, List.map (reduce amap visitedNames) ts)
    | t -> t

let reduceAlias amap name = reduce amap [name] (get amap name).entity
