namespace Alpa.Emit
open System

module List =
    let tryIter2 action ls rs =
        let rec aux ls rs =
            match ls, rs with
            | l::ls, r::rs -> action l r; aux ls rs
            | [], [] -> true
            | _ -> false
        aux ls rs

    let tryGetDuplicate xs =
        let rec aux set = function
            | [] -> None
            | x::_ when List.contains x set -> Some x
            | x::xs -> aux (x::set) xs
        aux [] xs

module HashMap =
    let add (map: HashMap<_,_>) k v = map.Add(k, v)
    let assign (map: HashMap<_,_>) k v = map.[k] <- v
    let get (map: HashMap<_,_>) k = map.[k]
    let tryGet (map: HashMap<_,_>) k (v: _ byref) = map.TryGetValue(k, &v)
    let values (map: HashMap<_,_>) = map.Values
    
[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Parameter =
    let paramType (Parameter(_,t)) = t

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module TypeVarMap =
    let emptyVarMap = TypeVarMap([], [])
    
[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module FullName =
    let toTypeName = function
    //    | FullName(name, [], [], None) -> name
    //    | FullName(name, [], [], Some asmName) -> name + ", " + asmName
    //    | FullName(name, [], [ns1], None) -> ns1 + "." + name
    //    | FullName(name, [], [ns1], Some asmName) -> ns1 + "." + name + ", " + asmName
        | FullName(name, nestersRev, nsRev, asmName) ->
            let b = System.Text.StringBuilder name
            let d = Type.Delimiter
            for nester in nestersRev do b.Insert(0, '+').Insert(0, nester) |> ignore
            for ns in nsRev do b.Insert(0, d).Insert(0, ns) |> ignore
            match asmName with
            | Some n -> b.Append(", ").Append(n) |> ignore
            | None -> ()

            b.ToString()

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module SolvedType =
    let getUnderlyingSystemType = function
        | RuntimeType t
        | TypeParam(_, RuntimeTypeParam t)
        | InstantiationType(closeType = t) -> t
        | TypeParam(_, TypeParamBuilder t) -> upcast t
        | Builder { t = t } -> upcast t
        
[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module EmitException =
    let raiseEmitExn e = raise <| EmitException e

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module TypeSpec =
    let rec getReplacedType subst = function
        | TypeSpec(n, ts) -> TypeSpec(n, List.map (getReplacedType subst) ts)
        | TypeVar v as t ->
            match List.tryFind (fun (v',_) -> v = v') subst with
            | Some(_,t) -> getReplacedType subst t
            | None -> t

        | t -> t

    let applyType n ({ aTypeParams = ps; entity = t } as v) ts =
        if List.length ps <> List.length ts then EmitException.raiseEmitExn <| AliasKindError(n, ts, v)
        let rec eval = function
            | TypeSpec(n, ts) -> TypeSpec(n, List.map eval ts)
            | TypeVar v -> List.item (List.findIndex ((=) v) ps) ts
            | TypeArgRef i -> List.item i ts
            | _ -> failwith "unreach"
        eval t

    let solveTypeVarMap vs v = List.find (fst >> (=) v) vs |> snd
    let rec solveTypeCore ({ senv = { map = map; amap = amap }; varMap = varMap; mVarMap = mVarMap; typeArgs = typeArgs; mTypeArgs = mTypeArgs } as env) t =
        let getTypeDef map name =
            let mutable ti = Unchecked.defaultof<_>
            if HashMap.tryGet map name &ti then Builder ti
            else RuntimeType <| Type.GetType(FullName.toTypeName name, true)
        
        let rec aux t =
            let mutable ad = Unchecked.defaultof<_>
            match t with
            | TypeSpec(FullName(name, [], [], None), ts) when HashMap.tryGet amap name &ad ->
                solveTypeCore env (applyType name ad ts)
                
            | TypeSpec(pathRev, []) -> getTypeDef map pathRev
            | TypeSpec(pathRev, ts) ->
                let vs = List.map (solveTypeCore env) ts
                let ts = Seq.map SolvedType.getUnderlyingSystemType vs |> Seq.toArray
                match getTypeDef map pathRev with
                | Builder({ t = t } as ti) -> InstantiationType(t.MakeGenericType ts, Some ti)
                | RuntimeType t ->
                    let t = t.MakeGenericType ts
                    if List.forall (function RuntimeType _ -> true | _ -> false) vs then RuntimeType t
                    else InstantiationType(t, None)

                | _ -> failwith "unreach"

            | TypeVar v -> TypeParam(v, solveTypeVarMap varMap v)
            | MethodTypeVar v -> TypeParam(v, solveTypeVarMap mVarMap v)
            | TypeArgRef i -> List.item i typeArgs
            | MethodTypeArgRef i -> List.item i mTypeArgs
            | ThisType -> Option.get thisType
            | BaseType -> Option.get baseType
        aux t

    let solveType env t = solveTypeCore env t |> SolvedType.getUnderlyingSystemType
    let solveTypes env ts = Seq.map (solveType env) ts |> Seq.toArray
    let solveParamTypes env pars = Seq.map (Parameter.paramType >> solveType env) pars |> Seq.toArray
