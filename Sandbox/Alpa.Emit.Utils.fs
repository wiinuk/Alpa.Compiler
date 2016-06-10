namespace Alpa.Emit
open System

[<AutoOpen>]
module internal InternalShortNames =
    type B = System.Reflection.BindingFlags
    type CC = System.Reflection.CallingConventions
    type T = System.Reflection.TypeAttributes
    type M = System.Reflection.MethodAttributes
    type P = System.Reflection.ParameterAttributes
    type F = System.Reflection.FieldAttributes
    type O = System.Reflection.Emit.OpCodes

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
module TypeVarMap =
    let emptyVarMap = TypeVarMap([], [])
    let typeParams (TypeVarMap(p,_)) = p
    let typeVarMapToSolvedType (TypeVarMap(vs,vs')) = Seq.map2 (fun v v' -> TypeParam(v, v')) vs vs'

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

    let addTypeName (FullName(name, nestersRev, nsRev, asmName)) typeName =
        FullName(typeName, name::nestersRev, nsRev, asmName)

    let ofTypeName (typeName, nsRev) = FullName(typeName, [], nsRev, None)
    let getName (FullName(name=name)) = name

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module SolveEnv =    
    open TypeVarMap
    let envOfTypeBuilder mVarMap ({ env = env; varMap = varMap } as ti) = {
        senv = env
        sVarMap = varMap
        sMVarMap = mVarMap
        typeArgs = []
        mTypeArgs = []
    }

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module SolvedType =
    let getUnderlyingSystemType = function
        | RuntimeType t
        | InstantiationType(closeType = t) -> t
        | TypeParam(_, t) -> upcast t
        | Builder { t = t } -> upcast t
        
    let typeEq l r = getUnderlyingSystemType l = getUnderlyingSystemType r

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module EmitException =
    let raiseEmitExn e = raise <| EmitException e
    
[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module TypeSpec =
    open HashMap

    let sysTypeValidate (t: Type) =
        if t.IsNested then failwithf "%A is GenericParameter." t
        if t.IsGenericParameter then failwithf "%A is GenericParameter." t

    let getPath t =
        sysTypeValidate t
        let nsRev =
            t.Namespace.Split Type.Delimiter
            |> Seq.rev
            |> Seq.toList

        FullName(t.Name, [], nsRev, Some(t.Assembly.GetName().Name))

    let rec typeOfT t =
        let rec typeOfTypeArgs (t: Type) = 
            if not t.IsGenericType then []
            else t.GetGenericArguments() |> Seq.map typeOfT |> Seq.toList

        TypeSpec(getPath t, typeOfTypeArgs t)

    [<RequiresExplicitTypeArguments>]
    let typeOf<'a> = typeOfT typeof<'a>

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

    let solveTypeVarMap (TypeVarMap(vs,vs')) v = List.item (List.findIndex ((=) v) vs) vs'
    let rec solveTypeCore ({ senv = { map = map; amap = amap }; sVarMap = varMap; sMVarMap = mVarMap; typeArgs = typeArgs; mTypeArgs = mTypeArgs } as env) t =
        let getTypeDef map name =
            let mutable ti = Unchecked.defaultof<_>
            if tryGet map name &ti then Builder ti
            else RuntimeType <| Type.GetType(FullName.toTypeName name, true)
        
        let rec aux t =
            let mutable ad = Unchecked.defaultof<_>
            match t with
            | TypeSpec(FullName(name, [], [], None), ts) when tryGet amap name &ad ->
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
        aux t

    let solveType env t = solveTypeCore env t |> SolvedType.getUnderlyingSystemType
    let solveTypes env ts = Seq.map (solveType env) ts |> Seq.toArray
    let solveParamTypes env pars = Seq.map (fun (Parameter(_,t)) -> solveType env t) pars |> Seq.toArray

module PreDefinedTypes =
    open TypeSpec

    let int8T = typeOf<int8>
    let int16T = typeOf<int16>
    let int32T = typeOf<int32>
    let int64T = typeOf<int64>
    
    let uint8T = typeOf<uint8>
    let uint16T = typeOf<uint16>
    let uint32T = typeOf<uint32>
    let uint64T = typeOf<uint64>
    
    let float32T = typeOf<single>
    let float64T = typeOf<double>

    let voidT = typeOfT typeof<System.Void>
    let boolT = typeOf<bool>
    let charT = typeOf<Char>
    let stringT = typeOf<string>
    let objectT = typeOf<obj>
    
[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Parameter =
    let paramType (Parameter(_,t)) = t
    let voidParam = Parameter(None, PreDefinedTypes.voidT)

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module MethodHead =
    let cctorHead = MethodHead(".cctor", [], [], Parameter.voidParam)
    let ctorHead pars = MethodHead(".ctor", [], pars, Parameter.voidParam)

module Member =
    open System.Reflection
    let metadataToken (m: MemberInfo) = m.MetadataToken
    let name (m: MemberInfo) = m.Name
    let getGenericArguments (m: MemberInfo) =
        match m with 
        | :? Reflection.MethodBase as m when m.IsGenericMethod -> m.GetGenericArguments()
        | _ -> Type.EmptyTypes

module Type =
    let isGeneric (t: Type) = t.IsGenericType
    let getOpenType t = if isGeneric t then t.GetGenericTypeDefinition() else t
    let getTypeParams t = if isGeneric t then t.GetGenericTypeDefinition().GetGenericArguments() else Type.EmptyTypes

    let getAllMethods (t: Type) =
        B.DeclaredOnly ||| B.Public ||| B.NonPublic ||| B.Static ||| B.Instance
        |> t.GetMethods

    let getMethods name t = getAllMethods t |> Seq.filter (fun m -> m.Name = name)
    let getConstructors (t: Type) = t.GetConstructors(B.DeclaredOnly ||| B.Public ||| B.NonPublic ||| B.Instance)

module Method =
    open System.Reflection
    let getTypeParams (m: MethodInfo) = if m.IsGenericMethod then m.GetGenericMethodDefinition().GetGenericArguments() else [||]

module MethodBase =
    open System.Reflection
    let getTypeParams : MethodBase -> _ = function
        | :? MethodInfo as m -> Method.getTypeParams m
        | _ -> Type.EmptyTypes

    let getParemeterTypes (m: MethodBase) = m.GetParameters() |> Seq.map (fun p -> p.ParameterType)

    let getReturnType (m: MethodBase) =
        match m with
        | :? MethodInfo as m -> m.ReturnType
        | _ -> typeof<Void>
        
    let makeCloseMethod openMethod mTypeArgs =
        if Seq.isEmpty mTypeArgs then openMethod
        else
            let m = (openMethod: MethodBase) :?> Reflection.MethodInfo
            upcast m.MakeGenericMethod(Seq.toArray mTypeArgs)

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module ILMethodBuilder =
    open Parameter
    open SolvedType

    let getUnderlyingSystemMethod { mb = m } =
        match m with
        | Choice1Of2 m -> m :> Reflection.MethodBase
        | Choice2Of2 m -> upcast m

    let getTypeParams { ILMethodBuilder.mVarMap = mVarMap } = mVarMap
    let getParemeterTypes { m = MethodInfo(MethodHead(pars=pars), _) } = Seq.map paramType pars
    let getReturnType { m = MethodInfo(MethodHead(ret=ret), _) } = paramType ret
    let makeCloseMethod m mTypeArgs =
        Seq.map getUnderlyingSystemType mTypeArgs
        |> MethodBase.makeCloseMethod (getUnderlyingSystemMethod m)

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module ILTypeBuilder =
    open HashMap

    let addMethod { mmap = mmap } (MethodHead(name=sign)) m =
        let mutable ms = Unchecked.defaultof<_>
        if tryGet mmap sign &ms then assign mmap sign (m::ms)
        else add mmap sign [m]

    let addCtor { cmap = cmap } c = cmap.Add c
    
    let newILTypeBuilder d t path env = {
        d = d
        t = t
        path = path
        varMap = TypeVarMap.emptyVarMap
        env = env
        cctor = None
        mmap = HashMap()
        cmap = CtorMap()
        fmap = HashMap()
    }
    let getMethods name { mmap = mmap } = HashMap.get mmap name |> List.toSeq
    let getTypeParams { varMap = varMap } = varMap
    let getConstructors { cmap = cmap } = cmap :> _ seq
