module Alpa.Emit.ILEmit
open Alpa.Emit
open Alpa.Emit.EmitException
open Alpa.Emit.FullName
open Alpa.Emit.HashMap
open Alpa.Emit.Parameter
open Alpa.Emit.SolvedType
open Alpa.Emit.TypeSpec
open Alpa.Emit.TypeVarMap
open Alpa.Emit.PreDefinedTypes
open Alpa.Emit.MethodHead
open Alpa.Emit.SolveEnv
open Alpa.Emit.ILMethodBuilder
open Alpa.Emit.ILTypeBuilder
open System
open System.Reflection.Emit

let defineVarMap typeParams defineGenericParameters =
    match typeParams with
    | [] -> emptyVarMap
    | _ ->
        let names = List.toArray typeParams
        TypeVarMap(typeParams, List.ofArray <| defineGenericParameters names)

let mDefineGP (m: MethodBuilder) xs = m.DefineGenericParameters xs
let tDefineGP (t: TypeBuilder) xs = t.DefineGenericParameters xs

module DefineTypes =
    let rec module'(defineType, toName, a, fullName, ({ map = map } as env), ({ mMembers = members } as md)) =
        let a = a ||| T.Abstract ||| T.Sealed
        let t = defineType(toName fullName, a)
        add map fullName <| newILTypeBuilder (Choice2Of2 md) t fullName env
        for m in members do moduleMember fullName t env m

    and type'(defineType, toName, a, fullName, ({ map = map } as env), ({ kind = kind; members = members } as d)) =
        let isInterfaceMember = function 
            | Literal _
            | Field _
            | MethodDef _
            | StaticMethodDef _
            | CtorDef _ 
            | CCtorDef _ -> false
            | AbstractDef _ -> true

        let kind =
            match kind with
            | Some k -> k
            | None ->
                match members with
                | [] -> Sealed
                | _ when List.forall isInterfaceMember members -> Interface
                | _ -> Sealed

        let a = 
            match kind with
            | Interface -> T.Abstract ||| T.Interface
            | Abstract -> T.Abstract
            | Sealed -> T.Sealed
            | Open -> T.Class
            ||| a
            ||| T.BeforeFieldInit

        let t = defineType(toName fullName, a)
        add map fullName <| newILTypeBuilder (Choice1Of2 d) t fullName env

    and moduleMember path (t: TypeBuilder) env = function
        | ModuleMethodDef _
        | ModuleCCtorDef _
        | ModuleValDef _ 
        | ModuleLiteralDef _ -> ()
        | ModuleModuleDef(name, ms) -> module'(t.DefineNestedType, getName, T.NestedPublic, addTypeName path name, env, ms)
        | ModuleTypeDef(name, td) -> type'(t.DefineNestedType, getName, T.NestedPublic, addTypeName path name, env, td)

    let topDef (m: ModuleBuilder) ({ amap = amap } as env) = function
        | TopModuleDef(path, ms) -> module'(m.DefineType, toTypeName, T.Public, ofTypeName path, env, ms)
        | TopTypeDef(name, td) -> type'(m.DefineType, toTypeName, T.Public, ofTypeName name, env, td)
        | TopAliasDef(name, ad) -> add amap name ad

let rec checkTypeParam aTypeParams = function
    | TypeSpec(_, ts) -> for t in ts do checkTypeParam aTypeParams t
    | TypeVar v ->
        if List.contains v aTypeParams then ()
        else raiseEmitExn <| UnownedAliasTypeParameter v

    | TypeArgRef i ->
        if List.length aTypeParams <= i then raiseEmitExn <| UnownedAliasTypeParameterRef i

    | MethodTypeArgRef i -> raiseEmitExn <| UnownedAliasTypeParameterRef i
    | MethodTypeVar v -> raiseEmitExn <| UnownedAliasTypeParameter v
    
let rec occur amap visitedNames = function
    | TypeSpec(FullName(n, [], [], None), ts) as t ->
        if List.contains n visitedNames then raiseEmitExn <| RecursiveAlias n

        let mutable v = Unchecked.defaultof<_>
        if tryGet amap n &v then
            let ts = List.map (occur amap visitedNames) ts
            occur amap (n::visitedNames) <| applyType n v ts
        else
            t

    | TypeSpec(n, ts) -> TypeSpec(n, List.map (occur amap visitedNames) ts)
    | t -> t

let checkAlias { amap = amap; map = map } =
    for kv in amap do
        let name, ({ aTypeParams = aTypeParams; entity = entity } as ad) = kv.Key, kv.Value

        match List.tryGetDuplicate aTypeParams with
        | Some x -> raiseEmitExn <| DuplicatedAliasTypeParameter x
        | _ -> ()

        checkTypeParam aTypeParams entity

        let mutable td = Unchecked.defaultof<_>
        if tryGet map (FullName(name, [], [], None)) &td then
            raiseEmitExn <| DuplicatedAliasName(name, ad, let { d = d } = td in d)

        let t = occur amap [name] entity
        assign amap name { aTypeParams = aTypeParams; entity = t }

let defineTypeParams { map = map } =
    for ({ d = d; t = t } as ti) in values map do
        match d with
        | Choice2Of2 _ -> ()
        | Choice1Of2 { typeParams = typeParams } ->
            ti.varMap <- defineVarMap typeParams <| tDefineGP t

let defineParam defineParameter i (Parameter(n, _)) = defineParameter(i, P.None, Option.toObj n) |> ignore
let defineParams defineParameter pars = List.iteri (fun i a -> defineParam defineParameter (i + 1) a) pars

let defineMethodHead ({ t = t } as ti) attr callconv (MethodHead(name,typeParams,pars,ret)) =
    let m = t.DefineMethod(name, attr, callconv)
    let mVarMap = defineVarMap typeParams <| mDefineGP m
    
    m.SetReturnType(solveType (envOfTypeBuilder mVarMap ti) (paramType ret))
    m.SetParameters(solveParamTypes (envOfTypeBuilder mVarMap ti) pars)

    defineParam m.DefineParameter 0 ret
    defineParams m.DefineParameter pars

    m, mVarMap

let defineMethodInfo dt a c (MethodInfo(head, _) as m) =
    let mb, mVarMap = defineMethodHead dt a c head
    addMethod dt head { m = m; mb = Choice1Of2 mb; mVarMap = mVarMap; dt = dt }

let defineMethodDef dt ov m =
    match ov with
    | None -> defineMethodInfo dt (M.Public ||| M.Final ||| M.HideBySig) CC.Standard m
    | Some Override ->
        let a = M.Public ||| M.Final ||| M.HideBySig ||| M.NewSlot ||| M.Virtual
        defineMethodInfo dt a CC.HasThis m

    | Some(BaseMethod _) ->
        let a = M.Private ||| M.Final ||| M.HideBySig ||| M.NewSlot ||| M.Virtual
        defineMethodInfo dt a CC.HasThis m
                // TODO: last path
//                        let bt = solveType map varMap <| typeRefToType baseType
//                        let pts = solveParamTypes map varMap pars
//                        let bm = bt.GetMethod(baseMethodName, pts)
//                        t.DefineMethodOverride(bm, m)
    
// (1) type name definition
// type IOrd`1 ... = ...;;
// type IMap`2 ... = ...;;
// type IntMap`1 ... = ...;;
// module Module =
//     type X = ...;
//     ...;;
//
// (2) type param definition
// type IOrd`1 a = ...;;
// type IMap`2(k <: IOrd, v) = ...;;
// type IntMap`1 v = ...;;
// module Module =
//     type X = ...;
//     ...;;
//
// (3) member definition
// type IOrd`1 a =
//     abstract CompareTo a : int;;
// type IMap`2(k <: IOrd, v) =
//     abstract Add(k, v) : void;;
// type IntMap`1 v <: object, IMap(int32, v) =
//     override Add(int32, v) : void = ...;;
// module Module =
//     type X = fun Member (a <: IOrd b, b) (a) : void = ...;
//     fun main () : void = ...;;
//
// (4) emit method body
// type IOrd`1 a =
//     abstract CompareTo a : int;;
// type IMap`2(k <: IOrd, v) =
//     abstract Add(k, v) : void;;
// type IntMap`1 v <: object, IMap(int32, v) =
//     override Add(int32, v) : void = ret;;
// module Module =
//     type X = fun Member (a <: IOrd b, b) (a) : void = ret;
//     fun main () : void = ret;;

let defineField ({ t = t; fmap = fmap } as ti) (isStatic, isMutable, name, ft) =
    let a = F.Public
    let a = if isStatic then a ||| F.Static else a
    let a = if isMutable then a else a ||| F.InitOnly
    let ft = solveType (envOfTypeBuilder emptyVarMap ti) ft
    let f = t.DefineField(name, ft, a)
    add fmap name f

let defineLiteral ({ t = t; fmap = fmap } as ti) name ft fv =
    let a = F.Public ||| F.Static ||| F.Literal
    let ft = solveType (envOfTypeBuilder emptyVarMap ti) ft
    let f = t.DefineField(name, ft, a)
    let literalValue = function
        | I1 v -> box v
        | U1 v -> box v
        | I2 v -> box v
        | U2 v -> box v
        | I4 v -> box v
        | U4 v -> box v
        | I8 v -> box v
        | U8 v -> box v
        | Bool v -> box v
        | F4 v -> box v
        | F8 v -> box v
        | Char v -> box v
        | String v -> box v
        | Null -> null

    f.SetConstant <| literalValue fv
    add fmap name f

let defineCCtor ({ t = t } as dt) body =
    let c = t.DefineTypeInitializer()
    dt.cctor <- Some {
        mb = Choice2Of2 c
        mVarMap = emptyVarMap
        dt = dt
        m = MethodInfo(cctorHead, body)
    }

let defineCtor ({ t = t } as dt) pars body =
    let pts = solveParamTypes (envOfTypeBuilder emptyVarMap dt) pars
    let c = t.DefineConstructor(M.SpecialName ||| M.RTSpecialName ||| M.Public, CC.HasThis, pts)
    defineParams c.DefineParameter pars
    addCtor dt {
        mb = Choice2Of2 c
        dt = dt
        mVarMap = emptyVarMap
        m = MethodInfo(ctorHead pars, body)
    }
    
let defineStaticMethod dt (MethodInfo(head, _) as m) =
    let mb, mVarMap = defineMethodHead dt (M.Public ||| M.Static) CC.Standard head
    addMethod dt head { mb = Choice1Of2 mb; mVarMap = mVarMap; m = m; dt = dt }

let defineMember dt = function
    | Field(isStatic, isMutable, n, ft) -> defineField dt (isStatic, isMutable, n, ft)
    | Literal(n, t, l) -> defineLiteral dt n t l
    | MethodDef(ov, m) -> defineMethodDef dt ov m
    | StaticMethodDef m -> defineStaticMethod dt m
    | CtorDef(pars, body) -> defineCtor dt pars body
    | CCtorDef body -> defineCCtor dt body
    | AbstractDef head ->
        let a = M.Public ||| M.HideBySig ||| M.NewSlot ||| M.Abstract ||| M.Virtual
        defineMethodHead dt a CC.HasThis head
        |> ignore

let defineTypeDef ({ t = t } as ti) { parent = parent; impls = impls; members = members } =
    let env = envOfTypeBuilder emptyVarMap ti

    match parent with
    | None -> ()
    | Some parent -> t.SetParent <| solveType env parent

    for impl in impls do t.AddInterfaceImplementation <| solveType env impl
    for m in members do defineMember ti m

let defineModuleMember dt = function
    | ModuleTypeDef _
    | ModuleModuleDef _ -> ()
    | ModuleValDef(isMutable, name, ft) -> defineField dt (true, isMutable, name, ft)
    | ModuleLiteralDef(name, ft, v) -> defineLiteral dt name ft v
    | ModuleMethodDef m -> defineStaticMethod dt m
    | ModuleCCtorDef b -> defineCCtor dt b

let defineMembers { map = map } =
    for { d = d } as ti in values map do
        match d with
        | Choice1Of2 td -> defineTypeDef ti td
        | Choice2Of2 { mMembers = members } ->
            for m in members do defineModuleMember ti m

let getField env parent name =
    match solveTypeCore env parent with
    | TypeParam _ -> failwith "getField: TypeParam"
    | RuntimeType t -> t.GetField(name, B.DeclaredOnly ||| B.Static ||| B.Instance ||| B.Public ||| B.NonPublic)
    | Builder { fmap = fmap } -> upcast get fmap name
    | InstantiationType(tb, Some { fmap = fmap }) -> TypeBuilder.GetField(tb, get fmap name)
    | InstantiationType(tb, None) ->
        let fd = tb.GetGenericTypeDefinition().GetField(name, B.DeclaredOnly ||| B.Static ||| B.Instance ||| B.Public ||| B.NonPublic)
        TypeBuilder.GetField(tb, fd)

//type IsMethodBase<'m> = {
//    getMTypeParams: 'm -> SolvedType list
//    getParameters: 'm -> SolvedType list
//}
//type IsMethodInfo<'m,'i,'b> = {
//    baseClass: IsMethodBase<'b>
//    toBase: 'm -> 'b
//    getSystemMethod: 'm -> 'i
//}
//type IsType<'t,'m,'c> = {
//    getMethodsOfName: string -> 't -> 'm seq
//    getCtors: 't -> 'c seq
//    getTypeParams: 't -> SolvedType list
//}
let parameterType (p: Reflection.ParameterInfo) = p.ParameterType

//let isMethodBaseOfRt = {
//    getMTypeParams = fun (m: Reflection.MethodBase) -> if m.IsGenericMethod then m.GetGenericArguments() |> Seq.map RuntimeType |> Seq.toList else []
//    getParameters = fun m ->
//        m.GetParameters()
//        |> Seq.map (parameterType >> RuntimeType)
//        |> Seq.toList
//}
//let isMethodInfoOfRt = {
//    baseClass = isMethodBaseOfRt
//    toBase = fun (m: Reflection.MethodInfo) -> upcast m
//    getSystemMethod = id
//}
//let isCtorOfRt = {
//    baseClass = isMethodBaseOfRt
//    toBase = fun (m: Reflection.ConstructorInfo) -> upcast m
//    getSystemMethod = id
//}
//let isTypeOfRt = {
//    getMethodsOfName = fun name (t: Type) -> t.GetMethods(B.DeclaredOnly ||| B.Public ||| B.NonPublic ||| B.Static ||| B.Instance) |> Seq.filter (fun m -> m.Name = name)
//    getCtors = fun t -> upcast t.GetConstructors(B.DeclaredOnly ||| B.Public ||| B.NonPublic ||| B.Instance)
//    getTypeParams = fun t -> t.GetGenericArguments() |> Seq.map RuntimeType |> Seq.toList
//}

let toTypeParams (TypeVarMap(typeParams, typeParams')) = List.map2 (fun t t' -> TypeParam(t, TypeParamBuilder t')) typeParams typeParams'

//let isMethodInfoOfTb = {
//    baseClass =
//        {
//        getMTypeParams = fun { ILMethodBuilder.mVarMap = mVarMap } -> toTypeParams mVarMap
//        getParameters = fun { dt = dt; mVarMap = mVarMap; m = MethodInfo(MethodHead(pars=pars),_) } ->
//            List.map (paramType >> solveTypeCore (envOfTypeBuilder mVarMap dt)) pars
//        }
//    toBase = id
//    getSystemMethod = fun { mb = mb } -> mb
//}
//let isCtorOfTb = {
//    baseClass =
//        {
//        getMTypeParams = fun _ -> []
//        getParameters = fun { dt = dt; pars = pars } ->
//            List.map (paramType >> solveTypeCore (envOfTypeBuilder emptyVarMap dt)) pars
//        }
//    toBase = id
//    getSystemMethod = fun { cb = cb } -> cb
//}
//let isTypeOfTb = {
//    getMethodsOfName = fun name { mmap = mmap } -> upcast get mmap name
//    getCtors = fun { cmap = cmap } -> upcast cmap
//    getTypeParams = fun { varMap = varMap } -> toTypeParams varMap
//}

/// require: closeType.GetType().Name = "RuntimeType" && closeType.IsGenericType
let getMemberOfRuntimeOpenType getMembers resolveMember (closeType: Type) (memberOfOpenType: Reflection.MemberInfo) =
    let openTypeParemeters = closeType.GetGenericTypeDefinition().GetGenericArguments()
    let methodGerenicArgs =
        match memberOfOpenType with 
        | :? Reflection.MethodBase as m when m.IsGenericMethod -> m.GetGenericArguments()
        | _ -> Type.EmptyTypes

    let mOpenTypeMd = memberOfOpenType.MetadataToken
    getMembers closeType (B.DeclaredOnly ||| B.Public ||| B.NonPublic ||| B.Instance ||| B.Static)
    |> Seq.find (fun (m: #Reflection.MemberInfo) ->
        m.Name = memberOfOpenType.Name &&
        let m' : Reflection.MemberInfo = resolveMember m.Module m.MetadataToken openTypeParemeters methodGerenicArgs
        m'.MetadataToken = mOpenTypeMd
    )

//let getMethodOfRuntimeOpenType closeType (methodOfOpenType: Reflection.MethodInfo) =
//    getMemberOfRuntimeOpenType
//        (fun t b -> t.GetMethods b)
//        (fun m md tps mtps -> upcast m.ResolveMethod(md, tps, mtps))
//        closeType methodOfOpenType
//
//let getCtorOfRuntimeOpenType closeType (ctorOfOpenType: Reflection.ConstructorInfo) =
//    getMemberOfRuntimeOpenType
//        (fun t b -> t.GetConstructors b)
//        (fun m md tps mtps -> upcast m.ResolveMethod(md, tps, mtps))
//        closeType ctorOfOpenType
//
//let getGenericMethod
//    { IsType.getMethodsOfName = getMethodsOfName; getTypeParams = getTypeParams }
//    { IsMethodInfo.getSystemMethod = getSystemMethod
//      toBase = toBase
//      baseClass = { getMTypeParams = getMTypeParams; getParameters = getParameters }}
//    (env, closeType, openType, name, mTypeArgs, argTypes) =
//
//    let typeParams = getTypeParams openType
//    let filter m =
//        let m = toBase m
//        let mTypeParams = getMTypeParams m
//        List.length mTypeParams = List.length mTypeArgs &&
//        let env = { env with typeArgs = typeParams; mTypeArgs = mTypeParams }
//        let pars = getParameters m
//        List.length pars = List.length argTypes &&
//        let methodParamTypesOfOpenType = solveTypes env argTypes
//        Seq.forall2 (=) methodParamTypesOfOpenType (List.map getUnderlyingSystemType pars)
//
//    let openMethodOfOpenType =
//        getMethodsOfName name openType
//        |> Seq.toList
//        |> List.filter filter
//        |> List.exactlyOne
//
//    let openMethodOfCloseType = TypeBuilder.GetMethod(closeType, getSystemMethod openMethodOfOpenType)
//
//    let mTypeArgs = Seq.map (solveType env) mTypeArgs |> Seq.toArray
//    if openMethodOfCloseType.IsGenericMethodDefinition then openMethodOfCloseType.MakeGenericMethod mTypeArgs
//    else openMethodOfCloseType

let getMethodGeneric (getMethodTypeParams, getParemeterTypes, getReturnType, typeEq, getOpenType, getTypeParams, getMethods, solveMethodOfCloseType, makeCloseMethod) env parent annot =
    let mTypeArgs, getOpenMethodOfOpenType =
        match annot with
        | None -> [], fun _ ms -> Seq.exactlyOne ms
        | Some(MethodTypeAnnotation(mTypeArgs, argTypes, returnType)) ->
            let filter env m =
                let mTypeParams = getMethodTypeParams m
                let env =
                    match mTypeParams with
                    | [] -> env
                    | _ -> { env with mTypeArgs = mTypeParams }

                let mParamTypes = getParemeterTypes env m

                match returnType with
                | None -> true
                | Some returnType ->
                    typeEq (solveTypeCore env returnType) (getReturnType env m)
                &&
                List.length mParamTypes = List.length argTypes &&
                let argTypes = List.map (solveTypeCore env) argTypes
                List.forall2 typeEq mParamTypes argTypes

            let select openTypeParams ms =
                Seq.filter (filter { env with typeArgs = openTypeParams }) ms
                |> Seq.exactlyOne

            mTypeArgs, select

    let openType = getOpenType parent
    let openTypeParams = getTypeParams openType
    let openMethodsOfOpenType = getMethods openType

    let openMethodOfOpenType = getOpenMethodOfOpenType openTypeParams openMethodsOfOpenType
    let mTypeArgs = List.map (solveTypeCore env) mTypeArgs

    let openMethodOfCloseType = solveMethodOfCloseType parent openMethodOfOpenType
    makeCloseMethod openMethodOfCloseType mTypeArgs

let getMethodBaseOfRuntimeType env parent getMethods getAllMethods annot =
    let getMethodTypeParams (m: Reflection.MethodBase) =
        match m.IsGenericMethod, m with
        | true, (:? Reflection.MethodInfo as m) ->
            let ts = m.GetGenericMethodDefinition().GetGenericArguments()
            [for t in ts -> RuntimeType t]
        | _ -> []

    let getParemeterTypes _ (m: Reflection.MethodBase) = [for p in m.GetParameters() -> RuntimeType p.ParameterType]
    let getReturnType _ (m: Reflection.MethodBase) =
        match m with
        | :? Reflection.MethodInfo as m -> RuntimeType m.ReturnType
        | _ -> RuntimeType typeof<Void>

    let typeEq l r = getUnderlyingSystemType l = getUnderlyingSystemType r
    let getOpenType (t: Type) = if t.IsGenericType then t.GetGenericTypeDefinition() else t
    let getTypeParams (t: Type) = if t.IsGenericType then [for t in t.GetGenericArguments() -> RuntimeType t] else []
    
    let solveMethodOfCloseType (closeParent: Type) (openMethodOfOpenType: Reflection.MethodBase) =
        if closeParent.IsGenericType then
            getMemberOfRuntimeOpenType
                getAllMethods
                (fun m md tps mtps -> upcast m.ResolveMethod(md, tps, mtps))
                closeParent openMethodOfOpenType
        else openMethodOfOpenType

    let makeCloseMethod (openMethod: Reflection.MethodBase) = function
        | [] -> openMethod
        | mTypeArgs ->
            let ts = Seq.map getUnderlyingSystemType mTypeArgs |> Seq.toArray
            upcast (openMethod :?> Reflection.MethodInfo).MakeGenericMethod ts

    getMethodGeneric(getMethodTypeParams, getParemeterTypes, getReturnType, typeEq, getOpenType, getTypeParams, getMethods, solveMethodOfCloseType, makeCloseMethod) env parent annot

let getMethodBaseOfNonGenericTypeBuilder env parent getMethods annot =
    let getMethodTypeParams { ILMethodBuilder.mVarMap = TypeVarMap(vs,vs') } =
        List.map2(fun v v' -> TypeParam(v, TypeParamBuilder v')) vs vs'

    let getParemeterTypes env { m = MethodInfo(MethodHead(pars=pars), _) } = List.map (paramType >> solveTypeCore env) pars
    let getReturnType env {  m = MethodInfo(MethodHead(ret=ret), _) } = paramType ret |> solveTypeCore env
    let typeEq l r = getUnderlyingSystemType l = getUnderlyingSystemType r
    let getOpenType t = t
    let getTypeParams { ILTypeBuilder.varMap = TypeVarMap(vs,vs') } = 
        List.map2(fun v v' -> TypeParam(v, TypeParamBuilder v')) vs vs'
    let solveMethodOfCloseType _ m = m
    let makeCloseMethod m = function
        | [] -> getUnderlyingSystemMethod m
        | mTypeArgs ->
            let ts = Seq.map getUnderlyingSystemType mTypeArgs |> Seq.toArray
            match getUnderlyingSystemMethod m with
            | :? Reflection.MethodInfo as m -> upcast m.MakeGenericMethod ts
            | _ -> failwith "error"

    getMethodGeneric(getMethodTypeParams, getParemeterTypes, getReturnType, typeEq, getOpenType, getTypeParams, getMethods, solveMethodOfCloseType, makeCloseMethod) env parent annot

let getMethodBaseOfCloseTypeBuilder env parent getMethods annot =
    let getMethodTypeParams { ILMethodBuilder.mVarMap = TypeVarMap(vs,vs') } =
        List.map2(fun v v' -> TypeParam(v, TypeParamBuilder v')) vs vs'

    let getParemeterTypes env { m = MethodInfo(MethodHead(pars=pars), _) } = List.map (paramType >> solveTypeCore env) pars
    let getReturnType env { m = MethodInfo(MethodHead(ret=ret), _) } = paramType ret |> solveTypeCore env
    let typeEq l r = getUnderlyingSystemType l = getUnderlyingSystemType r
    let getOpenType = snd
    let getTypeParams { ILTypeBuilder.varMap = TypeVarMap(vs,vs') } = 
        List.map2(fun v v' -> TypeParam(v, TypeParamBuilder v')) vs vs'
    let solveMethodOfCloseType (closeType, _) { mb = openMethodOfOpenType } =
        match openMethodOfOpenType with
        | Choice1Of2 m -> TypeBuilder.GetMethod(closeType, m) :> Reflection.MethodBase
        | Choice2Of2 m -> TypeBuilder.GetConstructor(closeType, m) :> _

    let makeCloseMethod (openMethod: Reflection.MethodBase) = function
        | [] -> openMethod
        | mTypeArgs ->
            let ts = Seq.map getUnderlyingSystemType mTypeArgs |> Seq.toArray
            upcast (openMethod :?> Reflection.MethodInfo).MakeGenericMethod ts

    getMethodGeneric(getMethodTypeParams, getParemeterTypes, getReturnType, typeEq, getOpenType, getTypeParams, getMethods, solveMethodOfCloseType, makeCloseMethod) env parent annot

let getMethodBaseOfRuntimeTypeOfTypeBuilder env parent getMethods annot =
    let getMethodTypeParams (m: Reflection.MethodBase) =
        match m.IsGenericMethod, m with
        | true, (:? Reflection.MethodInfo as m) ->
            let ts = m.GetGenericMethodDefinition().GetGenericArguments()
            [for t in ts -> RuntimeType t]
        | _ -> []

    let getParemeterTypes _ (m: Reflection.MethodBase) = [for p in m.GetParameters() -> RuntimeType p.ParameterType]
    let getReturnType _ (m: Reflection.MethodBase) =
        match m with
        | :? Reflection.MethodInfo as m -> RuntimeType m.ReturnType
        | _ -> RuntimeType typeof<Void>

    let typeEq l r = getUnderlyingSystemType l = getUnderlyingSystemType r
    let getOpenType (t: Type) = if t.IsGenericType then t.GetGenericTypeDefinition() else t
    let getTypeParams (t: Type) = if t.IsGenericType then [for t in t.GetGenericArguments() -> RuntimeType t] else []
    
    let solveMethodOfCloseType closeType (openMethodOfOpenType: Reflection.MethodBase) =
        match openMethodOfOpenType with
        | :? Reflection.MethodInfo as m -> TypeBuilder.GetMethod(closeType, m) :> Reflection.MethodBase
        | :? Reflection.ConstructorInfo as m -> TypeBuilder.GetConstructor(closeType, m) :> _
        | _ -> raise <| NotImplementedException()

    let makeCloseMethod (openMethod: Reflection.MethodBase) = function
        | [] -> openMethod
        | mTypeArgs ->
            let ts = Seq.map getUnderlyingSystemType mTypeArgs |> Seq.toArray
            upcast (openMethod :?> Reflection.MethodInfo).MakeGenericMethod ts

    getMethodGeneric(getMethodTypeParams, getParemeterTypes, getReturnType, typeEq, getOpenType, getTypeParams, getMethods, solveMethodOfCloseType, makeCloseMethod) env parent annot

let getMethodOfRuntimeType env parent name annot =
    let getAllMethods (t: Type) b = t.GetMethods b |> Seq.map(fun m -> m :> Reflection.MethodBase)

    let getMethods t =
        B.DeclaredOnly ||| B.Public ||| B.NonPublic ||| B.Static ||| B.Instance
        |> getAllMethods t
        |> Seq.filter (fun m -> m.Name = name) 

    getMethodBaseOfRuntimeType env parent getMethods getAllMethods annot :?> Reflection.MethodInfo

let getMethodOfNonGenericTypeBuilder env parent name annot =
    getMethodBaseOfNonGenericTypeBuilder env parent (fun { mmap = mmap } -> get mmap name) annot
    :?> Reflection.MethodInfo

let getMethodOfCloseTypeBuilder env parent name annot =
    getMethodBaseOfCloseTypeBuilder env parent (fun { mmap = mmap } -> get mmap name) annot
    :?> Reflection.MethodInfo

let getMethodOfRuntimeTypeOfTypeBuilder env parent name annot =
    let getMethods (t: Type) =
        B.DeclaredOnly ||| B.Public ||| B.NonPublic ||| B.Static ||| B.Instance
        |> t.GetMethods
        |> Seq.filter (fun m -> m.Name = name)

    getMethodBaseOfRuntimeTypeOfTypeBuilder env parent getMethods annot
    :?> Reflection.MethodInfo

let getMethod env parent name annot =
    match solveTypeCore env parent with
    | TypeParam _ -> failwith ""
    | RuntimeType parent -> getMethodOfRuntimeType env parent name annot
    | Builder parent -> getMethodOfNonGenericTypeBuilder env parent name annot
    | InstantiationType(closeType, Some openType) -> getMethodOfCloseTypeBuilder env (closeType, openType) name annot
    | InstantiationType(closeType, None) -> getMethodOfRuntimeTypeOfTypeBuilder env closeType name annot

//let getMethod env parent name annot =
//    let a = B.DeclaredOnly ||| B.Static ||| B.Instance ||| B.Public ||| B.NonPublic
//    let c = CC.Any
//
//    let parent = solveTypeCore env parent
//
//    match annot with
//    | None -> None, Seq.exactlyOne
//    | Some(MethodTypeAnnotation(mTypeArgs, argTypes, None)) ->
//
//        match parent with
//        | TypeParam _ -> failwith "TypeParam"
//        | RuntimeType t ->
//            if t.IsGenericType then
//                let openType = t.GetGenericTypeDefinition()
//                let typeParams = openType.GetGenericArguments()
//                let env = { env with typeArgs = Seq.map RuntimeType typeParams |> Seq.toList }
//                let argTypes = Seq.map (solveType env) argTypes |> Seq.toArray
//                let methodOfOpenType = openType.GetMethod(name, B.DeclaredOnly ||| B.Public ||| B.NonPublic ||| B.Static ||| B.Instance, null, argTypes, null)
//                getMethodOfRuntimeOpenType t methodOfOpenType
//            else
//                let argTypes = Seq.map (solveType env) argTypes |> Seq.toArray
//                t.GetMethod(name, a, null, c, argTypes, null)
//
//        | Builder { mmap = mmap } ->
//            let { mb = mb } =
//                get mmap name
//                |> List.filter (fun { mVarMap = TypeVarMap(mTypeParams,_); m = MethodInfo(MethodHead(_,tpars,pars,_),_) } ->
//                    List.length tpars = List.length mTypeArgs &&
//                    List.length pars = List.length argTypes &&
//                    let subst = List.zip mTypeParams mTypeArgs
//                    List.forall2
//                        (fun (Parameter(_,parT)) argT -> getReplacedType subst parT = argT)
//                        pars
//                        argTypes
//                )
//                |> List.exactlyOne
//            upcast mb
//
//        | InstantiationType(closeType, None) -> getGenericMethod isTypeOfRt isMethodInfoOfRt (env, closeType, closeType.GetGenericTypeDefinition(), name, mTypeArgs, argTypes)
//        | InstantiationType(closeType, Some openType) -> getGenericMethod isTypeOfTb isMethodInfoOfTb (env, closeType, openType, name, mTypeArgs, argTypes)

//let getGenericCtor
//    { IsType.getCtors = getCtors; getTypeParams = getTypeParams }
//    { IsMethodInfo.baseClass = { getParameters = getParameters }; toBase = toBase; getSystemMethod = getSystemMethod }
//    (env, closeType, openType, argTypes) =
//
//    let typeParams = getTypeParams openType
//    let m =
//        getCtors openType
//        |> Seq.toList
//        |> List.filter (fun m ->
//            let m = toBase m
//            let pars = getParameters m
//            List.length pars = List.length argTypes &&
//            let genericMethodDefParamTypes = solveTypes { env with typeArgs = typeParams } argTypes
//            let paramTypes = Seq.map getUnderlyingSystemType pars
//            Seq.forall2 (=) genericMethodDefParamTypes paramTypes
//        )
//        |> List.exactlyOne
//
//    TypeBuilder.GetConstructor(closeType, getSystemMethod m)

//let getCtor env parent argTypes =
//    match solveTypeCore env parent with
//    | TypeParam _ -> failwith "TypeParam"
//    | RuntimeType t ->
//        if t.IsGenericType then
//            let openType = t.GetGenericTypeDefinition()
//            let typeParams = openType.GetGenericArguments()
//            let env = { env with typeArgs = Seq.map RuntimeType typeParams |> Seq.toList }
//            let argTypes = Seq.map (solveType env) argTypes |> Seq.toArray
//            let ctorOfOpenType = openType.GetConstructor(B.DeclaredOnly ||| B.Public ||| B.NonPublic ||| B.Instance, null, argTypes, null)
//            getCtorOfRuntimeOpenType t ctorOfOpenType
//        else
//            let argTypes = Seq.map (solveType env) argTypes |> Seq.toArray
//            t.GetConstructor(B.DeclaredOnly ||| B.Public ||| B.NonPublic ||| B.Instance, null, CC.Any, argTypes, null)
//
//    | Builder { cmap = cmap } ->
//        let argTypes = solveTypes env argTypes
//        let { cb = cb } =
//            cmap
//            |> Seq.filter (fun { cb = cb } ->
//                let pars = cb.GetParameters()
//                Array.length pars = Array.length argTypes &&
//                Array.forall2 (fun p t -> parameterType p = t) pars argTypes
//            )
//            |> Seq.exactlyOne
//        upcast cb
//        
//    | InstantiationType(closeType, None) -> getGenericCtor isTypeOfRt isCtorOfRt (env, closeType, closeType.GetGenericTypeDefinition(), argTypes)
//    | InstantiationType(closeType, Some openType) -> getGenericCtor isTypeOfTb isCtorOfTb (env, closeType, openType, argTypes)

let emitInstr (g: ILGenerator) mVarMap dt (Instr(label, op, operand)) =
    match operand with
    | OpNone -> g.Emit op
    | OpI1 n -> g.Emit(op, n)
    | OpI2 n -> g.Emit(op, n)
    | OpI4 n -> g.Emit(op, n)
    | OpI8 n -> g.Emit(op, n)
    | OpF4 n -> g.Emit(op, n)
    | OpF8 n -> g.Emit(op, n)
    | OpString s -> g.Emit(op, s)
    | OpType t -> g.Emit(op, solveType (envOfTypeBuilder mVarMap dt) t)
    | OpField(parent, name) -> g.Emit(op, getField (envOfTypeBuilder mVarMap dt) parent name)
    | OpMethod(parent, name, annot) -> g.Emit(op, getMethod (envOfTypeBuilder mVarMap dt) parent name annot)
    | OpCtor(parent, argTypes) -> g.Emit(op, getCtor (envOfTypeBuilder mVarMap dt) parent argTypes)

let emitMethod g mVarMap dt (MethodBody instrs) =
    for instr in instrs do emitInstr g mVarMap dt instr

let emitMethods { map = map } =
    for { mmap = mmap; cmap = cmap; cctor = cctor } in values map do
        for mis in values mmap do
            for { mb = mb; mVarMap = mVarMap; dt = dt; m = MethodInfo(_, b) } in mis do
                emitMethod (mb.GetILGenerator()) mVarMap dt b

        for { cb = cb; dt = dt; body = body } in cmap do
            emitMethod (cb.GetILGenerator()) emptyVarMap dt body

        match cctor with
        | None -> ()
        | Some { cb = cb; dt = dt; body = body } ->
            emitMethod (cb.GetILGenerator()) emptyVarMap dt body

let createTypes { map = map } = for { t = t } in values map do t.CreateType() |> ignore

let emitIL m { topDefs = ds } =
    let env = { map = HashMap(); amap = AliasMap() }
    for d in ds do DefineTypes.topDef m env d
    checkAlias env
    defineTypeParams env
    defineMembers env
    emitMethods env
    createTypes env