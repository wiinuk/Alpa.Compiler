module Alpa.Emit.Solve

let getField env parent name =
    match solveTypeCore env parent with
    | TypeParam _ -> failwith "getField: TypeParam"
    | RuntimeType t -> t.GetField(name, B.DeclaredOnly ||| B.Static ||| B.Instance ||| B.Public ||| B.NonPublic)
    | Builder { fmap = fmap } -> upcast get fmap name
    | InstantiationType(tb, Some { fmap = fmap }) -> TypeBuilder.GetField(tb, get fmap name)
    | InstantiationType(tb, None) ->
        let fd = tb.GetGenericTypeDefinition().GetField(name, B.DeclaredOnly ||| B.Static ||| B.Instance ||| B.Public ||| B.NonPublic)
        TypeBuilder.GetField(tb, fd)

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