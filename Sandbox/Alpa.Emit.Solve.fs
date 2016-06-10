module Alpa.Emit.Solve
open System
open System.Reflection.Emit
open Alpa.Emit
open Alpa.Emit.TypeSpec
open Alpa.Emit.TypeVarMap
open Alpa.Emit.SolvedType
open Alpa.Emit.Parameter
open Alpa.Emit.HashMap
open Alpa.Emit.ILTypeBuilder
open Alpa.Emit.ILMethodBuilder
open Alpa.Emit.Member

/// require: closeType.GetType().Name = "RuntimeType" && closeType.IsGenericType
let getMemberOfRuntimeOpenType getMembers resolveMember closeType memberOfOpenType =
    let openTypeParemeters = Type.getTypeParams closeType
    let methodGerenicArgs = Member.getGenericArguments memberOfOpenType

    let mOpenTypeMd = metadataToken memberOfOpenType
    getMembers closeType
    |> Seq.find (fun m ->
        Member.name m = Member.name memberOfOpenType &&
        resolveMember m.Module m.MetadataToken openTypeParemeters methodGerenicArgs
        |> Member.metadataToken = mOpenTypeMd
    )

type Solver<'t,'ot,'m> =
    abstract GetMethodTypeParams: 'm -> SolvedType seq
    abstract GetParemeterTypes: SolveEnv * 'm -> SolvedType seq
    abstract GetReturnType: SolveEnv * 'm -> SolvedType
    abstract GetOpenType: 't -> 'ot
    abstract GetTypeParams: 'ot -> SolvedType seq
    abstract GetMethods: 'ot -> 'm seq
    abstract SolveMethodOfCloseType: 't * 'm -> Reflection.MethodBase

let getMethodGeneric env parent annot (s: Solver<_,_,_>) =
    let mTypeArgs, getOpenMethodOfOpenType =
        match annot with
        | None -> [], fun _ ms -> Seq.exactlyOne ms
        | Some(MethodTypeAnnotation(mTypeArgs, argTypes, returnType)) ->
            let filter env m =
                let mTypeParams = s.GetMethodTypeParams m |> Seq.cache
                let env =
                    if Seq.isEmpty mTypeParams then env
                    else { env with mTypeArgs = Seq.toList mTypeParams }

                let mParamTypes = s.GetParemeterTypes(env, m) |> Seq.cache

                match returnType with
                | None -> true
                | Some returnType ->
                    typeEq (solveTypeCore env returnType) (s.GetReturnType(env, m))
                &&
                Seq.length mParamTypes = List.length argTypes &&
                let argTypes = List.map (solveTypeCore env) argTypes
                Seq.forall2 typeEq mParamTypes argTypes

            let select openTypeParams ms =
                Seq.filter (filter { env with typeArgs = Seq.toList openTypeParams }) ms
                |> Seq.exactlyOne

            mTypeArgs, select

    let openType = s.GetOpenType parent
    let openTypeParams = s.GetTypeParams openType
    let openMethodsOfOpenType = s.GetMethods openType

    let openMethodOfOpenType = getOpenMethodOfOpenType openTypeParams openMethodsOfOpenType
    let mTypeArgs = List.map (solveTypeCore env) mTypeArgs

    let openMethodOfCloseType = s.SolveMethodOfCloseType(parent, openMethodOfOpenType)
    Seq.map getUnderlyingSystemType mTypeArgs
    |> MethodBase.makeCloseMethod openMethodOfCloseType 
    
let solveMany f env x = Seq.map (solveTypeCore env) <| f x
let solve f env x = solveTypeCore env <| f x

type RuntimeTypeSolver(getMethods, getAllMethods) =
    interface Solver<Type,Type,Reflection.MethodBase> with
        override __.GetMethodTypeParams m = MethodBase.getTypeParams m |> Seq.map RuntimeType
        override __.GetParemeterTypes(_,m) = MethodBase.getParemeterTypes m |> Seq.map RuntimeType
        override __.GetReturnType(_,m) = MethodBase.getReturnType m |> RuntimeType
        override __.GetOpenType t = Type.getOpenType t
        override __.GetTypeParams t = Type.getTypeParams t |> Seq.map RuntimeType
        override x.GetMethods t = getMethods t
        override x.SolveMethodOfCloseType(closeParent, openMethodOfOpenType) =
            if Type.isGeneric closeParent then
                getMemberOfRuntimeOpenType
                    getAllMethods
                    (fun m md tps mtps -> m.ResolveMethod(md, tps, mtps))
                    closeParent openMethodOfOpenType
            else openMethodOfOpenType
            
type RuntimeTypeOfTypeBuilderSolver(getMethods) =
    interface Solver<Type, Type, Reflection.MethodBase> with
        override __.GetMethodTypeParams m = MethodBase.getTypeParams m |> Seq.map RuntimeType
        override __.GetParemeterTypes(_,m) = MethodBase.getParemeterTypes m |> Seq.map RuntimeType
        override __.GetReturnType(_,m) = MethodBase.getReturnType m |> RuntimeType
        override __.GetOpenType t = Type.getOpenType t
        override __.GetTypeParams t = Type.getTypeParams t |> Seq.map RuntimeType
        override x.GetMethods t = getMethods t
        override __.SolveMethodOfCloseType(closeType, openMethodOfOpenType) =
            match openMethodOfOpenType with
            | :? Reflection.MethodInfo as m -> TypeBuilder.GetMethod(closeType, m) :> Reflection.MethodBase
            | :? Reflection.ConstructorInfo as m -> TypeBuilder.GetConstructor(closeType, m) :> _
            | _ -> raise <| NotImplementedException()

type NonGenericTypeBuilderSolver(getMethods) =
    interface Solver<ILTypeBuilder, ILTypeBuilder, ILMethodBuilder> with
        override __.GetMethodTypeParams m = ILMethodBuilder.getTypeParams m |> typeVarMapToSolvedType
        override __.GetParemeterTypes(env,m) = solveMany getParemeterTypes env m
        override __.GetReturnType(env,m) = solve getReturnType env m
        override __.GetOpenType t = t
        override __.GetTypeParams t = ILTypeBuilder.getTypeParams t |> typeVarMapToSolvedType
        override x.GetMethods t = getMethods t
        override __.SolveMethodOfCloseType(_, m) = getUnderlyingSystemMethod m
        
type CloseTypeBuilderSolver(getMethods) =
    interface Solver<Type * ILTypeBuilder, ILTypeBuilder, ILMethodBuilder> with
        override __.GetMethodTypeParams m = ILMethodBuilder.getTypeParams m |> typeVarMapToSolvedType
        override __.GetParemeterTypes(env,m) = solveMany getParemeterTypes env m
        override __.GetReturnType(env,m) = solve getReturnType env m
        override __.GetOpenType t = snd t
        override __.GetTypeParams t = ILTypeBuilder.getTypeParams t |> typeVarMapToSolvedType
        override __.GetMethods t = getMethods t
        override __.SolveMethodOfCloseType(t, { mb = openMethodOfOpenType }) =
            let closeType = fst t
            match openMethodOfOpenType with
            | Choice1Of2 m -> TypeBuilder.GetMethod(closeType, m) :> Reflection.MethodBase
            | Choice2Of2 m -> TypeBuilder.GetConstructor(closeType, m) :> _

let getMethodBase (getMethodsIL, getMethodsRT, getAllMethodsRT) env parent annot =
    match solveTypeCore env parent with
    | TypeParam _ -> failwith ""
    | RuntimeType parent -> RuntimeTypeSolver(getMethodsRT, getAllMethodsRT) |> getMethodGeneric env parent annot
    | Builder parent -> NonGenericTypeBuilderSolver getMethodsIL |> getMethodGeneric env parent annot
    | InstantiationType(closeType, Some openType) -> CloseTypeBuilderSolver getMethodsIL |> getMethodGeneric env (closeType, openType) annot
    | InstantiationType(parent, None) -> RuntimeTypeOfTypeBuilderSolver getMethodsRT |> getMethodGeneric env parent annot

let getMethodInfo name env parent annot =
    getMethodBase(
        getMethods name,
        (Type.getMethods name >> Seq.map (fun m -> upcast m)),
        (Type.getAllMethods >> Seq.map (fun m -> upcast m))
    ) env parent annot
    :?> Reflection.MethodInfo
    
let getConstructorInfo env parent annot =
    getMethodBase(
        getConstructors,
        (Type.getConstructors >> Seq.map (fun m -> upcast m)),
        (Type.getConstructors >> Seq.map (fun m -> upcast m))
    ) env parent annot
    :?> Reflection.MethodInfo

let getField env parent name =
    match solveTypeCore env parent with
    | TypeParam _ -> failwith "getField: TypeParam"
    | RuntimeType t -> t.GetField(name, B.DeclaredOnly ||| B.Static ||| B.Instance ||| B.Public ||| B.NonPublic)
    | Builder { fmap = fmap } -> upcast get fmap name
    | InstantiationType(tb, Some { fmap = fmap }) -> TypeBuilder.GetField(tb, get fmap name)
    | InstantiationType(tb, None) ->
        let fd = tb.GetGenericTypeDefinition().GetField(name, B.DeclaredOnly ||| B.Static ||| B.Instance ||| B.Public ||| B.NonPublic)
        TypeBuilder.GetField(tb, fd)