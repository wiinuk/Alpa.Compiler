﻿module Alpa.Emit.Solve
open System
open System.Reflection.Emit
open Alpa.Emit
open Alpa.Emit.TypeSpec
open Alpa.Emit.TypeVarMap
open Alpa.Emit.SolvedType
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

[<AbstractClass>]
type MethodSource() =
    abstract GetILMethods: ILTypeBuilder -> ILMethodBuilder seq
    abstract GetRTMethods: Type -> Reflection.MethodBase seq
    abstract GetRTAllMethods: Type -> Reflection.MethodBase seq

[<AbstractClass>]
type Solver<'t,'ot,'m>() =
//    val MethodSource: MethodSource
//    new (ms) = { MethodSource = ms }

    abstract GetMethodTypeParams: 'm -> SolvedType seq
    abstract GetParemeterTypes: SolveEnv * 'm -> SolvedType seq
    abstract GetReturnType: SolveEnv * 'm -> SolvedType
    abstract GetOpenType: 't -> 'ot
    abstract GetTypeParams: 'ot -> SolvedType seq
    abstract GetMethods: 'ot * name: string -> 'm seq
    abstract SolveMethodOfCloseType: 't * 'm -> Reflection.MethodBase
    
//let methodInfoSource name = { new MethodSource() with
//    override __.GetILMethods t = getMethods name t
//    override __.GetRTMethods t = Type.getMethodBases name t
//    override __.GetRTAllMethods t = Type.getAllMethodBases t :> _
//}

let runtimeTypeSolver() = { new Solver<_,_,_>() with
    override __.GetMethodTypeParams m = MethodBase.getTypeParams m |> Seq.map RuntimeType
    override __.GetParemeterTypes(_,m) = MethodBase.getParemeterTypes m |> Seq.map RuntimeType
    override __.GetReturnType(_,m) = MethodBase.getReturnType m |> RuntimeType
    override __.GetOpenType t = Type.getOpenType t
    override __.GetTypeParams t = Type.getTypeParams t |> Seq.map RuntimeType
    override __.GetMethods(t, name) = Type.getMethodBases name t
    override __.SolveMethodOfCloseType(closeParent, openMethodOfOpenType) =
        if Type.isGeneric closeParent then
            getMemberOfRuntimeOpenType
                Type.getAllMethodBases
                (fun m md tps mtps -> m.ResolveMethod(md, tps, mtps))
                closeParent openMethodOfOpenType
        else openMethodOfOpenType
}
let runtimeTypeOfTypeBuilderSolver() = { new Solver<_,_,_>() with
    override __.GetMethodTypeParams m = MethodBase.getTypeParams m |> Seq.map RuntimeType
    override __.GetParemeterTypes(_,m) = MethodBase.getParemeterTypes m |> Seq.map RuntimeType
    override __.GetReturnType(_,m) = MethodBase.getReturnType m |> RuntimeType
    override __.GetOpenType t = Type.getOpenType t
    override __.GetTypeParams t = Type.getTypeParams t |> Seq.map RuntimeType
    override __.GetMethods(t, name) = Type.getMethodBases name t
    override __.SolveMethodOfCloseType(closeType, openMethodOfOpenType: Reflection.MethodBase) =
        match openMethodOfOpenType with
        | :? Reflection.MethodInfo as m -> TypeBuilder.GetMethod(closeType, m) :> Reflection.MethodBase
        | :? Reflection.ConstructorInfo as m -> TypeBuilder.GetConstructor(closeType, m) :> _
        | _ -> raise <| NotImplementedException()
}
let nonGenericTypeBuilderSolver() = { new Solver<_,_,_>() with
    override __.GetMethodTypeParams m = ILMethodBuilder.getTypeParams m |> typeVarMapToSolvedType
    override __.GetParemeterTypes(env,m) = Seq.map (solveTypeCore env) <| getParemeterTypes m
    override __.GetReturnType(env,m) = solveTypeCore env <| getReturnType m
    override __.GetOpenType t = t
    override __.GetTypeParams t = ILTypeBuilder.getTypeParams t |> typeVarMapToSolvedType
    override __.GetMethods(t, name) = getMethods name t
    override __.SolveMethodOfCloseType(_, m) = getUnderlyingSystemMethod m
}
let closeTypeBuilderSolver() = { new Solver<_,_,_>() with
    override __.GetMethodTypeParams m = ILMethodBuilder.getTypeParams m |> typeVarMapToSolvedType
    override __.GetParemeterTypes(env,m) =
        getParemeterTypes m
        |> Seq.toList
        |> List.map (solveTypeCore env)
        :> _

    override __.GetReturnType(env,m) = solveTypeCore env <| getReturnType m
    override __.GetOpenType t = snd t
    override __.GetTypeParams t = ILTypeBuilder.getTypeParams t |> typeVarMapToSolvedType
    override __.GetMethods(t, name) = getMethods name t
    override __.SolveMethodOfCloseType(t, { mb = openMethodOfOpenType }) =
        let closeType = fst t
        match openMethodOfOpenType with
        | Choice1Of2 m -> TypeBuilder.GetMethod(closeType, m) :> Reflection.MethodBase
        | Choice2Of2 m -> TypeBuilder.GetConstructor(closeType, m) :> _
}
let getMethodGeneric env parent name annot (s: Solver<_,_,_>) =
    let filter env mTypeArgsLength argTypes returnType m =
        let mTypeParams = s.GetMethodTypeParams m |> Seq.cache
        Seq.length mTypeParams = mTypeArgsLength &&

        let env =
            if Seq.isEmpty mTypeParams then env
            else
                let mVarMap = Seq.choose (function TypeParam(v,v') -> Some(v,v') | _ -> None) mTypeParams
                { env with
                    mTypeArgs = Seq.toList mTypeParams
                    sMVarMap = Seq.toList mVarMap
                }

        let paramTypes = s.GetParemeterTypes(env, m) |> Seq.cache

        match returnType with
        | None -> true
        | Some returnType ->
            typeEq (solveTypeCore env returnType) (s.GetReturnType(env, m))
        &&
        Seq.length paramTypes = List.length argTypes &&
        let argTypes = List.map (solveTypeCore env) argTypes
        Seq.forall2 typeEq paramTypes argTypes

    let mTypeArgs, getOpenMethodOfOpenType =
        match annot with
        | None -> [], fun _ _ ms -> Seq.exactlyOne ms
        | Some(MethodTypeAnnotation(mTypeArgs, argTypes, returnType)) ->
            let select mTypeArgs openTypeParams ms =
                let mTypeArgsLength = Seq.length mTypeArgs
                let openTypeParams = Seq.toList openTypeParams
                let varMap = List.choose (function SolvedType.TypeParam(v, v') -> Some(v,v') | _ -> None) openTypeParams
                
                let env = { env with typeArgs = openTypeParams; sVarMap = varMap }
                Seq.filter (filter env mTypeArgsLength argTypes returnType) ms |> Seq.exactlyOne

            mTypeArgs, select

    let openType = s.GetOpenType parent
    let openTypeParams = s.GetTypeParams openType
    let openMethodsOfOpenType = s.GetMethods(openType, name)

    let openMethodOfOpenType = getOpenMethodOfOpenType mTypeArgs openTypeParams openMethodsOfOpenType
    let mTypeArgs = List.map (solveTypeCore env) mTypeArgs

    let openMethodOfCloseType = s.SolveMethodOfCloseType(parent, openMethodOfOpenType)
    Seq.map getUnderlyingSystemType mTypeArgs
    |> MethodBase.makeCloseMethod openMethodOfCloseType 
    
let getMethodBase env (MethodRef(parent, name, annot) as m) =
    match solveTypeCore env parent with
    | TypeParam _ 
    | PointerType _
    | ByrefType _
    | ArrayType _ -> failwithf "method not found { env = %A; method = %A }" env m

    | RuntimeType parent -> runtimeTypeSolver() |> getMethodGeneric env parent name annot
    | Builder parent -> nonGenericTypeBuilderSolver() |> getMethodGeneric env parent name annot
    | InstantiationType(closeType, Some openType, _) -> closeTypeBuilderSolver() |> getMethodGeneric env (closeType, openType) name annot
    | InstantiationType(parent, None, _) -> runtimeTypeOfTypeBuilderSolver() |> getMethodGeneric env parent name annot

let getField env parent name =
    match solveTypeCore env parent with
    | TypeParam _
    | PointerType _
    | ByrefType _
    | ArrayType _ -> failwithf "field not found { env = %A; parent = %A; name = %A }" env parent name

    | RuntimeType t -> t.GetField(name, B.DeclaredOnly ||| B.Static ||| B.Instance ||| B.Public ||| B.NonPublic)
    | Builder { fmap = fmap } -> upcast get fmap name
    | InstantiationType(tb, Some { fmap = fmap }, _) -> TypeBuilder.GetField(tb, get fmap name)
    | InstantiationType(tb, None, _) ->
        let fd = tb.GetGenericTypeDefinition().GetField(name, B.DeclaredOnly ||| B.Static ||| B.Instance ||| B.Public ||| B.NonPublic)
        TypeBuilder.GetField(tb, fd)