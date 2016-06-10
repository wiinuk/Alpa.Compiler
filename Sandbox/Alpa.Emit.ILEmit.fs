module Alpa.Emit.ILEmit
open Alpa.Emit
open Alpa.Emit.EmitException
open Alpa.Emit.FullName
open Alpa.Emit.HashMap
open Alpa.Emit.Parameter
open Alpa.Emit.TypeSpec
open Alpa.Emit.TypeVarMap
open Alpa.Emit.MethodHead
open Alpa.Emit.SolveEnv
open Alpa.Emit.ILMethodBuilder
open Alpa.Emit.ILTypeBuilder
open System.Reflection.Emit
open Solve

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
        
let defineVarMap typeParams defineGenericParameters =
    match typeParams with
    | [] -> emptyVarMap
    | _ ->
        let names = List.toArray typeParams
        List.zip typeParams (List.ofArray <| defineGenericParameters names)

let mDefineGP (m: MethodBuilder) xs = m.DefineGenericParameters xs
let tDefineGP (t: TypeBuilder) xs = t.DefineGenericParameters xs

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

let emitInstr (g: ILGenerator) env (Instr(label, op, operand)) =
    match operand with
    | OpNone -> g.Emit op
    | OpI1 n -> g.Emit(op, n)
    | OpI2 n -> g.Emit(op, n)
    | OpI4 n -> g.Emit(op, n)
    | OpI8 n -> g.Emit(op, n)
    | OpF4 n -> g.Emit(op, n)
    | OpF8 n -> g.Emit(op, n)
    | OpString s -> g.Emit(op, s)
    | OpType t -> g.Emit(op, solveType env t)
    | OpField(parent, name) ->
        let f = getField env parent name
        g.Emit(op, f)

    | OpMethod(parent, name, annot) ->
        let m = getMethodInfo env parent name annot
        g.Emit(op, m)

    | OpCtor(parent, argTypes) ->
        let annot = Some(MethodTypeAnnotation([], argTypes, None))
        let ctor = getConstructorInfo env parent annot
        g.Emit(op, ctor)

let emitMethod ({ mVarMap = mVarMap; dt = dt; m = MethodInfo(_,MethodBody instrs)} as m) =
    let g = getILGenerator m
    let env = envOfTypeBuilder mVarMap dt
    for instr in instrs do emitInstr g env instr

let emitMethods { map = map } =
    for { mmap = mmap; cmap = cmap; cctor = cctor } in values map do
        for mis in values mmap do
            for m in mis do emitMethod m

        for m in cmap do emitMethod m

        match cctor with
        | None -> ()
        | Some m -> emitMethod m

let createTypes { map = map } = for { t = t } in values map do t.CreateType() |> ignore

let emitIL m { topDefs = ds } =
    let env = { map = HashMap(); amap = AliasMap() }
    for d in ds do DefineTypes.topDef m env d
    checkAlias env
    defineTypeParams env
    defineMembers env
    emitMethods env
    createTypes env