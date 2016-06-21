module Alpa.Emit.ILEmit
open Alpa.Emit
open Alpa.Emit.Access
open Alpa.Emit.EmitException
open Alpa.Emit.FullName
open Alpa.Emit.HashMap
open Alpa.Emit.Parameter
open Alpa.Emit.TypeSpec
open Alpa.Emit.TypeVarMap
open Alpa.Emit.MethodHead
open Alpa.Emit.Solve
open Alpa.Emit.SolveEnv
open Alpa.Emit.ILMethodBuilder
open Alpa.Emit.ILTypeBuilder
open System.Reflection.Emit
open Alpa.Emit.PreDefinedTypes
open MethodBody

// (1) type name definition
// type IOrd`1 ... = ...;
// type IMap`2 ... = ...;
// type IntMap`1 ... = ...;
// module Module =
//     type X = ...;
//     ...;
//
// (2) type param definition
// type IOrd`1(a) = ...;
// type IMap`2(k + IOrd, v) = ...;
// type IntMap`1(v) = ...;
// module Module =
//     type X = ...;
//     ...;
//
// (3) member definition
// type IOrd`1(a) =
//     abstract CompareTo a : int32;
// type IMap`2(k + IOrd, v) =
//     abstract Add(k, v) : void;
// type IntMap`1(v) : object + IMap`2(int32, v) =
//     override Add(int32, v) : void = ...;
// module Module =
//     type X = fun Member (a + IOrd b, b) (a) : void = ...;
//     fun main () : void = ...;
//
// (4) emit method body
// type IOrd`1(a) =
//     abstract CompareTo a : int32;
// type IMap`2(k + IOrd, v) =
//     abstract Add(k, v) : void;
// type IntMap`1(v) : object + IMap`2(int32, v) =
//     override Add(int32, v) : void = ret;
// module Module =
//     type X = fun Member (a + IOrd b, b) (a) : void = ret;
//     fun main () : void = ret;

module DefineTypes =
    let rec type'(defineType, toName, accessAttr, fullName, ({ map = map } as env), ({ kind = kind; members = members } as d)) =
        let isInterfaceMember = function 
            | Literal _
            | Field _
            | MethodDef _
            | StaticMethodDef _
            | CtorDef _ 
            | CCtorDef _ 
            | NestedType _ -> false
            | AbstractDef _  -> true

        let getKind members = function
            | Some k -> k
            | None ->
                match members with
                | [] -> Sealed
                | _ when List.forall isInterfaceMember members -> Interface
                | _ -> Sealed

        let kindAttr = function
            | Interface -> T.Abstract ||| T.Interface
            | Abstract -> T.Abstract
            | TypeKind.Open -> T.Class
            | Sealed -> T.Sealed
            | Static -> T.Abstract ||| T.Sealed

        let k = getKind members kind
        let a = accessAttr ||| kindAttr k ||| T.BeforeFieldInit
        let t = defineType(toName fullName, a)
        add map fullName <| newILTypeBuilder d t fullName env

        for m in members do
            match m with
            | Literal _
            | Field _
            | AbstractDef _
            | CtorDef _
            | CCtorDef _
            | MethodDef _
            | StaticMethodDef _ -> ()
            | NestedType(access, name, td) ->
                type'(t.DefineNestedType, getName, nestedAccess access, addTypeName fullName name, env, td)

    let topDef (m: ModuleBuilder) ({ amap = amap } as env) = function
        | TopTypeDef(access, name, td) -> type'(m.DefineType, toTypeName env, typeAccess access, ofTypeName name, env, td)
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
    let amap' = AliasMap()
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
        add amap' name { aTypeParams = aTypeParams; entity = t }
    amap'

let defineVarMap typeParams defineGenericParameters =
    match typeParams with
    | [] -> emptyVarMap
    | _ ->
        let names = List.toArray typeParams
        List.zip typeParams (List.ofArray <| defineGenericParameters names)

let mDefineGP (m: MethodBuilder) xs = m.DefineGenericParameters xs
let tDefineGP (t: TypeBuilder) xs = t.DefineGenericParameters xs

let defineTypeParams { map = map } =
    for ({ d = { typeParams = typeParams }; t = t } as ti) in values map do
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

let defineMethodInfo dt a c ov (MethodInfo(head, body)) =
    let mb, mVarMap = defineMethodHead dt a c head
    addMethod dt head { h = head; b = Some body; mb = Choice1Of2 mb; mVarMap = mVarMap; ov = ov; dt = dt }

let defineMethodDef dt a ov k m =
    let kindAttr = function
        | None -> M.Final
        | Some Open -> M.Virtual

    let overrideAttr = function
        | Override[] -> M.Virtual
        | Override(_::_) -> M.Virtual ||| M.NewSlot

    let methodAttr ov k =
        match ov with
        | Some ov -> kindAttr k ||| overrideAttr ov
        | None ->
            let a =
                match k with
                | Some Open -> M.NewSlot
                | None -> enum 0

            a ||| kindAttr k

    let a = methodAccess a ||| methodAttr ov k ||| M.HideBySig

    match ov with
    | None -> defineMethodInfo dt a CC.Standard ov m
    | Some _ -> defineMethodInfo dt a CC.HasThis ov m

let defineField ({ t = t; fmap = fmap } as ti) (access, isStatic, isMutable, name, ft) =
    let a = fieldAccess access
    let a = if isStatic then a ||| F.Static else a
    let a = if isMutable then a else a ||| F.InitOnly
    let ft = solveType (envOfTypeBuilder emptyVarMap ti) ft
    let f = t.DefineField(name, ft, a)
    add fmap name f

let defineLiteral ({ t = t; fmap = fmap } as ti) access name ft fv =
    let a = fieldAccess access ||| F.Static ||| F.Literal
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
    addMethodOfSign dt ".cctor" {
        mb = Choice2Of2 c
        mVarMap = emptyVarMap
        dt = dt
        ov = None
        h = cctorHead
        b = Some body
    }

let defineCtor ({ t = t } as dt) a pars body =
    let pts = solveParamTypes (envOfTypeBuilder emptyVarMap dt) pars
    let a = methodAccess a ||| M.SpecialName ||| M.RTSpecialName
    let c = t.DefineConstructor(a, CC.HasThis, pts)
    defineParams c.DefineParameter pars
    addCtor dt {
        mb = Choice2Of2 c
        dt = dt
        mVarMap = emptyVarMap
        ov = None
        h = ctorHead pars
        b = Some body
    }
    
let defineStaticMethod dt a (MethodInfo(head, body)) =
    let mb, mVarMap = defineMethodHead dt (methodAccess a ||| M.Static) CC.Standard head
    addMethod dt head {
        mb = Choice1Of2 mb
        mVarMap = mVarMap
        h = head
        b = Some body
        ov = None
        dt = dt
    }

let defineMember dt = function
    | NestedType _ -> ()
    | Field(access, isStatic, isMutable, n, ft) -> defineField dt (access, isStatic, isMutable, n, ft)
    | Literal(a, n, t, l) -> defineLiteral dt a n t l
    | MethodDef(a, ov, k, m) -> defineMethodDef dt a ov k m
    | StaticMethodDef(a, m) -> defineStaticMethod dt a m
    | CtorDef(a, pars, body) -> defineCtor dt a pars body
    | CCtorDef body -> defineCCtor dt body
    | AbstractDef(a, head) ->
        let a = methodAccess a ||| M.HideBySig ||| M.NewSlot ||| M.Abstract ||| M.Virtual
        let mb, mVarMap = defineMethodHead dt a CC.HasThis head
        addMethod dt head {
            mb = Choice1Of2 mb
            mVarMap = mVarMap
            h = head
            b = None
            ov = None
            dt = dt
        }

let defineTypeDef ({ t = t; mmap = mmap; d = { parent = p }} as ti) { parent = parent; impls = impls; members = members } =
    let env = envOfTypeBuilder emptyVarMap ti

    match parent with
    | None -> ()
    | Some parent -> t.SetParent <| solveType env parent

    for impl in impls do t.AddInterfaceImplementation <| solveType env impl
    for m in members do defineMember ti m

    if not (t.IsInterface || (t.IsSealed && t.IsAbstract)) && not <| contines mmap ".ctor" then
        let a = M.RTSpecialName ||| M.Public ||| M.HideBySig
        let c = t.DefineConstructor(a, CC.Standard, null)
        let body =
            match p with
            | None -> defaultConstructerBodyOfObject
            | Some p -> defaultConstructerBody p

        addCtor ti {
            mb = Choice2Of2 c
            dt = ti
            mVarMap = emptyVarMap
            ov = None
            h = defaultCtorHead
            b = Some body
        }

let defineMembers { map = map } = for { d = d } as ti in values map do defineTypeDef ti d

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

    | OpMethod m ->
        match getMethodBase env m with
        | :? System.Reflection.MethodInfo as m -> g.Emit(op, m)
        | :? System.Reflection.ConstructorInfo as m -> g.Emit(op, m)
        | _ -> failwith "unreach"

let defineOverride env { dt = { t = t }; ov = ov; mb = mb } =
    match ov with
    | None
    | Some(Override[]) -> ()
    | Some(Override baseMethods) ->
        for bm in baseMethods do
            match getMethodBase env bm with
            | :? System.Reflection.ConstructorInfo -> raiseEmitExn <| ConstructorIsNotOverride bm
            | :? System.Reflection.MethodInfo as bm ->
                match mb with
                | Choice1Of2 m -> t.DefineMethodOverride(m, bm)
                | Choice2Of2 _ -> failwith "unreach"

            | _ -> raise <| System.NotImplementedException()

let emitMethod ({ mVarMap = mVarMap; dt = dt; b = body } as m) =
    match body with
    | None -> ()
    | Some(MethodBody(locals, instrs)) ->
        let env = envOfTypeBuilder mVarMap dt
        defineOverride env m
        let g = getILGenerator m
        for Local(t, isPinned) in locals do
            g.DeclareLocal(solveType env t, isPinned) |> ignore

        for instr in instrs do emitInstr g env instr

let emitMethods { map = map } =
    for { mmap = mmap } in values map do
        for mis in values mmap do
            for m in mis do emitMethod m

let createTypes { map = map } = for { t = t } in values map do t.CreateType() |> ignore

let loadAssemblyRef (d: System.AppDomain) r =
    let n = AssemblyRef.toAssemblyName r
    d.Load n |> ignore

let emitIL fileName (d: System.AppDomain)
    {
    assembly = AssemblyDef assemblyName
    moduleDef = moduleDef
    imports = imports
    topDefs = ds
    }
    =
    let moduleName = match moduleDef with None -> fileName | Some x -> x
    let n = System.Reflection.AssemblyName assemblyName
    let a = d.DefineDynamicAssembly(n, AssemblyBuilderAccess.Save)
    let m = a.DefineDynamicModule(moduleName, fileName+"")
    
    let imap = HashMap()
    for AssemblyImport({ name = name } as i, alias) in imports do
        add imap name i
        Option.iter (fun a ->
            if contines imap a then raiseEmitExn <| DuplicatedAssemblyAlias a
            else add imap a i
        ) alias
        loadAssemblyRef d i

    let env = {
        map = HashMap()
        amap = AliasMap()
        imap = imap
    }
    for d in ds do DefineTypes.topDef m env d
    let env = { env with amap = checkAlias env }
    defineTypeParams env
    defineMembers env
    emitMethods env
    createTypes env
    a