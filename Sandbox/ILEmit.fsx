module ILEmit

open System
open System.Collections.Generic
open System.Reflection.Emit
open System.Threading

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

type FullName = FullName of name: string * nestersRev: string list * namespaceRev: string list * assemblyName: string option

type TypeVar = string
and TypeSpec =
    /// ex: [mscorlib]System.Tuple(..., ...)
    | TypeSpec of pathRev: FullName * TypeSpec list
    /// ex: !T1
    | TypeVar of TypeVar
    /// ex: !!T1
    | MethodTypeVar of TypeVar
    /// ex: !0
    | TypeArgRef of int
    /// ex: !!0
    | MethodTypeArgRef of int

type MethodName = string
type Operand =
    | OpNone
    | OpI1 of int8
    | OpI2 of int16
    | OpI4 of int
    | OpI8 of int64
    | OpF4 of single
    | OpF8 of double
    | OpString of string
    | OpType of TypeSpec
    | OpField of thisType: TypeSpec * name: string
    | OpCtor of thisType: TypeSpec * argTypes: TypeSpec list
    | OpMethod of thisType: TypeSpec * name: MethodName * typeArgs: TypeSpec list * argTypes: TypeSpec list

type Macro =
    | BaseInit of TypeSpec list

type Instr = 
    | Instr of string * OpCode * Operand

type Override =
    | Override
    | BaseMethod of baseMethod: (TypeSpec * MethodName)

type Parameter = Parameter of name: string option * TypeSpec
type MethodBody = MethodBody of Instr list
type MethodHead = MethodHead of name: MethodName * typeParams: TypeVar list * pars: Parameter list * ret: Parameter
type MethodInfo = MethodInfo of MethodHead * MethodBody
type StaticMethodInfo = MethodInfo

type Literal =
    | Bool of bool
    | I1 of int8
    | U1 of uint8
    | I2 of int16
    | U2 of uint16
    | I4 of int32
    | U4 of uint32
    | I8 of int64
    | U8 of uint64
    | F4 of single
    | F8 of double
    | Char of char
    | String of string
    | Null

type MemberDef =
    | Literal of name: string * TypeSpec * Literal
    | Field of isStatic: bool * isMutable: bool * name: string * TypeSpec
    | AbstractDef of MethodHead
    | CtorDef of pars: Parameter list * MethodBody
    | MethodDef of Override option * MethodInfo
    | StaticMethodDef of StaticMethodInfo

type TypeKind = Abstract | Interface | Open | Sealed

type TypeDef = {
    kind: TypeKind option
    typeParams: TypeVar list
    parent: TypeSpec option
    /// Implement Interfaces
    impls: TypeSpec list
    members: MemberDef list
}
type ModuleMember =
    | ModuleMethodDef of StaticMethodInfo
    | ModuleTypeDef of name: string * TypeDef
    | ModuleModuleDef of name: string * ModuleMember list
    | ModuleValDef of isMutable: bool * name: string * TypeSpec
    | ModuleLiteralDef of name: string * TypeSpec * Literal

type TopDef =
    | TopTypeDef of pathRev: (string * string list) * TypeDef
    | TopModuleDef of pathRev: (string * string list) * ModuleMember list

type AssemblyDef = string
type IL = { topDefs: TopDef list }

[<Sealed; AllowNullLiteral>]
type HashMap<'k,'v when 'k : equality>() = inherit Dictionary<'k,'v>()

/// typeParams.Length = typeParamBuilders.Length
type TypeVarMap = TypeVarMap of typeParams: TypeVar list * typeParamBuilders: GenericTypeParameterBuilder list
type MethodSign = MethodName
type FieldSign = string

type ILTypeBuilder = {
    d: Choice<TypeDef, ModuleMember list>
    t: TypeBuilder

    path: FullName
    
    map: TypeMap
    mutable varMap: TypeVarMap

    mmap: MethodMap
    cmap: CtorMap
    fmap: FieldMap
}

and ILMethodBuilder = {
    /// DeclaringType
    dt: ILTypeBuilder
    mb: MethodBuilder
    mVarMap: TypeVarMap
    m: MethodInfo
}
and ILCtorBuilder = {
    /// DeclaringType
    dt: ILTypeBuilder
    cb: ConstructorBuilder
    pars: Parameter list
    body: MethodBody
}
and MethodMap = HashMap<MethodSign, ILMethodBuilder list>
and FieldMap = HashMap<FieldSign, FieldBuilder>
and TypeMap = HashMap<FullName, ILTypeBuilder>
and CtorMap = ResizeArray<ILCtorBuilder>

let add (map: HashMap<_,_>) k v = map.Add(k, v)
let assign (map: HashMap<_,_>) k v = map.[k] <- v
let get (map: HashMap<_,_>) k = map.[k]
let tryGet (map: HashMap<_,_>) k (v: _ byref) = map.TryGetValue(k, &v)

let values (map: HashMap<_,_>) = map.Values
let paramType (Parameter(_,t)) = t
let emptyVarMap = TypeVarMap([], [])
    
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

let solveTypeVarMap vs v = List.find (fst >> (=) v) vs |> snd
type SolvedTypeParam =
    | RuntimeTypeParam of Type
    | TypeParamBuilder of GenericTypeParameterBuilder
type SolvedType =
    | RuntimeType of Type
    | Builder of ILTypeBuilder
    | InstantiationType of closeType: Type * openType: ILTypeBuilder option
    | TypeParam of TypeVar * SolvedTypeParam

let getUnderlyingSystemType = function
    | RuntimeType t
    | TypeParam(_, RuntimeTypeParam t)
    | InstantiationType(closeType = t) -> t
    | TypeParam(_, TypeParamBuilder t) -> upcast t
    | Builder { t = t } -> upcast t

type SolveEnv = {
    tmap: TypeMap
    varMap: (TypeVar * SolvedTypeParam) list
    mVarMap: (TypeVar * SolvedTypeParam) list
    typeArgs: SolvedType list
    mTypeArgs: SolvedType list
}
let rec getReplacedType subst = function
    | TypeSpec(n, ts) -> TypeSpec(n, List.map (getReplacedType subst) ts)
    | TypeVar v as t ->
        match List.tryFind (fun (v',_) -> v = v') subst with
        | Some(_,t) -> getReplacedType subst t
        | None -> t

    | t -> t

let rec solveTypeCore ({ tmap = map; varMap = varMap; mVarMap = mVarMap; typeArgs = typeArgs; mTypeArgs = mTypeArgs } as env) t =
    let getCloseType map pathRev =
        let mutable ti = Unchecked.defaultof<_>
        if tryGet map pathRev &ti then Builder ti
        else RuntimeType <| Type.GetType(toTypeName pathRev, true)
        
    let rec aux = function
    | TypeSpec(pathRev, []) -> getCloseType map pathRev
    | TypeSpec(pathRev, ts) ->
        let vs = List.map (solveTypeCore env) ts
        let ts = Seq.map getUnderlyingSystemType vs |> Seq.toArray
        match getCloseType map pathRev with
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

let solveType env t = solveTypeCore env t |> getUnderlyingSystemType
let solveTypes env ts = Seq.map (solveType env) ts |> Seq.toArray
let solveParamTypes env pars = Seq.map (paramType >> solveType env) pars |> Seq.toArray

let defineVarMap typeParams defineGenericParameters =
    match typeParams with
    | [] -> emptyVarMap
    | _ ->
        let names = List.toArray typeParams
        TypeVarMap(typeParams, List.ofArray <| defineGenericParameters names)

let mDefineGP (m: MethodBuilder) xs = m.DefineGenericParameters xs
let tDefineGP (t: TypeBuilder) xs = t.DefineGenericParameters xs

let typeParams (TypeVarMap(p,_)) = p

let ctorHead { path = path; varMap = varMap } pars =
    let t = TypeSpec(path, typeParams varMap |> List.map TypeVar)
    MethodHead(".ctor", [], pars, Parameter(None, t))

let addTypeName (FullName(name, nestersRev, nsRev, asmName)) typeName =
    FullName(typeName, name::nestersRev, nsRev, asmName)

let ofTypeName (typeName, nsRev) = FullName(typeName, [], nsRev, None)
let getName (FullName(name=name)) = name

module DefineTypes =
    let newILTypeBuilder d t path map = {
        d = d
        t = t
        path = path
        varMap = emptyVarMap
        map = map
        mmap = HashMap()
        cmap = CtorMap()
        fmap = HashMap()
    }

    let rec module'(defineType, toName, a, fullName, map, ms) =
        let a = a ||| T.Abstract ||| T.Sealed
        let t = defineType(toName fullName, a)
        add map fullName <| newILTypeBuilder (Choice2Of2 ms) t fullName map
        for m in ms do moduleMember fullName t map m

    and type'(defineType, toName, a, fullName, map, ({ kind = kind; members = members } as d)) =
        let isInterfaceMember = function 
            | Literal _
            | Field _
            | MethodDef _
            | StaticMethodDef _
            | CtorDef _ -> false
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
        add map fullName <| newILTypeBuilder (Choice1Of2 d) t fullName map

    and moduleMember path (t: TypeBuilder) map = function
        | ModuleMethodDef _
        | ModuleValDef _ 
        | ModuleLiteralDef _ -> ()
        | ModuleModuleDef(name, ms) -> module'(t.DefineNestedType, getName, T.NestedPublic, addTypeName path name, map, ms)
        | ModuleTypeDef(name, td) -> type'(t.DefineNestedType, getName, T.NestedPublic, addTypeName path name, map, td)

    let topDef (m: ModuleBuilder) map = function
        | TopModuleDef(path, ms) -> module'(m.DefineType, toTypeName, T.Public, ofTypeName path, map, ms)
        | TopTypeDef(name, td) -> type'(m.DefineType, toTypeName, T.Public, ofTypeName name, map, td)

let defineTypeParams map =
    for ({ d = d; t = t } as ti) in values map do
        match d with
        | Choice2Of2 _ -> ()
        | Choice1Of2 { typeParams = typeParams } ->
            ti.varMap <- defineVarMap typeParams <| tDefineGP t

let toSign (MethodHead(name=name)) = name

let addMethod mmap head m =
    let sign = toSign head
    let mutable ms = Unchecked.defaultof<_>
    if tryGet mmap sign &ms then assign mmap sign (m::ms)
    else add mmap sign [m]

let addCtor (cmap: CtorMap) c = cmap.Add c

let defineParam defineParameter i (Parameter(n, _)) = defineParameter(i, P.None, Option.toObj n) |> ignore
let defineParams defineParameter pars = List.iteri (fun i a -> defineParam defineParameter (i + 1) a) pars

let typeVarMapToSolvedType (TypeVarMap(vs,vs')) =
    List.map2 (fun v v' -> v, TypeParamBuilder v') vs vs'

let envOfTypeBuilder mVarMap { map = map; varMap = varMap } = {
    tmap = map
    varMap = typeVarMapToSolvedType varMap
    mVarMap = typeVarMapToSolvedType mVarMap
    typeArgs = []
    mTypeArgs = []
}

let defineMethodHead ({ t = t } as ti) attr callconv (MethodHead(name,typeParams,pars,ret)) =
    let m = t.DefineMethod(name, attr, callconv)
    let mVarMap = defineVarMap typeParams <| mDefineGP m
    
    m.SetReturnType(solveType (envOfTypeBuilder mVarMap ti) (paramType ret))
    m.SetParameters(solveParamTypes (envOfTypeBuilder mVarMap ti) pars)

    defineParam m.DefineParameter 0 ret
    defineParams m.DefineParameter pars

    m, mVarMap

let defineMethodInfo ({ mmap = mmap } as dt) a c (MethodInfo(head, _) as m) =
    let mb, mVarMap = defineMethodHead dt a c head
    addMethod mmap head { m = m; mb = mb; mVarMap = mVarMap; dt = dt }

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

let defineCtor ({ t = t; cmap = cmap } as dt) pars body =
    let pts = solveParamTypes (envOfTypeBuilder emptyVarMap dt) pars
    let c = t.DefineConstructor(M.SpecialName ||| M.RTSpecialName ||| M.Public, CC.HasThis, pts)
    defineParams c.DefineParameter pars
    addCtor cmap { cb = c; dt = dt; pars = pars; body = body }
    
let defineStaticMethod ({ mmap = mmap } as dt) (MethodInfo(head, _) as m) =
    let mb, mVarMap = defineMethodHead dt (M.Public ||| M.Static) CC.Standard head
    addMethod mmap head { mb = mb; mVarMap = mVarMap; m = m; dt = dt }

let defineMember dt = function
    | Field(isStatic, isMutable, n, ft) -> defineField dt (isStatic, isMutable, n, ft)
    | Literal(n, t, l) -> defineLiteral dt n t l
    | MethodDef(ov, m) -> defineMethodDef dt ov m
    | StaticMethodDef m -> defineStaticMethod dt m
    | CtorDef(pars, body) -> defineCtor dt pars body
    | AbstractDef head ->
        let a = M.Public ||| M.HideBySig ||| M.NewSlot ||| M.Abstract ||| M.Virtual
        defineMethodHead dt a CC.HasThis head
        |> ignore

let defineTypeDef ({ t = t } as ti) { parent = parent; impls = impls; members = members } =
    match parent with
    | Some parent -> t.SetParent <| solveType (envOfTypeBuilder emptyVarMap ti) parent
    | _ -> ()

    for impl in impls do t.AddInterfaceImplementation <| solveType (envOfTypeBuilder emptyVarMap ti) impl
    for m in members do defineMember ti m

let defineModuleMember dt = function
    | ModuleTypeDef _
    | ModuleModuleDef _ -> ()
    | ModuleValDef(isMutable, name, ft) -> defineField dt (true, isMutable, name, ft)
    | ModuleLiteralDef(name, ft, v) -> defineLiteral dt name ft v
    | ModuleMethodDef m -> defineStaticMethod dt m

let defineMembers map =
    for ({ d = d } as ti) in values map do
        match d with
        | Choice1Of2 td -> defineTypeDef ti td
        | Choice2Of2 members -> for m in members do defineModuleMember ti m

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

let getField env parent name =
    match solveTypeCore env parent with
    | TypeParam _ -> failwith "getField: TypeParam"
    | RuntimeType t -> t.GetField(name, B.DeclaredOnly ||| B.Static ||| B.Instance ||| B.Public ||| B.NonPublic)
    | Builder { fmap = fmap } -> upcast get fmap name
    | InstantiationType(tb, Some { fmap = fmap }) -> TypeBuilder.GetField(tb, get fmap name)
    | InstantiationType(tb, None) ->
        let fd = tb.GetGenericTypeDefinition().GetField(name, B.DeclaredOnly ||| B.Static ||| B.Instance ||| B.Public ||| B.NonPublic)
        TypeBuilder.GetField(tb, fd)

type IsMethodBase<'m> = {
    getMTypeParams: 'm -> SolvedType list
    getParameters: 'm -> SolvedType list
}
type IsMethodInfo<'m,'i,'b> = {
    baseClass: IsMethodBase<'b>
    toBase: 'm -> 'b
    getSystemMethod: 'm -> 'i
}
type IsType<'t,'m,'c> = {
    getMethodsOfName: string -> 't -> 'm seq
    getCtors: 't -> 'c seq
    getTypeParams: 't -> SolvedType list
}
let parameterType (p: Reflection.ParameterInfo) = p.ParameterType

let isMethodBaseOfRt = {
    getMTypeParams = fun (m: Reflection.MethodBase) -> if m.IsGenericMethod then m.GetGenericArguments() |> Seq.map RuntimeType |> Seq.toList else []
    getParameters = fun m ->
        m.GetParameters()
        |> Seq.map (parameterType >> RuntimeType)
        |> Seq.toList
}
let isMethodInfoOfRt = {
    baseClass = isMethodBaseOfRt
    toBase = fun (m: Reflection.MethodInfo) -> upcast m
    getSystemMethod = id
}
let isCtorOfRt = {
    baseClass = isMethodBaseOfRt
    toBase = fun (m: Reflection.ConstructorInfo) -> upcast m
    getSystemMethod = id
}
let isTypeOfRt = {
    getMethodsOfName = fun name (t: Type) -> t.GetMethods(B.DeclaredOnly ||| B.Public ||| B.NonPublic ||| B.Static ||| B.Instance) |> Seq.filter (fun m -> m.Name = name)
    getCtors = fun t -> upcast t.GetConstructors(B.DeclaredOnly ||| B.Public ||| B.NonPublic ||| B.Instance)
    getTypeParams = fun t -> t.GetGenericArguments() |> Seq.map RuntimeType |> Seq.toList
}

let toTypeParams (TypeVarMap(typeParams, typeParams')) = List.map2 (fun t t' -> TypeParam(t, TypeParamBuilder t')) typeParams typeParams'

let isMethodInfoOfTb = {
    baseClass =
        {
        getMTypeParams = fun { ILMethodBuilder.mVarMap = mVarMap } -> toTypeParams mVarMap
        getParameters = fun { dt = dt; mVarMap = mVarMap; m = MethodInfo(MethodHead(pars=pars),_) } ->
            List.map (paramType >> solveTypeCore (envOfTypeBuilder mVarMap dt)) pars
        }
    toBase = id
    getSystemMethod = fun { mb = mb } -> mb
}
let isCtorOfTb = {
    baseClass =
        {
        getMTypeParams = fun _ -> []
        getParameters = fun { dt = dt; pars = pars } ->
            List.map (paramType >> solveTypeCore (envOfTypeBuilder emptyVarMap dt)) pars
        }
    toBase = id
    getSystemMethod = fun { cb = cb } -> cb
}
let isTypeOfTb = {
    getMethodsOfName = fun name { mmap = mmap } -> upcast get mmap name
    getCtors = fun { cmap = cmap } -> upcast cmap
    getTypeParams = fun { varMap = varMap } -> toTypeParams varMap
}

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

let getMethodOfRuntimeOpenType closeType (methodOfOpenType: Reflection.MethodInfo) =
    getMemberOfRuntimeOpenType
        (fun t b -> t.GetMethods b)
        (fun m md tps mtps -> upcast m.ResolveMethod(md, tps, mtps))
        closeType methodOfOpenType

let getCtorOfRuntimeOpenType closeType (ctorOfOpenType: Reflection.ConstructorInfo) =
    getMemberOfRuntimeOpenType
        (fun t b -> t.GetConstructors b)
        (fun m md tps mtps -> upcast m.ResolveMethod(md, tps, mtps))
        closeType ctorOfOpenType

let getGenericMethod
    { getMethodsOfName = getMethodsOfName; getTypeParams = getTypeParams }
    { getSystemMethod = getSystemMethod
      toBase = toBase
      baseClass = { getMTypeParams = getMTypeParams; getParameters = getParameters }}
    (env, closeType, openType, name, mTypeArgs, argTypes) =

    let typeParams = getTypeParams openType
    let openMethodOfOpenType =
        getMethodsOfName name openType
        |> Seq.toList
        |> List.filter (fun m ->
            let m = toBase m
            let mTypeParams = getMTypeParams m
            List.length mTypeParams = List.length mTypeArgs &&
            let env = { env with typeArgs = typeParams; mTypeArgs = mTypeParams }
            let pars = getParameters m
            List.length pars = List.length argTypes &&
            let methodParamTypesOfOpenType = solveTypes env argTypes
            Seq.forall2 (=) methodParamTypesOfOpenType (List.map getUnderlyingSystemType pars)
        )
        |> List.exactlyOne

    let openMethodOfCloseType = TypeBuilder.GetMethod(closeType, getSystemMethod openMethodOfOpenType)

    let mTypeArgs = Seq.map (solveType env) mTypeArgs |> Seq.toArray
    if openMethodOfCloseType.IsGenericMethodDefinition then openMethodOfCloseType.MakeGenericMethod mTypeArgs
    else openMethodOfCloseType

let getMethod env parent name mTypeArgs argTypes =
    let a = B.DeclaredOnly ||| B.Static ||| B.Instance ||| B.Public ||| B.NonPublic
    let c = CC.Any

    match solveTypeCore env parent with
    | TypeParam _ -> failwith "TypeParam"
    | RuntimeType t ->
        if t.IsGenericType then
            let openType = t.GetGenericTypeDefinition()
            let typeParams = openType.GetGenericArguments()
            let env = { env with typeArgs = Seq.map RuntimeType typeParams |> Seq.toList }
            let argTypes = Seq.map (solveType env) argTypes |> Seq.toArray
            let methodOfOpenType = openType.GetMethod(name, B.DeclaredOnly ||| B.Public ||| B.NonPublic ||| B.Static ||| B.Instance, null, argTypes, null)
            getMethodOfRuntimeOpenType t methodOfOpenType
        else
            let argTypes = Seq.map (solveType env) argTypes |> Seq.toArray
            t.GetMethod(name, a, null, c, argTypes, null)

    | Builder { mmap = mmap } ->
        let { mb = mb } =
            get mmap name
            |> List.filter (fun { mVarMap = TypeVarMap(mTypeParams,_); m = MethodInfo(MethodHead(_,tpars,pars,_),_) } ->
                List.length tpars = List.length mTypeArgs &&
                List.length pars = List.length argTypes &&
                let subst = List.zip mTypeParams mTypeArgs
                List.forall2
                    (fun (Parameter(_,parT)) argT -> getReplacedType subst parT = argT)
                    pars
                    argTypes
            )
            |> List.exactlyOne
        upcast mb

    | InstantiationType(closeType, None) -> getGenericMethod isTypeOfRt isMethodInfoOfRt (env, closeType, closeType.GetGenericTypeDefinition(), name, mTypeArgs, argTypes)
    | InstantiationType(closeType, Some openType) -> getGenericMethod isTypeOfTb isMethodInfoOfTb (env, closeType, openType, name, mTypeArgs, argTypes)

let getGenericCtor
    { getCtors = getCtors; getTypeParams = getTypeParams }
    { baseClass = { getParameters = getParameters }; toBase = toBase; getSystemMethod = getSystemMethod }
    (env, closeType, openType, argTypes) =

    let typeParams = getTypeParams openType
    let m =
        getCtors openType
        |> Seq.toList
        |> List.filter (fun m ->
            let m = toBase m
            let pars = getParameters m
            List.length pars = List.length argTypes &&
            let genericMethodDefParamTypes = solveTypes { env with typeArgs = typeParams } argTypes
            let paramTypes = Seq.map getUnderlyingSystemType pars
            Seq.forall2 (=) genericMethodDefParamTypes paramTypes
        )
        |> List.exactlyOne

    TypeBuilder.GetConstructor(closeType, getSystemMethod m)

let getCtor env parent argTypes =
    match solveTypeCore env parent with
    | TypeParam _ -> failwith "TypeParam"
    | RuntimeType t ->
        if t.IsGenericType then
            let openType = t.GetGenericTypeDefinition()
            let typeParams = openType.GetGenericArguments()
            let env = { env with typeArgs = Seq.map RuntimeType typeParams |> Seq.toList }
            let argTypes = Seq.map (solveType env) argTypes |> Seq.toArray
            let ctorOfOpenType = openType.GetConstructor(B.DeclaredOnly ||| B.Public ||| B.NonPublic ||| B.Instance, null, argTypes, null)
            getCtorOfRuntimeOpenType t ctorOfOpenType
        else
            let argTypes = Seq.map (solveType env) argTypes |> Seq.toArray
            t.GetConstructor(B.DeclaredOnly ||| B.Public ||| B.NonPublic ||| B.Instance, null, CC.Any, argTypes, null)

    | Builder { cmap = cmap } ->
        let argTypes = solveTypes env argTypes
        let { cb = cb } =
            cmap
            |> Seq.filter (fun { cb = cb } ->
                let pars = cb.GetParameters()
                Array.length pars = Array.length argTypes &&
                Array.forall2 (fun p t -> parameterType p = t) pars argTypes
            )
            |> Seq.exactlyOne
        upcast cb
        
    | InstantiationType(closeType, None) -> getGenericCtor isTypeOfRt isCtorOfRt (env, closeType, closeType.GetGenericTypeDefinition(), argTypes)
    | InstantiationType(closeType, Some openType) -> getGenericCtor isTypeOfTb isCtorOfTb (env, closeType, openType, argTypes)

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
    | OpMethod(parent, name, mTypeArgs, argTypes) -> g.Emit(op, getMethod (envOfTypeBuilder mVarMap dt) parent name mTypeArgs argTypes)
    | OpCtor(parent, argTypes) -> g.Emit(op, getCtor (envOfTypeBuilder mVarMap dt) parent argTypes)

let emitMethod g mVarMap dt (MethodBody instrs) =
    for instr in instrs do emitInstr g mVarMap dt instr

let emit map =
    for { mmap = mmap; cmap = cmap } in values map do
        for mis in values mmap do
            for { mb = mb; mVarMap = mVarMap; dt = dt; m = MethodInfo(_, b) } in mis do
                emitMethod (mb.GetILGenerator()) mVarMap dt b

        for { cb = cb; dt = dt; body = body } in cmap do
            emitMethod (cb.GetILGenerator()) emptyVarMap dt body

let createTypes map = for { t = t } in values map do t.CreateType() |> ignore

let emitIL m { topDefs = ds } =
    let map = HashMap()
    for d in ds do DefineTypes.topDef m map d
    defineTypeParams map
    defineMembers map
    emit map
    createTypes map

module PreDefinedTypes =
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