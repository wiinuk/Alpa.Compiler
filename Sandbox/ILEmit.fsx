module ILEmit

open System
open System.Collections.Generic
open System.Reflection.Emit
open System.Threading

type B = global.System.Reflection.BindingFlags
type CC = global.System.Reflection.CallingConventions
type T = global.System.Reflection.TypeAttributes
type M = global.System.Reflection.MethodAttributes
type P = global.System.Reflection.ParameterAttributes
type F = global.System.Reflection.FieldAttributes
type O = global.System.Reflection.Emit.OpCodes

module List =
    let tryIter2 action ls rs =
        let rec aux ls rs =
            match ls, rs with
            | l::ls, r::rs -> action l r; aux ls rs
            | [], [] -> true
            | _ -> false
        aux ls rs

let mutable private seed = 0

/// type Var<'a> = { id: int; value: 'a option ref }
[<Sealed; NoEquality; NoComparison>]
type Var<'T> =
    val Name: string
    val Id: int
    [<DefaultValue>]
    val mutable internal hasValue: bool
    [<DefaultValue>]
    val mutable internal value: 'T
    new (name) =
        let x = Interlocked.Increment &seed
        {
            Name = name
            Id = x
        }
    new (name, value) as self =
        let x = Interlocked.Increment &seed
        {
            Name = name
            Id = x
        }
        then
            self.hasValue <- true
            self.value <- value

    override x.ToString() =
        if x.hasValue then sprintf "Var(\"%s\", %d, %A)" x.Name x.Id x.value
        else sprintf "Var(\"%s\", %d)" x.Name x.Id

module Var =
    /// Option.isSome x.value
    let hasValue (x: _ Var) = x.hasValue

    let id (x: _ Var) = x.Id

    /// match !x.value with Some x -> x | None -> Unchecked.defaultof<_>
    let getValueOrDefault (x: _ Var) = x.value

    /// x.value := Some value
    let setSomeValue (x: _ Var) value =
        x.hasValue <- true
        x.value <- value

    /// x.value := None
    let setNoneValue (x: _ Var) =
        x.hasValue <- false
        x.value <- Unchecked.defaultof<_>

    let name (v: _ Var) = v.Name

type FullName = FullName of name: string * nestersRev: string list * namespaceRev: string list * assemblyName: string option

type TypeVar = Var<TypeSpec>
and [<NoEquality; NoComparison>] TypeSpec =
    /// ex: [mscorlib]System.Tuple(..., ...)
    | TypeSpec of pathRev: FullName * TypeSpec list
    /// ex: T1
    | TypeVar of Var<TypeSpec>
    /// ex: !0
    | TypeArgRef of int
    /// ex: !!0
    | MethodTypeArgRef of int

type ExtendTypeSpec =
    | ExtendTypeSpec of TypeSpec
    | TypeParamIndex of int
    | MethodTypeParamIndex of int

type Operand =
    | OpNone
    | OpCtor of thisType: TypeSpec * argTypes: TypeSpec list
    | OpI1 of int8
    | OpI4 of int
    | OpType of TypeSpec
    | OpField of thisType: TypeSpec * name: string
    | OpCall of thisType: TypeSpec * name: string * typeArgs: TypeSpec list * argTypes: TypeSpec list

type Macro =
    | BaseInit of TypeSpec list

type Instr = 
    | Instr of string * OpCode * Operand

type Override =
    | Override
    | BaseMethod of baseMethod: (TypeSpec * string)

type Parameter = Parameter of name: string option * TypeSpec
type MethodBody = MethodBody of Instr list
type MethodHead = MethodHead of name: string * typeParams: TypeVar list * pars: Parameter list * ret: Parameter
type MethodInfo = MethodInfo of MethodHead * MethodBody
type StaticMethodInfo = MethodInfo

type LiteralValue =
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

type Literal =
    | LiteralValue of LiteralValue
    | Enum of TypeSpec * LiteralValue
    | Null of TypeSpec

type MemberDef =
    | Literal of name: string * Literal
    | Field of isStatic: bool * isMutable: bool * name: string * TypeSpec
    | AbstractDef of MethodHead
    | CtorDef of pars: Parameter list * MethodBody
    | MethodDef of Override option * MethodInfo

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

type TopDef =
    | TopTypeDef of name: string * TypeDef
    | TopModuleDef of name: string * ModuleMember list

type IL = IL of TopDef list

[<Sealed; AllowNullLiteral>]
type HashMap<'k,'v when 'k : equality>() = inherit Dictionary<'k,'v>()

/// typeParams.Length = typeParamBuilders.Length
type TypeVarMap = TypeVarMap of typeParams: TypeVar list * typeParamBuilders: GenericTypeParameterBuilder list
type MethodSign = string
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

let rec typeSpecEq l r =
    match l, r with
    | TypeSpec(ln, ls), TypeSpec(rn, rs) -> ln = rn && List.length ls = List.length rs && List.forall2 typeSpecEq ls rs
    | TypeVar l, TypeSpec _ -> Var.hasValue l && typeSpecEq (Var.getValueOrDefault l) r
    | TypeSpec _, TypeVar r -> Var.hasValue r && typeSpecEq l (Var.getValueOrDefault r)
    | TypeVar l, TypeVar r -> typeVarEq l r

    | TypeArgRef l, TypeArgRef r -> l = r
    | MethodTypeArgRef l, MethodTypeArgRef r -> l = r
    | _ -> false

and typeVarEq l r =
    match Var.hasValue l, Var.hasValue r with
    | false, false -> Var.id l = Var.id r
    | true, true -> typeSpecEq (Var.getValueOrDefault l) (Var.getValueOrDefault r)
    | false, true ->
        match Var.getValueOrDefault r with
        | TypeVar r -> typeVarEq l r
        | TypeSpec _
        | TypeArgRef _
        | MethodTypeArgRef _ -> false


    | true, false ->
        match Var.getValueOrDefault l with
        | TypeVar l -> typeVarEq l r
        | TypeSpec _
        | TypeArgRef _
        | MethodTypeArgRef _ -> false

let solveTypeVarMap (TypeVarMap(vs,ts)) v =
    match List.tryFindIndex (fun v' -> typeVarEq v v') vs with
    | None -> None
    | Some i -> Some(List.item i ts)

let solveVar varMap mVarMap v =
    match solveTypeVarMap varMap v with
    | Some pb -> pb
    | None ->
        match solveTypeVarMap mVarMap v with
        | Some pb -> pb
        | None -> raise <| KeyNotFoundException()

type SolvedType =
    | RuntimeType of Type
    | Builder of ILTypeBuilder
    | InstantiationType of instantiation: Type * genericTypeDefinition: ILTypeBuilder option * typeArgs: SolvedType list
    | GenericParamBuilder of TypeVar * GenericTypeParameterBuilder

let getType = function
    | RuntimeType t
    | InstantiationType(instantiation = t) -> t
    | Builder { t = t } -> upcast t
    | GenericParamBuilder(_, t) -> upcast t

type SolveEnv = {
    tmap: TypeMap
    varMap: TypeVarMap
    mVarMap: TypeVarMap
    typeArgs: SolvedType list
    mTypeArgs: SolvedType list
}
let rec solveTypeCore ({ tmap = map; varMap = varMap; mVarMap = mVarMap; typeArgs = typeArgs; mTypeArgs = mTypeArgs } as env) t =
    let getGenericTypeDef map pathRev =
        let mutable ti = Unchecked.defaultof<_>
        if tryGet map pathRev &ti then Builder ti
        else RuntimeType <| Type.GetType(toTypeName pathRev, true)
        
    let rec aux = function
    | TypeSpec(pathRev, []) -> getGenericTypeDef map pathRev
    | TypeSpec(pathRev, ts) ->
        let vs = List.map (solveTypeCore env) ts
        let ts = Seq.map getType vs |> Seq.toArray
        match getGenericTypeDef map pathRev with
        | Builder({ t = t } as ti) -> InstantiationType(t.MakeGenericType ts, Some ti, vs)
        | RuntimeType t ->
            let t = t.MakeGenericType ts
            if List.forall (function RuntimeType _ -> true | _ -> false) vs then RuntimeType t
            else InstantiationType(t, None, vs)

        | _ -> failwith "unreach"

    | TypeVar v ->
        if Var.hasValue v then solveTypeCore env (Var.getValueOrDefault v)
        else GenericParamBuilder(v, solveVar varMap mVarMap v)

    | TypeArgRef i -> List.item i typeArgs
    | MethodTypeArgRef i -> List.item i mTypeArgs

    aux t

let solveType env t = solveTypeCore env t |> getType
let solveTypes env ts = Seq.map (solveType env) ts |> Seq.toArray
let solveParamTypes env pars = Seq.map (paramType >> solveType env) pars |> Seq.toArray

let defineVarMap typeParams defineGenericParameters =
    match typeParams with
    | [] -> emptyVarMap
    | _ ->
        let names = Seq.map Var.name typeParams |> Seq.toArray
        TypeVarMap(typeParams, List.ofArray <| defineGenericParameters names)

let mDefineGP (m: MethodBuilder) xs = m.DefineGenericParameters xs
let tDefineGP (t: TypeBuilder) xs = t.DefineGenericParameters xs

let typeParams (TypeVarMap(p,_)) = p

let ctorHead { path = path; varMap = varMap } pars =
    let t = TypeSpec(path, typeParams varMap |> List.map TypeVar)
    MethodHead(".ctor", [], pars, Parameter(None, t))

let addTypeName (FullName(name, nestersRev, nsRev, asmName)) typeName =
    FullName(typeName, name::nestersRev, nsRev, asmName)

let ofTypeName typeName = FullName(typeName, [], [], None)

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

    let rec module' defineType (FullName(name=name) as path) map ms =
        let t = defineType(name, T.Public ||| T.Abstract ||| T.Sealed)
        add map path <| newILTypeBuilder (Choice2Of2 ms) t path map
        for m in ms do moduleMember path t map m

    and type' defineType (FullName(name=name) as path) map ({ kind = kind; members = members } as d) =
        let isInterfaceMember = function 
            | Literal _
            | Field _
            | MethodDef _
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

        let a = a ||| T.Public ||| T.BeforeFieldInit
        let t = defineType(name, a)
        add map path <| newILTypeBuilder (Choice1Of2 d) t path map

    and moduleMember path (t: TypeBuilder) map = function
        | ModuleMethodDef _
        | ModuleValDef _ -> ()
        | ModuleModuleDef(name, ms) -> module' t.DefineNestedType (addTypeName path name) map ms
        | ModuleTypeDef(name, td) -> type' t.DefineNestedType (addTypeName path name) map td

    let topDef (m: ModuleBuilder) map = function
        | TopModuleDef(name, ms) -> module' m.DefineType (ofTypeName name) map ms
        | TopTypeDef(name, td) -> type' m.DefineType (ofTypeName name) map td

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
    let ms = if tryGet mmap sign &ms then m::ms else [m]
    add mmap sign ms

let addCtor (cmap: CtorMap) c = cmap.Add c

let defineParam defineParameter i (Parameter(n, _)) = defineParameter(i, P.None, Option.toObj n) |> ignore
let defineParams defineParameter pars = List.iteri (fun i a -> defineParam defineParameter (i + 1) a) pars

let envOfTypeBuilder mVarMap { map = map; varMap = varMap } = {
    tmap = map
    varMap = varMap
    mVarMap = mVarMap
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

let defineLiteral ({ t = t; fmap = fmap } as ti) name value =
    let a = F.Public ||| F.Static ||| F.Literal
    let fv, ft =
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

        match value with
        | LiteralValue v -> let v = literalValue v in v, v.GetType()
        | Enum(t, v) -> literalValue v, solveType (envOfTypeBuilder emptyVarMap ti) t
        | Null t -> null, solveType (envOfTypeBuilder emptyVarMap ti) t

    let f = t.DefineField(name, ft, a)
    f.SetConstant fv
    add fmap name f

let defineCtor ({ t = t; cmap = cmap } as dt) pars body =
    let pts = solveParamTypes (envOfTypeBuilder emptyVarMap dt) pars
    let c = t.DefineConstructor(M.SpecialName ||| M.RTSpecialName ||| M.Public, CC.HasThis, pts)
    defineParams c.DefineParameter pars
    addCtor cmap { cb = c; dt = dt; pars = pars; body = body }

let defineMember dt = function
    | Field(isStatic, isMutable, n, ft) -> defineField dt (isStatic, isMutable, n, ft)
    | Literal(n, l) -> defineLiteral dt n l
    | MethodDef(ov, m) -> defineMethodDef dt ov m
    | CtorDef(pars, body) -> defineCtor dt pars body
    | AbstractDef head ->
        let a = M.Public ||| M.HideBySig ||| M.NewSlot ||| M.Abstract ||| M.Virtual
        defineMethodHead dt a CC.HasThis head
        |> ignore

let defineModuleMethod ({ mmap = mmap } as dt) (MethodInfo(head, _) as m) =
    let mb, mVarMap = defineMethodHead dt (M.Public ||| M.Static) CC.Standard head
    addMethod mmap head { mb = mb; mVarMap = mVarMap; m = m; dt = dt }

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
    | ModuleMethodDef m -> defineModuleMethod dt m

let defineMembers map =
    for ({ d = d } as ti) in values map do
        match d with
        | Choice1Of2 td -> defineTypeDef ti td
        | Choice2Of2 members -> for m in members do defineModuleMember ti m

/// check: varMap.Length = typeArgs.Length;
/// require: Array.forall (box >> inNull >> not) varMap && Array.forall (fst >> Var.hasValue >> not) varMap
let substTypeArgs (TypeVarMap(typeParams,_)) typeArgs f =
    match typeArgs with
    | [] -> f()
    | _ ->
        try
            if List.tryIter2 Var.setSomeValue typeParams typeArgs then f()
            else invalidArg "typeArgs" "length diff"
        finally
            List.iter Var.setNoneValue typeParams
            
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
    | RuntimeType t -> t.GetField(name, B.DeclaredOnly ||| B.Static ||| B.Instance ||| B.Public ||| B.NonPublic)
    | Builder { fmap = fmap } -> upcast get fmap name
    | InstantiationType(tb, Some { fmap = fmap }, _) -> TypeBuilder.GetField(tb, get fmap name)
    | InstantiationType(tb, None, _) ->
        let fd = tb.GetGenericTypeDefinition().GetField(name, B.DeclaredOnly ||| B.Static ||| B.Instance ||| B.Public ||| B.NonPublic)
        TypeBuilder.GetField(tb, fd)

    | GenericParamBuilder _ -> failwith "getField: GenericParameterBuilder"

type IsMethodBase<'m> = {
    getMTypeParams: 'm -> SolvedType list
    getParameters: 'm -> Reflection.ParameterInfo array
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

let isMethodBaseOfRt = {
    getMTypeParams = fun (m: Reflection.MethodBase) -> if m.IsGenericMethod then m.GetGenericArguments() |> Seq.map RuntimeType |> Seq.toList else []
    getParameters = fun m -> m.GetParameters()
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
    getCtors = fun t -> upcast t.GetConstructors(B.DeclaredOnly ||| B.Public ||| B.NonPublic)
    getTypeParams = fun t -> t.GetGenericArguments() |> Seq.map RuntimeType |> Seq.toList
}

let toTypeParams (TypeVarMap(typeParams, typeParams')) = List.map2 (fun t t' -> GenericParamBuilder(t, t')) typeParams typeParams'

let isMethodInfoOfTb = {
    baseClass =
        {
        getMTypeParams = fun { ILMethodBuilder.mVarMap = mVarMap } -> toTypeParams mVarMap
        getParameters = fun { mb = mb } -> mb.GetParameters()
        }
    toBase = id
    getSystemMethod = fun { mb = mb } -> mb
}
let isCtorOfTb = {
    baseClass =
        {
        getMTypeParams = fun _ -> []
        getParameters = fun { cb = cb } -> cb.GetParameters()
        }
    toBase = id
    getSystemMethod = fun { cb = cb } -> cb
}
let isTypeOfTb = {
    getMethodsOfName = fun name { mmap = mmap } -> upcast get mmap name
    getCtors = fun { cmap = cmap } -> upcast cmap
    getTypeParams = fun { varMap = varMap } -> toTypeParams varMap
}

let parameterType (p: Reflection.ParameterInfo) = p.ParameterType
let getGenericMethod
    { getMethodsOfName = getMethodsOfName; getTypeParams = getTypeParams }
    { getSystemMethod = getSystemMethod
      toBase = toBase
      baseClass = { getMTypeParams = getMTypeParams; getParameters = getParameters }}
    (env, constructedTypeBuilder, genericTypeDef, name, mTypeArgs, argTypes) =

    let typeParams = getTypeParams genericTypeDef
    let m =
        getMethodsOfName name genericTypeDef
        |> Seq.filter (fun m ->
            let m = toBase m
            let pars = getParameters m
            Array.length pars = List.length argTypes &&
            let mTypeParams = getMTypeParams m
            List.length mTypeParams = List.length mTypeArgs &&
            let genericMethodDefParamTypes = solveTypes { env with typeArgs = typeParams; mTypeArgs = mTypeParams } argTypes
            let paramTypes = Seq.map parameterType pars
            Seq.forall2 (=) genericMethodDefParamTypes paramTypes
        )
        |> Seq.exactlyOne

    let m = TypeBuilder.GetMethod(constructedTypeBuilder, getSystemMethod m)
    let mTypeArgs = Seq.map (solveType env) mTypeArgs |> Seq.toArray
    m.MakeGenericMethod mTypeArgs

let getMethod env parent name mTypeArgs argTypes =
    let a = B.DeclaredOnly ||| B.Static ||| B.Instance ||| B.Public ||| B.NonPublic
    let c = CC.Any

    match solveTypeCore env parent with
    | GenericParamBuilder _ -> failwith "param builder"

    | RuntimeType t ->
        let argTypes = Seq.map (solveType env) argTypes |> Seq.toArray
        t.GetMethod(name, a, null, c, argTypes, null)

    | Builder { mmap = mmap } ->
        let { mb = mb } =
            get mmap name
            |> Seq.filter (fun { mVarMap = mVarMap; m = MethodInfo(MethodHead(_,tpars,pars,_),_) } ->
                List.length tpars = List.length mTypeArgs &&
                List.length pars = List.length argTypes &&
                substTypeArgs mVarMap mTypeArgs <| fun _ ->
                    List.forall2
                        (fun (Parameter(_,parType)) argType -> typeSpecEq parType argType)
                        pars
                        argTypes
            )
            |> Seq.exactlyOne
        upcast mb

    | InstantiationType(instantiation, None, _) -> getGenericMethod isTypeOfRt isMethodInfoOfRt (env, instantiation, instantiation.GetGenericTypeDefinition(), name, mTypeArgs, argTypes)
    | InstantiationType(instantiation, Some genericTypeDef, _) -> getGenericMethod isTypeOfTb isMethodInfoOfTb (env, instantiation, genericTypeDef, name, mTypeArgs, argTypes)

let getGenericCtor
    { getCtors = getCtors; getTypeParams = getTypeParams }
    { baseClass = { getParameters = getParameters }; toBase = toBase; getSystemMethod = getSystemMethod }
    (env, constructedTypeBuilder, genericTypeDef, argTypes) =

    let typeParams = getTypeParams genericTypeDef
    let m =
        getCtors genericTypeDef
        |> Seq.filter (fun m ->
            let m = toBase m
            let pars = getParameters m
            Array.length pars = List.length argTypes &&
            let genericMethodDefParamTypes = solveTypes { env with typeArgs = typeParams } argTypes
            let paramTypes = Seq.map parameterType pars
            Seq.forall2 (=) genericMethodDefParamTypes paramTypes
        )
        |> Seq.exactlyOne

    TypeBuilder.GetConstructor(constructedTypeBuilder, getSystemMethod m)

let getCtor env parent argTypes =
    match solveTypeCore env parent with
    | GenericParamBuilder _ -> failwith "param builder"
    | RuntimeType t ->
        let argTypes = Seq.map (solveType env) argTypes |> Seq.toArray
        t.GetConstructor(B.DeclaredOnly ||| B.Public ||| B.NonPublic, null, CC.Any, argTypes, null)

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
        
    | InstantiationType(instantiation, None, _) -> getGenericCtor isTypeOfRt isCtorOfRt (env, instantiation, instantiation.GetGenericTypeDefinition(), argTypes)
    | InstantiationType(instantiation, Some genericTypeDef, _) -> getGenericCtor isTypeOfTb isCtorOfTb (env, instantiation, genericTypeDef, argTypes)

let emitInstr (g: ILGenerator) mVarMap dt (Instr(label, op, operand)) =
    match operand with
    | OpNone -> g.Emit op
    | OpI1 n -> g.Emit(op, n)
    | OpI4 n -> g.Emit(op, n)
    | OpType t -> g.Emit(op, solveType (envOfTypeBuilder mVarMap dt) t)
    | OpField(parent, name) -> g.Emit(op, getField (envOfTypeBuilder mVarMap dt) parent name)
    | OpCall(parent, name, mTypeArgs, argTypes) -> g.Emit(op, getMethod (envOfTypeBuilder mVarMap dt) parent name mTypeArgs argTypes)
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

let emitIL m (IL ds) =
    let map = HashMap()
    for d in ds do DefineTypes.topDef m map d
    defineTypeParams map
    defineMembers map
    emit map
    createTypes map
