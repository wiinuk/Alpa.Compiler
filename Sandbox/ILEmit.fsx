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

let mutable seed = 0

type Vector<'a> = struct
    val internal items: 'a array
    internal new (items) = { items = items }
end
module Vector =
    type EmptyArray<'a> () =
        static let a: 'a array = [||]
        static member Value = a

    let empty<'a> = Vector EmptyArray<'a>.Value
    let private unsafeUnwrap (xs: _ Vector) = xs.items

    let tryFindIndexOrM1 pred xs =
        let items = unsafeUnwrap xs
        let l = items.Length
        let rec aux i =
            if l <= i then -1
            elif pred items.[i] then i
            else aux(i+1)
        aux 0

    let item i xs = unsafeUnwrap(xs).[i]
    let length xs = unsafeUnwrap(xs).Length
    
    let replicate count initial = Vector(Array.replicate count initial)

    let ofList xs = Vector(Array.ofList xs)
    let ofArray xs = Vector(Array.copy xs)

    let tryIter2 f xs1 xs2 =
        let items1 = unsafeUnwrap xs1
        let items2 = unsafeUnwrap xs2
        items1.Length = items2.Length &&
            let l = items1.Length
            let rec aux i = l <= i || (f items1.[i] items2.[i]; aux(i+1))
            aux 0

    let iter f xs =
        let items = unsafeUnwrap xs
        let l = items.Length
        let rec aux i = if l <= i then () else f items.[i]; aux (i+1)
        aux 0

    let toSeq xs = unsafeUnwrap xs :> _ seq
    let mapToArray mapping xs = Array.map mapping (unsafeUnwrap xs)
    let mapToList mapping xs =
        let items = unsafeUnwrap xs
        Array.foldBack (fun x rs -> mapping x::rs) items []

/// type Var<'a> = { id: int; value: 'a option ref }
[<Sealed; CustomEquality; CustomComparison>]
type Var<[<EqualityConditionalOn; ComparisonConditionalOn>] 'T> =
    val Name: string
    val internal id: int
    [<DefaultValue>]
    val mutable internal hasValue: bool
    [<DefaultValue>]
    val mutable internal value: 'T
    new (name) =
        let x = Interlocked.Increment &seed
        {
            Name = name
            id = x
        }
    new (name, value) as self =
        let x = Interlocked.Increment &seed
        {
            Name = name
            id = x
        }
        then
            self.hasValue <- true
            self.value <- value
    
    override x.ToString() =
        if x.hasValue then sprintf "Var(\"%s\", %A)" x.Name x.value
        else sprintf "Var(\"%s\")" x.Name
        
    override x.GetHashCode() = if x.hasValue then Unchecked.hash x.value else x.id
    static member private Eq(l: _ Var, r: _ Var) =
        match l.hasValue, r.hasValue with
        | true, true -> Unchecked.equals l.value r.value
        | false, false -> l.id = r.id
        | _ -> false

    override l.Equals r =
        match r with
        | :? Var<'T> as r -> Var<_>.Eq(l, r)
        | _ -> false

    interface IEquatable<Var<'T>> with
        override l.Equals r = Var<_>.Eq(l, r)

module Var =
    /// Option.isSome x.value
    let hasValue (x: _ Var) = x.hasValue

    /// !x.value
    let getValue x = if hasValue x then Some x.value else None
    
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
and TypeSpec = 
    | TypeSpec of pathRev: FullName * TypeSpec list
    | TypeVar of Var<TypeSpec>

type Operand =
    | OpNone
    | OpCtor of thisType: TypeSpec * argTypes: TypeSpec list
    | OpI1 of int8
    | OpI4 of int
    | OpType of TypeSpec
    | OpField of thisType: TypeSpec * name: string
    | OpCall of isStatic: bool * thisType: TypeSpec * name: string * typeArgs: TypeSpec list * argTypes: TypeSpec list

type Macro =
    | BaseInit of TypeSpec list

type Instr = 
    | Instr of string * OpCode * Operand
    | Macro of Macro

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
    | DateTime of DateTime
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
type TypeVarMap = TypeVarMap of typeParams: TypeVar Vector * typeParamBuilders: GenericTypeParameterBuilder Vector
type MethodSign = string
type TypeBuilderInfo = {
    d: Choice<TypeDef, ModuleMember list>
    t: TypeBuilder

    path: FullName

    mutable varMap: TypeVarMap
    /// SourceEnv
    map: TypeMap
    /// MethodMap
    mmap: MethodMap
}
and MethodBuilderInfo = {
    /// MethodBuilder
    mb: Choice<MethodBuilder, ConstructorBuilder>
    /// DeclaringType
    dt: TypeBuilderInfo
    /// Method
    m: MethodInfo
    mVarMap: TypeVarMap
}
and MethodMap = HashMap<MethodSign, MethodBuilderInfo list>
and TypeMap = HashMap<FullName, TypeBuilderInfo>

let add (map: HashMap<_,_>) k v = map.Add(k, v)
let get (map: HashMap<_,_>) k = map.[k]
let tryGet (map: HashMap<_,_>) k (v: _ byref) = map.TryGetValue(k, &v)

let values (map: HashMap<_,_>) = map.Values
let pathToNs (p,ps) = p::ps
let nsToPath ps name = name, ps
let paramType (Parameter(_,t)) = t
let emptyVarMap = TypeVarMap(Vector.empty, Vector.empty)
    
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

type SolvedType =
    | SBuilderType of TypeBuilderInfo
    | SBuilderGeneric of t: Type * genericDef: TypeBuilderInfo * genericArgs: SolvedType list
    | SType of Type
    | STypeVar of TypeVar * GenericTypeParameterBuilder

let solveTypeVarMap (TypeVarMap(vs,ts)) v =
    match Vector.tryFindIndexOrM1 (fun v' -> v = v') vs with
    | -1 -> None
    | i -> Some(Vector.item i ts)

let solveVar varMap mVarMap v =
    match solveTypeVarMap varMap v with
    | Some pb -> pb
    | None ->
        match solveTypeVarMap mVarMap v with
        | Some pb -> pb
        | None -> raise <| KeyNotFoundException()

let rec solveTypeCore typeMap varMap mVarMap t =
    let getGenericDef typeMap pathRev =
        let mutable ti = Unchecked.defaultof<_>
        if tryGet typeMap pathRev &ti then SBuilderType ti
        else SType <| Type.GetType(toTypeName pathRev, true)

    let rec aux = function
    | TypeSpec(pathRev, []) -> getGenericDef typeMap pathRev
    | TypeSpec(pathRev, vs) ->
        let vs = List.map (fun t -> solveTypeCore typeMap varMap mVarMap t) vs
        let vts =
            Seq.map (function
                | SType t
                | SBuilderGeneric(t = t) -> t
                | SBuilderType { t = td } -> upcast td
                | STypeVar(_, t) -> upcast t
            ) vs
            |> Seq.toArray

        match getGenericDef typeMap pathRev with
        | SBuilderType({ t = td } as ti) -> SBuilderGeneric(td.MakeGenericType vts, ti, vs)
        | SType td -> SType <| td.MakeGenericType vts
        | SBuilderGeneric _
        | STypeVar _ -> failwith "unreach"

    | TypeVar v ->
        if Var.hasValue v then solveTypeCore typeMap varMap mVarMap <| Var.getValueOrDefault v
        else STypeVar(v, solveVar varMap mVarMap v)
    aux t

let solveType map varMap mVarMap t =
    match solveTypeCore map varMap mVarMap t with
    | SBuilderGeneric(t = t)
    | SType t -> t
    | SBuilderType { t = t } -> upcast t
    | STypeVar(_, t) -> upcast t

let solveTypes map varMap mVarMap ts =
    Seq.map (solveType map varMap mVarMap) ts
    |> Seq.toArray
    
let solveParamTypes map varMap mVarMap pars =
    Seq.map (paramType >> solveType map varMap mVarMap) pars
    |> Seq.toArray

let defineVarMap typeParams defineGenericParameters =
    match typeParams with
    | [] -> emptyVarMap
    | _ ->
        let typeParams = Vector.ofList typeParams
        let names = Vector.mapToArray Var.name typeParams
        TypeVarMap(typeParams, Vector.ofArray <| defineGenericParameters names)

let mDefineGP (m: MethodBuilder) xs = m.DefineGenericParameters xs
let tDefineGP (t: TypeBuilder) xs = t.DefineGenericParameters xs

let typeParams (TypeVarMap(p,_)) = p

let ctorHead { path = path; varMap = varMap } pars =
    let t = TypeSpec(path, typeParams varMap |> Vector.mapToList TypeVar)
    MethodHead(".ctor", [], pars, Parameter(None, t))

let addTypeName (FullName(name, nestersRev, nsRev, asmName)) typeName =
    FullName(typeName, name::nestersRev, nsRev, asmName)

let ofTypeName typeName = FullName(typeName, [], [], None)

module DefineTypes =
    let rec module' defineType (FullName(name=name) as path) map ms =
        let t = defineType(name, T.Public ||| T.Abstract ||| T.Sealed)
        add map path {
            d = Choice2Of2 ms
            t = t
            path = path
            varMap = emptyVarMap
            map = map
            mmap = HashMap()
        }
        for m in ms do moduleMember path t map m

    and type' defineType (FullName(name=name) as path) map ({ kind = kind; typeParams = typeParams; members = members } as d) =
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
        add map path {
            t = t
            d = Choice1Of2 d
            path = path
            map = map
            varMap = emptyVarMap
            mmap = HashMap()
        }

    and moduleMember path (t: TypeBuilder) map = function
        | ModuleMethodDef _
        | ModuleValDef _ -> ()
        | ModuleModuleDef(name, ms) -> module' t.DefineNestedType (addTypeName path name) map ms
        | ModuleTypeDef(name, td) -> type' t.DefineNestedType (addTypeName path name) map td

    let topDef (m: ModuleBuilder) map = function
        | TopModuleDef(name, ms) -> module' m.DefineType (ofTypeName name) map ms
        | TopTypeDef(name, td) -> type' m.DefineType (ofTypeName name) map td

let copyToArray source target =
    if Array.length source <> Array.length target then invalidArg "source" "array length"
    Array.blit source 0 target 0 source.Length

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

module DefineMembers =
    let param defineParameter i (Parameter(n, _)) = defineParameter(i, P.None, Option.toObj n) |> ignore
    let params' defineParameter pars = List.iteri (fun i a -> param defineParameter (i + 1) a) pars
    
    let methodHead { t = t; map = map; varMap = varMap } attr callconv (MethodHead(name,typeParams,pars,ret)) =
        let m = t.DefineMethod(name, attr, callconv)
        let mVarMap = defineVarMap typeParams <| mDefineGP m
        
        m.SetReturnType(solveType map varMap mVarMap (paramType ret))
        m.SetParameters(solveParamTypes map varMap mVarMap pars)

        param m.DefineParameter 0 ret
        params' m.DefineParameter pars

        m, mVarMap

    let methodInfo ({ mmap = mmap } as dt) a c (MethodInfo(head, _) as m) =
        let mb, mVarMap = methodHead dt a c head
        addMethod mmap head { mb = Choice1Of2 mb; m = m; dt = dt; mVarMap = mVarMap }

    let methodDef dt ov m =
        match ov with
        | None -> methodInfo dt (M.Public ||| M.Final ||| M.HideBySig) CC.Standard m
        | Some Override ->
            let a = M.Public ||| M.Final ||| M.HideBySig ||| M.NewSlot ||| M.Virtual
            methodInfo dt a CC.HasThis m

        | Some(BaseMethod _) ->
            let a = M.Private ||| M.Final ||| M.HideBySig ||| M.NewSlot ||| M.Virtual
            methodInfo dt a CC.HasThis m
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

    let field { t = t; map = map; varMap = varMap } (isStatic, isMutable, name, ft) =
        let a = F.Public
        let a = if isStatic then a ||| F.Static else a
        let a = if isMutable then a else a ||| F.InitOnly
        let ft = solveType map varMap emptyVarMap ft
        t.DefineField(name, ft, a)

    let literal { t = t; map = map; varMap = varMap } n l =
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
                | DateTime v -> box v
                | Char v -> box v
                | String v -> box v

            match l with
            | LiteralValue v -> let v = literalValue v in v, v.GetType()
            | Enum(t, v) -> literalValue v, solveType map varMap emptyVarMap t
            | Null t -> null, solveType map varMap emptyVarMap t

        let f = t.DefineField(n, ft, a)
        f.SetConstant fv

    let ctorDef ({ t = t; map = map; varMap = varMap; mmap = mmap } as dt) pars body =
        let pts = solveParamTypes map varMap emptyVarMap pars
        let c = t.DefineConstructor(M.SpecialName ||| M.RTSpecialName ||| M.Public, CC.HasThis, pts)
                            
        params' c.DefineParameter pars

        let h = ctorHead dt pars
        let m = MethodInfo(h, body)
        addMethod mmap h { mb = Choice2Of2 c; m = m; dt = dt; mVarMap = emptyVarMap }

    let member' dt = function
        | Field(isStatic, isMutable, n, ft) ->
            let f = field dt (isStatic, isMutable, n, ft)
            ()

        | Literal(n, l) -> literal dt n l
        | MethodDef(ov, m) -> methodDef dt ov m
        | CtorDef(pars, body) -> ctorDef dt pars body
        | AbstractDef head ->
            let a = M.Public ||| M.HideBySig ||| M.NewSlot ||| M.Abstract ||| M.Virtual
            methodHead dt a CC.HasThis head
            |> ignore

    let moduleMethod ({ mmap = mmap } as dt) (MethodInfo(head, _) as m) =
        let mb, mVarMap = methodHead dt (M.Public ||| M.Static) CC.Standard head
        addMethod mmap head { mb = Choice1Of2 mb; m = m; dt = dt; mVarMap = mVarMap }

    let typeDef ({ t = t; map = map; varMap = varMap } as ti) { parent = parent; impls = impls; members = members } =
        match parent with
        | Some parent -> t.SetParent <| solveType map varMap emptyVarMap parent
        | _ -> ()

        for impl in impls do t.AddInterfaceImplementation <| solveType map varMap emptyVarMap impl
        for m in members do member' ti m

    let moduleMember dt = function
        | ModuleTypeDef _
        | ModuleModuleDef _ -> ()
        | ModuleValDef(isMutable, name, ft) ->
            let f = field dt (true, isMutable, name, ft)
            ()
        | ModuleMethodDef m -> moduleMethod dt m

    let defineMembers map =
        for ({ d = d } as ti) in values map do
            match d with
            | Choice1Of2 td -> typeDef ti td
            | Choice2Of2 members -> for m in members do moduleMember ti m

// type C (a) = fun M (b) (a, b) : b
//
// call C(char)::M (int) (char, int)
// call C(char)::M (int) (char, char) // invalid
// call C(char)::M (int) (int, char) // invalid
// call C(char)::M (int) (int, int) // invalid
//
// call C(char)::M (char) (char, char)
// call C(char)::M (char) (int, char) // invalid
// call C(char)::M (char) (char, int) // invalid
// call C(char)::M (char) (int, int) // invalid

/// check: varMap.Length = typeArgs.Length;
/// require: Array.forall (box >> inNull >> not) varMap && Array.forall (fst >> Var.hasValue >> not) varMap
let substTypeArgs (TypeVarMap(typeParams,_) as varMap) typeArgs f =
    try
        if Vector.tryIter2 Var.setSomeValue typeParams typeArgs then f varMap
        else invalidArg "typeArgs" "length diff"
    finally
        Vector.iter Var.setNoneValue typeParams

let findMethod { mmap = mmap; varMap = varMap } typeArgs name mTypeArgs argTypes = substTypeArgs varMap typeArgs <| fun _ ->
    get mmap name
    |> List.find (function
        | { mVarMap = TypeVarMap(mTypeParams,_) as mVarMap; m = MethodInfo(MethodHead(pars = pars), _)
            } ->
            List.length pars = List.length argTypes &&
            Vector.length mTypeParams = Vector.length mTypeArgs &&
            substTypeArgs mVarMap mTypeArgs <| fun _ ->
                List.forall2
                    (fun (Parameter(_,parType)) argType -> parType = argType)
                    pars
                    argTypes
    )

//    match solveTypeCore map varMap mVarMap t with
//    | SType t -> t.GetConstructor(B.Public ||| B.NonPublic, null, solveTypes map varMap mVarMap ts, null)
//
//    | SBuilderType { mmap = parentMMap } -> findMethod ts parentMMap
//
//    | SBuilderGeneric(t, genericDef, genericParams) -> failwith "Not implemented yet"
//    | STypeVar(_, _) -> failwith "Not implemented yet"

let emitMacroInstr (g: ILGenerator) typeArgs { mVarMap = mVarMap; dt = { map = map; varMap = varMap; d = d }} = function
    | BaseInit ts ->
        let ctor =
            match d with
            | Choice1Of2 { parent = Some parent } ->
                match solveTypeCore map varMap mVarMap parent with
                | SType t -> t.GetConstructor(B.Public ||| B.NonPublic, null, solveTypes map varMap mVarMap ts, null)
                | SBuilderType ti ->
                    match findMethod ti typeArgs ".ctor" Vector.empty ts with
                    | { mb = Choice2Of2 c } -> upcast c
                    | _ -> failwith "unreach"

                | SBuilderGeneric(t, genericDef, genericTypeArgs) ->
                    failwith "Not implemented yet"

                | STypeVar(_, _) -> failwith "Not implemented yet"

            | Choice1Of2 { parent = None }
            | Choice2Of2 _ ->
                typeof<obj>.GetConstructor(B.Public ||| B.NonPublic, null, solveTypes map varMap mVarMap ts, null)
                
        if List.isEmpty ts then g.Emit O.Ldarg_0 else ()
        g.Emit(O.Call, ctor)

let emitInstr (g: ILGenerator) ({ mVarMap = mVarMap; dt = { map = map; varMap = varMap; typeArgs = typeArgs; path = path; mmap = mmap; d = d } as dt } as ti) = function
    | Macro macro -> emitMacroInstr g typeArgs ti macro
    | Instr(label, op, operand) ->
        match operand with
        | OpNone -> g.Emit op
        | OpI1 n -> g.Emit(op, n)
        | OpI4 n -> g.Emit(op, n)
        | OpType t -> g.Emit(op, solveType map varMap mVarMap t)
        | OpField(parent, name) ->
            let parent = solveType map varMap mVarMap parent
            let f = parent.GetField(name, B.Static ||| B.Instance ||| B.Public ||| B.NonPublic)
            g.Emit(op, f)

        | OpCtor(parent, argTypes) ->
            let parent = solveType map varMap mVarMap parent
            let argTypes = solveTypes map varMap mVarMap argTypes
            let ctor = parent.GetConstructor(B.Public ||| B.NonPublic, null, argTypes, null)
            g.Emit(op, ctor)

        | OpCall(isStatic, parent, name, typeArgs, argTypes) ->
            let parent = solveType map varMap mVarMap parent
            let argTypes = solveTypes map varMap mVarMap argTypes
            let b = if isStatic then B.Static else B.Instance
            let b = b ||| B.Public ||| B.NonPublic
            let m = parent.GetMethod(name, b, null, argTypes, null)
            let m =
                if List.isEmpty typeArgs then m
                else
                    let argTypes = solveTypes map varMap mVarMap typeArgs
                    m.MakeGenericMethod(argTypes)
            g.Emit(op, m)

let emitMethodBody ({ mb = mb; m = MethodInfo(_, MethodBody instrs) } as mi) =
    let g =
        match mb with
        | Choice1Of2 m -> m.GetILGenerator()
        | Choice2Of2 m -> m.GetILGenerator()

    for instr in instrs do emitInstr g mi instr

let emit map =
    for { mmap = mmap } in values map do
        for mi in values mmap do
            emitMethodBody mi

let createTypes map = for { t = t } in values map do t.CreateType() |> ignore

let emitIL m (IL ds) =
    let map = HashMap()
    for d in ds do DefineTypes.topDef m map d
    defineTypeParams map
    for d in ds do DefineMembers.topDef map d
    emit map
    createTypes map
