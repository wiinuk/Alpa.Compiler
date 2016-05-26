module internal ILEmit

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
type TypeVar = struct
    val Name: string
    val Value: int
    new (name) =
        let x = Interlocked.Increment &seed
        {
            Name = name
            Value = x
        }
    override x.ToString() = sprintf "TypeVar \"%s\"" x.Name
end

type ValidName = struct
    val EscapedName: string
    private new (n, isEscape) =
        if isEscape then
            let n =
                if String.exists (function '`' | '\\' -> true | c -> c = Type.Delimiter) n then
                    let delim = sprintf "\\u%04x" <| int System.Type.Delimiter
                    String.collect (function '`' -> "\\u0060" | '\\' -> "\\u005c" | c -> if c = Type.Delimiter then delim else string c) n
                else n
            { EscapedName = n }
        else { EscapedName = n }

    new (n) = ValidName(n, true)
    override x.ToString() = sprintf "e\"%s\"" x.EscapedName
    static member NonEscape n = ValidName(n, false)
end
type PathRev = ValidName * ValidName list

type TypeRef = 
    | TypeRef of pathRev: PathRev * TypeRef list
    | TypeVar of TypeVar

type RealType = RealType of name: PathRev * TypeRef list

type Operand =
    | OpNone
    | OpCtor of thisType: TypeRef * argTypes: TypeRef list
    | OpI1 of int8
    | OpI4 of int
    | OpType of TypeRef
    | OpField of thisType: TypeRef * name: string
    | OpCall of isStatic: bool * thisType: TypeRef * name: string * typeArgs: TypeRef list * argTypes: TypeRef list

type Macro =
    | BaseInit of TypeRef list

type Instr = 
    | Instr of string * OpCode * Operand
    | Macro of Macro

type Argument = Argument of name: string option * TypeRef
type MethodBody = MethodBody of Instr list
type MethodHead =
    | CtorHead of args: Argument list
    | MethodHead of name: string * typeArgs: TypeVar list * args: Argument list * ret: Argument

type MethodBase = MethodBase of MethodHead * MethodBody
type StaticMethodInfo = MethodBase

type Override =
    | Override
    | BaseMethod of baseMethod: (RealType * string)

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
    | DateTime of System.DateTime
    | Char of char
    | String of string

type Literal =
    | LiteralValue of LiteralValue
    | Enum of TypeRef * LiteralValue
    | Null of TypeRef

type MemberDef =
    | Literal of name: string * Literal
    | Field of isStatic: bool * isMutable: bool * name: string * TypeRef
    | AbstractDef of MethodHead
    | MethodBaseDef of MethodBase

type TypeKind = Abstract | Interface | Open | Sealed
type TypeDef = {
    kind: TypeKind option
    name: ValidName
    typeArgs: TypeVar list
    parent: RealType option
    impls: RealType list
    members: MemberDef list
}
type ModuleMember =
    | ModuleMethodDef of StaticMethodInfo
    | ModuleTypeDef of TypeDef
    | ModuleModuleDef of name: ValidName * ModuleMember list

type TopDef =
    | TopTypeDef of TypeDef
    | TopModuleDef of name: ValidName * ModuleMember list

type IL = IL of TopDef list

[<Sealed; AllowNullLiteral>]
type HashMap<'k,'v when 'k : equality>() = inherit Dictionary<'k,'v>()
type TypeVarMap = (TypeVar * GenericTypeParameterBuilder) array
type MethodBuilderInfo = (unit -> ILGenerator) * MethodBase * TypeVarMap
type TypeBuilderInfo = {
    t: TypeBuilder
    varMap: TypeVarMap
    mmap: HashMap<MethodHead, MethodBuilderInfo>
}
type TypeMap = HashMap<PathRev, TypeBuilderInfo>

let escaped (x: ValidName) = x.EscapedName
let varName (v: TypeVar) = v.Name
let add (map: HashMap<_,_>) k v = map.Add(k, v)
let get (map: HashMap<_,_>) k = map.[k]
let values (map: HashMap<_,_>) = map.Values
let pathToNs (p,ps) = p::ps
let nsToPath ps name = name, ps
let typeRefToType (RealType(n,ts)) = TypeRef(n,ts)
let argType (Argument(_,t)) = t
let emptyVarMap : TypeVarMap = [||]
    
let toTypeName (delim: char) (p, path) =
    match path with
    | [] -> escaped p
    | _ ->
        let cs = System.Text.StringBuilder(escaped p)
        for p in path do
            cs.Insert(0, delim) |> ignore
            cs.Insert(0, escaped p) |> ignore
        cs.ToString()

let solveType typeMap varMap t =
    let get (typeMap: HashMap<_,_>) pathRev arity =
        let mutable ti = Unchecked.defaultof<_>
        if typeMap.TryGetValue(pathRev, &ti) then
            let { t = t } = ti
            t :> Type

        else
            let n = toTypeName Type.Delimiter pathRev
            let n = if arity = 0 then n else n + "`" + string arity
            Type.GetType(n, true)

    let rec aux = function
    | TypeRef(pathRev, []) -> get typeMap pathRev 0
    | TypeRef(pathRev, ts) -> get typeMap pathRev <| List.length ts
    | TypeVar v ->
        varMap
        |> Array.find (fun (v': TypeVar, _: GenericTypeParameterBuilder) -> v.Value = v'.Value)
        |> snd
        :> System.Type
    aux t

let solveTypes map varMap ts =
    Seq.map (solveType map varMap) ts
    |> Seq.toArray
    
let solveParamTypes map varMap args =
    Seq.map (argType >> solveType map varMap) args
    |> Seq.toArray

let makeVarMap typeArgs defineGenericParameters =
    match typeArgs with
    | [] -> [||]
    | _ ->
        let typeArgs = List.toArray typeArgs
        let names = typeArgs |> Array.map varName
        Array.zip typeArgs <| defineGenericParameters names

let mDefineGP (m: MethodBuilder) xs = m.DefineGenericParameters xs
let tDefineGP (t: TypeBuilder) xs = t.DefineGenericParameters xs

let ctorHead parentPath parentTypeArgs args =
    let t = TypeRef(parentPath, List.map TypeVar parentTypeArgs)
    MethodHead(".ctor", [], args, Argument(None, t))

module DefineTypes =
    let rec module' defineType nsRev name map ms =
        let t = defineType(escaped name, T.Public ||| T.Abstract ||| T.Sealed)
        let path = nsToPath nsRev name
        add map path {
            t = t
            varMap = emptyVarMap
            mmap = HashMap()
        }
        for m in ms do moduleMember path t map m

    and type' defineType nsRev map { kind = kind; typeArgs = typeArgs; name = name; members = members } =
        let isInterfaceMember = function 
            | Literal _
            | Field _
            | CtorDef _
            | MethodDef _ -> false
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

        let t = defineType(escaped name, a)
        add map (nsToPath nsRev name) {
            t = t
            varMap = Array.zeroCreate <| List.length typeArgs
            mmap = HashMap()
        }

    and moduleMember path (t: TypeBuilder) map = function
        | ModuleMethodDef(MethodBase _) -> ()
        | ModuleModuleDef(name, ms) -> module' t.DefineNestedType (pathToNs path) name map ms
        | ModuleTypeDef td -> type' t.DefineNestedType (pathToNs path) map td

    let topDef (m: ModuleBuilder) map = function
        | TopModuleDef(name, ms) -> module' m.DefineType [] name map ms
        | TopTypeDef td -> type' m.DefineType [] map td

module DefineMembers =
    let param defineParameter i (Argument(pn, _)) = defineParameter(i, P.None, Option.toObj pn) |> ignore
    let params' defineParameter args = List.iteri (fun i a -> param defineParameter (i + 1) a) args
    
    let methodHead defineMethod attr callconv (map, varMap) (MethodHead(name,typeArgs,args,ret)) =
        let m = defineMethod(name, attr, callconv)
        let mVarMap = makeVarMap typeArgs <| mDefineGP m
        let varMap = Array.append varMap mVarMap

        let pts = solveParamTypes map varMap args
        m.SetParameters(pts)
        params' m.DefineParameter args

        let rt = solveType map varMap (argType ret)
        m.SetReturnType rt
        param m.DefineParameter 0 ret
        m, varMap

    let methodInfo (t: TypeBuilder) a c (map, mmap, varMap) (MethodBase(head, body)) =
        let m, varMap = methodHead t.DefineMethod a c (map, varMap) head
        add mmap head ((m.GetILGenerator : unit -> _), body, varMap)

    let methodDef (t: TypeBuilder) maps ov m =
        match ov with
        | None -> methodInfo t (M.Public ||| M.HideBySig) CC.Standard maps m
        | Some Override ->
            let a = M.Public ||| M.Final ||| M.HideBySig ||| M.NewSlot ||| M.Virtual
            methodInfo t a CC.Standard maps m

        | Some(BaseMethod _) ->
            let a = M.Private ||| M.Final ||| M.HideBySig ||| M.NewSlot ||| M.Virtual
            methodInfo t a CC.HasThis maps m

                    // TODO: last path
//                        let bt = solveType map varMap <| typeRefToType baseType
//                        let pts = solveParamTypes map varMap args
//                        let bm = bt.GetMethod(baseMethodName, pts)
//                        t.DefineMethodOverride(bm, m)

    let member' path (t: TypeBuilder) typeArgs (map, mmap, varMap) = function
        | Field(isStatic, isMutable, n, ft) ->
            let a = F.Public
            let a = if isStatic then a ||| F.Static else a
            let a = if isMutable then a else a ||| F.InitOnly
            let ft = solveType map varMap ft
            t.DefineField(n, ft, a) |> ignore

        | Literal(n, l) ->
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
                | Enum(t, v) -> literalValue v, solveType map varMap t
                | Null t -> null, solveType map varMap t

            let f = t.DefineField(n, ft, a)
            f.SetConstant fv

        | MethodDef(ov, m) -> methodDef t (map, mmap, varMap) ov m
        | CtorDef(args, body) ->
            let pts = solveParamTypes map varMap args
            let c = t.DefineConstructor(M.SpecialName ||| M.RTSpecialName ||| M.Public, CC.HasThis, pts)
                            
            params' c.DefineParameter args

            let h = ctorHead path typeArgs args
            let head = ctorHead (ValidName ".ctor", [])
            add mmap h (c.GetILGenerator, body, varMap)

        | AbstractDef head ->
            let a = M.Public ||| M.HideBySig ||| M.NewSlot ||| M.Abstract ||| M.Virtual
            methodHead t.DefineMethod a CC.HasThis (map, varMap) head
            |> ignore

    let moduleMethod (t: TypeBuilder) map mmap (MethodBase(head, body)) =
        let m, varMap = methodHead t.DefineMethod (M.Public ||| M.Static) CC.Standard (map, emptyVarMap) head
        add mmap head ((m.GetILGenerator : unit -> _), body, varMap)

    let typeDef nsRev map { name = name; typeArgs = typeArgs; parent = parent; impls = impls; members = members } =
        let path = name, nsRev
        let { t = t; varMap = varMap; mmap = mmap } = get map path
        let varMap' = makeVarMap typeArgs <| tDefineGP t
        Array.blit varMap' 0 varMap 0 varMap'.Length

        match parent with
        | Some parent -> t.SetParent <| solveType map varMap (typeRefToType parent)
        | _ -> ()

        for impl in impls do t.AddInterfaceImplementation <| solveType map varMap (typeRefToType impl)
        for m in members do member' path t typeArgs (map, mmap, varMap) m

    let rec moduleMember path (t: TypeBuilder) map mmap = function
        | ModuleMethodDef m -> moduleMethod t map mmap m
        | ModuleTypeDef td -> typeDef (pathToNs path) map td
        | ModuleModuleDef(name, members) -> moduleDef (pathToNs path) name members map

    and moduleDef nsRev name members map =
        let path = nsToPath nsRev name
        let { t = t; mmap = mmap } = get map path
        t.SetParent <| typeof<obj>
        for m in members do moduleMember path t map mmap m

    // TODO: use *Builder lookup method?
    let topDef map = function
        | TopModuleDef(name, members) -> moduleDef [] name members map
        | TopTypeDef td -> typeDef [] map td

let emitInstr (g: ILGenerator) map varMap head = function
    | Macro(BaseInit ts) -> failwith "Not implemented yet"
    | Instr(label, op, operand) ->
        match operand with
        | OpNone -> g.Emit op
        | OpI1 n -> g.Emit(op, n)
        | OpI4 n -> g.Emit(op, n)
        | OpType t -> g.Emit(op, solveType map varMap t)
        | OpField(parent, name) ->
            let parent = solveType map varMap parent
            let f = parent.GetField(name, B.Static ||| B.Instance ||| B.Public ||| B.NonPublic)
            g.Emit(op, f)

        | OpCtor(parent, argTypes) ->
            let parent = solveType map varMap parent
            let argTypes = solveTypes map varMap argTypes
            let ctor = parent.GetConstructor argTypes
            g.Emit(op, ctor)

        | OpCall(isStatic, parent, name, typeArgs, argTypes) ->
            let parent = solveType map varMap parent
            let argTypes = solveTypes map varMap argTypes
            let b = if isStatic then B.Static else B.Instance
            let b = b ||| B.Public ||| B.NonPublic
            let m = parent.GetMethod(name, b, null, argTypes, null)
            let m =
                if List.isEmpty typeArgs then m
                else
                    let argTypes = solveTypes map varMap typeArgs
                    m.MakeGenericMethod(argTypes)
            g.Emit(op, m)

let emitMethodBody map (gen, MethodBase(head, MethodBody instrs), varMap) =
    let g = gen()
    for instr in instrs do emitInstr g map varMap head instr

let emit map =
    for { mmap = mmap } in values map do    
        for mi in values mmap do
            emitMethodBody map mi

let createTypes map = for { t = t } in values map do t.CreateType() |> ignore

let emitIL m (IL ds) =
    let map = HashMap()
    for d in ds do DefineTypes.topDef m map d
    for d in ds do DefineMembers.topDef map d
    emit map
    createTypes map
