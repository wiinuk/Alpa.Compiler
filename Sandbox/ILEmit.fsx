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
type Var = struct
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

type FullName = FullName of name: string * nestersRev: string list * namespaceRev: string list * assemblyName: string option

type TypeSpec = 
    | TypeSpec of pathRev: FullName * TypeSpec list
    | TypeVar of Var

type TypeRef = TypeRef of name: FullName * TypeSpec list

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
    | BaseMethod of baseMethod: (TypeRef * string)

type Argument = Argument of name: string option * TypeSpec
type MethodBody = MethodBody of Instr list
type MethodHead = MethodHead of name: string * typeArgs: Var list * args: Argument list * ret: Argument

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
    | DateTime of System.DateTime
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
    | CtorDef of args: Argument list * MethodBody
    | MethodDef of Override option * MethodInfo

type TypeKind = Abstract | Interface | Open | Sealed
type TypeDef = {
    kind: TypeKind option
    typeArgs: Var list
    parent: TypeRef option
    impls: TypeRef list
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
type TypeVarMap = (Var * GenericTypeParameterBuilder) array
type MethodBuilderInfo = {
    mb: Choice<MethodBuilder, ConstructorBuilder>
    parent: TypeBuilder
    m: MethodInfo
    varMap: TypeVarMap
}
type TypeBuilderInfo = {
    t: TypeBuilder
    varMap: TypeVarMap
    mmap: HashMap<MethodHead, MethodBuilderInfo>
}
type TypeMap = HashMap<FullName, TypeBuilderInfo>

let varName (v: Var) = v.Name
let add (map: HashMap<_,_>) k v = map.Add(k, v)
let get (map: HashMap<_,_>) k = map.[k]
let values (map: HashMap<_,_>) = map.Values
let pathToNs (p,ps) = p::ps
let nsToPath ps name = name, ps
let typeRefToType (TypeRef(n,ts)) = TypeSpec(n,ts)
let argType (Argument(_,t)) = t
let emptyVarMap : TypeVarMap = [||]
    
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

let rec solveType typeMap varMap t =
    let getGenericDef (typeMap: HashMap<_,_>) pathRev =
        let mutable ti = Unchecked.defaultof<_>
        if typeMap.TryGetValue(pathRev, &ti) then
            let { t = t } = ti
            t :> Type
        else
            Type.GetType(toTypeName pathRev, true)

    let rec aux = function
    | TypeSpec(pathRev, []) -> getGenericDef typeMap pathRev
    | TypeSpec(pathRev, vs) ->
        let td = getGenericDef typeMap pathRev
        let vs = Seq.map (solveType typeMap varMap) vs |> Seq.toArray
        td.MakeGenericType vs

    | TypeVar v ->
        varMap
        |> Array.find (fun (v': Var, _: GenericTypeParameterBuilder) -> v.Value = v'.Value)
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
    | [] -> emptyVarMap
    | _ ->
        let typeArgs = List.toArray typeArgs
        let names = typeArgs |> Array.map varName
        Array.zip typeArgs <| defineGenericParameters names

let mDefineGP (m: MethodBuilder) xs = m.DefineGenericParameters xs
let tDefineGP (t: TypeBuilder) xs = t.DefineGenericParameters xs

let ctorHead parentPath parentTypeArgs args =
    let t = TypeSpec(parentPath, List.map TypeVar parentTypeArgs)
    MethodHead(".ctor", [], args, Argument(None, t))

let addTypeName (FullName(name, nestersRev, nsRev, asmName)) typeName =
    FullName(typeName, name::nestersRev, nsRev, asmName)

let ofTypeName typeName = FullName(typeName, [], [], None)

module DefineTypes =
    let rec module' defineType (FullName(name=name) as path) map ms =
        let t = defineType(name, T.Public ||| T.Abstract ||| T.Sealed)
        add map path {
            t = t
            varMap = emptyVarMap
            mmap = HashMap()
        }
        for m in ms do moduleMember path t map m

    and type' defineType (FullName(name=name) as path) map { kind = kind; typeArgs = typeArgs; members = members } =
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
            varMap = Array.zeroCreate <| List.length typeArgs
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

module DefineMembers =
    let param defineParameter i (Argument(pn, _)) = defineParameter(i, P.None, Option.toObj pn) |> ignore
    let params' defineParameter args = List.iteri (fun i a -> param defineParameter (i + 1) a) args
    
    let methodHead defineMethod attr callconv (map, varMap) (MethodHead(name,typeArgs,args,ret)) =
        let m = defineMethod(name, attr, callconv)
        let mVarMap = makeVarMap typeArgs <| mDefineGP m
        let varMap = Array.append varMap mVarMap
        
        m.SetReturnType(solveType map varMap (argType ret))
        m.SetParameters(solveParamTypes map varMap args)

        param m.DefineParameter 0 ret
        params' m.DefineParameter args

        m, varMap

    let methodInfo (t: TypeBuilder) a c (map, mmap, varMap) (MethodInfo(head, _) as m) =
        let mb, varMap = methodHead t.DefineMethod a c (map, varMap) head
        add mmap head { mb = Choice1Of2 mb; m = m; parent = t; varMap = varMap }

    let methodDef (t: TypeBuilder) maps ov m =
        match ov with
        | None -> methodInfo t (M.Public ||| M.Final ||| M.HideBySig) CC.Standard maps m
        | Some Override ->
            let a = M.Public ||| M.Final ||| M.HideBySig ||| M.NewSlot ||| M.Virtual
            methodInfo t a CC.HasThis maps m

        | Some(BaseMethod _) ->
            let a = M.Private ||| M.Final ||| M.HideBySig ||| M.NewSlot ||| M.Virtual
            methodInfo t a CC.HasThis maps m

                    // TODO: last path
//                        let bt = solveType map varMap <| typeRefToType baseType
//                        let pts = solveParamTypes map varMap args
//                        let bm = bt.GetMethod(baseMethodName, pts)
//                        t.DefineMethodOverride(bm, m)
    
    let field (t: TypeBuilder) (isStatic, isMutable, name, ft) map varMap =
        let a = F.Public
        let a = if isStatic then a ||| F.Static else a
        let a = if isMutable then a else a ||| F.InitOnly
        let ft = solveType map varMap ft
        t.DefineField(name, ft, a) |> ignore

    let member' path (t: TypeBuilder) typeArgs (map, mmap, varMap) = function
        | Field(isStatic, isMutable, n, ft) -> field t (isStatic, isMutable, n, ft) map varMap
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
            let m = MethodInfo(h, body)
            add mmap h { mb = Choice2Of2 c; m = m; parent = t; varMap = varMap }

        | AbstractDef head ->
            let a = M.Public ||| M.HideBySig ||| M.NewSlot ||| M.Abstract ||| M.Virtual
            methodHead t.DefineMethod a CC.HasThis (map, varMap) head
            |> ignore

    let moduleMethod (t: TypeBuilder) map mmap (MethodInfo(head, body) as m) =
        let mb, varMap = methodHead t.DefineMethod (M.Public ||| M.Static) CC.Standard (map, emptyVarMap) head
        add mmap head { mb = Choice1Of2 mb; m = m; parent = t; varMap = varMap }

    let typeDef path map { typeArgs = typeArgs; parent = parent; impls = impls; members = members } =
        let { t = t; varMap = varMap; mmap = mmap } = get map path
        let varMap' = makeVarMap typeArgs <| tDefineGP t
        Array.blit varMap' 0 varMap 0 varMap'.Length

        match parent with
        | Some parent -> t.SetParent <| solveType map varMap (typeRefToType parent)
        | _ -> ()

        for impl in impls do t.AddInterfaceImplementation <| solveType map varMap (typeRefToType impl)
        for m in members do member' path t typeArgs (map, mmap, varMap) m

    let rec moduleMember path t map mmap = function
        | ModuleValDef(isMutable, name, ft) -> field t (true, isMutable, name, ft) map emptyVarMap
        | ModuleMethodDef m -> moduleMethod t map mmap m
        | ModuleTypeDef(name, td) -> typeDef (addTypeName path name) map td
        | ModuleModuleDef(name, members) -> moduleDef (addTypeName path name) members map

    and moduleDef path members map =
        let { t = t; mmap = mmap } = get map path
        t.SetParent <| typeof<obj>
        for m in members do moduleMember path t map mmap m

    // TODO: use *Builder lookup method?
    let topDef map = function
        | TopModuleDef(name, members) -> moduleDef (ofTypeName name) members map
        | TopTypeDef(name, td) -> typeDef (ofTypeName name) map td

let emitInstr (g: ILGenerator) map { varMap = varMap; parent = parent } = function
    | Macro(BaseInit ts) ->
        let ctor = parent.GetConstructor(B.Public ||| B.NonPublic, null, solveTypes map varMap ts, null)
        if List.isEmpty ts then g.Emit O.Ldarg_0 else ()
        g.Emit(O.Call, ctor)

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
            let ctor = parent.GetConstructor(B.Public ||| B.NonPublic, null, argTypes, null)
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

let emitMethodBody map ({ mb = mb; m = MethodInfo(_, MethodBody instrs) } as mi) =
    let g =
        match mb with
        | Choice1Of2 m -> m.GetILGenerator()
        | Choice2Of2 m -> m.GetILGenerator()

    for instr in instrs do emitInstr g map mi instr

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
