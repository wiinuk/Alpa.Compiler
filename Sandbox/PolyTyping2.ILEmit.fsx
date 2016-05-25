﻿module PolyTyping2.ILmit
#load "PolyTyping2.fsx"

open System.Collections.Generic
open System.Reflection.Emit
open System.Threading

type SystemType = global.System.Type
type C = global.System.TypeCode
type B = global.System.Reflection.BindingFlags
type CC = global.System.Reflection.CallingConventions
type T = global.System.Reflection.TypeAttributes
type M = global.System.Reflection.MethodAttributes
type P = global.System.Reflection.ParameterAttributes
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
end

type TypeName = struct
    val EscapedTypeName: string
    new (n) =
        let n =
            if String.exists (function '`' | '\\' -> true | c -> c = SystemType.Delimiter) n then
                let delim = sprintf "\\u%04x" <| int System.Type.Delimiter
                String.collect (function '`' -> "\\u0060" | '\\' -> "\\u005c" | c -> if c = SystemType.Delimiter then delim else string c) n
            else n
        { EscapedTypeName = n }
end
type PathRev = TypeName * TypeName list

type Type = 
    | Type of pathRev: PathRev * Type list
    | TypeVar of TypeVar

type TypeRef = TypeRef of name: PathRev * Type list

type Operand =
    | OpNone
    | OpCtor of thisType: Type * argTypes: Type list
    | OpInt of int
    | OpType of Type
    | OpField of thisType: Type * name: string
    | OpCall of isStatic: bool * thisType: Type * name: string * typeArgs: Type list * argTypes: Type list

type Macro =
    | BaseInit of Type list

type Instr = 
    | Instr of string * OpCode * Operand
    | Macro of Macro

type MethodBody = MethodBody of Instr list

type Argument = Argument of name: string option * Type
    
type MethodHead = MethodHead of name: string * typeArgs: TypeVar list * args: Argument list * ret: Argument
type MethodInfo = MethodInfo of MethodHead * body: MethodBody

type StaticMethodInfo = MethodInfo

type Override =
    | Override
    | BaseMethod of baseMethod: (TypeRef * string)

type MemberDef =
    | CtorDef of args: Argument list * MethodBody
    | AbstractDef of MethodHead
    | MethodDef of Override option * MethodInfo

type TypeDef = {
    isAbstract: bool
    name: TypeName
    typeArgs: TypeVar list
    parent: TypeRef
    impls: TypeRef list
    members: MemberDef list
}
type ModuleMember =
    | ModuleMethodDef of StaticMethodInfo
    | ModuleTypeDef of TypeDef
    | ModuleModuleDef of name: TypeName * ModuleMember list

type TopDef =
    | TopTypeDef of TypeDef
    | TopModuleDef of name: TypeName * ModuleMember list

type IL = IL of TopDef list

let escapeTypeName name =
    if String.exists (function '.' | '\\' -> true | _ -> false) name
    then String.collect (function '.' -> "\\u002e" | '\\' -> "\\\\" | c -> string c) name
    else name

let escaped (x: TypeName) = x.EscapedTypeName

    
[<Sealed; AllowNullLiteral>]
type HashMap<'k,'v when 'k : equality>() = inherit Dictionary<'k,'v>()
type TypeVarMap = (TypeVar * GenericTypeParameterBuilder) array
type MethodBuilderInfo = (unit -> ILGenerator) * MethodBody * TypeVarMap
type TypeBuilderInfo = {
    t: TypeBuilder
    varMap: TypeVarMap
    mmap: HashMap<MethodHead, MethodBuilderInfo>
}
type TypeMap = HashMap<PathRev, TypeBuilderInfo>

let varName (v: TypeVar) = v.Name
let add (map: HashMap<_,_>) k v = map.Add(k, v)
let get (map: HashMap<_,_>) k = map.[k]
let addName (p, path) name = name, p::path
let pathToNs (p,ps) = p::ps
let nsToPath ps name = name, ps
    
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
        let mutable { t = t } as ti = Unchecked.defaultof<_>
        if typeMap.TryGetValue(pathRev, &ti) then t :> SystemType
        else
            let n = toTypeName SystemType.Delimiter pathRev
            let n = if arity = 0 then n else n + "`" + string arity
            SystemType.GetType(n, true)

    let rec aux = function
    | Type(pathRev, []) -> get typeMap pathRev 0
    | Type(pathRev, ts) -> get typeMap pathRev <| List.length ts
    | TypeVar v ->
        varMap
        |> Array.find (fun (v': TypeVar, _: GenericTypeParameterBuilder) -> v.Value = v'.Value)
        |> snd
        :> System.Type
    aux t

let solveTypes map varMap ts =
    Seq.map (solveType map varMap) ts
    |> Seq.toArray

let makeVarMap typeArgs defineGenericParameters =
    match typeArgs with
    | [] -> [||]
    | _ ->
        let typeArgs = List.toArray typeArgs
        let names = typeArgs |> Array.map varName
        Array.zip typeArgs <| defineGenericParameters names

let typeRefToType (TypeRef(n,ts)) = Type(n,ts)
let argType (Argument(_,t)) = t

let solveParamTypes map varMap args =
    Seq.map (argType >> solveType map varMap) args
    |> Seq.toArray

let emptyVarMap : TypeVarMap = [||]
let mDefineGP (m: MethodBuilder) xs = m.DefineGenericParameters xs
let tDefineGP (t: TypeBuilder) xs = t.DefineGenericParameters xs

let ctorHead parentPath parentTypeArgs args =
    let t = Type(parentPath, List.map TypeVar parentTypeArgs)
    MethodHead(".ctor", [], args, Argument(None, t))

module DefineTypes =
    let rec defineModule defineType nsRev name map ms =
        let t = defineType(escaped name, T.Public ||| T.Abstract ||| T.Sealed)
        let path = nsToPath nsRev name
        add map path {
            t = t
            varMap = emptyVarMap
            mmap = HashMap()
        }
        for m in ms do defineModuleMember path t map m

    and defineType defineType nsRev map { isAbstract = isAbstract; typeArgs = typeArgs; name = name; members = members } =
        let isAbstractMember = function 
            | CtorDef _
            | MethodDef _ -> false
            | AbstractDef _ -> true

        let isInterface = List.forall isAbstractMember members
        let a = T.Public ||| T.BeforeFieldInit
        let a = if isInterface then a ||| T.Interface else a
        let a = if isAbstract then a ||| T.Abstract else a
        let a = if not isAbstract && List.forall (not << isAbstractMember) members then a ||| T.Sealed else a
        let t = defineType(escaped name, a)
        add map (nsToPath nsRev name) {
            t = t
            varMap = Array.zeroCreate <| List.length typeArgs
            mmap = HashMap()
        }

    and defineModuleMember path (t: TypeBuilder) map = function
        | ModuleMethodDef(MethodInfo _) -> ()
        | ModuleModuleDef(name, ms) -> defineModule t.DefineNestedType (pathToNs path) name map ms
        | ModuleTypeDef td -> defineType t.DefineNestedType (pathToNs path) map td

    let defineTopDef (m: ModuleBuilder) map = function
        | TopModuleDef(name, ms) -> defineModule m.DefineType [] name map ms
        | TopTypeDef td -> defineType m.DefineType [] map td

module DefineMethods =
    let defineParam defineParameter i (Argument(pn, _)) = defineParameter(i, P.None, Option.toObj pn) |> ignore
    let emitParams defineParameter args = List.iteri (fun i a -> defineParam defineParameter (i + 1) a) args
    
    let defineMethodHead defineMethod attr callconv (map, varMap) (MethodHead(name,typeArgs,args,ret)) =
        let m = defineMethod(name, attr, callconv)
        let mVarMap = makeVarMap typeArgs <| mDefineGP m
        let varMap = Array.append varMap mVarMap

        let pts = solveParamTypes map varMap args
        m.SetParameters(pts)
        emitParams m.DefineParameter args

        let rt = solveType map varMap (argType ret)
        m.SetReturnType rt
        defineParam m.DefineParameter 0 ret
        m, varMap

    let defineMethodInfo (t: TypeBuilder) a c (map, mmap, varMap) (MethodInfo(head, body)) =
        let m, varMap = defineMethodHead t.DefineMethod a c (map, varMap) head
        add mmap head ((m.GetILGenerator : unit -> _), body, varMap)

    let defineMethodDef (t: TypeBuilder) maps ov m =
        match ov with
        | None -> defineMethodInfo t (M.Public ||| M.HideBySig) CC.Standard maps m
        | Some Override ->
            let a = M.Public ||| M.Final ||| M.HideBySig ||| M.NewSlot ||| M.Virtual
            defineMethodInfo t a CC.Standard maps m

        | Some(BaseMethod _) ->
            let a = M.Private ||| M.Final ||| M.HideBySig ||| M.NewSlot ||| M.Virtual
            defineMethodInfo t a CC.HasThis maps m

                    // TODO: last path
//                        let bt = solveType map varMap <| typeRefToType baseType
//                        let pts = solveParamTypes map varMap args
//                        let bm = bt.GetMethod(baseMethodName, pts)
//                        t.DefineMethodOverride(bm, m)

    let defineMember path (t: TypeBuilder) typeArgs (map, mmap, varMap) = function
        | MethodDef(ov, m) -> defineMethodDef t (map, mmap, varMap) ov m
        | CtorDef(args, body) ->
            let pts = solveParamTypes map varMap args
            let c = t.DefineConstructor(M.SpecialName ||| M.RTSpecialName ||| M.Public, CC.HasThis, pts)
                            
            emitParams c.DefineParameter args

            let h = ctorHead path typeArgs args
            add mmap h (c.GetILGenerator, body, varMap)

        | AbstractDef head ->
            let a = M.Public ||| M.HideBySig ||| M.NewSlot ||| M.Abstract ||| M.Virtual
            defineMethodHead t.DefineMethod a CC.HasThis (map, varMap) head
            |> ignore

    let defineModuleMethod (t: TypeBuilder) map mmap (MethodInfo(head, body)) =
        let m, varMap = defineMethodHead t.DefineMethod (M.Public ||| M.Static) CC.Standard (map, emptyVarMap) head
        add mmap head ((m.GetILGenerator : unit -> _), body, varMap)

    let defineTypeDef nsRev map { name = name; typeArgs = typeArgs; parent = parent; impls = impls; members = members } =
        let path = name, nsRev
        let { t = t; varMap = varMap; mmap = mmap } = get map path
        let varMap' = makeVarMap typeArgs <| tDefineGP t
        Array.blit varMap' 0 varMap 0 varMap'.Length
        t.SetParent <| solveType map varMap (typeRefToType parent)

        for impl in impls do t.AddInterfaceImplementation <| solveType map varMap (typeRefToType impl)
        for m in members do defineMember path t typeArgs (map, mmap, varMap) m

    let rec defineModuleMember path (t: TypeBuilder) map mmap = function
        | ModuleMethodDef m -> defineModuleMethod t map mmap m
        | ModuleTypeDef td -> defineTypeDef (pathToNs path) map td
        | ModuleModuleDef(name, members) -> defineModuleDef (pathToNs path) name members map

    and defineModuleDef nsRev name members map =
        let path = nsToPath nsRev name
        let { t = t; mmap = mmap } = get map path
        t.SetParent <| typeof<obj>
        for m in members do defineModuleMember path t map mmap m

    // TODO: use *Builder lookup method?
    let defineTopDef (m: ModuleBuilder) map = function
        | TopModuleDef(name, members) -> defineModuleDef [] name members map
        | TopTypeDef td -> defineTypeDef [] map td

let emitInstr (g: ILGenerator) map mmap varMap = function
    | Macro(BaseInit ts) -> failwith "Not implemented yet"
    | Instr(label, op, operand) ->
        match operand with
        | OpNone -> g.Emit op
        | OpInt n -> g.Emit(op, n)
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

let emitMethodInfo map mmap (MethodInfo(head, MethodBody instrs)) =
    let gen, _, varMap = get mmap head
    let g: ILGenerator = gen()
    for instr in instrs do emitInstr g map mmap varMap instr

let emitMember path t typeArgs (map, mmap, varMap) = function
    | AbstractDef _ -> ()
    | MethodDef(ov, m) -> emitMethodInfo map mmap m
    | CtorDef(args, body) ->
        let h = ctorHead path typeArgs args
        emitMethodInfo map mmap (MethodInfo(h, body))

let emitTypeDef nsRev map { name = name; typeArgs = typeArgs; parent = parent; impls = impls; members = members } =
    let path = nsToPath nsRev name
    let { t = t; varMap = varMap; mmap = mmap } = get map path
    for m in members do emitMember path t typeArgs (map, mmap, varMap) m

let rec emitModuleMember path (t: TypeBuilder) map mmap = function
    | ModuleMethodDef m -> emitMethodInfo map mmap m
    | ModuleTypeDef td -> emitTypeDef (pathToNs path) map td
    | ModuleModuleDef(name, members) -> emitModuleDef (pathToNs path) name members map

and emitModuleDef nsRev name members map =
    let path = nsToPath nsRev name
    let { t = t; mmap = mmap } = get map path
    for m in members do emitModuleMember path t map mmap m

let emitTopDef (m: ModuleBuilder) map = function
    | TopModuleDef(name, members) -> emitModuleDef [] name members map
    | TopTypeDef td -> emitTypeDef [] map td

//.class public auto ansi beforefieldinit EqInt
//    extends [mscorlib]System.Object
//    implements class InterfaceEq`1<int32>
//{
//    .method public final hidebysig newslot virtual instance bool Eq (int32 l, int32 r) cil managed 
//    { ... }
//
//.class public auto ansi beforefieldinit ExplicitEqInt
//    extends [mscorlib]System.Object
//    implements class InterfaceEq`1<int32>
//{
//    .method private final hidebysig newslot virtual instance bool 'ConsoleApplication0.InterfaceEq<System.Int32>.Eq' (int32 l, int32 r) cil managed 
//    {
//        .override method instance bool class InterfaceEq`1<int32>::Eq(!0, !0)
//        ...
//    }

let emitIL m (IL ds) =
    let map = HashMap()
    for d in ds do DefineTypes.defineTopDef m map d
    for d in ds do DefineMethods.defineTopDef m map d
    for d in ds do emitTopDef m map d

open System
open System.Reflection

let current il =
    let a = AppDomain.CurrentDomain.DefineDynamicAssembly(AssemblyName("test"), AssemblyBuilderAccess.Save)
    let m = a.DefineDynamicModule "test"
    emitIL m il

let t n = TypeName n
IL [
    TopTypeDef { 
        isAbstract = false
        name = t"Type"
        typeArgs = []
        parent = typerefof<obj> // TypeRef((t"Object", [t"System"]), [])
        impls = []
        members = []
    }
]
|> current