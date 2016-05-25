module PolyTyping2.ILmit
#load "PolyTyping2.fsx"

open System.Collections.Generic
open System.Reflection.Emit
open System.Threading

type ST = global.System.Type
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

type TypeName = struct val EscapedTypeName: string end
type PathRev = TypeName * TypeName list

type Type = 
    | Type of pathRev: PathRev * Type list
    | TypeVar of TypeVar

type TypeRef = TypeRef of name: PathRev * Type list

type Operand =
    | OpNone
    | OpCtor of Type * Type list
    | OpInt of int
    | OpType of Type
    | OpField of Type * name: string
    | OpCall of Type option * name: string * typeArgs: Type list * argTypes: Type list

type Instr = string * OpCode * Operand
type MethodBody = MethodBody of baseInit: Type list option * Instr list

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
type MethodBuilderInfo = unit -> ILGenerator * MethodBody * TypeVarMap
type TypeBuilderInfo = TypeBuilder * HashMap<MethodHead, MethodBuilderInfo>
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
    let get (typeMap: TypeMap) pathRev arity =
        let mutable (t',_) as t = Unchecked.defaultof<_>
        if typeMap.TryGetValue(pathRev, &t) then t' :> ST
        else
            let n = toTypeName ST.Delimiter pathRev
            let n = if arity = 0 then n else n + "`" + string arity
            ST.GetType(n, true)

    let rec aux = function
    | Type(pathRev, []) -> get typeMap pathRev 0
    | Type(pathRev, ts) -> get typeMap pathRev <| List.length ts
    | TypeVar v ->
        varMap
        |> Array.find (fun (v': TypeVar, _: GenericTypeParameterBuilder) -> v.Value = v'.Value)
        |> snd
        :> System.Type

    aux t
 
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

module DefineTypes =
    let rec defineModule defineType nsRev name map ms =
        let t = defineType(escaped name, T.Public ||| T.Abstract ||| T.Sealed)
        let path = nsToPath nsRev name
        add map path (t, HashMap())
        for m in ms do defineModuleMember path t map m

    and defineType defineType nsRev map { isAbstract = isAbstract; name = name; members = members } =
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
        add map (nsToPath nsRev name) (t, HashMap())

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

    let defineMethodHead defineMethod attr callconv map varMap (MethodHead(name,typeArgs,args,ret)) =
        let m : MethodBuilder = defineMethod(name, attr, callconv)
        let mVarMap = makeVarMap typeArgs <| fun x -> m.DefineGenericParameters x
        let varMap = Array.append varMap mVarMap

        let pts = solveParamTypes map varMap args
        m.SetParameters(pts)
        emitParams m.DefineParameter args

        let rt = solveType map varMap (argType ret)
        m.SetReturnType rt
        defineParam m.DefineParameter 0 ret
        m, varMap

    let defineMethodInfo (t: TypeBuilder) a c (map, mmap, varMap) (MethodInfo(head, body)) =
        let m, varMap = defineMethodHead t.DefineMethod a c map varMap head
        add mmap head (m.GetILGenerator, body, varMap)

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

            let t = Type(path, List.map TypeVar typeArgs)
            let h = MethodHead(".ctor", [], args, Argument(None, t))
            add mmap h (c.GetILGenerator, body, varMap)

        | AbstractDef head ->
            let a = M.Public ||| M.HideBySig ||| M.NewSlot ||| M.Abstract ||| M.Virtual
            defineMethodHead t.DefineMethod a CC.HasThis map varMap head
            |> ignore

    let defineModuleMethod (t: TypeBuilder) map mmap (MethodInfo(head,_)) =
        defineMethodHead t.DefineMethod (M.Public ||| M.Static) CC.Standard map head
        |> Choice1Of2
        |> add mmap head

    let defineTypeDef nsRev map { name = name; typeArgs = typeArgs; parent = parent; impls = impls; members = members } =
        let path = name, nsRev
        let (t: TypeBuilder), mmap = get map path
        let varMap = makeVarMap typeArgs <| fun x -> t.DefineGenericParameters x
        t.SetParent <| solveType map varMap (typeRefToType parent)

        for impl in impls do t.AddInterfaceImplementation <| solveType map varMap (typeRefToType impl)
        for m in members do defineMember path t typeArgs (map, mmap, varMap) m

    let rec defineModuleMember path (t: TypeBuilder) map mmap = function
        | ModuleMethodDef m -> defineModuleMethod t map mmap m
        | ModuleTypeDef td -> defineTypeDef (pathToNs path) map td
        | ModuleModuleDef(name, members) -> defineModuleDef (pathToNs path) name members map

    and defineModuleDef nsRev name members map =
        let path = nsToPath nsRev name
        let t, mmap = get map path
        t.SetParent <| typeof<obj>
        for m in members do defineModuleMember path t map mmap m

    // TODO: using *Builder lookup method?
    let defineTopDef (m: ModuleBuilder) map = function
        | TopModuleDef(name, members) -> defineModuleDef [] name members map
        | TopTypeDef td -> defineTypeDef [] map td

let emitModuleMethod (t: TypeBuilder) map mmap (MethodInfo(head,body)) =
    let m: MethodBuilder = get mmap head

let rec emitModuleMember path (t: TypeBuilder) map mmap = function
    | ModuleMethodDef m -> emitModuleMethod t map mmap m
//    | ModuleTypeDef td -> defineTypeDef (pathToNs path) map td
//    | ModuleModuleDef(name, members) -> defineModuleDef (pathToNs path) name members map

and emitModuleDef nsRev name members map =
    let path = nsToPath nsRev name
    let t, mmap = get map path
    for m in members do emitModuleMember path t map mmap m
    
let emitTopDef (m: ModuleBuilder) map = function
    | TopModuleDef(name, members) -> emitModuleDef [] name members map

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