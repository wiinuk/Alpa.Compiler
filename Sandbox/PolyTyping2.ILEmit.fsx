module internal PolyTyping2.ILEmit

open System.Collections.Generic
open System.Reflection.Emit
open System.Threading

type SystemType = global.System.Type
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
let newTypeVar name = TypeVar name

type TypeName = struct
    val EscapedTypeName: string
    private new (n, isEscape) =
        if isEscape then
            let n =
                if String.exists (function '`' | '\\' -> true | c -> c = SystemType.Delimiter) n then
                    let delim = sprintf "\\u%04x" <| int System.Type.Delimiter
                    String.collect (function '`' -> "\\u0060" | '\\' -> "\\u005c" | c -> if c = SystemType.Delimiter then delim else string c) n
                else n
            { EscapedTypeName = n }
        else { EscapedTypeName = n }

    new (n) = TypeName(n, true)

    override x.ToString() = sprintf "e\"%s\"" x.EscapedTypeName

    static member NonEscape n = TypeName(n, false)
end
type PathRev = TypeName * TypeName list

type Type = 
    | Type of pathRev: PathRev * Type list
    | TypeVar of TypeVar

type TypeRef = TypeRef of name: PathRev * Type list

type Operand =
    | OpNone
    | OpCtor of thisType: Type * argTypes: Type list
    | OpI1 of int8
    | OpI4 of int
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
    | Enum of Type * LiteralValue
    | Null of Type

type MemberDef =
    | Literal of name: string * Literal
    | Field of isStatic: bool * isMutable: bool * name: string * Type
    | CtorDef of args: Argument list * MethodBody
    | AbstractDef of MethodHead
    | MethodDef of Override option * MethodInfo

type TypeKind = Abstract | Interface | Open | Sealed
type TypeDef = {
    kind: TypeKind option
    name: TypeName
    typeArgs: TypeVar list
    parent: TypeRef option
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

let escaped (x: TypeName) = x.EscapedTypeName
let varName (v: TypeVar) = v.Name
let add (map: HashMap<_,_>) k v = map.Add(k, v)
let get (map: HashMap<_,_>) k = map.[k]
let values (map: HashMap<_,_>) = map.Values
let pathToNs (p,ps) = p::ps
let nsToPath ps name = name, ps
let typeRefToType (TypeRef(n,ts)) = Type(n,ts)
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
            t :> SystemType

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
    let t = Type(parentPath, List.map TypeVar parentTypeArgs)
    MethodHead(".ctor", [], args, Argument(None, t))

[<AbstractClass>]
type Abs =
    val F: int
    new () = { F = 0 }
    abstract M : int -> int

typeof<Abs>.IsAbstract

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
        | ModuleMethodDef(MethodInfo _) -> ()
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

    let methodInfo (t: TypeBuilder) a c (map, mmap, varMap) (MethodInfo(head, body)) =
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
            add mmap h (c.GetILGenerator, body, varMap)

        | AbstractDef head ->
            let a = M.Public ||| M.HideBySig ||| M.NewSlot ||| M.Abstract ||| M.Virtual
            methodHead t.DefineMethod a CC.HasThis (map, varMap) head
            |> ignore

    let moduleMethod (t: TypeBuilder) map mmap (MethodInfo(head, body)) =
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

let emitInstr (g: ILGenerator) map varMap = function
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

let emitMethodBody map (gen, MethodBody instrs, varMap) =
    let g = gen()
    for instr in instrs do emitInstr g map varMap instr

let emit map =
    for { mmap = mmap } in values map do    
        for mi in values mmap do
            emitMethodBody map mi

let createTypes map = for { t = t } in values map do t.CreateType() |> ignore

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
    for d in ds do DefineTypes.topDef m map d
    for d in ds do DefineMembers.topDef map d
    emit map
    createTypes map
    
let sysTypeValidate (t: SystemType) =
    if t.IsNested then failwithf "%A is GenericParameter." t
    if t.IsGenericParameter then failwithf "%A is GenericParameter." t

let getPath t =
    sysTypeValidate t
    let nsRev =
        t.Namespace.Split SystemType.Delimiter
        |> Seq.map TypeName.NonEscape
        |> Seq.rev
        |> Seq.toList

    nsToPath nsRev <| TypeName.NonEscape t.Name

let rec typeOfT t = Type(getPath t, typeOfTypeArgs t)
and typeOfTypeArgs t = if not t.IsGenericType then [] else t.GetGenericArguments() |> Seq.map typeOfT |> Seq.toList
let typeRefOfT t = TypeRef(getPath t, typeOfTypeArgs t)

[<RequiresExplicitTypeArguments>]
let typeOf<'a> = typeOfT typeof<'a>

[<RequiresExplicitTypeArguments>]
let typeRefOf<'a> = typeRefOfT typeof<'a>

module TypeRefs =
    let objR = typeRefOf<obj>

module Types =
    let intT = typeOf<int>
    let bigintT = typeOf<bigint>

open TypeRefs
open Types

let t n = TypeName n
let p n = (t n, [])

open System
open System.Reflection
open System.IO
open System.Diagnostics

let ildasm path =
    let outPath = Path.ChangeExtension(path, ".il")
    let p = Process.Start(@"C:\Program Files\Microsoft SDKs\Windows\v10.0A\bin\NETFX 4.6.1 Tools\ildasm.exe", sprintf "\"%s\" /out=\"%s\" /utf8 /metadata=VALIDATE" path outPath)
    p.WaitForExit()

    let trivia = System.Text.RegularExpressions.Regex("\s*//.*$")
    let sourceLines =
        File.ReadLines outPath
        |> Seq.map (fun l -> trivia.Replace(l, ""))
        |> Seq.filter (not << String.IsNullOrWhiteSpace)

    String.concat "\n" sourceLines

let emitDll name il =
    let moduleName = Path.ChangeExtension(name, ".dll")
    let path = Path.Combine(Path.GetTempPath(), moduleName)

    if File.Exists path then File.Delete path else ()

    let d = AppDomain.CurrentDomain
    let a = d.DefineDynamicAssembly(AssemblyName name, AssemblyBuilderAccess.Save)
    let m = a.DefineDynamicModule moduleName
    emitIL m il
    a.Save moduleName
    ildasm path, File.ReadAllBytes path
    
let typeDef = {
    kind = None
    name = t""
    typeArgs = []
    parent = None
    impls = []
    members = []
}

let type0D name parent impls members =
    TopTypeDef {
        kind = None
        name = t name
        typeArgs = []
        parent = parent
        impls = impls
        members = members
    }

let type1D name v1 f =
    let v1 = newTypeVar v1
    let make parent impls members =
        TopTypeDef {
            kind = None
            name = t name
            typeArgs = [v1]
            parent = parent
            impls = impls
            members = members
        }
    f make (TypeVar v1)
    
let type1 t v1 = Type.Type(t, [v1])
let type2 t v1 v2 = Type.Type(t, [v1; v2])
let typeRef1 n v1 = TypeRef(n, [v1])
let typeRef2 n v1 v2 = TypeRef(n, [v1; v2])

let abstract2T name v1 v2 f =
    let v1, v2 = newTypeVar v1, newTypeVar v2
    let make parent impls members =
        TopTypeDef {
            kind = Some Abstract
            name = t name
            typeArgs = [v1; v2]
            parent = parent
            impls = impls
            members = members
        }
    f make (TypeVar v1) (TypeVar v2)

let arg n t = Argument(Some n, t)
let argT t = Argument(None, t)

let methodHead0 name args retT = MethodHead(name, [], args, Argument(None, retT))
let methodInfo0 name args retT body = MethodInfo.MethodInfo(methodHead0 name args retT, body)

let abstract0 name args retT = AbstractDef <| methodHead0 name args retT
let override0 name args retT instrs = MethodDef(Some Override, methodInfo0 name args retT <| MethodBody.MethodBody instrs)

//type abstract `->` (a, b) = abstract `_ _` a : b;;
//
//type Num a =
//    ofInteger Integer : a;
//    `_+_` (a, a) : a;;
//
//type #(Num Int32) <: Object, Num Int32 =
//    override ofInteger Integer : Int32 { ... };
//    override `_+_` (Int32, Int32) : Int32 { ... };;
//
//type CloSucc2 a <: (a -> a) =
//    val item1 : Num a
//    new (Num a) =
//        base()
//        ldarg.0
//        stfld CloSucc2::item
//        ret;
//
//    override `_ _` a : a =
//        ldfld CloSucc2::item
//        ldarg.0
//        ldfld CloSucc2::item
//        ldsfld bigint::One
//        callvirt Num a::ofInteger(a)
//        callvirt Num a::`_+_`
//        ret;;
//
//type CloSucc a <: (Num a -> a -> a) =
//    override `_ _` (Num a) : a -> a =
//        ldarg.0
//        newobj (CloSucc2 a) (Num a)
//        ret;;
//
//module Program =
//    fun succ a () : Num a -> a -> a = newobj (CloSucc a) ();;
//
//    val #(Num Int32) : Num Int32;;
//    val ten : Int32;;
//    fun init () : void =
//        newobj #(Num Int32) ()
//        stfld Program::#(Num Int32)
//        ldc_i4 10i
//        stfld ten
//        ret;;
//
//    fun main () : void =
//        call init ()
//
//        ldfld ten
//        ldfld #(Num Int32)
//        call succ Int32 ()
//        callvirt `->`(Num Int32, Int32 -> Int32)::` `(Num Int32)
//        callvirt `->`(Int32, Int32)::` `(Int32)
//        ret;;
//;;

let ctor args is = CtorDef(args, MethodBody.MethodBody is)

let inRange lo hi x = lo <= x && x <= hi
let inlinedI4 (i1Op, i4Op, lo, hi) n inlined =
    match n with
    | n when inRange lo hi n -> Instr("", inlined n, OpNone)
    | n when inRange -128 127 n -> Instr("", i1Op, OpI1 <| int8 n)
    | n -> Instr("", i4Op, OpI4 n)

module SimpleInstructions =
    let base_init ts = Macro(BaseInit ts)
    let ret = Instr("", O.Ret, OpNone)

    let newobj thisType argTypes = Instr("", O.Newobj, OpCtor(thisType, argTypes))

    let ldc_i4 n = inlinedI4 (O.Ldc_I4_S, O.Ldc_I4, -1, 8) n <| function
        | 0 -> O.Ldc_I4_0
        | 1 -> O.Ldc_I4_1
        | 2 -> O.Ldc_I4_2
        | 3 -> O.Ldc_I4_3
        | 4 -> O.Ldc_I4_4
        | 5 -> O.Ldc_I4_5
        | 6 -> O.Ldc_I4_6
        | 7 -> O.Ldc_I4_7
        | 8 -> O.Ldc_I4_8
        | _ -> O.Ldc_I4_M1

    let ldarg n = inlinedI4 (O.Ldarg_S, O.Ldarg, 0, 3) n <| function
        | 0 -> O.Ldarg_0
        | 1 -> O.Ldarg_1
        | 2 -> O.Ldarg_2
        | _ -> O.Ldarg_3

    let stfld t n = Instr("", O.Stfld, OpField(t, n))
    let ldfld t n = Instr("", O.Ldfld, OpField(t, n))

open SimpleInstructions

let field n t = Field(false, false, n, t)

IL [
    abstract2T "->`2" "a" "b" <| fun f a b ->
        f None [] [abstract0 "_ _" [arg "arg" a] b]

    type1D "Num`1" "a" <| fun f a ->
        f None [] [
            abstract0 "ofInteger" [argT bigintT] a
            abstract0 "_+_" [argT a; argT a] a
        ]

    type0D "Num(System.Int32)" None [typeRef1 (p"Num`1") intT] [
        override0 "ofInteger" [argT bigintT] intT [ldc_i4 0; ret]
        override0 "_+_" [argT intT; argT intT] intT [ldc_i4 0; ret]
    ]

    //type CloSucc2 a <: (a -> a) =
    //    val item1 : Num a
    //    new (Num a) =
    //        base()
    //        ldarg.0
    //        stfld CloSucc2 a::item1
    //        ret;
    //
    //    override `_ _` a : a =
    //        ldfld CloSucc2 a::item1
    //        ldarg.0
    //        ldfld CloSucc2 a::item1
    //        ldsfld bigint::One
    //        callvirt Num a::ofInteger(a)
    //        callvirt Num a::`_+_`(a, a)
    //        ret;;
    type1D "CloSucc2`1" "a" <| fun f a ->
        let numAT = type1 (p"Num`1") a
        let cloSucc2AT = type1 (p"CloSucc2`1") a

        f (Some(typeRef2 (p"->`2") a a)) [] [
            field "item1" numAT

            // new (Num a) = base(); @item1 <- $0;
            ctor [argT numAT] [
                base_init []
                ldarg 0
                stfld cloSucc2AT "item1"
                ret
            ]

            // override `_ _` a : a = @item1.`_+_`($0, @item1.ofInteger(bigint::One));
            override0 "_ _" [argT a] a [
                ldfld cloSucc2AT "item1"
                ldarg 0
                ldfld cloSucc2AT "item1"
                ldsfld bigintT "One"
                callvirt numAT "ofInteger" [a]
                callvirt numAT "_+_" [a; a]
                ret
            ]
        ]

    type1D "CloSucc`1" "a" <| fun f a ->
        f (Some(typeRef2 (p"->`2") a (type2 (p"->`2") a a))) [] [
            override0 "_ _" [argT (type1 (p"Num`1") a)] (type2 (p"->`2") a a) [
                ldarg 0
                newobj (type1 (p"CloSucc2`1") a) [type1 (p"Num`1") a]
                ret
            ]
        ]

]
|> emitDll "test"


let __ _ =
//    let d = TopTypeDef {
//            kind = None
//            name = t"Type"
//            typeArgs = []
//            parent = typeRefOf<obj>
//            impls = []
//            members = []
//        }
//        
//    let name = "test" // sprintf "%s_%d" "test" Environment.TickCount
//    let moduleName = Path.ChangeExtension(name, ".dll")
//    let path = Path.Combine(Path.GetTempPath(), moduleName)
//
//    if File.Exists path then File.Delete path else ()
//
//    let d = AppDomain.CurrentDomain
//    let a = d.DefineDynamicAssembly(AssemblyName name, AssemblyBuilderAccess.Save)
//    let m = a.DefineDynamicModule moduleName
//    let t = m.DefineType("Type1", T.Public ||| T.Sealed ||| T.BeforeFieldInit, typeof<obj>)
//    //t.DefineField("f1", t, FieldAttributes.InitOnly ||| FieldAttributes.Public) |> ignore
//    t.CreateType() |> ignore
//
//    //if File.Exists path then File.Delete path else ()
//    a.Save moduleName
//
//    ildasm path = ".assembly extern mscorlib
//{
//  .publickeytoken = (B7 7A 5C 56 19 34 E0 89 )
//  .ver 4:0:0:0
//}
//.assembly test
//{
//  .hash algorithm 0x00008004
//  .ver 0:0:0:0
//}
//.module test.dll
//.imagebase 0x00400000
//.file alignment 0x00000200
//.stackreserve 0x00100000
//.subsystem 0x0003
//.corflags 0x00000001
//.class public auto ansi sealed beforefieldinit Type1
//       extends [mscorlib]System.Object
//{
//  .method public specialname rtspecialname 
//          instance void  .ctor() cil managed
//  {
//    .maxstack  2
//    IL_0000:  ldarg.0
//    IL_0001:  call       instance void [mscorlib]System.Object::.ctor()
//    IL_0006:  ret
//  }
//}"      |> ignore
//
//
//    let map = HashMap()
//    DefineTypes.topDef m map d
//    createTypes map
//    a.Save("test.dll")
//
//    m.GetTypes()
//
//    map.[t"Type", []]

    IL [
        TopTypeDef {
            kind = None
            name = t"Type"
            typeArgs = []
            parent = None
            impls = []
            members = []
        }
    ]
    |> emitDll "test.dll"