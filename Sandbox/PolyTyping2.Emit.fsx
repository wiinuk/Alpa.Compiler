module PolyTyping2_Emit
#load "PolyTyping2.fsx"

open PolyTyping2
open System.Reflection
open System.Reflection.Emit
open System

type C = global.System.TypeCode
type B = global.System.Reflection.BindingFlags
type O = global.System.Reflection.Emit.OpCodes

type TypeScheme' = TypeScheme' of TypeVar list * Type

type VarKind = V | I
type Var = Var of VarKind * string

[<NoComparison>]
type Exp' = Exp' of ExpInfo * PolyTyping2.Type
and [<NoComparison>] ExpInfo =
    | Lit' of Lit
    | Var' of Var
    | Lam' of Var * Exp'
    | App' of Exp' * Exp'
    | Ext' of Var * TypeScheme' * Exp'
    | Let' of Var * Exp' * Exp'
    | LetRec' of assoc<Var, TypeScheme' * Exp'> * Exp'
    
    | Mat' of Exp' * (Pat * Exp') * (Pat * Exp') list

    | TypeDef' of name: Symbol * TypeDef * Exp'

type VarInfo =
    | MonoVar of PolyTyping2.Type * FieldBuilder
    /// `id = \x -> x`;
    /// `none : type a. Option a = None`
    | PolyVar of TypeScheme' * MethodBuilder


module IL =
    let mutable seed = 0
    type TypeVar = struct
        val Name: string
        val Value: int
        new (name) =
            let x = System.Threading.Interlocked.Increment &seed
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

    type Op = 
        | Op of OpCode
        | OpCtor of OpCode * Type * Type list
        | OpInt of OpCode * int
        | OpType of Type
        | OpField of Type * name: string
        | OpCall of Type option * name: string * typeArgs: Type list * argTypes: Type list

    type MethodBody = MethodBody of baseInit: Type list option * (string * Op) list

    type Argument = Argument of name: string option * Type
    
    type MethodHead = MethodHead of name: string * typeArgs: TypeVar list * args: Argument list * ret: Argument
    type MethodInfo = MethodInfo of MethodHead * body: MethodBody

    type StaticMethodInfo = MethodInfo

    type MemberDef =
        | CtorDef of args: Argument list * MethodBody
        | SlotDef of MethodHead
        | MethodDef of baseMethod: (TypeRef * string) option * MethodInfo

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

//    System.AppDomain.CurrentDomain.DefineDynamicAssembly("", enum 0).DefineDynamicModule("").DefineGlobalMethod

    type IL = IL of TopDef list

    type T = System.Reflection.TypeAttributes
    type M = System.Reflection.MethodAttributes
    type P = System.Reflection.ParameterAttributes
    type CC = System.Reflection.CallingConventions
    open System.Collections.Generic

    let escapeTypeName name =
        if String.exists (function '.' | '\\' -> true | _ -> false) name
        then String.collect (function '.' -> "\\u002e" | '\\' -> "\\\\" | c -> string c) name
        else name

    let escaped (x: TypeName) = x.EscapedTypeName

    
    [<Sealed>]
    type HashMap<'k,'v when 'k : equality>() = inherit Dictionary<'k,'v>()
    type TypeMap = HashMap<PathRev, TypeBuilder>

    let varName (v: TypeVar) = v.Name
    let add (map: TypeMap) k v = map.Add(k, v)
    let get (map: TypeMap) k = map.[k]
    let addName (p, path) name = name, p::path
    let make1 name = name, []
    
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
            let mutable t = null
            if typeMap.TryGetValue(pathRev, &t) then t :> System.Type
            else
                let n = toTypeName Type.Delimiter pathRev
                let n = if arity = 0 then n else n + "`" + string arity
                System.Type.GetType(n, true)

        let rec aux = function
        | Type(pathRev, []) -> get typeMap pathRev 0
        | Type(pathRev, ts) -> get typeMap pathRev <| List.length ts
        | TypeVar v ->
            varMap
            |> Array.find (fun (v': TypeVar, _: GenericTypeParameterBuilder) -> v.Value = v'.Value)
            |> snd
            :> System.Type

        aux t
 
    let rec defineModule defineType addName' map name ms =
        let t = defineType(escaped name, T.Public ||| T.Abstract ||| T.Sealed)
        let path = addName' name
        add map path t
        for m in ms do defineModuleMember path t map m

    and defineType defineType addName' map { isAbstract = isAbstract; name = name; members = members } =
        let isAbstractMember = function 
            | CtorDef _
            | MethodDef _ -> false
            | SlotDef _ -> true

        let isInterface = List.forall isAbstractMember members
        let a = T.Public ||| T.BeforeFieldInit
        let a = if isInterface then a ||| T.Interface else a
        let a = if isAbstract then a ||| T.Abstract else a
        let a = if not isAbstract && List.forall (not << isAbstractMember) members then a ||| T.Sealed else a
        let t = defineType(escaped name, a)
        add map (addName' name) t

    and defineModuleMember path (t: TypeBuilder) map = function
        | ModuleMethodDef(MethodInfo _) -> ()
        | ModuleModuleDef(name, ms) -> defineModule t.DefineNestedType (addName path) map name ms
        | ModuleTypeDef td -> defineType t.DefineNestedType (addName path) map td

    let defineTopDef (m: ModuleBuilder) map = function
        | TopModuleDef(name, ms) -> defineModule m.DefineType make1 map name ms
        | TopTypeDef td -> defineType m.DefineType make1 map td
        
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
        Seq.map argType args
        |> Seq.map (solveType map varMap) 
        |> Seq.toArray

    let emitParam defineParameter i (Argument(pn, _)) = defineParameter(i, P.None, Option.toObj pn) |> ignore
    let emitParams defineParameter args = List.iteri (fun i a -> emitParam defineParameter (i + 1) a) args

    let emitMethodHead defineMethod attr callconv map (MethodHead(name,typeArgs,args,ret)) =
        let m : MethodBuilder = defineMethod(name, attr, callconv)
        let varMap = makeVarMap typeArgs <| fun x -> m.DefineGenericParameters x

        let pts = solveParamTypes map varMap args
        m.SetParameters(pts)
        emitParams m.DefineParameter args

        let rt = solveType map varMap (argType ret)
        m.SetReturnType rt
        emitParam m.DefineParameter 0 ret
        m

    let emitTopDef (m: ModuleBuilder) map = function
        | TopModuleDef(name, ms) ->
            let t = get map (name, [])
            for m in ms do
                match m with
                | ModuleMethodDef(MethodInfo(head,body)) ->
                    let a = M.Public ||| M.Static
                    let c = CC.Standard
                    let m = emitMethodHead t.DefineMethod a c map head

                    // TODO: emitBody
                    ()

                | ModuleTypeDef { name = name; typeArgs = typeArgs; parent = parent; impls = impls; members = members } ->
                    let t = get map (make1 name)
                    let varMap = makeVarMap typeArgs <| fun x -> t.DefineGenericParameters x

                    t.SetParent <| solveType map varMap (typeRefToType parent)
                    for impl in impls do t.AddInterfaceImplementation <| solveType map varMap (typeRefToType impl)

                    for m in members do
                        match m with
                        | CtorDef(args, body) ->
                            let pts = solveParamTypes map varMap args
                            let c = t.DefineConstructor(M.SpecialName ||| M.RTSpecialName ||| M.Public, CC.HasThis, pts)
                            
                            emitParams c.DefineParameter args
                            
                            // TODO: emitBody
                            ()

                        | SlotDef head ->
                            let a = M.Abstract ||| M.HideBySig ||| M.Public ||| M.Virtual
                            let a = if t.IsInterface then a ||| M.NewSlot else a
                            let c = CC.HasThis
                            let m = emitMethodHead t.DefineMethod a c map head
                            ()

                        | MethodDef(Some(baseType, baseMethodName), MethodInfo(MethodHead(args = args) as head, body)) ->
                            
                            let a = M.Final ||| M.HideBySig ||| M.Virtual
                            let c = CC.HasThis
                            let m = emitMethodHead t.DefineMethod a c map head
                            
                            /// TODO: last path
                            let bt = solveType map varMap <| typeRefToType baseType
                            let pts = solveParamTypes map varMap args
                            let bm = bt.GetMethod(baseMethodName, pts)

                            t.DefineMethodOverride(bm, m)

                | ModuleModuleDef(name, _) -> failwith "Not implemented yet"

    let emitIL m (IL ds) =
        let map = HashMap()
        for d in ds do defineTopDef m map d
        for d in ds do emitTopDef m map d


type EmitEnv = {
    g: ILGenerator
    vars: Map<Var, VarInfo>
    defineType: TypeAttributes -> string -> Type -> Type list -> TypeBuilder * string
}
let fleshTypeName baseName env = baseName, env


let inRange lo hi x = lo <= x && x <= hi
let gen { g = g } op = g.Emit op
let genI1 { g = g } op (n: int8) = g.Emit(op, n)
let genI4 { g = g } op (n: int32) = g.Emit(op, n)
let genI8 { g = g } op (n: int64) = g.Emit(op, n)
let genR4 { g = g } op (r: single) = g.Emit(op, r)
let genR8 { g = g } op (r: double) = g.Emit(op, r)
let genString { g = g } op (x: string) = g.Emit(op, x)
let genType { g = g } op (t: Type) = g.Emit(op, t)
let genLocal { g = g } op (l: LocalBuilder) = g.Emit(op, l)
let genCtor { g = g } op (c: ConstructorInfo) = g.Emit(op, c)
let genField { g = g } op (f: FieldInfo) = g.Emit(op, f)
let genMethod { g = g } op (m: MethodInfo) = g.Emit(op, m)
let local { g = g } t = g.DeclareLocal t

let emitInt64 g n =
    genI8 g O.Ldc_I8 n
    gen g O.Conv_I8

let emitUInt64 g n =
    genI8 g O.Ldc_I8 <| int64<uint64> n
    gen g O.Conv_U8

let emitInt g = function
    | n when inRange -1 8 n ->
        match n with
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
        |> gen g

    | n when inRange -128 127 n -> genI1 g O.Ldc_I4_S <| sbyte n
    | n -> genI4 g O.Ldc_I4 n

let emitUInt8 g n =
    emitInt g <| int<byte> n
    gen g O.Conv_U1

let emitChar g v =
    emitInt g <| int<char> v
    gen g O.Conv_U2
    
let emitFloat g r = genR8 g O.Ldc_R8 r
let emitString g x = genString g O.Ldstr x

let emitStoreElement g (t: Type) =
    if t.IsEnum then genType g O.Stelem t
    else

    match Type.GetTypeCode t with
    | C.Boolean
    | C.SByte
    | C.Byte -> gen g O.Stelem_I1
    | C.Char
    | C.Int16
    | C.UInt16 -> gen g O.Stelem_I2
    | C.Int32
    | C.UInt32 -> gen g O.Stelem_I4
    | C.Int64
    | C.UInt64 -> gen g O.Stelem_I8
    | C.Single -> gen g O.Stelem_R4
    | C.Double -> gen g O.Stelem_R8
    | _ when t.IsValueType -> genType g O.Stelem t
    | _ -> gen g O.Stelem_Ref


let emitArray g emitValue (xs: 'a array) =
    emitInt g xs.Length
    genType g O.Newarr typeof<'a>
    Array.iteri (fun i x ->
        gen g O.Dup
        emitValue g x
        emitInt g i
        emitStoreElement g typeof<'a>
    ) xs

    
let int32Min = bigint Int32.MinValue
let int32Max = bigint Int32.MaxValue
let int64Min = bigint Int64.MinValue
let int64Max = bigint Int64.MaxValue
let uint64Min = bigint UInt64.MinValue
let uint64Max = bigint UInt64.MaxValue

let emitDefault g t =
    match Type.GetTypeCode t with
    | C.Empty
    | C.String
    | C.DBNull -> gen g O.Ldnull

    | C.Boolean
    | C.Char
    | C.SByte
    | C.Byte
    | C.Int16
    | C.UInt16
    | C.Int32
    | C.UInt32 -> gen g O.Ldc_I4_0

    | C.Int64
    | C.UInt64 ->
        gen g O.Ldc_I4_0
        gen g O.Conv_I8

    | C.Single -> genR4 g O.Ldc_R4 0.0f
    | C.Double -> genR8 g O.Ldc_R8 0.0
    | C.Decimal ->
        gen g O.Ldc_I4_0
        genCtor g O.Newobj <| typeof<Decimal>.GetConstructor [|typeof<int>|]

    | _ ->
        if t.IsValueType then
            let l = local g t
            genLocal g O.Ldloca l
            genType g O.Initobj t
            genLocal g O.Ldloc l
        else
            gen g O.Ldnull

let useVirtual (m: MethodInfo) = not (m.IsStatic || m.DeclaringType.IsValueType)

let emitCall g (m: MethodInfo) =
    if m.CallingConvention = CallingConventions.VarArgs then failwithf "UnexpectedVarArgsCall(%A)" m
    else
        let o = if useVirtual m then O.Callvirt else O.Call

        // Object#GetType, Object#ToString, Object#GetHashCode, Object#Equals
        if o = O.Callvirt && m.ReflectedType.IsValueType then
            genType g O.Constrained m.ReflectedType

        genMethod g o m

let emitPropertyGet g (p: PropertyInfo) = emitCall g <| p.GetGetMethod true

let emitLit g = function
    | CharLit c -> emitChar g c
    | IntegerLit n ->
        if n.IsZero then emitDefault g typeof<bigint>
        elif n.IsOne then
            emitPropertyGet g <| typeof<bigint>.GetProperty("One", B.Public ||| B.Static)

        elif n = bigint.MinusOne then
            emitPropertyGet g <| typeof<bigint>.GetProperty("MinusOne", B.Public ||| B.Static)

        elif inRange int32Min int32Max n then
            let n = int32<bigint> n
            emitInt g n
            genCtor g O.Newobj <| typeof<bigint>.GetConstructor [| typeof<int> |]

        elif inRange int64Min int64Max n then
            let n = int64<bigint> n
            emitInt64 g n
            genCtor g O.Newobj <| typeof<bigint>.GetConstructor [| typeof<int64> |]

        elif inRange uint64Min uint64Max n then
            let n = uint64<bigint> n
            emitUInt64 g n
            genCtor g O.Newobj <| typeof<bigint>.GetConstructor [| typeof<uint64> |]

        else
            emitArray g emitUInt8 <| n.ToByteArray()
            genCtor g O.Newobj <| typeof<bigint>.GetConstructor [| typeof<array<byte>> |]

    | IntLit n -> emitInt g n
    | FloatLit r -> emitFloat g r
    | StringLit x -> emitString g x

let emitVar g v =
    (*
    `
    class Num a =
        ofInteger : Integer -> a
        (_+_) : a -> a -> a
    
    instance Num Int =
        ofInteger = ...
        a + b = ...
    
    (ten: Int) = 10i in
    (succ: type a. Num a -> a -> a) = \(_i: Num a) (n: a) -> _i.``_+_`` n (_i.ofInteger 1I) in
    succ ten
    `
     
    `
    type abstract `->` (a, b) <: Object =
        abstract ` ` a : b;;

    type interface Num a <: Object =
        abstract ofInteger (Integer) : a;
        abstract `_+_` (a, a) : a;;

    type #(Num Int32) <: Object, Num Int32 =
        ctor () = base_init ret;
        override ofInteger (Integer) : Int32 { ... };
        override `_+_` (Int32, Int32) : Int32 { ... };;

    val #(Num Int32) : Num Int32;;
    val ten : Int32;;

    type CloSucc a <: (Num a -> a -> a) =
        ctor () = base_init ret;
        override ` ` (Num a) : a -> a =
            ldarg.0
            newobj (CloSucc2 a) (Num a)
            ret;;
    
    fun succ (a) () : Num a -> a -> a = newobj (CloSucc a) ();;
    fun init() =
        newobj #(Num Int32) ()
        stfld #(Num Int32)
        ldc_i4 10i
        stfld ten
        ret;;

    fun main() =
        call init ()

        ldfld ten
        ldfld #(Num Int32)
        call succ Int32 ()
        callvirt `->`(Num Int32, Int32 -> Int32)#` ` (Num Int32)
        callvirt `->`(Int32, Int32)#` `(Int32)
        ret;;
    `
    *)

    match Map.find v g.vars with
    | MonoVar(_, f) -> genField g O.Ldfld f
    | PolyVar(_, m) -> genMethod g O.Call m

//type TA = TypeAttributes
//let rec emit g (Exp'(e, t)) =
//    match e with
//    | Lit' l -> emitLit g l
//    | Var' v -> emitVar g v
//    | Lam'(v, e) ->
//        let t, tn = g.defineType (TA.Public ||| TA.BeforeFieldInit) "clo" g.lamType []
//        ()
//        (*
//        \x -> x
//        \() -> 1i
//        *)
//
//    | App'(_, _) -> failwith "Not implemented yet"
//    | Ext'(_, _, _) -> failwith "Not implemented yet"
//    | Let'(_, _, _) -> failwith "Not implemented yet"
//    | LetRec'(_, _) -> failwith "Not implemented yet"
//    | Mat'(_, _, _) -> failwith "Not implemented yet"
//    | TypeDef'(name, _, _) -> failwith "Not implemented yet"
//
