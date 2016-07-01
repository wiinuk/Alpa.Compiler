open System.Reflection
open System.Reflection.Emit
open System.Collections.Generic
open System
open Microsoft.FSharp.Quotations

type O = System.Reflection.Emit.OperandType
type C = System.Reflection.ExceptionHandlingClauseOptions

type Instr = Instr of offset: int * OpCode * value1: int64 * value2: obj

type MEnv = {
    Modules : Module list
    TypeArgs : Type array
    MethodTypeArgs : Type array
    Handlers : ExceptionHandlingClause array
}

type Stream = {
    mutable index : int
    items : byte array
}

let makeStream xs = {
    index = 0
    items = Seq.toArray xs
}

let canRead s = s.index < s.items.Length

let readU1 s = 
    let x = s.index
    s.index <- x + 1
    s.items.[x]

let readI1 s = readU1 s |> int8
let readI2 s = int16 (readU1 s) ||| (int16 (readU1 s) <<< 8)
let readI4 s = 
    let read s n = int (readU1 s) <<< n
    read s 0 ||| read s 8 ||| read s 16 ||| read s 24
let readI8 s = int64 (readI4 s) ||| (int64 (readI4 s) <<< 32)
let readF8 s = readI8 s |> BitConverter.Int64BitsToDouble
let readF4 s = BitConverter.ToSingle(readI4 s |> BitConverter.GetBytes, 0)


let envOfMethodBase (m : MethodBase) = 
    let t = m.DeclaringType
    let rec baseModules (t: Type) =
        match t.BaseType with
        | null -> []
        | b when b = typeof<obj> -> [b.Module]
        | b -> b.Module::baseModules b
    {
        Modules = m.Module::t.Module::baseModules t
        TypeArgs = 
            if t.IsGenericType then t.GetGenericArguments()
            else null

        MethodTypeArgs = 
            if m.IsGenericMethod then m.GetGenericArguments()
            else null

        Handlers = Seq.toArray <| m.GetMethodBody().ExceptionHandlingClauses
    }

let opMap = 
    let xs = 
        typeof<OpCodes>.GetFields()
        |> Seq.map (fun f -> f.GetValue null)
        |> Seq.choose (function :? OpCode as x -> Some x | _ -> None)
        |> Seq.map (fun x -> x.Value, x)
        |> dict
    Dictionary xs


let printTupleLike print (xs: #seq<_>) =
    use e = xs.GetEnumerator()
    printf "("
    if e.MoveNext() then
        print e.Current
        while e.MoveNext() do
            printf ", "
            print e.Current 
    printf ")"
    
let printString q x = 
    printf "%c" q
    for x in x do
        if x = q then printf "\\%c" q
        elif Char.IsLetterOrDigit x then printf "%c" x
        else printf "\\u%04x" <| int16 x
    printf "%c" q

let isIdStartOrContinue = function '_' | '`' -> true | c -> Char.IsLetterOrDigit c
let isIdStart = function '_' -> true | c -> Char.IsLetter c

let printId = function
    | "" -> printf "''"
    | s when isIdStart s.[0] && String.forall isIdStartOrContinue s -> printf "%s" s
    | s -> printString '\'' s

let rec printType (x: Type) = 
    printId x.Name
    if x.IsGenericType then printTupleLike printType <| x.GetGenericArguments()

let printMethod (m : MethodBase) = 
    printType m.DeclaringType
    printf "::"
    printId m.Name
    if m.IsGenericMethod then printTupleLike printType <| m.GetGenericArguments()
    else ()

    m.GetParameters() |> printTupleLike (fun p -> printType p.ParameterType)

    printf " : "
    let ret = 
        match m with
        | :? MethodInfo as x -> x.ReturnType
        | _ -> typeof<Void>
    printType ret

let printField (x: FieldInfo) = 
    printType x.DeclaringType
    printf "::"
    printId x.Name
    printf " : "
    printType x.FieldType

let printBr x = printf "@x%04X" x

let resolve resolveOrRaise { Modules = ms } =
    Seq.pick (fun r -> try Some <| resolveOrRaise r with _ -> None) ms

let resolveType ({ TypeArgs = targs; MethodTypeArgs = mtargs } as env) md =
    resolve (fun m -> m.ResolveType(md, targs, mtargs)) env

let printOperand ({ TypeArgs = targs; MethodTypeArgs = mtargs } as env) s = 
    function 
    | O.InlineBrTarget -> printBr <| readI4 s + s.index
    | O.InlineField ->
        let md = readI4 s
        resolve (fun m -> m.ResolveField(md, targs, mtargs)) env
        |> printField

    | O.InlineI -> printf "%d" <| readI4 s
    | O.InlineI8 -> printf "%dL" <| readI8 s
    | O.InlineMethod -> 
        let md = readI4 s
        resolve (fun m -> m.ResolveMethod(md, targs, mtargs)) env
        |> printMethod

    | O.InlineNone -> ()
    | O.InlineR -> printf "%f" <| readF8 s
    | O.InlineSig ->
        let md = readI4 s
        resolve (fun m -> m.ResolveSignature md) env |> printf "signature (%A)"

    | O.InlineString ->
        let md = readI4 s
        resolve (fun m -> m.ResolveString md) env |> printString '"'

    | O.InlineSwitch -> 
        let count = readI4 s
        let offset = s.index + count * 4

        Seq.init count (fun _ -> offset + readI4 s)
        |> printTupleLike printBr

    | O.InlineTok -> 
        let tok = readI4 s
        resolve (fun m -> m.ResolveMember(tok, targs, mtargs)) env |> function 
        | :? FieldInfo as x -> printField x
        | :? MethodBase as x -> printMethod x
        | :? Type as x -> printType x
        | _ -> printf "member(%06X)" tok

    | O.InlineType -> readI4 s |> resolveType env |> printType
    | O.InlineVar -> printf "%d" <| int32 (readI2 s)
    | O.ShortInlineBrTarget -> printBr <| int (readI1 s) + s.index
    | O.ShortInlineI -> printf "%dy" <| readI1 s
    | O.ShortInlineR -> printf "%ff" <| readF4 s
    | O.ShortInlineVar -> printf "%d" <| int32 (readU1 s)
    | _ -> failwith ""

//DEFAULT         = 0x00uy = 0b00000000uy
//EXPLICITTHIS    = 0x40uy = 0b01000000uy
//HASTHIS         = 0x20uy = 0b00100000uy
//GENERIC         = 0x10uy = 0b00010000uy
//FASTCALL        = 0x04uy = 0b00000100uy
//STDCALL         = 0x02uy = 0b00000010uy
//C               = 0x01uy = 0b00000001uy
//VARARG          = 0x05uy = 0b00000101uy
//THISCALL        = 0x03uy = 0b00000011uy
//
//module ELEMENT_TYPE =
//    VOID        = 0x01
//    BOOLEAN     = 0x02
//    CHAR        = 0x03
//    I1          = 0x04
//    U1          = 0x05
//    I2          = 0x06
//    U2          = 0x07
//    I4          = 0x08
//    U4          = 0x09
//    I8          = 0x0a
//    U8          = 0x0b
//    R4          = 0x0c
//    R8          = 0x0d
//    STRING      = 0x0e
//    PTR         = 0x0f
//    BYREF       = 0x10
//    VALUETYPE   = 0x11
//    CLASS       = 0x12
//    VAR         = 0x13
//    ARRAY       = 0x14
//    GENERICINST = 0x15
//    TYPEDBYREF  = 0x16
//    I           = 0x18 // System.IntPtr
//    U           = 0x19 // System.UIntPtr
//    FNPTR       = 0x1b
//    OBJECT      = 0x1c // System.Object
//    SZARRAY     = 0x1d
//    MVAR        = 0x1e
//    CMOD_REQD   = 0x1f
//    CMOD_OPT    = 0x20
//    SENTINEL    = 0x41 // Sentinel for vararg method signature
//
//open ELEMENT_TYPE
//
//thisKind = HASTHIS EXPLICITTHIS?
//
//bit = 0b | 1b
//number =
//    | 0b bit{7}           (0x00..0x7F)
//    | 1b 0b bit{14}       (0x0080..0x3FFF)
//    | 1b 1b 0b bit{29}    (0x00040000..0x1FFFFFFF)
//
//rank = number (1..)
//arrayShape = rank (numSizes: number) (size: number)* (numLoBounds: number) (loBound: number)*
//
// // 0x49 = 0x01000012
//typeDefOrRefEncoded = number |>> fun n ->
//    int32 ((uint32 n &&& 0b11u <<< 24) ||| (uint32 n >>> 2))
//
//type =
//    | BOOLEAN
//    | CHAR
//    | I1
//    | U1
//    | I2
//    | U2
//    | I4
//    | U4
//    | I8
//    | U8
//    | R4
//    | R8
//    | I
//    | U
//    | ARRAY type arrayShape // general array
//    | CLASS typeDefOrRefEncoded
//    | FNPTR methodDefSig
//    | FNPTR methodRefSig
//    | GENERICINST (CLASS | VALUETYPE) typeDefOrRefEncoded (genArgCount: number) type*
//    | MVAR number
//    | OBJECT
//    | PTR customMod* type
//    | PTR customMod* VOID
//    | STRING
//    | SZARRAY customMod* type // zsarray
//    | VALUETYPE typeDefOrRefEncoded
//    | VAR number
//
//customMod = (CMOD_OPT | CMOD_REQD) typeDefOrRefEncoded
//
//retType = customMod* (BYREF? type | TYPEDBYREF | VOID)
//param = customMod* (BYREF? type | TYPEDBYREF)
//
//methodDefSigHead =
//    | (thisKind? ||| (DEFAULT | VARARG)) 
//    | (thisKind? ||| GENERIC) (genParamCount: number)
//
//methodDefSig = methodDefSigHead (paramCount: number) retType param*
//methodRefSig =
//    | (thisKind? ||| VARARG) (paramCount: number) retType param* SENTINEL param*
//    | methodDefSig
//
//standAloneMethodSigAttr =
//    | DEFAULT
//    | C
//    | STDCALL
//    | THISCALL
//    | FASTCALL
//
//standAloneMethodSig =
//    | (thisKind? ||| standAloneMethodSigAttr) (paramCount: number) retParam param*
//    | (thisKind? ||| VARARG) (paramCount: number) retParam param* (SENTINEL param*)?

[<Flags>]
type MethodAttr =
    | DEFAULT       = 0x00
    | EXPLICITTHIS  = 0x40
    | HASTHIS       = 0x20
    | GENERIC       = 0x10
    | FASTCALL      = 0x04
    | STDCALL       = 0x02
    | C             = 0x01
    | VARARG        = 0x05
    | THISCALL      = 0x03

type ELEMENT_TYPE =
    | VOID = 0x01
    | BOOLEAN = 0x02
    | CHAR = 0x03
    | I1 = 0x04
    | U1 = 0x05
    | I2 = 0x06
    | U2 = 0x07
    | I4 = 0x08
    | U4 = 0x09
    | I8 = 0x0a
    | U8 = 0x0b
    | R4 = 0x0c
    | R8 = 0x0d
    | STRING = 0x0e
    | PTR = 0x0f
    | BYREF = 0x10
    | VALUETYPE = 0x11
    | CLASS = 0x12
    | VAR = 0x13
    | ARRAY = 0x14
    | GENERICINST = 0x15
    /// System.TypedReference
    | TYPEDBYREF = 0x16
    /// System.IntPtr
    | I = 0x18
    /// System.UIntPtr
    | U = 0x19
    | FNPTR = 0x1b
    /// System.Object
    | OBJECT = 0x1c
    | SZARRAY = 0x1d
    | MVAR = 0x1e
    | CMOD_REQD = 0x1f
    | CMOD_OPT = 0x20
    /// Sentinel for vararg method signature
    | SENTINEL = 0x41

let readNumber s =
    let v1 = int <| readI1 s
    if v1 &&& 0b10000000 = 0 then v1
    elif v1 &&& 0b11000000 = 0b10000000 then
        ((v1 &&& 0b00111111) <<< 8) ||| int (readI1 s)
    else
        let v2 = int <| readI1 s
        let v3 = int <| readI1 s
        let v4 = int <| readI1 s
        ((v1 &&& 0b00011111) <<< 24) ||| (v2 <<< 16) ||| (v3 <<< 8) ||| v4

let readCount read n s =
    let rec aux xs n = if n <= 0 then List.rev xs else aux (read s::xs) (n-1)
    aux [] n

type ArrayShape = ArrayShape of rank: int * sizes: int list * loBounds: int list
let readArrayShape s =
    ArrayShape(
        readNumber s,
        readCount readNumber (readNumber s) s,
        readCount readNumber (readNumber s) s
    )

let readTypeDefOrRefEncoded s =
    let n = uint32 <| readNumber s
    int32 ((n &&& 0b11u <<< 24) ||| (n >>> 2))

type E = ELEMENT_TYPE

let readElementType s = enum(int (readU1 s))

type M = MethodAttr

type Mod = Mod of isOpt: bool * Type
type Param = Param of isByref: bool * Mod list * Type
type Sig = Sig of MethodAttr * retType: Param * genParams: Param list * methodParams: Param list * varargParams: Param list

[<Sealed>]
type GenericArrayType(elementType: Type, shape: ArrayShape) =
    inherit Type()
//    override __.IsArrayImpl() = true
//    override __.HasElementTypeImpl() = true
//    override __.GetElementType() = elementType

[<Sealed>]
type FnptrType(signature: Sig) =
    inherit Type()


let ruadCustomModTail elementType env s =
    let md = readTypeDefOrRefEncoded s
    Mod((elementType = E.CMOD_OPT), resolveType env md)

let rec readType env s = readTypeTail (readElementType s) env s
and readTypeTail elementType env s =
    match elementType with
    | E.BOOLEAN -> typeof<bool>
    | E.CHAR -> typeof<char>
    | E.I1 -> typeof<int8>
    | E.U1 -> typeof<uint8>
    | E.I2 -> typeof<int16>
    | E.U2 -> typeof<uint16>
    | E.I4 -> typeof<int32>
    | E.U4 -> typeof<uint32>
    | E.I8 -> typeof<int64>
    | E.U8 -> typeof<uint64>
    | E.R4 -> typeof<single>
    | E.R8 -> typeof<double>
    | E.I -> typeof<nativeint>
    | E.U -> typeof<unativeint>
    | E.ARRAY ->
        let t = readType env s
        match readArrayShape s with
        | ArrayShape(0,[],[]) -> t.MakeArrayType()
        | ArrayShape(rank,[],[]) -> t.MakeArrayType rank
        | shape -> upcast GenericArrayType(t, shape)

    | E.CLASS -> readTypeDefOrRefEncoded s |> resolveType env
    | E.FNPTR -> upcast FnptrType(readSigAny env s)
    | E.GENERICINST ->
        let classOrValueType = readElementType s
        let md = readTypeDefOrRefEncoded s
        let genArgCount = readNumber s
        let typeArgs = readCount (readType env) genArgCount s

        let openType = resolveType env md
        openType.MakeGenericType(List.toArray typeArgs)

    | E.MVAR ->
        let i = readNumber s
        env.MethodTypeArgs.[i]

    | E.OBJECT -> typeof<obj>
    | E.PTR ->
        let rec aux ms s =
            match readElementType s with
            | E.CMOD_OPT
            | E.CMOD_REQD as et ->
                let m = ruadCustomModTail et env s
                aux (m::ms) s

            | e ->
                let t = if e = E.VOID then typeof<Void> else readTypeTail e env s
                match ms with
                | [] -> t.MakePointerType()
                | ms -> upcast PointerType(List.rev ms, t)
        aux [] s

    | E.STRING -> typeof<string>
    | E.SZARRAY -> readCustomModsAndType
    | E.VALUETYPE ->
    | E.VAR ->

//type =
//    | STRING
//    | SZARRAY customMod* type // zsarray
//    | VALUETYPE typeDefOrRefEncoded
//    | VAR number

and readRetOrParamTail elementType ms env s =
    match elementType with
    | E.CMOD_OPT
    | E.CMOD_REQD ->
        let m = ruadCustomModTail elementType env s
        readRetOrParamTail (readElementType s) (m::ms) env s

    | E.BYREF -> Param(true, List.rev ms, readType env s)
    | E.TYPEDBYREF -> Param(false, List.rev ms, typeof<TypedReference>)
    | E.VOID -> Param(false, List.rev ms, typeof<Void>)
    | e -> Param(false, List.rev ms, readTypeTail e env s)

and readRetOrParam env s = readRetOrParamTail (readElementType s) [] env s

and readParamAndVarargParams count env s =
    let rec aux isVararg ps vs count =
        if count <= 0 then List.rev ps, List.rev vs
        else
            match readElementType s with
            | E.SENTINEL -> aux true ps vs count
            | e ->
                let p = readRetOrParamTail e [] env s
                let ps, vs = if isVararg then ps, (p::vs) else (p::ps), vs
                aux isVararg ps vs (count - 1)

    aux false [] [] count

and readSigAny env s =
    let attr = enum(int (readU1 s))
    let genParamCount = if attr &&& M.GENERIC = M.GENERIC then readNumber s else 0
    let paramCount = readNumber s
    let retType = readRetOrParam env s
    let genParams = readCount (readRetOrParam env) genParamCount s
    let methodParams, varargParams = readParamAndVarargParams paramCount env s
    Sig(attr, retType, genParams, methodParams, varargParams)

type SignatureInfo =
    | StandAloneMethodSig

type Operand =
    | InlineBrTarget of int32
    | InlineField of FieldInfo
    | InlineI4 of int32
    | InlineI8 of int64
    | InlineMethod of MethodBase
    | InlineNone
    | InlineR of double
    | InlineSig of SignatureInfo
    
let readOperand ({ TypeArgs = targs; MethodTypeArgs = mtargs } as env) s = function 
    | O.InlineBrTarget -> InlineBrTarget <| readI4 s + s.index
    | O.InlineField ->
        let md = readI4 s
        InlineField <| resolve (fun m -> m.ResolveField(md, targs, mtargs)) env

    | O.InlineI -> InlineI4 <| readI4 s
    | O.InlineI8 -> InlineI8 <| readI8 s
    | O.InlineMethod -> 
        let md = readI4 s
        InlineMethod <| resolve (fun m -> m.ResolveMethod(md, targs, mtargs)) env

    | O.InlineNone -> InlineNone
    | O.InlineR -> InlineR <| readF8 s
    | O.InlineSig ->
        let md = readI4 s
        resolve (fun m -> m.ResolveSignature md) env |> printf "signature (%A)"

    | O.InlineString ->
        let md = readI4 s
        resolve (fun m -> m.ResolveString md) env |> printString '"'

    | O.InlineSwitch -> 
        let count = readI4 s
        let offset = s.index + count * 4

        Seq.init count (fun _ -> offset + readI4 s)
        |> printTupleLike printBr

    | O.InlineTok -> 
        let tok = readI4 s
        resolve (fun m -> m.ResolveMember(tok, targs, mtargs)) env |> function 
        | :? FieldInfo as x -> printField x
        | :? MethodBase as x -> printMethod x
        | :? Type as x -> printType x
        | _ -> printf "member(%06X)" tok

    | O.InlineType ->
        let md = readI4 s
        printType <| resolve (fun m -> m.ResolveType(md, targs, mtargs)) env

    | O.InlineVar -> printf "%d" <| int32 (readI2 s)
    | O.ShortInlineBrTarget -> printBr <| int (readI1 s) + s.index
    | O.ShortInlineI -> printf "%dy" <| readI1 s
    | O.ShortInlineR -> printf "%ff" <| readF4 s
    | O.ShortInlineVar -> printf "%d" <| int32 (readU1 s)
    | _ -> failwith ""

let readOpValue s = 
    match readU1 s with
    | 0xFEuy -> (0xFEs <<< 8) ||| int16 (readU1 s)
    | v -> int16 v

let printIndent i = for _ in 1..i do printf "    "

let printBlockStart i { Handlers = hs } offset =
    let h =
        hs 
        |> Seq.tryFind (fun h ->
            h.TryOffset = offset ||
            h.HandlerOffset = offset ||
            (h.Flags = C.Filter && h.FilterOffset = offset)
        )
    match h with
    | None -> i
    | Some h when h.TryOffset = offset -> 
        printIndent i
        printfn "try"
        i + 1

    | Some h when h.HandlerOffset = offset -> 
        printIndent i
        match h.Flags with
        | C.Finally -> printfn "finally"
        | C.Fault -> printfn "fault"
        | C.Clause -> 
            printf "catch "
            printType h.CatchType
            printfn ""
        | C.Filter -> printfn "then"
        | _ -> failwith ""
        i + 1

    | Some _ -> 
        printIndent i
        printfn "filter"
        i + 1

let printBlockEnd i { Handlers = hs } offset = 
    let h =
        hs 
        |> Seq.tryFind (fun h -> 
           h.TryOffset + h.TryLength = offset ||
           h.HandlerOffset + h.HandlerLength = offset ||
           (h.Flags = C.Filter && h.HandlerOffset = offset)
        )
    match h with
    | None -> i
    | Some h when offset = h.HandlerOffset -> i - 1
    | Some _ -> 
        let i = i - 1
        printfn ""
        printIndent i
        printf ";"
        i

let printInstr i env s = 
    let offset = s.index
    let op = opMap.[readOpValue s]
    let i = printBlockStart i env offset
    printIndent i
    printBr offset
    printf " %s " op.Name
    printOperand env s op.OperandType
    printBlockEnd i env s.index

let printIL env s = 
    if not <| canRead s then ()
    else 
        let i = printInstr 0 env s
        
        let rec aux i = 
            if not <| canRead s then ()
            else 
                printfn ""
                let i = printInstr i env s
                aux i
        aux i

let printLocals (b: MethodBody) = 
    let vs = Seq.toArray b.LocalVariables
    match vs with
    | null | [||] -> ()
    | _ -> 
        printf "let "
        if not b.InitLocals then printf "noinit "
        vs
        |> printTupleLike (fun v ->
            if v.IsPinned then printf "pinned " else ()
            printType v.LocalType
        ) 
        printfn ""

let printMethodBase m = 
    let env = envOfMethodBase m
    let b = m.GetMethodBody()
    let xs = b.GetILAsByteArray()
    printLocals b
    printIL env (makeStream xs)

let rec tryPick (|Pick|_|) = 
    function 
    | Pick x -> Some x
    | ExprShape.ShapeCombination(_, xs) -> List.tryPick (tryPick (|Pick|_|)) xs
    | ExprShape.ShapeLambda(_, x) -> tryPick (|Pick|_|) x
    | ExprShape.ShapeVar _ -> None

let getMethod e = 
    tryPick (function 
        | Patterns.Call(_, m, _) -> m :> MethodBase |> Some
        | Patterns.NewObject(m, _) -> m :> MethodBase |> Some
        | Patterns.PropertyGet(_, p, _) -> p.GetGetMethod() :> MethodBase |> Some
        | Patterns.PropertySet(_, p, _, _) -> p.GetSetMethod() :> MethodBase |> Some
        | _ -> None
    ) e
    |> Option.get

let print e = getMethod e |> printMethodBase; printfn ""
let x() = [|20n; 30n|]
let app f x = f x

let tryf() = try 1 / 0 with :? DivideByZeroException -> 0

// print <@ let mutable x = ResizeArray.Enumerator() in x.MoveNext() @>


let y() = [|1s;2s|]
print <@ y @>

try print <@ tryf @>
with e -> printfn "%A" e


type Pair<'a,'b> = struct
    val mutable Key: 'a
    val mutable Value: 'b
end
type T =
    static member F(x: Pair<_,_> byref) =
        let v = &x.Value
        v

printMethodBase <| typeof<T>.GetMethod("F")

open System.Linq.Expressions
type B = System.Linq.Expressions.MemberBindingType
type N = System.Linq.Expressions.ExpressionType
type E = System.Linq.Expressions.Expression

let rec memberBindingExpressions (m: MemberBinding) =
    match m.BindingType with
    | B.Assignment -> let m = m :?> MemberAssignment in Seq.singleton m.Expression
    | B.MemberBinding -> let m = m :?> MemberMemberBinding in Seq.collect memberBindingExpressions m.Bindings
    | B.ListBinding -> let m = m :?> MemberListBinding in m.Initializers |> Seq.collect (fun i -> i.Arguments)
    | _ -> Seq.empty

let paramExprsToExprs (xs: ParameterExpression seq) : Expression seq = unbox(box xs)
let objToSeq = function null -> Seq.empty | x -> upcast [|x|]
let staticOrInstance this xs = if isNull this then xs else seq { yield this; yield! xs }

let (|Parameter|Lambda|Combination|) (e: Expression) =
    match e.NodeType with
    | N.Add
    | N.AddChecked
    | N.And
    | N.AndAlso
    | N.ArrayIndex
    | N.Coalesce
    | N.Divide
    | N.Equal
    | N.ExclusiveOr
    | N.GreaterThan
    | N.GreaterThanOrEqual
    | N.LeftShift
    | N.LessThan
    | N.LessThanOrEqual
    | N.Modulo
    | N.Multiply
    | N.MultiplyChecked
    | N.NotEqual
    | N.Or
    | N.OrElse
    | N.Power
    | N.RightShift
    | N.Subtract
    | N.SubtractChecked
    | N.Assign
    | N.AddAssign
    | N.AndAssign
    | N.DivideAssign
    | N.ExclusiveOrAssign
    | N.LeftShiftAssign
    | N.ModuloAssign
    | N.MultiplyAssign
    | N.OrAssign
    | N.PowerAssign
    | N.RightShiftAssign
    | N.SubtractAssign
    | N.AddAssignChecked
    | N.MultiplyAssignChecked
    | N.SubtractAssignChecked ->
        let e = e :?> BinaryExpression
        Combination(box e, [|e.Left; e.Right|] :> _ seq)

    | N.ArrayLength
    | N.Convert
    | N.ConvertChecked
    | N.Negate
    | N.UnaryPlus
    | N.NegateChecked
    | N.Not
    | N.Quote
    | N.TypeAs
    | N.Decrement
    | N.Increment
    | N.Throw
    | N.Unbox
    | N.PreIncrementAssign
    | N.PreDecrementAssign
    | N.PostIncrementAssign
    | N.PostDecrementAssign
    | N.OnesComplement
    | N.IsTrue
    | N.IsFalse ->
        let e = e :?> UnaryExpression
        Combination(box e, upcast [|e.Operand|])

    | N.Call ->
        let e = e :?> MethodCallExpression
        Combination(box e, staticOrInstance e.Object e.Arguments)

    | N.Conditional ->
        let ce = e :?> ConditionalExpression
        Combination(box ce, upcast [|ce.Test; ce.IfTrue; ce.IfFalse|])

    | N.Constant
    | N.DebugInfo
    | N.Default
    | N.Extension -> Combination(box e, Seq.empty)
    
    | N.Parameter -> Parameter(e :?> ParameterExpression)
    | N.Invoke ->
        let e = e :?> InvocationExpression
        Combination(box e, seq { yield e.Expression; yield! e.Arguments })

    | N.Lambda -> Lambda(e :?> LambdaExpression)
    | N.ListInit ->
        let e = e :?> ListInitExpression
        let xs = seq {
            yield e.NewExpression :> E
            for i in e.Initializers do yield! i.Arguments
        }
        Combination(box e, xs)

    | N.MemberAccess ->
        let e = e :?> MemberExpression
        Combination(box e, upcast [| e.Expression |])

    | N.MemberInit ->
        let e = e :?> MemberInitExpression
        let xs = seq {
            yield e.NewExpression :> E
            for b in e.Bindings do yield! memberBindingExpressions b
        }
        Combination(box e, xs)

    | N.New ->
        let e = e :?> NewExpression
        Combination(box e, upcast e.Arguments)

    | N.NewArrayInit
    | N.NewArrayBounds ->
        let e = e :?> NewArrayExpression
        Combination(box e, upcast e.Expressions)

    | N.TypeIs
    | N.TypeEqual ->
        let e = e :?> TypeBinaryExpression
        Combination(box e, upcast [| e.Expression |])

    | N.Block ->
        let e = e :?> BlockExpression
        let xs = seq {
            yield! paramExprsToExprs e.Variables
            yield! e.Expressions
            yield e.Result
        }
        Combination(box e, xs)

    | N.Dynamic ->
        let e = e :?> DynamicExpression
        Combination(box e, upcast e.Arguments)

    | N.Goto ->
        let e = e :?> GotoExpression
        Combination(box e, objToSeq e.Value)

    | N.Index ->
        let e = e :?> IndexExpression
        Combination(box e, staticOrInstance e.Object e.Arguments)

    | N.Label ->
        let e = e :?> LabelExpression
        Combination(box e, objToSeq e.DefaultValue)

    | N.RuntimeVariables ->
        let e = e :?> RuntimeVariablesExpression
        Combination(box e, paramExprsToExprs e.Variables)

    | N.Loop ->
        let e = e :?> LoopExpression
        Combination(box e, upcast [|e.Body|])

    | N.Switch ->
        let e = e :?> SwitchExpression
        let xs = seq {
            yield e.SwitchValue 
            for c in e.Cases do
                yield! c.TestValues
                yield c.Body
            yield! objToSeq e.DefaultBody
        }
        Combination(box e, xs)

    | N.Try ->
        let e = e :?> TryExpression
        let xs = seq {
            yield e.Body
            yield! objToSeq e.Fault
            for c in e.Handlers do
                yield upcast c.Variable
                yield c.Filter
                yield c.Body
            yield! objToSeq e.Finally
        }
        Combination(box e, xs)

    | _ -> failwith ""

let rec tryPickL (|Pick|_|) = function
    | Pick x -> Some x
    | Combination(_, xs) -> Seq.tryPick (tryPickL (|Pick|_|)) xs
    | Lambda l -> Seq.tryPick (tryPickL (|Pick|_|)) l.Parameters
    | Parameter _ -> None


let getMethodL (e: Expression) =
    tryPickL (function
        | :? MethodCallExpression as e -> Some(e.Method :> System.Reflection.MethodBase)
        | :? NewExpression as e -> Some(e.Constructor :> _)
        | _ -> None
    ) e

getMethodL (E.Call(typeof<string>.GetMethod("Copy"), E.Constant("abc")))