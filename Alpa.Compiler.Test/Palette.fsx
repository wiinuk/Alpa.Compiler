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

let readCount read n s =
    let rec aux xs n = if n <= 0 then List.rev xs else aux (read s::xs) (n-1)
    aux [] n


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

//module IMAGE_CEE_CS_CALLCONV =
//    DEFAULT         = 0x00 = 0b00000000
//    C               = 0x01 = 0b00000001
//    STDCALL         = 0x02 = 0b00000010
//    FASTCALL        = 0x04 = 0b00000100
//    PROPERTY        = 0x08 = 0b00001000
//    GENERIC         = 0x10 = 0b00010000
//    HASTHIS         = 0x20 = 0b00100000
//    EXPLICITTHIS    = 0x40 = 0b01000000
//    THISCALL        = 0x03 = 0b00000011
//    VARARG          = 0x05 = 0b00000101
//    FIELD           = 0x06 = 0b00000110
//    LOCAL_SIG       = 0x07 = 0b00000111
//    GENERICINST     = 0x0A = 0b00001010
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
//    SENTINEL    = 0x41
//    PINNED      = 0x45  
//
//open CALLCONV
//open ELEMENT_TYPE
//
//thisKind = HASTHIS EXPLICITTHIS?
//
//number =
//    bit = 0b | 1b
//    | 0b bit{7}           (0x00..0x7F)
//    | 1b 0b bit{14}       (0x0080..0x3FFF)
//    | 1b 1b 0b bit{29}    (0x00040000..0x1FFFFFFF)
//
//arrayShape =
//    rank = number (1..)
//    rank (numSizes: number) (size: number)* (numLoBounds: number) (loBound: number)*
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
//    | SZARRAY customMod* type // szarray
//    | VALUETYPE typeDefOrRefEncoded
//    | VAR number
//
//customMod = (CMOD_OPT | CMOD_REQD) typeDefOrRefEncoded
//
//retType = customMod* (BYREF? type | TYPEDBYREF | VOID)
//param = customMod* (BYREF? type | TYPEDBYREF)
//
//methodDefSig =
//    methodDefSigHead =
//        | (thisKind? ||| (DEFAULT | VARARG)) 
//        | (thisKind? ||| GENERIC) (genParamCount: number)
//    methodDefSigHead (paramCount: number) retType param*
//
//methodRefSig =
//    | (thisKind? ||| VARARG) (paramCount: number) retType param* SENTINEL param*
//    | methodDefSig
//
//standAloneMethodSig =
//    standAloneMethodSigAttr =
//        | DEFAULT
//        | C
//        | STDCALL
//        | THISCALL
//        | FASTCALL
//    | (thisKind? ||| standAloneMethodSigAttr) (paramCount: number) retParam param*
//    | (thisKind? ||| VARARG) (paramCount: number) retParam param* (SENTINEL param*)?
//
//fieldSig = FIELD customMod* type
//propertySig = (PROPERTY ||| HASTHIS) (paramCount: number) customMod* type param*
//
//constraint = PINNED
//localVarSig =
//    local = TYPEDBYREF | (customMod | constraint)* BYREF? type
//    LOCAL_SIG (count: number (1..0xFFFE)) local+
//
//typeSpec =
//    | PTR customMod* VOID
//    | PTR customMod* type
//    | FNPTR methodDefSig
//    | FNPTR methodRefSig
//    | ARRAY type arrayShape
//    | SZARRAY customMod* type
//    | GENERICINST (CLASS | VALUETYPE) typeDefOrRefEncoded (genArgCount: number) type type*
//
//methodSpec = IMAGE_CEE_CS_CALLCONV.GENERICINST (genArgCount: number) type type*

[<Flags>]
type SigKind =
    | DEFAULT       = 0x00
    | C             = 0x01
    | STDCALL       = 0x02
    | FASTCALL      = 0x04
    | PROPERTY      = 0x08
    | GENERIC       = 0x10
    | HASTHIS       = 0x20
    | EXPLICITTHIS  = 0x40
    | THISCALL      = 0x03
    | VARARG        = 0x05
    | FIELD         = 0x06
    | LOCAL_SIG     = 0x07
    //| GENERICINST   = 0x0A

type ELEMENT_TYPE =
    | VOID          = 0x01
    | BOOLEAN       = 0x02
    | CHAR          = 0x03
    | I1            = 0x04
    | U1            = 0x05
    | I2            = 0x06
    | U2            = 0x07
    | I4            = 0x08
    | U4            = 0x09
    | I8            = 0x0a
    | U8            = 0x0b
    | R4            = 0x0c
    | R8            = 0x0d
    | STRING        = 0x0e
    | PTR           = 0x0f
    | BYREF         = 0x10
    | VALUETYPE     = 0x11
    | CLASS         = 0x12
    | VAR           = 0x13
    | ARRAY         = 0x14
    | GENERICINST   = 0x15
    /// System.TypedReference
    | TYPEDBYREF    = 0x16
    /// System.IntPtr
    | I             = 0x18
    /// System.UIntPtr
    | U             = 0x19
    | FNPTR         = 0x1b
    /// System.Object
    | OBJECT        = 0x1c
    | SZARRAY       = 0x1d
    | MVAR          = 0x1e
    | CMOD_REQD     = 0x1f
    | CMOD_OPT      = 0x20
    | SENTINEL      = 0x41
    | PINNED        = 0x45  
    
type ArrayShape = ArrayShape of rank: int * sizes: int list * loBounds: int list

type E = ELEMENT_TYPE
type K = SigKind

type Mod = Mod of isOpt: bool * Type
type Param = Param of isByref: bool * Mod list * Type

type ThisKind = ThisNone | HasThis | ExplicitThis
type CallKind = DefaultCall | Vararg | C | Stdcall | Thiscall | Fastcall
type MethodSig = {
    thisKind: ThisKind
    callKind: CallKind
    retType: Param
    genParams: Param list
    methodParams: Param list
    varargParams: Param list
}
type FieldSig = {
    mods: Mod list
    fieldType: Type
}
type PropertySig = {
    hasThis: bool
    mods: Mod list
    propType: Type
    propParams: Param list
}
type Local = {
    mods: Mod list
    isPinned: bool
    isByref: bool
    localType: Type
}
type LocalSig = {
    locals: Local list
}

let hasFlag v f = v &&& f = f

let readNumber s =
    let v1 = int <| readU1 s
    if v1 &&& 0b10000000 = 0 then v1
    elif v1 &&& 0b11000000 = 0b10000000 then
        ((v1 &&& 0b00111111) <<< 8) ||| int (readU1 s)
    else
        let v2 = int <| readU1 s
        let v3 = int <| readU1 s
        let v4 = int <| readU1 s
        ((v1 &&& 0b00011111) <<< 24) ||| (v2 <<< 16) ||| (v3 <<< 8) ||| v4

let test () =
    let test orig comp =
        let decomp = readNumber (makeStream comp)
        if decomp <> orig then failwithf "comp: %A, decomp: %A, orig: %A" comp decomp orig

    test 0x03 "\x03"B
    test 0x7F "\x7F"B
    test 0x80 "\x80\x80"B
    test 0x2E57 "\xAE\x57"B
    test 0x3FFF "\xBF\xFF"B
    test 0x4000 "\xC0\x00\x40\x00"B
    test 0x1FFFFFFF "\xDF\xFF\xFF\xFF"B

    0b11
    0b110

    //test 3 "\x06"B
    //test -3 "\x7B"B
    //test 64 "\x80\x80"B
    //test -64 "\x01"B
    //test 8192 "\xC0\x00\x40\x00"B
    //test -8192 "\x80\x01"B
    //test 268435455 "\xDF\xFF\xFF\xFE"B
    //test -268435456 "\xC0\x00\x00\x01"B

let readArrayShape s =
    ArrayShape(
        readNumber s,
        readCount readNumber (readNumber s) s,
        readCount readNumber (readNumber s) s
    )

let readTypeDefOrRefEncoded env s =
    let n = uint32 <| readNumber s
    resolveType env <| int32 ((n &&& 0b11u <<< 24) ||| (n >>> 2))

let readElementType s = enum(int (readU1 s))
let readSigKind s = enum(int (readU1 s))

let readModTail e env s = Mod((e = E.CMOD_OPT), readTypeDefOrRefEncoded env s)
let readModsTail elementType env s =
    let rec aux ms et s =
        match et with
        | E.CMOD_OPT
        | E.CMOD_REQD -> let m = readModTail et env s in aux (m::ms) (readElementType s) s
        | _ -> List.rev ms, et

    aux [] elementType s


let x = System.Array.CreateInstance(typeof<int>, [|3|], [|1|])
x.GetType() <> typeof<int[]>
x.Get

#load @"C:\Users\pc-2\project\Sandbox\Alpa.Compiler.Test\Alpa.IL.Helpers.fsx"
open Alpa.IL.Helpers

ilasm (System.IO.Path.Combine(__SOURCE_DIRECTORY__, "test.dll")) "

.assembly extern mscorlib {}
.assembly test {}

.class public test.T1
{
    .field public static int32[2...,3...] F1
}
"
#r "./test.dll"
let f = global.test.T1.F1
typeof<global.test.T1>.GetField("F1").FieldType = typeof<int[,]>

type GeneralArrayType(elementType: Type, shape: ArrayShape) =
    inherit Type()
    let o = Array.CreateInstance(elementType, )
//    override __.GetNestedType(_,_) = null
//    override __.GetMembers()

type FnptrType(signature: MethodSig) = inherit Type()
type ModifiedType(m: Mod, ms: Mod list, t: Type) = inherit Type()

let readMods env s = readModsTail (readElementType s) env s
let makeModType ms t =
    match ms with
    | [] -> t
    | m::ms -> ModifiedType(m, ms, t) :> Type
    
let rec readModsAndType env s =
    let ms, et = readMods env s
    let t = readTypeTail et env s
    ms, t

and readType env s = readTypeTail (readElementType s) env s
and readTypeTail elementType ({ TypeArgs = vars; MethodTypeArgs = mvars } as env) s =
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
        | shape -> upcast GeneralArrayType(t, shape)

    | E.CLASS -> readTypeDefOrRefEncoded env s
    | E.FNPTR -> upcast FnptrType(readAnyMethodSig env s)
    | E.GENERICINST ->
        match readElementType s with
        | E.CLASS
        | E.VALUETYPE -> ()
        | _ -> failwith ""

        let openType = readTypeDefOrRefEncoded env s
        let genArgCount = readNumber s
        let typeArgs = readCount (readType env) genArgCount s
        openType.MakeGenericType(List.toArray typeArgs)

    | E.MVAR -> Array.item (readNumber s) vars
    | E.OBJECT -> typeof<obj>
    | E.PTR ->
        let ms, et = readMods env s
        let t = if et = E.VOID then typeof<Void> else readTypeTail et env s
        makeModType ms <| t.MakePointerType()

    | E.STRING -> typeof<string>
    | E.SZARRAY ->
        let ms, t = readModsAndType env s
        makeModType ms <| t.MakeArrayType()

    | E.VALUETYPE -> readTypeDefOrRefEncoded env s
    | E.VAR -> Array.item (readNumber s) vars
    | _ -> failwith ""

and readRetOrParamTail elementType env s =
    let ms, et = readModsTail elementType env s
    match et with
    | E.BYREF -> Param(true, ms, readType env s)
    | E.TYPEDBYREF -> Param(false, ms, typeof<TypedReference>)
    | E.VOID -> Param(false, ms, typeof<Void>)
    | _ -> Param(false, ms, readTypeTail et env s)

and readRetOrParam env s = readRetOrParamTail (readElementType s) env s

and readParamAndVarargParams count env s =
    let rec aux isVararg ps vs count =
        if count <= 0 then List.rev ps, List.rev vs
        else
            match readElementType s with
            | E.SENTINEL -> aux true ps vs count
            | e ->
                let p = readRetOrParamTail e env s
                let ps, vs = if isVararg then ps, (p::vs) else (p::ps), vs
                aux isVararg ps vs (count - 1)

    aux false [] [] count

and readAnyMethodSigTail kind env s =
    let genParamCount = if hasFlag kind K.GENERIC then readNumber s else 0
    let paramCount = readNumber s
    let retType = readRetOrParam env s
    let genParams = readCount (readRetOrParam env) genParamCount s
    let methodParams, varargParams = readParamAndVarargParams paramCount env s
    {
        thisKind =
            if hasFlag kind K.EXPLICITTHIS then ExplicitThis
            elif hasFlag kind K.HASTHIS then HasThis
            else ThisNone

        callKind =
            if hasFlag kind K.C then C
            elif hasFlag kind K.FASTCALL then Fastcall
            elif hasFlag kind K.STDCALL then Stdcall
            elif hasFlag kind K.THISCALL then Thiscall
            elif hasFlag kind K.VARARG then Vararg
            else DefaultCall

        retType = retType
        genParams = genParams
        methodParams = methodParams
        varargParams = varargParams
    }
and readAnyMethodSig env s = readAnyMethodSigTail (readSigKind s) env s

type Operand =
    | InlineI1 of int8
    | InlineI4 of int32
    | InlineI8 of int64
    | InlineR4 of single
    | InlineBrTarget of int32
    | InlineBrTargetI1 of int8
    | InlineField of FieldInfo
    | InlineMethod of MethodBase
    | InlineNone
    | InlineR8 of double
    | InlineSig of MethodSig
    | InlineString of string
    | InlineSwitch of int list
    | InlineToken of MemberInfo
    | InlineType of Type
    | InlineVar of int16
    | InlineVarI1 of int8

let parseSig env xs = readAnyMethodSig env <| makeStream xs

let readOperand ({ TypeArgs = targs; MethodTypeArgs = mtargs } as env) s = function 
    | O.InlineBrTarget -> InlineBrTarget <| readI4 s
    | O.InlineField ->
        let md = readI4 s
        InlineField <| resolve (fun m -> m.ResolveField(md, targs, mtargs)) env

    | O.InlineI -> InlineI4 <| readI4 s
    | O.InlineI8 -> InlineI8 <| readI8 s
    | O.InlineMethod -> 
        let md = readI4 s
        InlineMethod <| resolve (fun m -> m.ResolveMethod(md, targs, mtargs)) env

    | O.InlineNone -> InlineNone
    | O.InlineR -> InlineR8 <| readF8 s
    | O.InlineSig ->
        let md = readI4 s
        resolve (fun m -> m.ResolveSignature md) env
        |> parseSig env
        |> InlineSig

    | O.InlineString ->
        let md = readI4 s
        InlineString <| resolve (fun m -> m.ResolveString md) env

    | O.InlineSwitch -> 
        let count = readI4 s
        InlineSwitch <| List.init count (fun _ -> readI4 s)

    | O.InlineTok -> 
        let tok = readI4 s
        InlineToken <| resolve (fun m -> m.ResolveMember(tok, targs, mtargs)) env

    | O.InlineType -> InlineType <| resolveType env (readI4 s)
    | O.InlineVar -> InlineVar <| readI2 s
    | O.ShortInlineBrTarget -> InlineBrTargetI1 <| readI1 s
    | O.ShortInlineI -> InlineI1 <| readI1 s
    | O.ShortInlineR -> InlineR4 <| readF4 s
    | O.ShortInlineVar -> InlineVarI1 <| readI1 s
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
