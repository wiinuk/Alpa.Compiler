open System.Reflection
open System.Reflection.Emit
open System.Collections.Generic
open System

type Stream = {
    mutable index: int
    items: byte array
}
let makeStream xs = { index = 0; items = Seq.toArray xs }
let canRead s = s.index < s.items.Length
let readU1 s = let x = s.index in s.index <- x + 1; s.items.[x]
let readI1 s = readU1 s |> int8
let readI2 s = int16 (readU1 s) ||| (int16 (readU1 s) <<< 8)
let readI4 s =
    let read s n = int (readU1 s) <<< n
    read s 0 ||| read s 8 ||| read s 16 ||| read s 24

let readI8 s = int64 (readI4 s) ||| (int64 (readI4 s) <<< 32)

let readF8 s = readI8 s |> BitConverter.Int64BitsToDouble
let readF4 s = BitConverter.ToSingle(readI4 s |> BitConverter.GetBytes, 0)

type MEnv = {
    Module: Module
    BaseModule: Module
    TypeArgs: Type array
    MethodTypeArgs: Type array
}
let envOfMethodBase (m: MethodBase) =
    let t = m.DeclaringType
    {
        Module = m.Module
        BaseModule = t.BaseType.Module
        TypeArgs = if t.IsGenericType then t.GetGenericArguments() else null
        MethodTypeArgs = if m.IsGenericMethod then m.GetGenericArguments() else null
    }

let opMap =
    typeof<OpCodes>.GetFields()
    |> Seq.map (fun f -> f.GetValue null)
    |> Seq.choose (function :? OpCode as x -> Some x | _ -> None)
    |> Seq.map (fun x -> x.Value, x)
    |> dict
    |> Dictionary

let readOpValue s =
    match readU1 s with
    | 0xFEuy -> (int16 (readU1 s) <<< 8) ||| 0xFEs
    | v -> int16 v

type O = System.Reflection.Emit.OperandType
type Operand =
    | OpNone
    | OpI1 of int8
    | OpI2 of int16
    | OpI4 of int32
    | OpI8 of int64
    | OpU1 of uint8
    | OpF8 of double
    | OpF4 of single
    | OpBr of int32
    | OpVar of int32
    | OpSwitch of int array
    | OpString of string
    | OpField of FieldInfo
    | OpMethod of MethodBase
    | OpType of Type
    | OpMember of MemberInfo
    | OpSig of byte array

let readOperand env s = function
    | O.InlineBrTarget -> OpBr <| readI4 s + s.index
    | O.InlineField -> OpField <| env.Module.ResolveField(readI4 s, env.TypeArgs, env.MethodTypeArgs)
    | O.InlineI -> OpI4 <| readI4 s
    | O.InlineI8 -> OpI8 <| readI8 s
    | O.InlineMethod ->
        let md = readI4 s
        try env.Module.ResolveMethod(md, env.TypeArgs, env.MethodTypeArgs)
        with _ -> env.BaseModule.ResolveMethod(md, env.TypeArgs, env.MethodTypeArgs)
        |> OpMethod

    | O.InlineNone -> OpNone
    | O.InlineR -> OpF8 <| readF8 s
    | O.InlineSig -> OpSig <| env.Module.ResolveSignature(readI4 s)
    | O.InlineString -> OpString <| env.Module.ResolveString(readI4 s)
    | O.InlineSwitch ->
        let count = readI4 s
        let offset = s.index + count * 4
        OpSwitch <| Array.init count (fun _ -> offset + readI4 s)

    | O.InlineTok -> OpMember <| env.Module.ResolveMember(readI4 s, env.TypeArgs, env.MethodTypeArgs)
    | O.InlineType -> OpType <| env.Module.ResolveType(readI4 s, env.TypeArgs, env.MethodTypeArgs)
    | O.InlineVar -> OpVar <| int32 (readI2 s)
    | O.ShortInlineBrTarget -> OpBr <| int (readI1 s) + s.index
    | O.ShortInlineI -> OpI1 <| readI1 s
    | O.ShortInlineR -> OpF4 <| readF4 s
    | O.ShortInlineVar -> OpVar <| int32 (readU1 s)
    | _ -> failwith ""

type Instr = Instr of offset: int * OpCode * Operand

let readInstr env s =
    let op = opMap.[readOpValue s]
    let offset = s.index - 1
    Instr(offset, op, readOperand env s op.OperandType)

let readIL env s = seq { while canRead s do yield readInstr env s }

let read m =
    let env = envOfMethodBase m
    let b = m.GetMethodBody()
    let xs = b.GetILAsByteArray()
    readIL env (makeStream xs)

let rec printType (x: Type) =
    printf "%s" x.Name
    if x.IsGenericType then
        printf "("
        match x.GetGenericArguments() |> Array.toList with
        | [] -> ()
        | t::ts ->
            printType t
            for t in ts do
                printf ", "
                printType t
        printf ")"

let printMethod (m: MethodBase) =
    printType m.DeclaringType
    printf "::"
    printf "%s(" m.Name
    if m.IsGenericMethod then
        match m.GetGenericArguments() |> Array.toList with
        | [] -> ()
        | t::ts ->
            printType t
            for t in ts do
                printf ", "
                printType t

        printf ")("
    else ()

    match m.GetParameters() |> Array.toList with
    | [] -> ()
    | p::ps ->
        printType p.ParameterType
        for p in ps do
            printf ", "
            printType p.ParameterType
    printf ") : "

    let ret =
        match m with
        | :? MethodInfo as x -> x.ReturnType
        | _ -> typeof<Void>
    printType ret

let printString x =
    printf "\""
    for x in x do
        match x with
        | '"' -> printf "\\\""
        | _ when Char.IsLetterOrDigit x -> printf "%c" x
        | _ -> printf "\\u%04x" <| int16 x

    printf "\""

let printField (x: FieldInfo) =
    printType x.DeclaringType
    printf "::%s : " x.Name
    printType x.FieldType

let printOperand = function
    | OpNone -> ()
    | OpI1 x -> printf "%dy" x
    | OpI2 x -> printf "%ds" x
    | OpI4 x -> printf "%d" x
    | OpI8 x -> printf "%dL" x
    | OpU1 x -> printf "%duy" x

    | OpF4 x -> printf "%ff" x
    | OpF8 x -> printf "%f" x

    | OpSwitch xs ->
        printf "("
        match Array.toList xs with
        | [] -> ()
        | b::bs ->
            printf "@IL%d" b
            for b in bs do
                printf ", "
                printf "@IL%d" b
        printf ")"

    | OpString x -> printString x
    | OpField x -> printField x
    | OpMethod x -> printMethod x
    | OpMember x ->
        match x with
        | :? FieldInfo as x -> printField x
        | :? MethodBase as x -> printMethod x
        | :? Type as x -> printType x
        | _ -> failwith ""

    | OpType x -> printType x

    | OpSig x -> printf "signature (%A)" x
    | OpBr x -> printf "@IL%04d" x
    | OpVar x -> printf "%d" x

let printInstr (Instr(offset, op, operand)) =
    printf "@IL%04d %s " offset op.Name
    printOperand operand

let (@) l r = Array.append l r

let x =
    let t = typeof<ResizeArray<int>>
    let typeArgs = t.GetGenericArguments()
    t.Module.ResolveField(0x0A0005E0, typeArgs, [||])

// ldarg.0
"\x02"B @
// ldfld 
"\x7B"B @
// 0x0A0005E0
"\xE0\x05\x00\x0A"B @
"\x02\x7B\xDF\x05\x00\x0A\x8E\x69\x33\x0E\x02\x02\x7B\xE0\x05\x00\x0A\x17\x58\x28\xE5\x05\x00\x0A\x02\x7B\xDF\x05\x00\x0A\x02\x02\x7B\xE0\x05\x00\x0A\x0A\x06\x17\x58\x7D\xE0\x05\x00\x0A\x06\x03\xA4\xCB\x00\x00\x1B\x02\x02\x7B\xE2\x05\x00\x0A\x17\x58\x7D\xE2\x05\x00\x0A\x2A"B

printfn "%08X" 167773664
System.BitConverter.ToInt32("\xE0\x05\x00\x0A"B, 0)
opMap.[0x7Bs]

let m = typeof<ResizeArray<int>>.GetMethod("Add")
let b = m.GetMethodBody()
let bs = b.GetILAsByteArray()

let bs' =
    [|2uy; 123uy; 224uy; 5uy; 0uy; 10uy; 2uy; 123uy; 223uy; 5uy; 0uy; 10uy;
        142uy; 105uy; 51uy; 14uy; 2uy; 2uy; 123uy; 224uy; 5uy; 0uy; 10uy; 23uy;
        88uy; 40uy; 229uy; 5uy; 0uy; 10uy; 2uy; 123uy; 223uy; 5uy; 0uy; 10uy; 2uy;
        2uy; 123uy; 224uy; 5uy; 0uy; 10uy; 10uy; 6uy; 23uy; 88uy; 125uy; 224uy;
        5uy; 0uy; 10uy; 6uy; 3uy; 164uy; 203uy; 0uy; 0uy; 27uy; 2uy; 2uy; 123uy;
        226uy; 5uy; 0uy; 10uy; 23uy; 88uy; 125uy; 226uy; 5uy; 0uy; 10uy; 42uy|]
    // "\x02\x7B\xE0\x05\x00\x0A\x02\x7B\xDF\x05\x00\x0A\x8E\x69\x33\x0E\x02\x02\x7B\xE0\x05\x00\x0A\x17\x58\x28\xE5\x05\x00\x0A\x02\x7B\xDF\x05\x00\x0A\x02\x02\x7B\xE0\x05\x00\x0A\x0A\x06\x17\x58\x7D\xE0\x05\x00\x0A\x06\x03\xA4\xCB\x00\x00\x1B\x02\x02\x7B\xE2\x05\x00\x0A\x17\x58\x7D\xE2\x05\x00\x0A\x2A"B

let showByteArray xs =
    Seq.map (sprintf "\\x%02X") xs
    |> String.concat ""
    |> sprintf "\"%s\"B"

fsi.AddPrinter showByteArray

"\x10"
showByteArray "\005\123\224\005\000\010"B
envOfMethodBase(m)

for i in read m do
    printInstr i
    printfn ""

let ReadInt32 s =
    let val0 = readU1 s
    let val1 = readU1 s
    let val2 = readU1 s
    let val3 = readU1 s
    (int32 val3 <<< 24) ||| (int32 val2 <<< 16) ||| (int32 val1 <<< 8) ||| int32 val0

let xs = [|0x12uy; 0x34uy; 0x56uy; 0x78uy|]
readI4 (makeStream xs) = ReadInt32 (makeStream xs)