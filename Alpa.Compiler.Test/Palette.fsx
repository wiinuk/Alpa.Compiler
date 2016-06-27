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
type Body = {
    il: Instr seq
}

let readInstr env s =
    let op = opMap.[readOpValue s]
    let offset = s.index - 1
    Instr(offset, op, readOperand env s op.OperandType)

let readIL env s = seq { while canRead s do yield readInstr env s }

let read m =
    let env = envOfMethodBase m
    let b = m.GetMethodBody()
    let xs = b.GetILAsByteArray()
    {
        il = readIL env (makeStream xs)
    }

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

let printInstr printOffset (Instr(offset, op, operand)) =
    if printOffset then printf "@IL%04d " offset
    printf "%s "  op.Name
    match operand with
    | OpNone -> printf " "
    | _ -> ()
    printOperand operand

let printBody { il = il } =
    let il = Seq.cache il
    let brs =
        Seq.collect (function
            | Instr(_,_,OpBr x) -> [|x|]
            | Instr(_,_,OpSwitch xs) -> xs
            | _ -> [||]
        ) il
        |> Seq.cache

    for Instr(offset,_,_) as il in il do
        printInstr (Seq.contains offset brs) il
        printfn ""

open FSharp.Quotations
let rec tryPick (|Pick|_|) = function
    | Pick x -> Some x
    | ExprShape.ShapeCombination(_, xs) -> List.tryPick (tryPick (|Pick|_|)) xs
    | ExprShape.ShapeLambda(_, x) -> tryPick (|Pick|_|) x
    | ExprShape.ShapeVar _ -> None

let getMethod e =
    tryPick (function 
        | Patterns.Call(_,m,_) -> m :> MethodBase |> Some
        | Patterns.NewObject(m,_) -> m :> MethodBase |> Some
        | _ -> None
    ) e
    |> Option.get

let print e = getMethod e |> read |> printBody

let x() = [|20n; 30n|]

print <@ x @>