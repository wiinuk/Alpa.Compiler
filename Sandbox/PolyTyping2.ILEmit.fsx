module PolyTyping2.ILEmit
#load "PolyTyping2.Typing.fsx"
#r "./bin/debug/Alpa.Compiler.dll"
open Alpa.Emit
open PolyTyping2
open PolyTyping2.Typing
type O = System.Reflection.Emit.OpCodes

let emitI4 = function
    | -1 -> Instr("", O.Ldc_I4_M1, OpNone)
    | 0 -> Instr("", O.Ldc_I4_0, OpNone)
    | 1 -> Instr("", O.Ldc_I4_1, OpNone)
    | 2 -> Instr("", O.Ldc_I4_2, OpNone)
    | 3 -> Instr("", O.Ldc_I4_3, OpNone)
    | 4 -> Instr("", O.Ldc_I4_4, OpNone)
    | 5 -> Instr("", O.Ldc_I4_5, OpNone)
    | 6 -> Instr("", O.Ldc_I4_6, OpNone)
    | 7 -> Instr("", O.Ldc_I4_7, OpNone)
    | 8 -> Instr("", O.Ldc_I4_8, OpNone)
    | n when int System.SByte.MinValue <= n && n <= int System.SByte.MaxValue -> Instr("", O.Ldc_I4_S, OpI1 <| int8 n)
    | n -> Instr("", O.Ldc_I4, OpI4 n)

type LocalEnv = {
    Locals: ResizeArray<Local>
}
let emitDefault env =
    
	IL_0016: ldloca.s 0
	IL_0018: initobj [System.Numerics]System.Numerics.BigInteger
	IL_001e: ldloc.0


let emitBigint (n: bigint) = 
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
let emitLit = function
    | CharLit x -> emitI4 <| int x
    | IntegerLit n -> failwith "Not implemented yet"
    | IntLit(_) -> failwith "Not implemented yet"
    | FloatLit(_) -> failwith "Not implemented yet"
    | StringLit(_) -> failwith "Not implemented yet"

let emit = function
    | Lit l -> emitLit l