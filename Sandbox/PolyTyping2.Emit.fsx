module PolyTyping2_Emit
#load "PolyTyping2.fsx"

open PolyTyping2
open System.Reflection
open System.Reflection.Emit
type O = global.System.Reflection.Emit.OpCodes

let emitInt (g: ILGenerator) = function
    | n when -1 <= n && n <= 8 ->
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
        |> g.Emit

    | n when -128 <= n && n <= 127 -> g.Emit(O.Ldc_I4_S, sbyte n)
    | n -> g.Emit(O.Ldc_I4, n)

let emitChar g v =
    emitInt g <| int<char> v
    g.Emit O.Conv_U2

let emitLit g = function
    | CharLit c -> emitChar g c
    | IntegerLit n ->
        if n.IsZero then emitFieldGet None typeof<bigint> "Zero"
        elif n.IsOne then emitFieldGet Nond typeof<bigint> "One"
        elif n = bigint.MinusOne then emitFieldGet None typeof<bigint> "MinusOne"
        elif n 
        emitNew
    | IntLit(_) -> failwith "Not implemented yet"
    | FloatLit(_) -> failwith "Not implemented yet"
    | StringLit(_) -> failwith "Not implemented yet"
    

let rec emit = function
    | Lit _ -> ()
    | Var(_) -> failwith "Not implemented yet"
    | Lam(_, _) -> failwith "Not implemented yet"
    | App(_, _) -> failwith "Not implemented yet"
    | Ext(_, _, _) -> failwith "Not implemented yet"
    | Let(_, _, _) -> failwith "Not implemented yet"
    | LetRec(_, _) -> failwith "Not implemented yet"
    | Mat(_, _, _) -> failwith "Not implemented yet"
    | TypeDef(name, _, _) -> failwith "Not implemented yet"
    | InstanceDef(name, typeArgs, methodImpls, cont) -> failwith "Not implemented yet"
