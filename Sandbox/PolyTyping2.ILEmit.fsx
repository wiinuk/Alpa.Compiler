module PolyTyping2.ILEmit
#load "PolyTyping2.Typing.fsx"
#r "./bin/debug/Alpa.Compiler.dll"
open Alpa.Emit
open PolyTyping2
open PolyTyping2.Typing
open Alpa.Emit.TypeSpec

type E = PolyTyping2.Typing.TExp

type CLit =
    | LitI4 of int32
    | LitI8 of int64
    | LitU1 of uint8
    | LitU8 of uint64
    | LitC of char
    | LitF8 of double
    | LitS of string

type Type = TypeSpec
type LocalName = Var
type CExp =
    /// ex: 10i; 'c'; "test"; null[string]
    | Lit of CLit
    /// ex: a
    | LVar of LocalName
    /// ex: a: string in x
    | LetZero of LocalName * Type * CExp
    /// ex: a: string <- "" in x
    | Let of LocalName * Type option * CExp * CExp
    /// ex: a; b
    | Next of CExp * CExp

    /// ex: x.[object::ToString]()
    | VCall of CExp * MethodRef * CExp list
    /// ex: object::ReferenceEquals(x, y);
    ///     string::Equals(string, string)();
    ///     "".Equals(string)(null)
    | Call of MethodRef * CExp list

    /// ex: upcast "" IEquatable`1(string)
    | Upcast of CExp * Type

    /// ex: [1; 2; 3]
    | NewArray of CExp list

    /// ex: &a
    | Ref of CExp
    /// ex: *a
    | Deref of CExp

    /// ex: initobj &a
    | Initobj of CExp
    /// ex: newobj string('a', 10i)
    | Newobj of MethodRef * CExp list

//let emitI4 = function
//    | -1 -> Instr("", O.Ldc_I4_M1, OpNone)
//    | 0 -> Instr("", O.Ldc_I4_0, OpNone)
//    | 1 -> Instr("", O.Ldc_I4_1, OpNone)
//    | 2 -> Instr("", O.Ldc_I4_2, OpNone)
//    | 3 -> Instr("", O.Ldc_I4_3, OpNone)
//    | 4 -> Instr("", O.Ldc_I4_4, OpNone)
//    | 5 -> Instr("", O.Ldc_I4_5, OpNone)
//    | 6 -> Instr("", O.Ldc_I4_6, OpNone)
//    | 7 -> Instr("", O.Ldc_I4_7, OpNone)
//    | 8 -> Instr("", O.Ldc_I4_8, OpNone)
//    | n when int System.SByte.MinValue <= n && n <= int System.SByte.MaxValue -> Instr("", O.Ldc_I4_S, OpI1 <| int8 n)
//    | n -> Instr("", O.Ldc_I4, OpI4 n)

/// a: T in initobj &a; !a
let emitDefault t = LetZero("a", t, Next(Initobj(Ref(LVar "a")), Deref(LVar "a")))


let bigintT = typeOf<bigint>
let rec tryPick (|Pick|_|) = function
    | Pick x -> Some x
    | Quotations.ExprShape.ShapeCombination(_,es) -> List.tryPick (tryPick (|Pick|_|)) es
    | Quotations.ExprShape.ShapeLambda(_,e) -> tryPick (|Pick|_|) e
    | Quotations.ExprShape.ShapeVar _ -> None

let tryFindMethodBase e =
    tryPick (function 
        | Quotations.Patterns.Call(_,m,_) -> Some(m :> System.Reflection.MethodBase)
        | Quotations.Patterns.NewObject(m,_) -> Some(m :> _)
        | _ -> None
    ) e

let methodOf e =
    match tryFindMethodBase e with
    | None -> failwithf "%A" e
    | Some m ->
        let mTypeArgs = if m.IsGenericMethod then [for t in m.GetGenericArguments() -> typeOfT t] else []
        let argTypes = [for p in m.GetParameters() -> typeOfT p.ParameterType]
        let at = MethodTypeAnnotation(mTypeArgs, argTypes, None)
        MethodRef(typeOfT m.DeclaringType, m.Name, Some at)

let inRange l h x = l <= x && x <= h
let int32Min = bigint(System.Int32.MinValue)
let int32Max = bigint(System.Int32.MaxValue)
let int64Min = bigint(System.Int64.MinValue)
let int64Max = bigint(System.Int64.MaxValue)
let uint64Min = bigint(System.UInt64.MinValue)
let uint64Max = bigint(System.UInt64.MaxValue)

let emitBigint (n: bigint) = 
    if n.IsZero then emitDefault bigintT
    elif n.IsOne then Call(methodOf <@ bigint.get_One @>, [])
    elif n = bigint.MinusOne then Call(methodOf <@ bigint.get_MinusOne @>, [])
    elif inRange int32Min int32Max n then
        Newobj(methodOf <@ bigint : int32 -> _ @>, [Lit <| LitI4(int32 n)])

    elif inRange int64Min int64Max n then
        Newobj(methodOf <@ bigint : int64 -> _ @>, [Lit <| LitI8(int64 n)])

    elif inRange uint64Min uint64Max n then
        Newobj(methodOf <@ bigint : uint64 -> _ @>, [Lit <| LitU8(uint64 n)])

    else
        let xs = NewArray [for x in n.ToByteArray() -> Lit(LitU1 x)]
        Newobj(methodOf <@ bigint : byte array -> _ @>, [xs])

let emitLit = function
    | CharLit n -> Lit(LitC n)
    | IntegerLit n -> emitBigint n
    | IntLit n -> Lit(LitI4 n)
    | FloatLit n -> Lit(LitF8 n)
    | StringLit s -> Lit(LitS s)

(*
a = 10;
f a =
    \() -> _ = a; ""
*)

let mutable ident = 0
let fleshId() = ident <- ident + 1; ident
let lambdaT x r = TypeSpec(FullName("Lambda`2", [], [], None), [x; r])
let emit = function
    | E.Lit l -> emitLit l
    | E.Var(v, _) -> LVar v
    | E.Lam(v, vt, b) ->
        // closure = tuple, func
        let lamType tps =
            let name =
                match tps with
                | [] -> sprintf "ALambda@%d" (fleshId())
                | _ -> sprintf "ALambda@%d`%d" (fleshId()) (List.length tps)

            TopTypeDef(
                Some TypeAccess.Private,
                (name, []),
                {
                    kind = None
                    typeParams = tps
                    parent = Some <| lambdaT vt rt
                    impls = []
                    members = [
                        
                    ]
                }
            )

        Newobj()

    | E.App(_, _) -> failwith "Not implemented yet"
    | E.Ext(_, _, _) -> failwith "Not implemented yet"
    | E.Let(_, _, _, _) -> failwith "Not implemented yet"
    | E.LetRec(_, _) -> failwith "Not implemented yet"
    | E.Mat(_, _, _) -> failwith "Not implemented yet"
    | E.TypeDef(name, _, _) -> failwith "Not implemented yet"
    | E.InstanceDef(name, typeArgs, methodImpls, cont) -> failwith "Not implemented yet"