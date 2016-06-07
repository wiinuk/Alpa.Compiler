module Alpa.IL.Lexer.Test

#if INTERACTIVE
#load "Alpa.IL.Helpers.fsx"
#endif

open FsCheck.Xunit
open Xunit
open Xunit.Sdk
open Alpa.RegexLexer
open Alpa.IL.Parser

module Result =
    let map mapping = function
        | Ok x -> Ok <| mapping x
        | Error x -> Error x

let lex = lex >> Result.map (Array.map Source.value)

let ops = opKeyword()
let findOp name = Array.find (fst >> (=) name) ops |> snd

let rec tryPick (|Pick|_|) e =
    match e with
    | Pick x -> Some x
    | Quotations.ExprShape.ShapeCombination(_, es) -> List.tryPick (tryPick (|Pick|_|)) es
    | Quotations.ExprShape.ShapeLambda(_, e) -> tryPick (|Pick|_|) e
    | Quotations.ExprShape.ShapeVar _ -> None

let findMethod e =
    tryPick (function Quotations.Patterns.Call(_,m,_) -> Some m | _ -> None) e
    |> Option.get

let assertEq (act: 'a) (exp: 'a) =
    if typeof<'a> = typeof<string> then
        Assert.Equal(unbox<string> exp, unbox<string> act)
    else
        let implSeq =
            typeof<'a>.GetInterfaces()
            |> Seq.tryFind (fun i ->
                i.IsGenericType &&
                i.GetGenericTypeDefinition() = typedefof<_ seq>
            )
        match implSeq with
        | Some i ->
            let t1 = i.GetGenericArguments().[0]
            let equals = findMethod <@@ Assert.Equal<int>([], [], LanguagePrimitives.FastGenericEqualityComparer) @@>
            let equals = equals.GetGenericMethodDefinition().MakeGenericMethod(t1)

            let getFastGEC = findMethod <@@ LanguagePrimitives.FastGenericEqualityComparer @@>
            let getFastGEC = getFastGEC.GetGenericMethodDefinition().MakeGenericMethod(t1)
            let c = getFastGEC.Invoke(null, null)

            try
                equals.Invoke(null, [|exp; act; c|]) |> ignore
            with
            | :? System.Reflection.TargetInvocationException as e -> raise e.InnerException

        | None -> Assert.StrictEqual(exp, act)

let assertTokenEq xs = for t, ts in xs do assertEq (lex t) (Ok ts)
let assertLexEq xs = for t, e in xs do assertEq (lex t) e

[<Fact>]
let lexTest() =
    assertTokenEq [
        "-3", [| LInt32(false, -3) |]
        "0xFFFFFFFF", [| LInt32(true, 0xFFFFFFFF) |]
        "0x100000000", [| LInt64(true, 0x100000000L) |]
        "0xFFFFFFFFFFFFFFFF", [| LInt64(true, 0xFFFFFFFFFFFFFFFFL) |]
        "1.2e12", [| LFloat64 1.2e12 |]
        "10e", [| LInt32(false, 10); Id "e" |]
        "type", [| TokenKind.Type |]
        "typeof", [| Id "typeof" |]
        "ldc", [| Id "ldc" |]
        "ldc.i4", [| findOp "ldc.i4" |]
        "ldc.i4.0", [| findOp "ldc.i4.0" |]
        "''", [| SQString "" |]
        "'\\t\\'\\u0061'", [| SQString "\t'a" |]
        ";", [| Semicolon |]
        ";;", [| DSemicolon |]

        // TODO: ???
        ";;;", [| DSemicolon; Semicolon |]

        ",", [|Comma|]
        "()", [|LParen; RParen|]

        "C`1", [| Id "C`1" |]
    ]
    assertLexEq [
        "0x10000000000000000", Error(0, Some IntegerOverflow, None)
        "- 3", Error(0, None, None)
        " `1", Error(1, None, None)
    ]

