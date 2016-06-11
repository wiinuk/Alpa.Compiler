module Alpa.IL.Lexer.Test

#if INTERACTIVE
#load "Alpa.IL.Helpers.fsx"
#endif

open FsCheck.Xunit
open Xunit
open Xunit.Sdk
open Alpa.RegexLexer
open Alpa.IL.Parser
open Alpa.IL.Helpers

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
        ":", [| Colon |]
        "::", [| DColon |]

        // TODO: ???
        ":::", [| DColon; Colon |]

        ",", [|Comma|]
        "()", [|LParen; RParen|]

        "C`1", [| Id "C`1" |]
    ]
    assertLexEq [
        "0x10000000000000000", Error(0, Some IntegerOverflow, None)
        "- 3", Error(0, None, None)
    ]

