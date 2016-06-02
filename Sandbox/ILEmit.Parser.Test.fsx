#load "ILEmit.Helpers.fsx"
open RegexLexer
open ILEmit
open ILEmit.Parser
open ILEmit.Helpers
open ILEmit.Helpers.SimpleInstructions
open ILEmit.PreDefinedTypes

let findOp name = Array.find (fst >> (=) name) opTable |> snd

lex "-3" = Ok [| LInt32(false, -3) |]
lex "0xFFFFFFFF" = Ok [| LInt32(true, 0xFFFFFFFF) |]
lex "0x100000000" = Ok [| LInt64(true, 0x100000000L) |]
lex "0xFFFFFFFFFFFFFFFF" = Ok [| LInt64(true, 0xFFFFFFFFFFFFFFFFL) |]
lex "0x10000000000000000"
lex "1.2e12" = Ok [| LFloat64 1.2e12 |]
lex "10e" = Ok [| LInt32(false, 10); Id "e" |]

lex "- 3" = Error 0

lex "type" = Ok [| token.Type |]
lex "typeof" = Ok [| Id "typeof" |]
lex "ldc" = Ok [| Id "ldc" |]
lex "ldc.i4" = Ok [| findOp "ldc.i4" |]
lex "ldc.i4.0" = Ok [| findOp "ldc.i4.0" |]
lex "''" = Ok [| SQString "" |]
lex "'\\t\\'\\u0061'" = Ok [| SQString "\t'a" |]

lex ";" = Ok [| Semicolon |]
lex ";;" = Ok [| DSemicolon |]
lex "," = Ok [|Comma|]
lex "()" = Ok[|LParen; RParen|]

lex "C`1" = Ok [| Id "C`1" |]
lex " `1" = Error 1

let tuple2T = type2 <| FullName("Tuple`2", [], ["System"], Some "mscorlib")
    
let (!) = TypeVar
let (!!) = MethodTypeVar
let (!+) = TypeArgRef
let (!++) = MethodTypeArgRef
fsi.AddPrinter <| fun (x: System.Reflection.Emit.OpCode) -> x.Name


let toIlasm name source =
    match parse source with
    | Error e -> failwithf "%A" e
    | Ok il ->
        let name =
            match name with 
            | null
            | "" -> sprintf "anon%s" <| System.DateTime.Now.ToString "yyyyMMdd_hhmmss_FFFFFFF"
            | n -> n

        let source, _ = emitDll name il in source

let il ds = { topDefs = ds }

parse "type C`0 =" = Ok (il [type0D "C`0" None [] []])
parse "type Make`1(T1) = fun Tuple(T2)(!T1, !!T2) : void = ret" =
    Ok (il [
            typeD "Make`1" ["T1"] None [] [
                methodD "Tuple" ["T2"] [paramT !"T1"; paramT !!"T2"] voidT [ret]
            ]
        ]
    )

parse "
type Make`1(T1) =
    fun Tuple(T2)(item1: !T1, item2: !!T2) : void =
        ldarg.0
        ldarg.1
        newobj [mscorlib]System.Tuple`2(!T1,!!T2)(!0,!1)
        ret
" =
    Ok (il [
            typeD "Make`1" ["T1"] None [] [
                methodD "Tuple" ["T2"] [param "item1" !"T1"; param "item2" !!"T2"] voidT [
                    ldarg 0
                    ldarg 1
                    newobj (tuple2T !"T1" !!"T2") [!+0; !+1]
                    ret
                ]
            ]
        ])

parse "type T1 =;; type T2 =" = Ok(il [typeD "T1" [] None [] []; typeD "T2" [] None [] []])

toIlasm "test1" """
type T1 =;;
type T2 =
""" = ".assembly extern mscorlib
{
  .publickeytoken = (B7 7A 5C 56 19 34 E0 89 )
  .ver 4:0:0:0
}
.assembly test1
{
  .hash algorithm 0x00008004
  .ver 0:0:0:0
}
.module test1.dll
.imagebase 0x00400000
.file alignment 0x00000200
.stackreserve 0x00100000
.subsystem 0x0003
.corflags 0x00000001
.class public auto ansi sealed beforefieldinit T1
       extends [mscorlib]System.Object
{
  .method public specialname rtspecialname 
          instance void  .ctor() cil managed
  {
    .maxstack  2
    IL_0000:  ldarg.0
    IL_0001:  call       instance void [mscorlib]System.Object::.ctor()
    IL_0006:  ret
  }
}
.class public auto ansi sealed beforefieldinit T2
       extends [mscorlib]System.Object
{
  .method public specialname rtspecialname 
          instance void  .ctor() cil managed
  {
    .maxstack  2
    IL_0000:  ldarg.0
    IL_0001:  call       instance void [mscorlib]System.Object::.ctor()
    IL_0006:  ret
  }
}"


toIlasm "" """
type Make`1(T1) =
    fun static Tuple (T2) (!T1, !!T2) : [mscorlib]System.Tuple`2(!T1,!!T2) = ldnull ret;;

module Program =
    fun main(): void =
        ldnull
        ldnull
        call Make`1(string)::Tuple(string)(!0, !!0)
        pop
        ret
"""

toIlasm "MakeTuple2" """
type Make`1(T1) =
    fun static Tuple (T2) (!T1, !!T2) : [mscorlib]System.Tuple`2(!T1,!!T2) =
        ldarg.0
        ldarg.1
        newobj [mscorlib]System.Tuple`2(!T1,!!T2)(!0, !1)
        ret;;

module Program =
    fun main(): [mscorlib]System.Tuple`2(int32, string) =
        ldc.i4.1
        ldstr "2"
        call Make`1(int32)::Tuple(string)(!0, !!0)
        ret
"""

toIlasm "" "
module Ops =
    fun Add (int32, int32) : int32 = ldarg.0 ldarg.1 add ret;
    fun Add (float32, float32) : float32 = ldarg.0 ldarg.1 add ret;;

module Main =
    fun main(): float32 =
        ldc.i4.1
        ldc.i4.3
        call Ops::Add(int32, int32)
        conv.r4
        ldc.r4 7.11
        call Ops::Add(float32, float32)
        ret
"
parseWith instr "ldc.r4"
O.Ldc_R4
let asm = @"C:\Users\pc-2\AppData\Local\Temp\MakeTuple2.dll"

toIlasm "test1" """
type Make`1(T1) =
    fun Tuple (T2) (!T1, !!T2) : [mscorlib]System.Tuple`2(!T1,!!T2) = 
        ldarg.0
        ldarg.1
        newobj [mscorlib]System.Tuple`2(!T1,!!T2)(!0, !1)
        ret;

    fun Tuple (string, string) : [mscorlib]System.Tuple`2(string, string) =
        ldarg.0
        ldarg.1
        newobj [mscorlib]System.Tuple`2(string, string)(!0, !1)
        ret;;

module Prodram =
    fun main(): void =
        ldnull
        ldnull
        ldnull
        ldnull
        call Make`1(string)::Tuple(string)(!0, !!0)
        call Make`1(string)::Tuple()(string, string)
        pop
        pop
        ret
"""