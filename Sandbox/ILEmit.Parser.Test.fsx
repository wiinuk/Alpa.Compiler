#load "ILEmit.Helpers.fsx"
open RegexLexer
open ILEmit
open ILEmit.Parser
open ILEmit.Helpers
open ILEmit.Helpers.SimpleInstructions
open ILEmit.Emit
open ILEmit.Emit.PreDefinedTypes

module Result =
    let map mapping = function
        | Ok x -> Ok <| mapping x
        | Error x -> Error x

let findOp name = Array.find (fst >> (=) name) opTable |> snd

let lex = lex >> Result.map (Array.map Source.value)

let tuple2T = type2 <| FullName("Tuple`2", [], ["System"], Some "mscorlib")
    
let (!) = TypeVar
let (!!) = MethodTypeVar
let (!+) = TypeArgRef
let (!++) = MethodTypeArgRef
fsi.AddPrinter <| fun (x: System.Reflection.Emit.OpCode) -> x.Name


let ildasm name source =
    match parse source with
    | Error e -> failwithf "%A" e
    | Ok il ->
        let name =
            match name with 
            | null
            | "" -> sprintf "anon%s" <| System.DateTime.Now.ToString "yyyyMMdd_hhmmss_FFFFFFF"
            | n -> n
        emitDll name il

let il ds = { topDefs = ds }

lex "-3" = Ok [| LInt32(false, -3) |]
lex "0xFFFFFFFF" = Ok [| LInt32(true, 0xFFFFFFFF) |]
lex "0x100000000" = Ok [| LInt64(true, 0x100000000L) |]
lex "0xFFFFFFFFFFFFFFFF" = Ok [| LInt64(true, 0xFFFFFFFFFFFFFFFFL) |]
lex "0x10000000000000000"= Error(0, Some IntegerOverflow, None)
lex "1.2e12" = Ok [| LFloat64 1.2e12 |]
lex "10e" = Ok [| LInt32(false, 10); Id "e" |]

lex "- 3" = Error(0, None, None)

lex "type" = Ok [| TokenKind.Type |]
lex "typeof" = Ok [| Id "typeof" |]
lex "ldc" = Ok [| Id "ldc" |]
lex "ldc.i4" = Ok [| findOp "ldc.i4" |]
lex "ldc.i4.0" = Ok [| findOp "ldc.i4.0" |]
lex "''" = Ok [| SQString "" |]
lex "'\\t\\'\\u0061'" = Ok [| SQString "\t'a" |]

lex ";" = Ok [| Semicolon |]
lex ";;" = Ok [| DSemicolon |]
// TODO: ???
lex ";;;" = Ok [| DSemicolon; Semicolon |]
lex "," = Ok [|Comma|]
lex "()" = Ok[|LParen; RParen|]

lex "C`1" = Ok [| Id "C`1" |]
lex " `1" = Error(1, None, None)

parse "type C`0 =" = Ok (il [type0D [] "C`0" None [] []])
parse "type Make`1(T1) = fun Tuple(T2)(!T1, !!T2) : void = ret" =
    Ok (il [
            typeD [] "Make`1" ["T1"] None [] [
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
            typeD [] "Make`1" ["T1"] None [] [
                methodD "Tuple" ["T2"] [param "item1" !"T1"; param "item2" !!"T2"] voidT [
                    ldarg 0
                    ldarg 1
                    newobj (tuple2T !"T1" !!"T2") [!+0; !+1]
                    ret
                ]
            ]
        ])

parse "type T1 =;; type T2 =" = Ok(il [typeD [] "T1" [] None [] []; typeD [] "T2" [] None [] []])

begin
    let source = "type T1 =;; type T2 ="
    let expected = ".assembly extern mscorlib
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
    ildasm "test1" source = expected
end

begin
    let source = "
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
    let expected = ".assembly extern mscorlib
{
  .publickeytoken = (B7 7A 5C 56 19 34 E0 89 )
  .ver 4:0:0:0
}
.assembly AddOps
{
  .hash algorithm 0x00008004
  .ver 0:0:0:0
}
.module AddOps.dll
.imagebase 0x00400000
.file alignment 0x00000200
.stackreserve 0x00100000
.subsystem 0x0003
.corflags 0x00000001
.class public abstract auto ansi sealed Ops
       extends [mscorlib]System.Object
{
  .method public static int32  Add(int32 A_0,
                                   int32 A_1) cil managed
  {
    .maxstack  2
    IL_0000:  ldarg.0
    IL_0001:  ldarg.1
    IL_0002:  add
    IL_0003:  ret
  }
  .method public static float32  Add(float32 A_0,
                                     float32 A_1) cil managed
  {
    .maxstack  2
    IL_0000:  ldarg.0
    IL_0001:  ldarg.1
    IL_0002:  add
    IL_0003:  ret
  }
}
.class public abstract auto ansi sealed Main
       extends [mscorlib]System.Object
{
  .method public static float32  main() cil managed
  {
    .maxstack  2
    IL_0000:  ldc.i4.1
    IL_0001:  ldc.i4.3
    IL_0002:  call       int32 Ops::Add(int32,
                                        int32)
    IL_0007:  conv.r4
    IL_0008:  ldc.r4     7.1100001
    IL_000d:  call       float32 Ops::Add(float32,
                                          float32)
    IL_0012:  ret
  }
}"
    ildasm "AddOps" source = expected
end

begin
    let source = "
module NestedType =
    type Type1 =
        fun static Method1() : void = ret;
    module Module1 =
        fun Fun1() : void = ret;;
    ;
    module Module2 =
        fun Fun1() : void = ret
    ;;
"
    let expected = ".assembly extern mscorlib
{
  .publickeytoken = (B7 7A 5C 56 19 34 E0 89 )
  .ver 4:0:0:0
}
.assembly NestedType
{
  .hash algorithm 0x00008004
  .ver 0:0:0:0
}
.module NestedType.dll
.imagebase 0x00400000
.file alignment 0x00000200
.stackreserve 0x00100000
.subsystem 0x0003
.corflags 0x00000001
.class public abstract auto ansi sealed NestedType
       extends [mscorlib]System.Object
{
  .class auto ansi sealed nested public beforefieldinit Type1
         extends [mscorlib]System.Object
  {
    .method public static void  Method1() cil managed
    {
      .maxstack  0
      IL_0000:  ret
    }
    .method public specialname rtspecialname 
            instance void  .ctor() cil managed
    {
      .maxstack  2
      IL_0000:  ldarg.0
      IL_0001:  call       instance void [mscorlib]System.Object::.ctor()
      IL_0006:  ret
    }
  }
  .class abstract auto ansi sealed nested public Module1
         extends [mscorlib]System.Object
  {
    .method public static void  Fun1() cil managed
    {
      .maxstack  0
      IL_0000:  ret
    }
  }
  .class abstract auto ansi sealed nested public Module2
         extends [mscorlib]System.Object
  {
    .method public static void  Fun1() cil managed
    {
      .maxstack  0
      IL_0000:  ret
    }
  }
}"
    ildasm "NestedType" source = expected
end

//ildasm "Test" "
//module Prog.Main =
//    fun main(): [mscorlib]System.Tuple`2(int32,int32) =
//        ldc.i4.1
//        ldc.i4.2
//        newobj [mscorlib]System.Tuple`2(int32,int32)(!0, !1)
//        ret
//"
begin
    let source = """
    type MakeTuple2.Make`1(T1) =
        fun static Tuple (T2) (!T1, !!T2) : [mscorlib]System.Tuple`2(!T1,!!T2) =
            ldarg.0
            ldarg.1
            newobj [mscorlib]System.Tuple`2(!T1,!!T2)(!0, !1)
            ret;;

    module MakeTuple2.Main =
        fun main(): [mscorlib]System.Tuple`2(int32, string) =
            ldc.i4.1
            ldstr "2"
            call MakeTuple2.Make`1(int32)::Tuple(string)(!0, !!0)
            ret
    """
    let expected = """.assembly extern mscorlib
{
  .publickeytoken = (B7 7A 5C 56 19 34 E0 89 )
  .ver 4:0:0:0
}
.assembly MakeTuple2
{
  .hash algorithm 0x00008004
  .ver 0:0:0:0
}
.module MakeTuple2.dll
.imagebase 0x00400000
.file alignment 0x00000200
.stackreserve 0x00100000
.subsystem 0x0003
.corflags 0x00000001
.class public auto ansi sealed beforefieldinit MakeTuple2.Make`1<T1>
       extends [mscorlib]System.Object
{
  .method public static class [mscorlib]System.Tuple`2<!T1,!!T2> 
          Tuple<T2>(!T1 A_0,
                    !!T2 A_1) cil managed
  {
    .maxstack  3
    IL_0000:  ldarg.0
    IL_0001:  ldarg.1
    IL_0002:  newobj     instance void class [mscorlib]System.Tuple`2<!T1,!!T2>::.ctor(!0,
                                                                                       !1)
    IL_0007:  ret
  }
  .method public specialname rtspecialname 
          instance void  .ctor() cil managed
  {
    .maxstack  2
    IL_0000:  ldarg.0
    IL_0001:  call       instance void [mscorlib]System.Object::.ctor()
    IL_0006:  ret
  }
}
.class public abstract auto ansi sealed MakeTuple2.Main
       extends [mscorlib]System.Object
{
  .method public static class [mscorlib]System.Tuple`2<int32,string> 
          main() cil managed
  {
    .maxstack  2
    IL_0000:  ldc.i4.1
    IL_0001:  ldstr      "2"
    IL_0006:  call       class [mscorlib]System.Tuple`2<!0,!!0> class MakeTuple2.Make`1<int32>::Tuple<string>(!0,
                                                                                                              !!0)
    IL_000b:  ret
  }
}"""
    ildasm "MakeTuple2" source = expected
end

begin
    let source = "
    module RuntimeTypeGenericArg.Program =
        fun Main (string, string) : [mscorlib]System.Tuple`2(string, string) =
            ldarg.0
            ldarg.1
            newobj [mscorlib]System.Tuple`2(string, string)(!0, !1)
            ret
    "
    let expected = ".assembly extern mscorlib
{
  .publickeytoken = (B7 7A 5C 56 19 34 E0 89 )
  .ver 4:0:0:0
}
.assembly RuntimeTypeGenericArg
{
  .hash algorithm 0x00008004
  .ver 0:0:0:0
}
.module RuntimeTypeGenericArg.dll
.imagebase 0x00400000
.file alignment 0x00000200
.stackreserve 0x00100000
.subsystem 0x0003
.corflags 0x00000001
.class public abstract auto ansi sealed RuntimeTypeGenericArg.Program
       extends [mscorlib]System.Object
{
  .method public static class [mscorlib]System.Tuple`2<string,string> 
          Main(string A_0,
               string A_1) cil managed
  {
    .maxstack  3
    IL_0000:  ldarg.0
    IL_0001:  ldarg.1
    IL_0002:  newobj     instance void class [mscorlib]System.Tuple`2<string,string>::.ctor(!0,
                                                                                            !1)
    IL_0007:  ret
  }
}"
    ildasm "RuntimeTypeGenericArg" source = expected
end

let source = """
type MakeTupleOverload.Make`1(T1) =
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

module MakeTupleOverload.Main =
    fun main(string, string, string, string): [mscorlib]System.Tuple`2([mscorlib]System.Tuple`2(string, string), [mscorlib]System.Tuple`2(string, string)) =
        ldarg.0
        ldarg.1
        call MakeTupleOverload.Make`1(string)::Tuple(string)(!0, !!0)
        ldarg.2
        ldarg.3
        call MakeTupleOverload.Make`1(string)::Tuple()(string, string)
        newobj [mscorlib]System.Tuple`2([mscorlib]System.Tuple`2(string, string), [mscorlib]System.Tuple`2(string, string))(!0, !1)
        ret
"""

let expected = ""
ildasm "MakeTupleOverload" source


// #r @"C:\Users\pc-2\AppData\Local\Temp\AddOps.dll"