module Alpa.IL.Emit.Test

#if INTERACTIVE
#load "Alpa.IL.Lexer.Test.fsx"
#endif

open Alpa.IL.Lexer.Test
open FsCheck.Xunit
open Xunit
open Xunit.Sdk
open Alpa.RegexLexer
open Alpa.IL.Helpers
open Alpa.IL.Parser
open System.IO
open System

let toILSource nl name source =
    match parse source with
    | Error e -> failwithf "%A" e
    | Ok il ->
        let name =
            match name with 
            | null
            | "" -> sprintf "anon%s" <| System.DateTime.Now.ToString "yyyyMMdd_hhmmss_FFFFFFF"
            | n -> n
        emitDll nl name il
        
let (==?) act exp = assertEq act exp

let assertOfFile name =
    let source = File.ReadAllText(name + ".ail")
    let expected = File.ReadAllText(name + ".il")
    toILSource "\r\n" name source ==? expected

[<Fact>]
let SimpleType() = assertOfFile "SimpleType"
[<Fact>]
let OverloadOps() = assertOfFile "OverloadOps"
[<Fact>]
let NestedType() = assertOfFile "NestedType"
[<Fact>]
let MakeTuple2() = assertOfFile "MakeTuple2"
[<Fact>]
let RuntimeTypeGenericArg() = assertOfFile "RuntimeTypeGenericArg"

begin
    let source = """
    type MakeTupleOverload.Make`1(`T1) =
        let Tuple (``T2) (`T1, ``T2) : [mscorlib]System.Tuple`2(`T1,``T2) = 
            ldarg.0
            ldarg.1
            newobj [mscorlib]System.Tuple`2(`T1,``T2)(`0,`1)
            ret;

        let Tuple (string, string) : [mscorlib]System.Tuple`2(string, string) =
            ldarg.0
            ldarg.1
            newobj [mscorlib]System.Tuple`2(string, string)(`0,`1)
            ret;;

    module MakeTupleOverload.Main =
        let main(string, string, string, string): [mscorlib]System.Tuple`2([mscorlib]System.Tuple`2(string, string), [mscorlib]System.Tuple`2(string, string)) =
            ldarg.0
            ldarg.1
            call MakeTupleOverload.Make`1(string)::Tuple(string)(`0, ``0)
            ldarg.2
            ldarg.3
            call MakeTupleOverload.Make`1(string)::Tuple()(string, string)
            newobj [mscorlib]System.Tuple`2([mscorlib]System.Tuple`2(string, string), [mscorlib]System.Tuple`2(string, string))(`0, `1)
            ret
    """
    let expected = ".assembly extern mscorlib
{
  .publickeytoken = (B7 7A 5C 56 19 34 E0 89 )
  .ver 4:0:0:0
}
.assembly MakeTupleOverload
{
  .hash algorithm 0x00008004
  .ver 0:0:0:0
}
.module MakeTupleOverload.dll
.imagebase 0x00400000
.file alignment 0x00000200
.stackreserve 0x00100000
.subsystem 0x0003
.corflags 0x00000001
.class public auto ansi sealed beforefieldinit MakeTupleOverload.Make`1<T1>
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
  .method public static class [mscorlib]System.Tuple`2<string,string> 
          Tuple(string A_0,
                string A_1) cil managed
  {
    .maxstack  3
    IL_0000:  ldarg.0
    IL_0001:  ldarg.1
    IL_0002:  newobj     instance void class [mscorlib]System.Tuple`2<string,string>::.ctor(!0,
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
.class public abstract auto ansi sealed MakeTupleOverload.Main
       extends [mscorlib]System.Object
{
  .method public static class [mscorlib]System.Tuple`2<class [mscorlib]System.Tuple`2<string,string>,class [mscorlib]System.Tuple`2<string,string>> 
          main(string A_0,
               string A_1,
               string A_2,
               string A_3) cil managed
  {
    .maxstack  3
    IL_0000:  ldarg.0
    IL_0001:  ldarg.1
    IL_0002:  call       class [mscorlib]System.Tuple`2<!0,!!0> class MakeTupleOverload.Make`1<string>::Tuple<string>(!0,
                                                                                                                      !!0)
    IL_0007:  ldarg.2
    IL_0008:  ldarg.3
    IL_0009:  call       class [mscorlib]System.Tuple`2<string,string> class MakeTupleOverload.Make`1<string>::Tuple(string,
                                                                                                                     string)
    IL_000e:  newobj     instance void class [mscorlib]System.Tuple`2<class [mscorlib]System.Tuple`2<string,string>,class [mscorlib]System.Tuple`2<string,string>>::.ctor(!0,
                                                                                                                                                                          !1)
    IL_0013:  ret
  }
}"
    toILSource "\n" "MakeTupleOverload" source = expected
end
//
//begin
//    let source = "
//    type Fields =
//        member I1 : int32;
//        member mutable IM1 : int32;
//        let S1 : int32;
//        let mutable SM1 : int32;
//
//        let C1 = true;
//        let C2 = 'a';
//        let C3 = \"test\";
//        let C4 = null;
//        let C5 : object = null;
//
//        let Int32C1 = 11;
//        let Int32C2 = 0xFFFFFFFF;
//        let Int32C3 = int32 11;
//    
//        let Int64C1 = 0x100000000;
//        let Int64C2 = int64 11;
//
//        let Int8C1 = int8 11;
//
//        let Float64C1 = 11.0;
//        let Float64C2 = float64 11.0;
//
//        let Float32C2 = float32 11.0;
//    
//        let EnumC1 : [mscorlib]System.ConsoleColor = 0
//    "
//    let expected = ".assembly extern mscorlib
//{
//  .publickeytoken = (B7 7A 5C 56 19 34 E0 89 )
//  .ver 4:0:0:0
//}
//.assembly Field
//{
//  .hash algorithm 0x00008004
//  .ver 0:0:0:0
//}
//.module Field.dll
//.imagebase 0x00400000
//.file alignment 0x00000200
//.stackreserve 0x00100000
//.subsystem 0x0003
//.corflags 0x00000001
//.class public auto ansi sealed beforefieldinit Fields
//       extends [mscorlib]System.Object
//{
//  .field public initonly int32 I1
//  .field public int32 IM1
//  .field public static initonly int32 S1
//  .field public static int32 SM1
//  .field public static literal bool C1 = bool(true)
//  .field public static literal char C2 = char(0x0061)
//  .field public static literal string C3 = \"test\"
//  .field public static literal object C4 = nullref
//  .field public static literal object C5 = nullref
//  .field public static literal int32 Int32C1 = int32(0x0000000B)
//  .field public static literal int32 Int32C2 = int32(0xFFFFFFFF)
//  .field public static literal int32 Int32C3 = int32(0x0000000B)
//  .field public static literal int64 Int64C1 = int64(0x100000000)
//  .field public static literal int64 Int64C2 = int64(0xB)
//  .field public static literal int8 Int8C1 = int8(0x0B)
//  .field public static literal float64 Float64C1 = float64(11.)
//  .field public static literal float64 Float64C2 = float64(11.)
//  .field public static literal float32 Float32C2 = float32(11.)
//  .field public static literal valuetype [mscorlib]System.ConsoleColor EnumC1 = int32(0x00000000)
//  .method public specialname rtspecialname 
//          instance void  .ctor() cil managed
//  {
//    .maxstack  2
//    IL_0000:  ldarg.0
//    IL_0001:  call       instance void [mscorlib]System.Object::.ctor()
//    IL_0006:  ret
//  }
//}"
//    ildasm "Field" source = expected
//end
//
//begin
//    let source = "
//    type EqualsInt <: [mscorlib]System.IEquatable`1(int32) =
//        override Equals(int32): bool = ldc.i4.1 ret
//    "
//    let expected = ".assembly extern mscorlib
//{
//  .publickeytoken = (B7 7A 5C 56 19 34 E0 89 )
//  .ver 4:0:0:0
//}
//.assembly EqualsInt
//{
//  .hash algorithm 0x00008004
//  .ver 0:0:0:0
//}
//.module EqualsInt.dll
//.imagebase 0x00400000
//.file alignment 0x00000200
//.stackreserve 0x00100000
//.subsystem 0x0003
//.corflags 0x00000001
//.class public auto ansi sealed beforefieldinit EqualsInt
//       extends [mscorlib]System.Object
//       implements class [mscorlib]System.IEquatable`1<int32>
//{
//  .method public hidebysig newslot virtual final 
//          instance bool  Equals(int32 A_1) cil managed
//  {
//    .maxstack  1
//    IL_0000:  ldc.i4.1
//    IL_0001:  ret
//  }
//  .method public specialname rtspecialname 
//          instance void  .ctor() cil managed
//  {
//    .maxstack  2
//    IL_0000:  ldarg.0
//    IL_0001:  call       instance void [mscorlib]System.Object::.ctor()
//    IL_0006:  ret
//  }
//}"
//    ildasm "EqualsInt" source = expected
//end