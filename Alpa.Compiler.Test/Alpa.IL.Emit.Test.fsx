module Alpa.IL.Emit.Test

#if INTERACTIVE
#load "Alpa.IL.Lexer.Test.fsx"
#endif

open Alpa.IL.Helpers
open Alpa.Emit
open System
open Xunit
open Alpa.IL.Parser

type MB = Reflection.MethodBase
    
[<Fact>]
let AliasError1() =
    "alias error1 = error1"
    |> assertThrowEmitException (RecursiveAlias "error1")
    
[<Fact>]
let AliasError2() =
    "alias error2 `a = [mscorlib]System.Collections.Generic.List`1(error2 `a)"
    |> assertThrowEmitException (RecursiveAlias "error2")
    
[<Fact>]
let AliasError3A() =
    "
    alias error3A `a = [mscorlib]System.Collections.Generic.List`1(error3B `a)
    alias error3B `a = [mscorlib]System.Collections.Generic.List`1(error3A `a)
    "
    |> assertThrowEmitException (RecursiveAlias "error3A")

[<Fact>]
let SimpleType() = assertOfFile <| MB.GetCurrentMethod().Name
[<Fact>]
let OverloadOps() = assertOfFile <| MB.GetCurrentMethod().Name
[<Fact>]
let NestedType() = assertOfFile <| MB.GetCurrentMethod().Name
[<Fact>]
let MakeTuple2() = assertOfFile <| MB.GetCurrentMethod().Name
[<Fact>]
let RuntimeTypeGenericArg() = assertOfFile <| MB.GetCurrentMethod().Name
[<Fact>]
let MakeTupleOverload() = assertOfFile <| MB.GetCurrentMethod().Name
[<Fact>]
let Fields() = assertOfFile <| MB.GetCurrentMethod().Name
[<Fact>]
let Inherits() = assertOfFile <| MB.GetCurrentMethod().Name
[<Fact>]
let AliasSuccess() = assertOfFile <| MB.GetCurrentMethod().Name
//
//"
//alias integer = [System.Numerics]System.Numerics.BigInteger
//alias `a -> `b = Fun`2(`a, `b)
//
//type abstract Fun`2(`a, `b) =
//    abstract Apply(`a): `b
//;
//type Num(`a) =
//    abstract ofInteger(integer): `a
//    abstract '_+_'(`a, `a) : `a
//;
//type 'Num(int32)' + Num(int32) =
//    override ofInteger(integer): int32 =
//        ldarg.1
//        call integer::op_Explicit(integer): int32
//        ret
//
//    override '_+_'(int32, int32): int32 =
//        ldarg.1
//        ldarg.2
//        add
//        ret
//;
//type CloSucc2(`a) : (`a -> `a) =
//    member item1: Num(`a)
////    new (Num(`a)) =
////        ldarg.0
////        call base::new()
////        ldarg.1
////        stfld this::item1
////        ret
//    override Apply(`a): `a =
//        ldarg.0
//        ldfld this::item1
//        pop
////        call integer::get_One
////        callvirt Num(`a)::ofInteger
////        callvirt Num(`a)::'_+_'
//        ret
//;
////type CloSucc(`a) : (Num(`a) -> `a -> `a) =
////    override Apply(Num(`a)) : (`a -> `a) =
////        ldarg.1
////        newobj CloSucc2(`a)::new(Num(`a))
////        ret
////;
//
////module Program =
////    let succ(``a)() : (Num(``a) -> ``a -> ``a) = newobj CloSucc(``a)::new() ret
////    let 'Num(int32)' : Num(int32)
////    let ten : int32
////
////    static new() =
////        newobj 'Num(int32)'::new()
////        stsfld this::'Num(int32)'
////        ldc_i4 10
////        stsfld this::ten
////        ret
////
////    let main() : void =
////        ldsfld this::ten
////        ldsfld this::'Num(int32)'
////        call this::succ(int32)()
////        callvirt (Num(int32) -> int32 -> int32)::Apply
////        callvirt (int32 -> int32)::Apply
////        ret
////;
//"
//|> toILSource "\n" "Complex"
//
//
//"
//type abstract Fun`2(`a, `b) =
//    new() = ldarg.0 call base::new() ret
//    abstract Apply(`a): `b
//;
//type Id(`a) : Fun`2(`a,`a) =
//    new() = ldarg.0 call base::new() ret
//    override Apply(`a): `a = ldarg.1 ret
//;
//"
//|> toILSource "\n" "Complex"
//
//ilasm (__SOURCE_DIRECTORY__ + "\\" + "out.dll") "
//.assembly extern mscorlib { }
//.assembly Out { }
//
//.class public auto ansi abstract beforefieldinit Fun`2<a, b>	extends [mscorlib]System.Object
//{
//	.method public hidebysig specialname rtspecialname instance void .ctor () cil managed 
//	{
//		.maxstack 8
//		ldarg.0
//		call instance void [mscorlib]System.Object::.ctor()
//		ret
//	}
//	.method public hidebysig newslot abstract virtual instance !b Apply (!a arg0) cil managed {}
//}
//.class public auto ansi sealed beforefieldinit Id`1<a> extends class Fun`2<!a, !a>
//{
//	.method public hidebysig specialname rtspecialname instance void .ctor () cil managed 
//	{
//		.maxstack 8
//		ldarg.0
//		call instance void class Fun`2<!a, !a>::.ctor()
//		ret
//	}
//	.method public hidebysig virtual instance !a Apply (!a arg0) cil managed 
//	{
//		.maxstack 8
//		ldarg.1
//		ret
//	}
//}
//"