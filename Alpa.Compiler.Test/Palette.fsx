module Alpa.IL.Emit.Test

#load "Alpa.IL.Lexer.Test.fsx"

open Alpa.IL.Helpers
open Alpa.Emit
open System
open Xunit
open Alpa.IL.Parser


"
alias integer = [System.Numerics]System.Numerics.BigInteger
alias `a -> `b = Fun`2(`a, `b)

type abstract Fun`2(`a, `b) =
    abstract Apply(`a): `b
;
type Num(`a) =
    abstract ofInteger(integer): `a
    abstract '_+_'(`a, `a) : `a
;
type 'Num(int32)' / Num(int32) =
    override ofInteger(integer): int32 =
        ldarg.1
        call integer::op_Explicit(integer): int32
        ret

    override '_+_'(int32, int32): int32 =
        ldarg.1
        ldarg.2
        add
        ret
;
type CloSucc2(`a) : (`a -> `a) =
    member item1: Num(`a)
    new (Num(`a)) =
        ldarg.0
        call base::new()
        ldarg.0
        ldarg.1
        stfld this::item1
        ret

    // override Apply(`a): `a = $0.item1.'_+_'($1, $0.item1.ofInteger(integer::get_One()))
    override Apply(`a): `a =
        ldarg.0                     // .., this
        ldfld this::item1           // .., this::item1
        ldarg.1                     // .., this::item1, arg1
        ldarg.0                     // .., this::item1, arg1, this
        ldfld this::item1           // .., this::item1, arg1, this::item1
        call integer::get_One       // .., this::item1, arg1, this::item1, 1I
        callvirt Num(`a)::ofInteger // .., this::item1, arg1, 1
        callvirt Num(`a)::'_+_'     // .., (arg1 + 1)
        ret
;
//type CloSucc(`a) : (Num(`a) -> `a -> `a) =
//    override Apply(Num(`a)) : (`a -> `a) =
//        ldarg.1
//        newobj CloSucc2(`a)::new(Num(`a))
//        ret
//;

//module Program =
//    let succ(``a)() : (Num(``a) -> ``a -> ``a) = newobj CloSucc(``a)::new() ret
//    let 'Num(int32)' : Num(int32)
//    let ten : int32
//
//    static new() =
//        newobj 'Num(int32)'::new()
//        stsfld this::'Num(int32)'
//        ldc_i4 10
//        stsfld this::ten
//        ret
//
//    let main() : void =
//        ldsfld this::ten
//        ldsfld this::'Num(int32)'
//        call this::succ(int32)()
//        callvirt (Num(int32) -> int32 -> int32)::Apply
//        callvirt (int32 -> int32)::Apply
//        ret
//;
"
|> toILSource "\n" "Complex"
|> ilasm (__SOURCE_DIRECTORY__ + @"\bin\debug\Out.dll")

#r "./bin/debug/Out.dll"
do
    let (==?) x y = if not <| LanguagePrimitives.PhysicalEquality x y then failwithf "(==?) %A %A" x y
    let (=?) x y = if x <> y then failwithf "(=?) %A %A" x y
    let x: Fun<_,_> = null
    let y: Num<_> = null

    let x = ``Num(int32)``()
    let y: Num<int> = upcast x

    x.ofInteger(10I) =? 10
    x.``_+_``(1, 2) =? 3
    y.ofInteger(11I) =? 11
    y.``_+_``(2, 3) =? 5
    
    let x = CloSucc2<_>(y)
    x.Apply 1 =? 2
    x.item1 ==? y

"
type abstract Fun`2(`a, `b) =
    new() = ldarg.0 call base::new() ret
    abstract Apply(`a): `b
;
type Id(`a) : Fun`2(`a,`a) =
    new() = ldarg.0 call base::new() ret
    override Apply(`a): `a = ldarg.1 ret
;
"
|> toILSource "\n" "Complex"

ilasm (__SOURCE_DIRECTORY__ + "\\" + "out.dll") "
.assembly extern mscorlib { }
.assembly Out { }

.class public auto ansi abstract beforefieldinit Fun`2<a, b>	extends [mscorlib]System.Object
{
	.method public hidebysig specialname rtspecialname instance void .ctor () cil managed 
	{
		.maxstack 8
		ldarg.0
		call instance void [mscorlib]System.Object::.ctor()
		ret
	}
	.method public hidebysig newslot abstract virtual instance !b Apply (!a arg0) cil managed {}
}
.class public auto ansi sealed beforefieldinit Id`1<a> extends class Fun`2<!a, !a>
{
	.method public hidebysig specialname rtspecialname instance void .ctor () cil managed 
	{
		.maxstack 8
		ldarg.0
		call instance void class Fun`2<!a, !a>::.ctor()
		ret
	}
	.method public hidebysig virtual instance !a Apply (!a arg0) cil managed 
	{
		.maxstack 8
		ldarg.1
		ret
	}
}
"