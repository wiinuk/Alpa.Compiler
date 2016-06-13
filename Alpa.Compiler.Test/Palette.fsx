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
type Num`1(`a) =
    abstract ofInteger(integer): `a
    abstract '_+_'(`a, `a) : `a
;
type 'Num`1(int32)' / Num`1(int32) =
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
type CloSucc2`1(`a) : (`a -> `a) =
    member item1: Num`1(`a)
    new (Num`1(`a)) =
        ldarg.0
        call base::new()
        ldarg.0
        ldarg.1
        stfld this::item1
        ret

    // override Apply(`a): `a = $0.item1.'_+_'($1, $0.item1.ofInteger(integer::get_One()))
    override Apply(`a): `a =
        ldarg.0                         // .., this
        ldfld this::item1               // .., this::item1
        ldarg.1                         // .., this::item1, arg1
        ldarg.0                         // .., this::item1, arg1, this
        ldfld this::item1               // .., this::item1, arg1, this::item1
        call integer::get_One           // .., this::item1, arg1, this::item1, 1I
        callvirt Num`1(`a)::ofInteger   // .., this::item1, arg1, 1
        callvirt Num`1(`a)::'_+_'       // .., (arg1 + 1)
        ret
;
type CloSucc`1(`a) : (Num`1(`a) -> `a -> `a) =
    override Apply(Num`1(`a)) : (`a -> `a) =
        ldarg.1
        newobj CloSucc2`1(`a)::new(Num`1(`0))
        ret
;

module Program =
    let succ(``a)() : (Num`1(``a) -> ``a -> ``a) = newobj CloSucc`1(``a)::new() ret
    let 'Num`1(int32)' : Num`1(int32)
    let ten : int32

    static new() =
//        newobj 'Num`1(int32)'::new()
//        stsfld this::'Num`1(int32)'
//        ldc.i4 10
//        stsfld this::ten
        ret

//    let main() : void =
//        ldsfld this::ten
//        ldsfld this::'Num`1(int32)'
//        call this::succ(int32)()
//        callvirt (Num`1(int32) -> int32 -> int32)::Apply
//        callvirt (int32 -> int32)::Apply
//        ret
//
;
"
|> toILSource "\n" "Complex"
|> ilasm (__SOURCE_DIRECTORY__ + @"\bin\debug\Out.dll")

#r "./bin/debug/Out.dll"
do
    let (==?) x y = if not <| LanguagePrimitives.PhysicalEquality x y then failwithf "(==?) %A %A" x y
    let (=?) x y = if x <> y then failwithf "(=?) %A %A" x y

    let x = ``Num`1(int32)``()
    let y: Num<int> = upcast x

    x.ofInteger 10I =? 10
    x.``_+_``(1, 2) =? 3
    y.ofInteger 11I =? 11
    y.``_+_``(2, 3) =? 5
    
    let x = CloSucc2<_>(y)
    x.Apply 1 =? 2
    x.item1 ==? y

    let c = CloSucc<_>()
    c.Apply(y).Apply 10 =? 11

    let i = Program.``Num`1(int32)``
    i.ofInteger 2I =? 2
    i.``_+_``(1, 2) =? 3
    Program.succ().Apply(i).Apply(3) =? 4
    Program.ten =? 10

"
alias integer = [System.Numerics]System.Numerics.BigInteger
alias `a -> `b = Fun`2(`a, `b)

type abstract Fun`2(`a, `b) =
    abstract Apply(`a): `b
;
type Num`1(`a) =
    abstract ofInteger(integer): `a
    abstract '_+_'(`a, `a) : `a
;
module A =
    let main(``a)((Num`1(``a) -> (``a -> ``a))): void = ret
;
"
|> toILSource "\n" "Test"