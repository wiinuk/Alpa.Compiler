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
    "alias error2(`a) = [mscorlib]System.Collections.Generic.List`1(error2(`a))"
    |> assertThrowEmitException (RecursiveAlias "error2")
    
[<Fact>]
let AliasError3A() =
    "
    alias error3A(`a) = [mscorlib]System.Collections.Generic.List`1(error3B(`a))
    alias error3B(`a) = [mscorlib]System.Collections.Generic.List`1(error3A(`a))
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