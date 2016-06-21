module Alpa.IL.Emit.Test

#load "Alpa.IL.Lexer.Test.fsx"

open Alpa.IL.Helpers
open Alpa.Emit
open System
open Xunit
open Alpa.IL.Parser

"""
assembly [AssemblyImport]
import [System.Numerics] version=4,0,0,0 culture=neutral public_key_token=B"B7 7A 5C 56 19 34 E0 89" as [numerics]
import [FSharp.Core] version=4,4,0,0 culture=neutral public_key_token=B"b03f5f7f11d50a3a" as [fs]

module AssemblyImport.Program =
    let Main([fs]Microsoft.FSharp.Core.Unit, [numerics]System.Numerics.BigInteger): void = ret
;
"""
|> toILSource "\n"


"""
assembly [AssemblyImportError]
import [System.Numerics] version=4,0,0,0 culture=neutral public_key_token=B"B7 7A 5C 56 19 34 E0 89" as [asm]
import [FSharp.Core] version=4,4,0,0 culture=neutral public_key_token=B"b03f5f7f11d50a3a" as [asm]
"""
|> toILSource "\n"

"FSharp.Core, Version=4.4.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a"

typeof<unit>.AssemblyQualifiedName