module internal Alpa.IL.Helpers

#if INTERACTIVE
#r "./../packages/FsCheck.2.4.0/lib/net45/FsCheck.dll"
#r "./../packages/FsCheck.Xunit.2.4.0/lib/net45/FsCheck.Xunit.dll"
#r "./../packages/xunit.runner.visualstudio.2.1.0/build/net20/../_common/xunit.abstractions.dll"
#r "./../packages/xunit.assert.2.1.0/lib/dotnet/xunit.assert.dll"
#r "./../packages/xunit.extensibility.core.2.1.0/lib/dotnet/xunit.core.dll"
#r "./../packages/xunit.extensibility.execution.2.1.0/lib/net45/xunit.execution.desktop.dll"
#r "./../Sandbox/bin/debug/Alpa.Compiler.dll"
#endif

open Alpa.Emit
open Alpa.Emit.ILEmit
open System

type O = System.Reflection.Emit.OpCodes

let newTypeVar name = name

let sysTypeValidate (t: Type) =
    if t.IsNested then failwithf "%A is GenericParameter." t
    if t.IsGenericParameter then failwithf "%A is GenericParameter." t

let getPath t =
    sysTypeValidate t
    let nsRev =
        t.Namespace.Split Type.Delimiter
        |> Seq.rev
        |> Seq.toList

    FullName(t.Name, [], nsRev, Some(t.Assembly.GetName().Name))

let rec typeOfT t = TypeSpec(getPath t, typeOfTypeArgs t)
and typeOfTypeArgs t = if not t.IsGenericType then [] else t.GetGenericArguments() |> Seq.map typeOfT |> Seq.toList
let typeRefOfT t = TypeSpec(getPath t, typeOfTypeArgs t)

[<RequiresExplicitTypeArguments>]
let typeSpecOf<'a> = typeOfT typeof<'a>

[<RequiresExplicitTypeArguments>]
let typeRefOf<'a> = typeRefOfT typeof<'a>

let t n = n
let p n = FullName(t n, [], [], None)

let typeDef = {
    kind = None
    typeParams = []
    inherits = []
    members = []
}

let typeD ns name typeParams inherits ms =
    let def = {
        kind = None
        typeParams = typeParams
        inherits = inherits
        members = ms
    }
    TopTypeDef((name, List.rev ns), def)

let type0D ns name inherits members =
    TopTypeDef((name, List.rev ns), {
        kind = None
        typeParams = []
        inherits = inherits
        members = members
    })

let type1D ns name v1 f =
    let v1 = newTypeVar v1
    let make inherits members =
        TopTypeDef((name, List.rev ns), {
            kind = None
            typeParams = [v1]
            inherits = inherits
            members = members
        })
    f make (TypeVar v1)
    
let type0 t = TypeSpec(t, [])
let type1 t v1 = TypeSpec(t, [v1])
let type2 t v1 v2 = TypeSpec(t, [v1; v2])
let typeRef1 n v1 = TypeSpec(n, [v1])
let typeRef2 n v1 v2 = TypeSpec(n, [v1; v2])

let abstract2T name v1 v2 f =
    let v1, v2 = newTypeVar v1, newTypeVar v2
    let make inherits members =
        TopTypeDef(name, {
            kind = Some Abstract
            typeParams = [v1; v2]
            inherits = inherits
            members = members
        })
    f make (TypeVar v1) (TypeVar v2)

let param n t = Parameter(Some n, t)
let paramT t = Parameter(None, t)

let methodD name mTypeParams parameters returnType instrs =
    MethodDef(None, MethodInfo(MethodHead(name, mTypeParams, parameters, paramT returnType), MethodBody instrs))
let methodHead0 name pars retT = MethodHead(name, [], pars, Parameter(None, retT))
let methodInfo0 name pars retT body = MethodInfo(methodHead0 name pars retT, body)

let abstract0 name pars retT = AbstractDef <| methodHead0 name pars retT
let override0 name pars retT instrs = MethodDef(Some Override, methodInfo0 name pars retT <| MethodBody instrs)
let method1 name v1 f =
    let v1 = newTypeVar v1
    let make pars ret instrs = MethodDef(None, MethodInfo(MethodHead(name, [v1], pars, paramT ret), MethodBody instrs))
    f make <| TypeVar v1

let ctor pars is = CtorDef(pars, MethodBody is)

let field n t = Field(false, false, n, t)
let moduleD name ms = TopModuleDef(name, ms)
let mutD name t = ModuleValDef(true, name, t)
let fun1 name v1 f =
    let v1 = newTypeVar v1
    let make pars ret instrs =
        ModuleMethodDef(MethodInfo(MethodHead(name, [v1], pars, paramT ret), MethodBody instrs))

    f make (TypeVar v1)

let fun0 name pars ret instrs =
    ModuleMethodDef(MethodInfo(MethodHead(name, [], pars, paramT ret), MethodBody instrs))
    
let inRange lo hi x = lo <= x && x <= hi
let inlinedI4 (i1Op, i4Op, lo, hi) n inlined =
    match n with
    | n when inRange lo hi n -> Instr("", inlined n, OpNone)
    | n when inRange -128 127 n -> Instr("", i1Op, OpI1 <| int8 n)
    | n -> Instr("", i4Op, OpI4 n)
    
module SimpleInstructions =
    let ret = Instr("", O.Ret, OpNone)

    let newobj thisType argTypes = Instr("", O.Newobj, OpCtor(thisType, argTypes))

    let ldc_i4 n = inlinedI4 (O.Ldc_I4_S, O.Ldc_I4, -1, 8) n <| function
        | 0 -> O.Ldc_I4_0
        | 1 -> O.Ldc_I4_1
        | 2 -> O.Ldc_I4_2
        | 3 -> O.Ldc_I4_3
        | 4 -> O.Ldc_I4_4
        | 5 -> O.Ldc_I4_5
        | 6 -> O.Ldc_I4_6
        | 7 -> O.Ldc_I4_7
        | 8 -> O.Ldc_I4_8
        | _ -> O.Ldc_I4_M1

    let ldarg n = inlinedI4 (O.Ldarg_S, O.Ldarg, 0, 3) n <| function
        | 0 -> O.Ldarg_0
        | 1 -> O.Ldarg_1
        | 2 -> O.Ldarg_2
        | _ -> O.Ldarg_3

    let stfld t n = Instr("", O.Stfld, OpField(t, n))
    let ldfld t n = Instr("", O.Ldfld, OpField(t, n))
    let stsfld t n = Instr("", O.Stsfld, OpField(t, n))
    let ldsfld t n = Instr("", O.Ldsfld, OpField(t, n))

    let callvirt parent name typeArgs argTypes = Instr("", O.Callvirt, OpMethod(parent, name, typeArgs, argTypes))
    let call thisType name typeArgs argTypes = Instr("", O.Call, OpMethod(thisType, name, typeArgs, argTypes))
    let call_static thisType name typeArgs argTypes = call thisType name typeArgs argTypes


open System.Diagnostics
open System.IO
open System.Reflection
open System.Reflection.Emit
open System.Text.RegularExpressions
open System.Collections.Concurrent
open System.Text

let startCore enc fileName args =
    let i =
        ProcessStartInfo(
            FileName = fileName,
            Arguments = args,
            UseShellExecute = false,
            CreateNoWindow = true,
            RedirectStandardOutput = true,
            RedirectStandardError = true,
            StandardOutputEncoding = enc,
            StandardErrorEncoding = enc,
            RedirectStandardInput = false
        )
    
    use p = new Process(StartInfo = i)

    let sources = ConcurrentQueue()
    let errors = ConcurrentQueue()
    p.OutputDataReceived.Add <| fun e -> sources.Enqueue e.Data
    p.ErrorDataReceived.Add <| fun e -> errors.Enqueue e.Data

    p.Start() |> ignore

    p.BeginOutputReadLine()
    p.BeginErrorReadLine()

    p.WaitForExit()
    String.concat "\n" sources, String.concat "\n" errors

let start fileName args = startCore Encoding.Default fileName args

let ilasm outPath source =
    let path = Path.GetTempFileName()
    File.WriteAllText(path, source, Encoding.Unicode)
    let out = start @"C:\WINDOWS\Microsoft.NET\Framework\v4.0.30319\ilasm.exe" <| sprintf "\"%s\" /output=\"%s\" /dll /clock /nologo" path outPath
    File.Delete path
    out

let ildasm nl path =
    let paths = [
        @"C:\Program Files\Microsoft SDKs\Windows\v10.0A\bin\NETFX 4.6.1 Tools\ildasm.exe"
        @"C:\Program Files (x86)\Microsoft SDKs\Windows\v10.0A\bin\NETFX 4.6.1 Tools\ildasm.exe"
    ]
    let out, error =
        sprintf "\"%s\" /text /unicode /nobar /metadata=VALIDATE" path
        |> start (List.find File.Exists paths)

    let trivia = Regex "\s*//.*$"
    let source = out + nl + error
    source.Split([|"\r\n"; "\n"|], StringSplitOptions.RemoveEmptyEntries)
    |> Seq.map (fun l -> trivia.Replace(l, ""))
    |> Seq.filter (not << System.String.IsNullOrWhiteSpace)
    |> String.concat nl

let emitDll nl name il =
    let moduleName = Path.ChangeExtension(name, ".dll")
    let path = Path.Combine(System.Environment.CurrentDirectory, moduleName)

    if File.Exists path then File.Delete path else ()

    let d = AppDomain.CurrentDomain
    let a = d.DefineDynamicAssembly(AssemblyName name, AssemblyBuilderAccess.Save)
    let m = a.DefineDynamicModule moduleName
    emitIL m il
    a.Save moduleName
    let source = ildasm nl path
    File.Delete path
    source