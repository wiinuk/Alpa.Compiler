module internal Alpa.IL.Helpers

#if INTERACTIVE
#r "./../packages/System.Threading.Tasks.4.0.0/ref/dotnet/System.Threading.Tasks.dll"
#r "./../packages/FsCheck.2.5.0/lib/net45/FsCheck.dll"
#r "./../packages/FsCheck.Xunit.2.5.0/lib/net45/FsCheck.Xunit.dll"
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
    parent = None
    impls = []
    members = []
}

let typeD ns name typeParams parent impls ms =
    let def = {
        kind = None
        typeParams = typeParams
        parent = parent
        impls = impls
        members = ms
    }
    TopTypeDef(None, (name, List.rev ns), def)

let type0D ns name parent impls members =
    TopTypeDef(None, (name, List.rev ns), {
        kind = None
        typeParams = []
        parent = parent
        impls = impls
        members = members
    })

let type1D ns name v1 f =
    let v1 = newTypeVar v1
    let make parent impls members =
        TopTypeDef(None, (name, List.rev ns), {
            kind = None
            typeParams = [v1]
            parent = parent
            impls = impls
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
    let make parent impls members =
        TopTypeDef(None, name, {
            kind = Some Abstract
            typeParams = [v1; v2]
            parent = parent
            impls = impls
            members = members
        })
    f make (TypeVar v1) (TypeVar v2)


let inRange lo hi x = lo <= x && x <= hi
let inlinedI4 (i1Op, i4Op, lo, hi) n inlined =
    match n with
    | n when inRange lo hi n -> Instr("", inlined n, OpNone)
    | n when inRange -128 127 n -> Instr("", i1Op, OpI1 <| int8 n)
    | n -> Instr("", i4Op, OpI4 n)
    
module SimpleInstructions =
    let ret = Instr("", O.Ret, OpNone)

    let newobj thisType argTypes = Instr("", O.Newobj, OpMethod(MethodRef(thisType, ".ctor", argTypes)))

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

    let annot typeArgs argTypes = MethodTypeAnnotation(typeArgs, argTypes, None) |> Some
    let callvirt parent name typeArgs argTypes = Instr("", O.Callvirt, OpMethod(MethodRef(parent, name, annot typeArgs argTypes)))
    let call thisType name typeArgs argTypes = Instr("", O.Call, OpMethod(MethodRef(thisType, name, annot typeArgs argTypes)))
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
    
open Parser
open Alpa
open Alpa.RegexLexer
open Xunit

module Result =
    let map mapping = function
        | Ok x -> Ok <| mapping x
        | Error x -> Error x

let lex = Alpa.IL.Parser.lex >> Result.map (Array.map Source.value)

let ops = opKeyword()
let findOp name = Array.find (fst >> (=) name) ops |> snd

let rec tryPick (|Pick|_|) e =
    match e with
    | Pick x -> Some x
    | Quotations.ExprShape.ShapeCombination(_, es) -> List.tryPick (tryPick (|Pick|_|)) es
    | Quotations.ExprShape.ShapeLambda(_, e) -> tryPick (|Pick|_|) e
    | Quotations.ExprShape.ShapeVar _ -> None

let findMethod e =
    tryPick (function Quotations.Patterns.Call(_,m,_) -> Some m | _ -> None) e
    |> Option.get

let assertEq (act: 'a) (exp: 'a) =
    if typeof<'a> = typeof<string> then
        Assert.Equal(unbox<string> exp, unbox<string> act)
    else
        let implSeq =
            typeof<'a>.GetInterfaces()
            |> Seq.tryFind (fun i ->
                i.IsGenericType &&
                i.GetGenericTypeDefinition() = typedefof<_ seq>
            )
        match implSeq with
        | Some i ->
            let t1 = i.GetGenericArguments().[0]
            let equals = findMethod <@@ Assert.Equal<int>([], [], LanguagePrimitives.FastGenericEqualityComparer) @@>
            let equals = equals.GetGenericMethodDefinition().MakeGenericMethod(t1)

            let getFastGEC = findMethod <@@ LanguagePrimitives.FastGenericEqualityComparer @@>
            let getFastGEC = getFastGEC.GetGenericMethodDefinition().MakeGenericMethod(t1)
            let c = getFastGEC.Invoke(null, null)

            try
                equals.Invoke(null, [|exp; act; c|]) |> ignore
            with
            | :? System.Reflection.TargetInvocationException as e -> raise e.InnerException

        | None -> Assert.StrictEqual(exp, act)

let assertTokenEq xs = for t, ts in xs do assertEq (lex t) (Ok ts)
let assertLexEq xs = for t, e in xs do assertEq (lex t) e

let toILSource nl name source =
    match parse source with
    | Error(e, token) ->
        let clamp x = min (source.Length-1) (max 0 x)
        let eps = "..."
        let src =
            match token with
            | None -> eps
            | Some { startPos = sp; endPos = ep } ->
                let startIndex = clamp sp
                let endIndex = clamp(ep-1)

                let viewStartIndex = clamp (startIndex - 10)
                let viewEndIndex = clamp (endIndex + 10)
                let startEps = if viewStartIndex <> 0 then eps else "" 
                let endEps = if viewEndIndex <> source.Length-1 then eps else ""

                let escape = function
                    | '\r' -> "\\r"
                    | '\n' -> "\\n"
                    | c -> string c

                let viewL = String.collect escape <| source.Substring(viewStartIndex, startIndex - viewStartIndex)
                let escaped = String.collect escape <| source.Substring(startIndex, endIndex-startIndex)
                let viewR = String.collect escape <| source.Substring(clamp(endIndex+ 1), viewEndIndex - clamp(endIndex+ 1))
                let indent = String.replicate (startEps.Length + viewL.Length) " "
                let underline = String.replicate escaped.Length "~"
                startEps + viewL + escaped + viewR + endEps + "\n" + indent + underline

        failwithf "%A, %A\n%s" e token src

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

let assertThrowEmitException exp source =
    let e = Assert.Throws<EmitException>(fun _ -> toILSource "\n" "error" source |> ignore)
    assertEq e.Data0 exp