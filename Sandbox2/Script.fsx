open System.Diagnostics
open System.IO
open System.Collections.Concurrent
open System.Text

let exe fileName args =
    let i =
        ProcessStartInfo(
            FileName = fileName,
            Arguments = args,
            UseShellExecute = false,
            CreateNoWindow = true,
            RedirectStandardOutput = true,
            RedirectStandardError = true,
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

let ilasm outPath source =
    let path = Path.GetTempFileName()
    File.WriteAllText(path, source, Encoding.Unicode)
    let out =
        exe
            @"C:\WINDOWS\Microsoft.NET\Framework\v4.0.30319\ilasm.exe"
            (sprintf "\"%s\" /output=\"%s\" /dll /clock /nologo" path outPath)

    File.Delete path
    out

ilasm (Path.Combine(__SOURCE_DIRECTORY__, "test.dll")) "
.assembly test { }

.line 12,12:12,12 'Test.alpa'
.method static void () cil managed {
    .entrypoint
    ret
}
"

open System
open System.Reflection
open System.Reflection.Emit
type T = TypeAttributes
type M = MethodAttributes
type O = OpCodes

let name = "test"
let a = AppDomain.CurrentDomain.DefineDynamicAssembly(AssemblyName name, AssemblyBuilderAccess.RunAndSave)
let f = a.DefineDynamicModule(name + ".dll")

// 10 : enum System.ConsoleKey
// null : object
//
// type Ty(T1) =
//     static M1(T1) : int32 = ldc.i4.1 ret; 
//     static M2() : int32 =
//         ldnull
//         call Ty(string)::M1()
//         ret

let ty = f.DefineType("Ty", T.Public ||| T.Sealed)
let t1 = ty.DefineGenericParameters("T1").[0]
let m1 = ty.DefineMethod("M1", M.Public ||| M.Static)
m1.SetParameters t1
m1.SetReturnType typeof<int32>
do
    let g = m1.GetILGenerator()
    g.Emit O.Ldc_I4_1
    g.Emit O.Ret

let m2 = ty.DefineMethod("M2", M.Public ||| M.Static)
m2.SetParameters()
m2.SetReturnType typeof<int32>

let tyOfStringM1 = TypeBuilder.GetMethod(ty.MakeGenericType(typeof<string>), m1)

tyOfStringM1.DeclaringType.IsGenericType
tyOfStringM1.GetType().Name

do
    let g = m2.GetILGenerator()
    g.Emit O.Ldnull
    g.Emit(O.Call, tyOfStringM1)
    g.Emit O.Ret

ty.CreateType()
a.Save(name + ".dll")

type G<'a>() =
    member __.M x = x + ""
    member __.M(x: 'a) = x

let gt = typeof<G<string>>

let getMethod (closeType: Type) (methodOfOpenType: MethodInfo) =
    let openTypeParemeters = closeType.GetGenericTypeDefinition().GetGenericArguments()
    let methodGerenicArgs = methodOfOpenType.GetGenericArguments()
    let mOpenTypeMd = methodOfOpenType.MetadataToken
    closeType.GetMethods()
    |> Seq.filter(fun m ->
        m.Name = methodOfOpenType.Name &&
        m.Module.ResolveMethod(m.MetadataToken, openTypeParemeters, methodGerenicArgs).MetadataToken = mOpenTypeMd
    )
    |> Seq.exactlyOne

let ``G<'a>.M(string)`` = typedefof<G<_>>.GetMethod("M", [|typeof<string>|])
let ``G<'a>.M('a)`` = typedefof<G<_>>.GetMethod("M", [|typedefof<G<_>>.GetGenericArguments().[0]|])

let ``G<string>.M(string)`` = getMethod typeof<G<string>> ``G<'a>.M(string)``
let ``G<string>.M(!0)`` = getMethod typeof<G<string>> ``G<'a>.M('a)``


let mMethods = typeof<G<string>>.GetMethods() |> Seq.filter (fun m -> m.Name = "M") |> Seq.toArray
``G<string>.M(string)`` <> ``G<string>.M(!0)`` &&
Seq.contains ``G<string>.M(string)`` mMethods &&
Seq.contains ``G<string>.M(!0)`` mMethods

gt.GetMethods()
|> Seq.filter(fun m ->
    let genericTypeDefMethod = m.Module.ResolveMethod(m.MetadataToken, gt.GetGenericTypeDefinition().GetGenericArguments(), null)
    genericTypeDefMethod = gt.GetGenericTypeDefinition().GetMethod("M", [|typeof<string>|])
)

typeof<G<string>>.GetMethod("M", [|typeof<string>|])

let mString = typedefof<G<_>>.GetMethod("M", [|typeof<string>|])
let mA = typedefof<G<_>>.GetMethod("M", [|typedefof<G<_>>.GetGenericArguments().[0]|])
let mA' = mA.Module.ResolveMethod(mA.MetadataToken, [|typeof<string>|], null)
mA'.GetParameters()
mA'.MetadataToken = mA.MetadataToken

let parameterTypes = mA.GetParameters() |> Array.map (fun p -> p.ParameterType)
let returnType = mA.ReturnType
let call = m

let g = G<string>()
g.M("")

//#r @"C:\Users\pc-2\AppData\Local\Temp\test.dll"
//Ty<_>.M2()