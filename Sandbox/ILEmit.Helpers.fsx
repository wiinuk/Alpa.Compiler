module ILEmit.Helpers
#load "ILEmit.fsx"

open ILEmit
open System

let newTypeVar name = Var name

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
let typeOf<'a> = typeOfT typeof<'a>

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

let type0D name parent impls members =
    TopTypeDef(name, {
        kind = None
        typeParams = []
        parent = parent
        impls = impls
        members = members
    })

let type1D name v1 f =
    let v1 = newTypeVar v1
    let make parent impls members =
        TopTypeDef(name, {
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
        TopTypeDef(name, {
            kind = Some Abstract
            typeParams = [v1; v2]
            parent = parent
            impls = impls
            members = members
        })
    f make (TypeVar v1) (TypeVar v2)

let param n t = Parameter(Some n, t)
let paramT t = Parameter(None, t)

let methodHead0 name pars retT = MethodHead(name, [], pars, Parameter(None, retT))
let methodInfo0 name pars retT body = MethodInfo(methodHead0 name pars retT, body)

let abstract0 name pars retT = AbstractDef <| methodHead0 name pars retT
let override0 name pars retT instrs = MethodDef(Some Override, methodInfo0 name pars retT <| MethodBody instrs)

let method1 name v1 f =
    let v1 = newTypeVar v1
    let pars, ret, instrs = f <| TypeVar v1
    MethodDef(None, MethodInfo(MethodHead(name, [v1], pars, paramT ret), MethodBody instrs))

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
    let base_init ts = Macro(BaseInit ts)
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

    let callvirt parent name typeArgs argTypes = Instr("", O.Callvirt, OpCall(false, parent, name, typeArgs, argTypes))
    let call isStatic thisType name typeArgs argTypes = Instr("", O.Call, OpCall(isStatic, thisType, name, typeArgs, argTypes))
    let call_static thisType name typeArgs argTypes = call true thisType name typeArgs argTypes


open System.Diagnostics
open System.IO
open System.Reflection
open System.Reflection.Emit
open System.Text.RegularExpressions

let ildasm path =
    let outPath = Path.ChangeExtension(path, ".il")
    Process.Start(
        @"C:\Program Files\Microsoft SDKs\Windows\v10.0A\bin\NETFX 4.6.1 Tools\ildasm.exe",
        sprintf "\"%s\" /out=\"%s\" /utf8 /metadata=VALIDATE" path outPath
    ).WaitForExit()

    let trivia = Regex "\s*//.*$"
    let sourceLines =
        File.ReadLines outPath
        |> Seq.map (fun l -> trivia.Replace(l, ""))
        |> Seq.filter (not << String.IsNullOrWhiteSpace)

    String.concat "\n" sourceLines

let emitDll name il =
    let moduleName = Path.ChangeExtension(name, ".dll")
    let path = Path.Combine(Path.GetTempPath(), moduleName)

    if File.Exists path then File.Delete path else ()

    let d = AppDomain.CurrentDomain
    let a = d.DefineDynamicAssembly(AssemblyName name, AssemblyBuilderAccess.Save)
    let m = a.DefineDynamicModule moduleName
    emitIL m il
    a.Save moduleName
    ildasm path, File.ReadAllBytes path