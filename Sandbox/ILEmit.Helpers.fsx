module internal ILEmit.Helpers
#load "ILEmit.fsx"

open ILEmit
open System
open System.Diagnostics
open System.IO
open System.Reflection
open System.Reflection.Emit
open System.Text.RegularExpressions

let newTypeVar name = Var name

let sysTypeValidate (t: Type) =
    if t.IsNested then failwithf "%A is GenericParameter." t
    if t.IsGenericParameter then failwithf "%A is GenericParameter." t

let getPath t =
    sysTypeValidate t
    let nsRev =
        t.Namespace.Split Type.Delimiter
        |> Seq.map ValidName.NonEscape
        |> Seq.rev
        |> Seq.toList

    nsToPath nsRev <| ValidName.NonEscape t.Name

let rec typeOfT t = TypeSpec(getPath t, typeOfTypeArgs t)
and typeOfTypeArgs t = if not t.IsGenericType then [] else t.GetGenericArguments() |> Seq.map typeOfT |> Seq.toList
let typeRefOfT t = TypeRef(getPath t, typeOfTypeArgs t)

[<RequiresExplicitTypeArguments>]
let typeOf<'a> = typeOfT typeof<'a>

[<RequiresExplicitTypeArguments>]
let typeRefOf<'a> = typeRefOfT typeof<'a>

[<AutoOpen>]
module TypeRefs =
    let objR = typeRefOf<obj>
    
[<AutoOpen>]
module Types =
    let intT = typeOf<int>
    let voidT = typeOf<System.Void>
    let bigintT = typeOf<bigint>

let t n = ValidName n
let p n = (t n, [])

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
    
let typeDef = {
    kind = None
    name = t""
    typeArgs = []
    parent = None
    impls = []
    members = []
}

let type0D name parent impls members =
    TopTypeDef {
        kind = None
        name = t name
        typeArgs = []
        parent = parent
        impls = impls
        members = members
    }

let type1D name v1 f =
    let v1 = newTypeVar v1
    let make parent impls members =
        TopTypeDef {
            kind = None
            name = t name
            typeArgs = [v1]
            parent = parent
            impls = impls
            members = members
        }
    f make (TypeVar v1)
    
let type0 t = TypeSpec(t, [])
let type1 t v1 = TypeSpec(t, [v1])
let type2 t v1 v2 = TypeSpec(t, [v1; v2])
let typeRef1 n v1 = TypeRef(n, [v1])
let typeRef2 n v1 v2 = TypeRef(n, [v1; v2])

let abstract2T name v1 v2 f =
    let v1, v2 = newTypeVar v1, newTypeVar v2
    let make parent impls members =
        TopTypeDef {
            kind = Some Abstract
            name = t name
            typeArgs = [v1; v2]
            parent = parent
            impls = impls
            members = members
        }
    f make (TypeVar v1) (TypeVar v2)

let arg n t = Argument(Some n, t)
let argT t = Argument(None, t)

let methodHead0 name args retT = MethodHead(name, [], args, Argument(None, retT))
let methodInfo0 name args retT body = MethodInfo.MethodInfo(methodHead0 name args retT, body)

let abstract0 name args retT = AbstractDef <| methodHead0 name args retT
let override0 name args retT instrs = MethodDef(Some Override, methodInfo0 name args retT <| MethodBody.MethodBody instrs)

let ctor args is = CtorDef(args, MethodBody.MethodBody is)

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

open SimpleInstructions

let field n t = Field(false, false, n, t)
let moduleD name ms = TopModuleDef(name, ms)
let mutD name t = ModuleValDef(true, name, t)
let fun1 name v1 f =
    let v1 = newTypeVar v1
    let make args ret instrs =
        ModuleMethodDef(MethodInfo.MethodInfo(MethodHead(name, [v1], args, argT ret), MethodBody.MethodBody instrs))

    f make (TypeVar v1)

let fun0 name args ret instrs =
    ModuleMethodDef(MethodInfo.MethodInfo(MethodHead(name, [], args, argT ret), MethodBody.MethodBody instrs))


//type abstract `->` (a, b) = abstract `_ _` a : b;;
//
//type Num a =
//    ofInteger Integer : a;
//    `_+_` (a, a) : a;;
//
//type #(Num Int32) <: Object, Num Int32 =
//    override ofInteger Integer : Int32 { ... };
//    override `_+_` (Int32, Int32) : Int32 { ... };;
//
//type CloSucc2 a <: (a -> a) =
//    val item1 : Num a
//    new (Num a) =
//        base()
//        ldarg.0
//        stfld CloSucc2::item
//        ret;
//
//    override `_ _` a : a =
//        ldfld CloSucc2::item
//        ldarg.0
//        ldfld CloSucc2::item
//        ldsfld bigint::One
//        callvirt Num a::ofInteger(a)
//        callvirt Num a::`_+_`
//        ret;;
//
//type CloSucc a <: (Num a -> a -> a) =
//    override `_ _` (Num a) : a -> a =
//        ldarg.0
//        newobj (CloSucc2 a) (Num a)
//        ret;;
//
//module Program =
//    fun succ a () : Num a -> a -> a = newobj (CloSucc a) () ret;;
//
//    val #(Num Int32) : Num Int32;;
//    val ten : Int32;;
//    fun init () : void =
//        newobj #(Num Int32) ()
//        stsfld Program::#(Num Int32)
//        ldc_i4 10i
//        stsfld Program::ten
//        ret;;
//
//    fun main () : void =
//        call static Program::init ()
//
//        ldsfld Program::ten
//        ldsfld Program::#(Num Int32)
//        call static Program::succ Int32 ()
//        callvirt `->`(Num Int32, Int32 -> Int32)::` `(Num Int32)
//        callvirt `->`(Int32, Int32)::` `(Int32)
//        ret;;
//;;
let arrowT = p"->`2"
let (..->) a b = typeRef2 arrowT a b
let (.->) a b = type2 arrowT a b
let numR = typeRef1 (p"Num`1")
let numT = type1 (p"Num`1")
let programT = type0 (p"Program")
IL [
    abstract2T "->`2" "a" "b" <| fun f a b ->
        f None [] [abstract0 "_ _" [arg "arg" a] b]

    type1D "Num`1" "a" <| fun f a ->
        f None [] [
            abstract0 "ofInteger" [argT bigintT] a
            abstract0 "_+_" [argT a; argT a] a
        ]

    type0D "#Num(System_Int32)" None [numR intT] [
        override0 "ofInteger" [argT bigintT] intT [ldc_i4 0; ret]
        override0 "_+_" [argT intT; argT intT] intT [ldc_i4 0; ret]
    ]

    type1D "CloSucc2`1" "a" <| fun f a ->
        let numAT = numT a
        let cloSucc2AT = type1 (p"CloSucc2`1") a

        f (Some(a ..-> a)) [] [
            field "item1" numAT

            // new (Num a) = base(); @item1 <- $0;
            ctor [argT numAT] [
                base_init []
                ldarg 0
                stfld cloSucc2AT "item1"
                ret
            ]

            // override `_ _` a : a = @item1.`_+_`($0, @item1.ofInteger(bigint::One));
            override0 "_ _" [argT a] a [
                ldfld cloSucc2AT "item1"
                ldarg 0
                ldfld cloSucc2AT "item1"
                ldsfld bigintT "One"
                callvirt numAT "ofInteger" [] [a]
                callvirt numAT "_+_" [] [a; a]
                ret
            ]
        ]

    type1D "CloSucc`1" "a" <| fun f a ->
        f (Some(a ..-> (a .-> a))) [] [
            override0 "_ _" [argT (numT a)] (a .-> a) [
                ldarg 0
                newobj (type1 (p"CloSucc2`1") a) [numT a]
                ret
            ]
        ]

    moduleD (t"Program") [
        fun1 "succ" "a" <| fun f a -> f [] (numT a .-> (a .-> a)) [newobj (type1 (p"CloSucc`1") a) []; ret]
        mutD "#Num(System_Int32)" <| numT intT
        mutD "ten" intT
        fun0 "init" [] voidT [
            newobj (type0 (p"#Num(System_Int32)")) []
            stsfld programT "#Num(System_Int32)"
            ldc_i4 10
            stsfld programT "ten"
            ret
        ]

        fun0 "main" [] voidT [
            call_static programT "init" [] []

            ldsfld programT "ten"
            ldsfld programT "#Num(System_Int32)"
            call_static programT "succ" [intT] []
            callvirt (numT intT .-> (intT .-> intT)) "_ _" [] [numT intT]
            callvirt (intT .-> intT) "_ _" [] [intT]
            ret
        ]
    ]
]
|> emitDll "test"

let __ _ =
//    let d = TopTypeDef {
//            kind = None
//            name = t"Type"
//            typeArgs = []
//            parent = typeRefOf<obj>
//            impls = []
//            members = []
//        }
//        
//    let name = "test" // sprintf "%s_%d" "test" Environment.TickCount
//    let moduleName = Path.ChangeExtension(name, ".dll")
//    let path = Path.Combine(Path.GetTempPath(), moduleName)
//
//    if File.Exists path then File.Delete path else ()
//
//    let d = AppDomain.CurrentDomain
//    let a = d.DefineDynamicAssembly(AssemblyName name, AssemblyBuilderAccess.Save)
//    let m = a.DefineDynamicModule moduleName
//    let t = m.DefineType("Type1", T.Public ||| T.Sealed ||| T.BeforeFieldInit, typeof<obj>)
//    //t.DefineField("f1", t, FieldAttributes.InitOnly ||| FieldAttributes.Public) |> ignore
//    t.CreateType() |> ignore
//
//    //if File.Exists path then File.Delete path else ()
//    a.Save moduleName
//
//    ildasm path = ".assembly extern mscorlib
//{
//  .publickeytoken = (B7 7A 5C 56 19 34 E0 89 )
//  .ver 4:0:0:0
//}
//.assembly test
//{
//  .hash algorithm 0x00008004
//  .ver 0:0:0:0
//}
//.module test.dll
//.imagebase 0x00400000
//.file alignment 0x00000200
//.stackreserve 0x00100000
//.subsystem 0x0003
//.corflags 0x00000001
//.class public auto ansi sealed beforefieldinit Type1
//       extends [mscorlib]System.Object
//{
//  .method public specialname rtspecialname 
//          instance void  .ctor() cil managed
//  {
//    .maxstack  2
//    IL_0000:  ldarg.0
//    IL_0001:  call       instance void [mscorlib]System.Object::.ctor()
//    IL_0006:  ret
//  }
//}"      |> ignore
//
//
//    let map = HashMap()
//    DefineTypes.topDef m map d
//    createTypes map
//    a.Save("test.dll")
//
//    m.GetTypes()
//
//    map.[t"Type", []]

    IL [
        TopTypeDef {
            kind = None
            name = t"Type"
            typeArgs = []
            parent = None
            impls = []
            members = []
        }
    ]
    |> emitDll "test.dll"