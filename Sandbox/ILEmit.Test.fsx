module internal ILEmit.Test
#load "ILEmit.Helpers.fsx"
open ILEmit
open ILEmit.Helpers
open ILEmit.Helpers.SimpleInstructions

let intT = typeOf<int>
let voidT = typeOfT typeof<System.Void>
let bigintT = typeOf<bigint>

let (==?) act exp = 
    if act <> exp then printfn "(==?) {act = %A; exp = %A}" act exp
    else printfn "ok"

let (===?) act exp = fst act ==? exp

let emptyTypeMap = HashMap()
let solveT = solveType emptyTypeMap emptyVarMap 

solveT typeOf<int> ==? typeof<int>
solveT typeOf<Map<int,Set<string>>> ==? typeof<Map<int,Set<string>>>

open System
open System.Reflection
open System.Reflection.Emit
let a = AppDomain.CurrentDomain.DefineDynamicAssembly(AssemblyName("test2"), AssemblyBuilderAccess.RunAndSave)
let f = a.DefineDynamicModule("test2.dll")

let ds = [
    type0D "EqualsInt" None [typeRefOf<System.IEquatable<int>>] [
        override0 "Equals" [argT intT] typeOf<bool> [ldc_i4 1; ret]
    ]
]

let map = HashMap()
let i = map.[p"EqualsInt"].t.ImplementedInterfaces |> Seq.item 0
i.GetGenericArguments().[0]

for d in ds do DefineTypes.topDef f map d
for d in ds do DefineMembers.topDef map d
emit map
createTypes map

//let t = f.DefineType("EqualsInt", T.Public ||| T.Sealed, typeof<obj>, [| typeof<IEquatable<int>> |])
//let m = t.DefineMethod("Equals", M.Public ||| M.Final ||| M.HideBySig ||| M.NewSlot ||| M.Virtual, CC.Standard, typeof<bool>, [|typeof<int>|])
//let g = m.GetILGenerator()
//g.Emit O.Ldc_I4_1
//g.Emit O.Ret
//
//
//t.CreateType()

a.Save("test2.dll")

IL [
    type0D "EqualsInt" None [typeRefOf<System.IEquatable<int>>] [
        override0 "Equals" [argT intT] typeOf<bool> [ldc_i4 1; ret]
    ]
]
|> emitDll "test3"

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
//
//    type1D "CloSucc2`1" "a" <| fun f a ->
//        let numAT = numT a
//        let cloSucc2AT = type1 (p"CloSucc2`1") a
//
//        f (Some(a ..-> a)) [] [
//            field "item1" numAT
//
//            // new (Num a) = base(); @item1 <- $0;
//            ctor [argT numAT] [
//                base_init []
//                ldarg 0
//                stfld cloSucc2AT "item1"
//                ret
//            ]
//
//            // override `_ _` a : a = @item1.`_+_`($0, @item1.ofInteger(bigint::One));
//            override0 "_ _" [argT a] a [
//                ldfld cloSucc2AT "item1"
//                ldarg 0
//                ldfld cloSucc2AT "item1"
//                ldsfld bigintT "One"
//                callvirt numAT "ofInteger" [] [a]
//                callvirt numAT "_+_" [] [a; a]
//                ret
//            ]
//        ]
//
//    type1D "CloSucc`1" "a" <| fun f a ->
//        f (Some(a ..-> (a .-> a))) [] [
//            override0 "_ _" [argT (numT a)] (a .-> a) [
//                ldarg 0
//                newobj (type1 (p"CloSucc2`1") a) [numT a]
//                ret
//            ]
//        ]
//
//    moduleD (t"Program") [
//        fun1 "succ" "a" <| fun f a -> f [] (numT a .-> (a .-> a)) [newobj (type1 (p"CloSucc`1") a) []; ret]
//        mutD "#Num(System_Int32)" <| numT intT
//        mutD "ten" intT
//        fun0 "init" [] voidT [
//            newobj (type0 (p"#Num(System_Int32)")) []
//            stsfld programT "#Num(System_Int32)"
//            ldc_i4 10
//            stsfld programT "ten"
//            ret
//        ]
//
//        fun0 "main" [] voidT [
//            call_static programT "init" [] []
//
//            ldsfld programT "ten"
//            ldsfld programT "#Num(System_Int32)"
//            call_static programT "succ" [intT] []
//            callvirt (numT intT .-> (intT .-> intT)) "_ _" [] [numT intT]
//            callvirt (intT .-> intT) "_ _" [] [intT]
//            ret
//        ]
//    ]
]
|> emitDll "test" ===? ".assembly extern mscorlib
{
  .publickeytoken = (B7 7A 5C 56 19 34 E0 89 )
  .ver 4:0:0:0
}
.assembly extern System.Numerics
{
  .publickeytoken = (B7 7A 5C 56 19 34 E0 89 )
  .ver 4:0:0:0
}
.assembly test
{
  .hash algorithm 0x00008004
  .ver 0:0:0:0
}
.module test.dll
.imagebase 0x00400000
.file alignment 0x00000200
.stackreserve 0x00100000
.subsystem 0x0003
.corflags 0x00000001
.class public abstract auto ansi beforefieldinit '->`2'<a,b>
       extends [mscorlib]System.Object
{
  .method public hidebysig newslot abstract virtual 
          instance !b  '_ _'(!a arg) cil managed
  {
  }
  .method public specialname rtspecialname 
          instance void  .ctor() cil managed
  {
    .maxstack  2
    IL_0000:  ldarg.0
    IL_0001:  call       instance void [mscorlib]System.Object::.ctor()
    IL_0006:  ret
  }
}
.class interface public abstract auto ansi beforefieldinit Num`1<a>
{
  .method public hidebysig newslot abstract virtual 
          instance !a  ofInteger(valuetype [System.Numerics]System.Numerics.BigInteger A_1) cil managed
  {
  }
  .method public hidebysig newslot abstract virtual 
          instance !a  '_+_'(!a A_1,
                             !a A_2) cil managed
  {
  }
}"


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
        TopTypeDef(t"Type", {
            kind = None
            typeArgs = []
            parent = None
            impls = []
            members = []
        })
    ]
    |> emitDll "test.dll"