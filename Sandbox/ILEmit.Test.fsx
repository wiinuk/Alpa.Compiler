//module internal ILEmit.Test
//#load "ILEmit.Helpers.fsx"
//open ILEmit
//open ILEmit.Helpers
//open ILEmit.Helpers.SimpleInstructions
//
//open System
//open System.Reflection
//open System.Reflection.Emit
//type T = TypeAttributes
//type M = MethodAttributes
//type O = OpCodes
//let name = "test1"
//let a = AppDomain.CurrentDomain.DefineDynamicAssembly(AssemblyName name, AssemblyBuilderAccess.RunAndSave)
//let d = a.DefineDynamicModule(name + ".dll")
//
//let ty1 = d.DefineType("Ty1", T.Public)
//
//let m1 = ty1.DefineMethod("M1", M.Public ||| M.Final)
//m1.SetParameters typeof<int>
//m1.GetILGenerator().Emit O.Ret
//m1.SetReturnType typeof<System.Void>
//
//let m1_char = ty1.DefineMethod("M1", M.Public ||| M.Final)
//m1_char.SetParameters typeof<int>
//m1_char.GetILGenerator().Emit O.Ret
//m1_char.SetReturnType typeof<System.Void>
//
//ty1.CreateType()
//
//a.Save(name + ".dll")
//
//let bigintT = typeSpecOf<bigint>
//
//ResizeArray().ConvertAll()
//
//
////let findMethod { mmap = mmap; varMap = varMap; typeArgs = typeArgs } name mTypeArgs argTypes = substTypeArgs varMap typeArgs <| fun _ ->
////    get mmap name
////    |> List.find (function
////        | { mVarMap = TypeVarMap(mTypeParams,_) as mVarMap; m = MethodInfo(MethodHead(pars = pars), _)
////            } ->
////            List.length pars = List.length argTypes &&
////            List.length mTypeParams = List.length mTypeArgs &&
////            substTypeArgs mVarMap mTypeArgs <| fun _ ->
////                List.forall2
////                    (fun (Parameter(_,parType)) argType -> typeSpecEq parType argType)
////                    pars
////                    argTypes
////    )
////    |> fun mi -> { mi with mTypeArgs = mTypeArgs }
//
////    match solveTypeCore map varMap mVarMap t with
////    | SType t -> t.GetConstructor(B.Public ||| B.NonPublic, null, solveTypes map varMap mVarMap ts, null)
////
////    | SBuilderType { mmap = parentMMap } -> findMethod ts parentMMap
////
////    | SBuilderGeneric(t, genericDef, genericParams) -> failwith "Not implemented yet"
////    | STypeVar(_, _) -> failwith "Not implemented yet"
//
//// class Make`1<int32>::Tuple<string>(!0, !!0)
//
//    // Builder::GetMethod is not implemented
//
//        // type C =
//        //     fun M (a) (a): a = ...;
//        //     fun M () (string): string = ...;;
//        //
//        // getMethod C "M" () (string)
//        // getMethod C "M" (string) (string)
//        // getMethod C "M" (string) (!!0)
//
//    // type Make`1 (T1) =
//    //     fun Tuple (T2) (T1, T2) : Tuple(T1, T2) = ...;
//    //
//    // call Make`1(int32)::Tuple (string) (!0, !!0)
//
//    // type C`1(T) =
//    //     fun M () (T) : T = ...;
//    //     fun M () (List(T)) : List T = ...;
//    //     fun M () (string) : string = ...;
//    //
//    // call C`1(string)::M () (string) => ok "fun M () (string) : string = ...;"
//    // call C`1(string)::M () (!0) => ok "fun M () (!0) : !0 = ...;"
//    //
//    // [T,List(a)]
//    // fun Main(a) () = call C`1(List(a))::() (List(a)) => ok
//    // fun Main(a) () = call C`1(a)::() (a) => ok
//
//
//// call class [mscorlib]System.Tuple`2<!0, !!0> class Make`1<int32>::Tuple<string>(!0, !!0)
//let (==?) act exp = 
//    if act <> exp then printfn "(==?) {act = %A; exp = %A}" act exp
//    else printfn "ok"
//
//let (===?) act exp = fst act ==? exp
//
//let emptyTypeMap = HashMap()
//let solveT = solveType emptyTypeMap emptyVarMap  emptyVarMap
//
//open System
//open System.Reflection
//open System.Reflection.Emit
//
//// type C (a) = fun M (b) (a, b) : b
////
//// call C(char)::M (int) (char, int)
//// call C(char)::M (int) (char, char) // invalid
//// call C(char)::M (int) (int, char) // invalid
//// call C(char)::M (int) (int, int) // invalid
////
//// call C(char)::M (char) (char, char)
//// call C(char)::M (char) (int, char) // invalid
//// call C(char)::M (char) (char, int) // invalid
//// call C(char)::M (char) (int, int) // invalid
//begin
//    let ds = [
//        type1D "C" "a" <| fun f a ->
//            f None [] [
//                method1 "M" "b" <| fun f b -> f [paramT a; paramT b] b [ldarg 1; ret]
//            ]
//    ]
//    let name = "test1"
//    let a = AppDomain.CurrentDomain.DefineDynamicAssembly(AssemblyName name, AssemblyBuilderAccess.RunAndSave)
//    let m = a.DefineDynamicModule(name + ".dll")
//
//    let map = HashMap()
//    for d in ds do DefineTypes.topDef m map d
//    defineTypeParams map
//    defineMembers map
//
//    let charT = typeSpecOf<char>
//    let cCharT = TypeSpec(FullName("C", [], [], None), [charT])
//    let (ILType.ILConstructedGenericType(_, cCharTI)) = solveTypeCore map emptyVarMap emptyVarMap cCharT
//    findMethod cCharTI "M" [intT] [charT; intT]
//
////    emit map
////    createTypes map
//end
//
//begin
//    let a = AppDomain.CurrentDomain.DefineDynamicAssembly(AssemblyName "test10", AssemblyBuilderAccess.RunAndSave)
//    let m = a.DefineDynamicModule("test10.dll")
//    let t = m.DefineType("Ty")
//
//    t.DefineGenericParameters [|"a"|] |> ignore
//
//    let tint = t.MakeGenericType([|typeof<int>|])
//    tint.GetType() |> ignore
//
//    let t2 = m.DefineType("Ty2")
//
//    t2.SetParent t
//    t2.BaseType
//end
//
//solveT typeSpecOf<int> ==? typeof<int>
//solveT typeSpecOf<Map<int,Set<string>>> ==? typeof<Map<int,Set<string>>>
//
////#r @"C:\Users\pc-2\AppData\Local\Temp\test3.dll"
//
////type abstract `->` (a, b) = abstract `_ _` a : b;;
////
////type Num a =
////    abstract ofInteger Integer : a;
////    abstract `_+_` (a, a) : a;;
////
////type #(Num Int32) <: Object, Num Int32 =
////    override ofInteger Integer : Int32 { ... };
////    override `_+_` (Int32, Int32) : Int32 { ... };;
////
////type CloSucc2 a <: (a -> a) =
////    val item1 : Num a
////    new (Num a) =
////        base()
////        ldarg.0
////        stfld CloSucc2::item
////        ret;
////
////    override `_ _` a : a =
////        ldfld CloSucc2::item
////        ldarg.0
////        ldfld CloSucc2::item
////        ldsfld bigint::One
////        callvirt Num a::ofInteger(a)
////        callvirt Num a::`_+_`
////        ret;;
////
////type CloSucc a <: (Num a -> a -> a) =
////    override `_ _` (Num a) : a -> a =
////        ldarg.0
////        newobj (CloSucc2 a) (Num a)
////        ret;;
////
////module Program =
////    fun succ a () : Num a -> a -> a = newobj (CloSucc a) () ret;;
////
////    val #(Num Int32) : Num Int32;;
////    val ten : Int32;;
////    fun init () : void =
////        newobj #(Num Int32) ()
////        stsfld Program::#(Num Int32)
////        ldc_i4 10i
////        stsfld Program::ten
////        ret;;
////
////    fun main () : void =
////        call static Program::init ()
////
////        ldsfld Program::ten
////        ldsfld Program::#(Num Int32)
////        call static Program::succ Int32 ()
////        callvirt `->`(Num Int32, Int32 -> Int32)::` `(Num Int32)
////        callvirt `->`(Int32, Int32)::` `(Int32)
////        ret;;
////;;
//let arrowT = p"->`2"
//let (..->) a b = typeRef2 arrowT a b
//let (.->) a b = type2 arrowT a b
//let numR = typeRef1 (p"Num`1")
//let numT = type1 (p"Num`1")
//let programT = type0 (p"Program")
//
//IL [
//    abstract2T "->`2" "a" "b" <| fun f a b ->
//        f None [] [abstract0 "_ _" [param "param" a] b]
//
//    type1D "Num`1" "a" <| fun f a ->
//        f None [] [
//            abstract0 "ofInteger" [paramT bigintT] a
//            abstract0 "_+_" [paramT a; paramT a] a
//        ]
//    type0D "#Num(System_Int32)" None [numR intT] [
//        override0 "ofInteger" [paramT bigintT] intT [ldc_i4 0; ret]
//        override0 "_+_" [paramT intT; paramT intT] intT [ldc_i4 0; ret]
//    ]
//
//    type1D "CloSucc2`1" "a" <| fun f a ->
//        let numAT = numT a
//        let cloSucc2AT = type1 (p"CloSucc2`1") a
//
//        f (Some(a ..-> a)) [] [
//            field "item1" numAT
//
//            // new (Num a) = base(); @item1 <- $0;
//            ctor [paramT numAT] [
//                base_init []
//                ldarg 0
//                stfld cloSucc2AT "item1"
//                ret
//            ]
//
//            // override `_ _` a : a = @item1.`_+_`($0, @item1.ofInteger(bigint::One));
//            override0 "_ _" [paramT a] a [
//                ldfld cloSucc2AT "item1"
//                ldarg 0
//                ldfld cloSucc2AT "item1"
//                ldsfld bigintT "One"
//                callvirt numAT "ofInteger" [] [a]
//                callvirt numAT "_+_" [] [a; a]
//                ret
//            ]
//        ]
////
////    type1D "CloSucc`1" "a" <| fun f a ->
////        f (Some(a ..-> (a .-> a))) [] [
////            override0 "_ _" [paramT (numT a)] (a .-> a) [
////                ldarg 0
////                newobj (type1 (p"CloSucc2`1") a) [numT a]
////                ret
////            ]
////        ]
////
////    moduleD (t"Program") [
////        fun1 "succ" "a" <| fun f a -> f [] (numT a .-> (a .-> a)) [newobj (type1 (p"CloSucc`1") a) []; ret]
////        mutD "#Num(System_Int32)" <| numT intT
////        mutD "ten" intT
////        fun0 "init" [] voidT [
////            newobj (type0 (p"#Num(System_Int32)")) []
////            stsfld programT "#Num(System_Int32)"
////            ldc_i4 10
////            stsfld programT "ten"
////            ret
////        ]
////
////        fun0 "main" [] voidT [
////            call_static programT "init" [] []
////
////            ldsfld programT "ten"
////            ldsfld programT "#Num(System_Int32)"
////            call_static programT "succ" [intT] []
////            callvirt (numT intT .-> (intT .-> intT)) "_ _" [] [numT intT]
////            callvirt (intT .-> intT) "_ _" [] [intT]
////            ret
////        ]
////    ]
//]
//|> emitDll "test" ===? ".assembly extern mscorlib
//{
//  .publickeytoken = (B7 7A 5C 56 19 34 E0 89 )
//  .ver 4:0:0:0
//}
//.assembly extern System.Numerics
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
//.class public abstract auto ansi beforefieldinit '->`2'<a,b>
//       extends [mscorlib]System.Object
//{
//  .method public hidebysig newslot abstract virtual 
//          instance !b  '_ _'(!a param) cil managed
//  {
//  }
//  .method public specialname rtspecialname 
//          instance void  .ctor() cil managed
//  {
//    .maxstack  2
//    IL_0000:  ldarg.0
//    IL_0001:  call       instance void [mscorlib]System.Object::.ctor()
//    IL_0006:  ret
//  }
//}
//.class interface public abstract auto ansi beforefieldinit Num`1<a>
//{
//  .method public hidebysig newslot abstract virtual 
//          instance !a  ofInteger(valuetype [System.Numerics]System.Numerics.BigInteger A_1) cil managed
//  {
//  }
//  .method public hidebysig newslot abstract virtual 
//          instance !a  '_+_'(!a A_1,
//                             !a A_2) cil managed
//  {
//  }
//}
//.class public auto ansi sealed beforefieldinit '#Num(System_Int32)'
//       extends [mscorlib]System.Object
//       implements class Num`1<int32>
//{
//  .method public hidebysig newslot virtual final 
//          instance int32  ofInteger(valuetype [System.Numerics]System.Numerics.BigInteger A_1) cil managed
//  {
//    .maxstack  1
//    IL_0000:  ldc.i4.0
//    IL_0001:  ret
//  }
//  .method public hidebysig newslot virtual final 
//          instance int32  '_+_'(int32 A_1,
//                                int32 A_2) cil managed
//  {
//    .maxstack  1
//    IL_0000:  ldc.i4.0
//    IL_0001:  ret
//  }
//  .method public specialname rtspecialname 
//          instance void  .ctor() cil managed
//  {
//    .maxstack  2
//    IL_0000:  ldarg.0
//    IL_0001:  call       instance void [mscorlib]System.Object::.ctor()
//    IL_0006:  ret
//  }
//}"
//
//
//let __ _ =
////    let d = TopTypeDef {
////            kind = None
////            name = t"Type"
////            typeParams = []
////            parent = typeRefOf<obj>
////            impls = []
////            members = []
////        }
////        
////    let name = "test" // sprintf "%s_%d" "test" Environment.TickCount
////    let moduleName = Path.ChangeExtension(name, ".dll")
////    let path = Path.Combine(Path.GetTempPath(), moduleName)
////
////    if File.Exists path then File.Delete path else ()
////
////    let d = AppDomain.CurrentDomain
////    let a = d.DefineDynamicAssembly(AssemblyName name, AssemblyBuilderAccess.Save)
////    let m = a.DefineDynamicModule moduleName
////    let t = m.DefineType("Type1", T.Public ||| T.Sealed ||| T.BeforeFieldInit, typeof<obj>)
////    //t.DefineField("f1", t, FieldAttributes.InitOnly ||| FieldAttributes.Public) |> ignore
////    t.CreateType() |> ignore
////
////    //if File.Exists path then File.Delete path else ()
////    a.Save moduleName
////
////    ildasm path = ".assembly extern mscorlib
////{
////  .publickeytoken = (B7 7A 5C 56 19 34 E0 89 )
////  .ver 4:0:0:0
////}
////.assembly test
////{
////  .hash algorithm 0x00008004
////  .ver 0:0:0:0
////}
////.module test.dll
////.imagebase 0x00400000
////.file alignment 0x00000200
////.stackreserve 0x00100000
////.subsystem 0x0003
////.corflags 0x00000001
////.class public auto ansi sealed beforefieldinit Type1
////       extends [mscorlib]System.Object
////{
////  .method public specialname rtspecialname 
////          instance void  .ctor() cil managed
////  {
////    .maxstack  2
////    IL_0000:  ldarg.0
////    IL_0001:  call       instance void [mscorlib]System.Object::.ctor()
////    IL_0006:  ret
////  }
////}"      |> ignore
////
////
////    let map = HashMap()
////    DefineTypes.topDef m map d
////    createTypes map
////    a.Save("test.dll")
////
////    m.GetTypes()
////
////    map.[t"Type", []]
//
//    IL [
//        TopTypeDef(t"Type", {
//            kind = None
//            typeParams = []
//            parent = None
//            impls = []
//            members = []
//        })
//    ]
//    |> emitDll "test.dll"

#r "./bin/debug/Alpa.Compiler.dll"
open Alpa.Emit
open Alpa.Emit.EmitException
open Alpa.Emit.HashMap
open Alpa.Emit.TypeSpec
open Alpa.Emit.ILEmit

let makeCloseType t ts =
    match t with
    | TypeSpec(n, ps) when List.length ps = List.length ts -> TypeSpec(n, ts)
    | _ -> failwithf "makeCloseType %A %A" t ts

let (!) = TypeVar
let typeSpec n ts = TypeSpec(FullName(n, [], [], None), ts)
let type0 n = typeSpec n []
let type1 n t1 = typeSpec n [t1]
let type2 n (t1, t2) = typeSpec n [t1;t2]

let alias n ps t = n, { aTypeParams = ps; entity = t }

let rec reduce amap visitedNames = function
    | TypeSpec(FullName(n, [], [], None), ts) as t ->
        if List.contains n visitedNames then raiseEmitExn <| RecursiveAlias n

        let mutable v = Unchecked.defaultof<_>
        if tryGet amap n &v then
            let ts = List.map (reduce amap visitedNames) ts
            reduce amap (n::visitedNames) <| applyType n v ts
        else
            t

    | TypeSpec(n, ts) -> TypeSpec(n, List.map (reduce amap visitedNames) ts)
    | t -> t

let reduceAlias amap name = reduce amap [name] (get amap name).entity

    
// alias vector `a = [mscolrib]...List`1(`a);;
// alias tuple(`a,`b) = MyTuple`2(`a,`b);;
// alias assoc(`k,`v) = vector(tuple(`k,`v))
// alias hash_map(`k,`v) = assoc(int32,assoc(`k,`v));;
//
// type MyTuple`2(`t1,`t2) = ...

// alias error1 = error1
// alias error2 `a = [mscolrib]...List`1(error2 `a)
// alias error3A `a = [mscolrib]...List`1(error3B `a)
// alias error3B `a = [mscolrib]...List`1(error3A `a)

let list = makeCloseType typeOf<ResizeArray<_>> << List.singleton
let myTuple = type2 "MyTuple`2"

let amap =
    HashMap [
        alias "vector" ["t"] <| list !"t"
        alias "tuple" ["t1";"t2"] <| myTuple(!"t1",!"t2")
        alias "assoc" ["a";"b"] <| type1 "vector" (type2 "tuple"(!"a",!"b"))
        alias "hash_map" ["k";"v"] <| type2 "assoc"(typeOf<int32>, type2 "assoc"(!"k",!"v"))

        alias "error1" [] <| type0 "error1"
        alias "error2" ["a"] <| list(type1 "error2" !"a")
        alias "error3A" ["a"] <| list(type1 "error3B" !"a")
        alias "error3B" ["a"] <| list(type1 "error3A" !"a")
    ]

reduceAlias amap "hash_map" = list(myTuple(typeOf<int32>,list(myTuple(!"k",!"v"))))

try reduceAlias amap "error1" |> ignore; false with
| EmitException(RecursiveAlias "error1") -> true
| _ -> false

try reduceAlias amap "error2" |> ignore; false with
| EmitException(RecursiveAlias "error2") -> true
| _ -> false

try reduceAlias amap "error3A" |> ignore; false with
| EmitException(RecursiveAlias "error3A") -> true
| _ -> false

try reduceAlias amap "error3B" |> ignore; false with
| EmitException(RecursiveAlias "error3B") -> true
| _ -> false