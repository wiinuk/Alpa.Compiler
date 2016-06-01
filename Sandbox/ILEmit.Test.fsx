module internal ILEmit.Test
#load "ILEmit.Helpers.fsx"
open ILEmit
open ILEmit.Helpers
open ILEmit.Helpers.SimpleInstructions

let intT = typeSpecOf<int>
let voidT = typeOfT typeof<System.Void>
let bigintT = typeSpecOf<bigint>

type R = System.Text.RegularExpressions.Regex
let lexTrivia = R @"\s+|//[^\n]*|/\*.*?\*/"

type Custom<'t,'r> = Custom of name: string * regex: 'r * (string -> 't)
type LexData<'t,'r> = {
    trivia: 'r
    keyword: Custom<'t,'r>
    custom: Custom<'t,'r> array
}
let custom n r f = Custom(n, r, f)
let table name table =
    let concat pred sep table =
        Seq.filter (fst >> pred) table
        |> Seq.map (fst >> System.Text.RegularExpressions.Regex.Escape)
        |> String.concat sep

    let chars = concat (String.length >> (=) 1) "" table
    let strings = concat (String.length >> (<>) 1) "|" table

    let regex = if String.length chars = 0 then strings else "[" + chars + "]|" + strings
    let map = System.Collections.Generic.Dictionary()
    for k, v in table do map.Add(k, v)

    custom name regex <| fun t -> map.[t]
    
open System.Text.RegularExpressions

let compile { trivia = trivia; keyword = keyword; custom = custom } =
    let r p = Regex(p, RegexOptions.Compiled)
    let customR (Custom(n, p, f)) = Custom(n, r p, f)
    {
        trivia = r trivia
        keyword = customR keyword
        custom = Array.map customR custom
    }
type Result<'T,'E> = Ok of 'T | Error of 'E
let lexer data =
    let {
        trivia = trivia
        keyword = keyword 
        custom = custom
        } = compile data

    fun source ->
        let scanR (r: Regex) source i =
            let m = r.Match(source, i)
            if m.Success && m.Index = i then i + m.Length
            else -1
            
        let rs = ResizeArray()
        let mutable errorIndex = -1

        let scanC (Custom(n, r: Regex, f)) source i =
            let m = r.Match(source, i)
            if m.Success && m.Index = i then
                rs.Add(f m.Value)
                i + m.Length
            else -1

        let rec skipTrivias i = match scanR trivia source i with -1 -> i | i -> skipTrivias i
        
        let rec scanToken i customI customs =
            if customI = Array.length customs then -1
            else
                match scanC customs.[customI] source i with
                | -1 -> scanToken i (customI + 1) customs
                | i' ->
                    match scanC keyword source i with
                    | -1 -> i'
                    | i'' when i' <= i'' -> rs.RemoveAt(rs.Count-2); i''
                    | _ -> rs.RemoveAt(rs.Count-1); i'

        let rec scan i =
            let i = skipTrivias i
            if String.length source <= i then Ok <| rs.ToArray()
            else
                let i = scanToken i 0 custom
                if i = -1 then Error errorIndex
                else scan i
        scan 0

type token =
    /// "("
    | LParen
    /// ")"
    | RParen
    /// "["
    | LSBraket
    /// "]"
    | RSBraket
    /// ":"
    | Coron
    /// "="
    | Equals
    /// "/"
    | Slash
    /// "!"
    | Bang
    /// ","
    | Comma
    /// "."
    | Dot
    /// ";"
    | SemiCoron
    /// "+"
    | Plus
    /// "!!"
    | DoubleBang
    /// "::"
    | DoubleCoron
    /// ";;"
    | DoubleSemiCoron
    /// "<:"
    | LessThanCoron
    /// "->"
    | HyphenGreaterThan

    | Abstract
    | Export
    | Fun
    | Override
    | Type
    | Static
    | Val
    | Open
    | Interface
    | Sealed
    | Mutable
    | Literal
    | Module

    | Null
    | True
    | False

    | Op of System.Reflection.Emit.OpCode

    | Id of string

    | Int32 of int32
    | Int64 of int64
    | Float64 of double
    | QString of string
    | SQString of string

let ops =
    typeof<System.Reflection.Emit.OpCodes>.GetFields()
    |> Array.map (fun f -> f.GetValue null |> unbox<System.Reflection.Emit.OpCode>)

let delimiter = [|
    "(", LParen
    ")", RParen
    "[", LSBraket
    "]", RSBraket
    ":", Coron
    "=", Equals
    "/", Slash
    "!", Bang
    ",", Comma
    ".", Dot
    ";", SemiCoron
    "+", Plus
    "!!", DoubleBang
    "::", DoubleCoron
    ";;", DoubleSemiCoron
    "<:", LessThanCoron
    "->", HyphenGreaterThan
|]

let keyword = [|
    "abstract", Abstract
    "export", Export
    "fun", Fun
    "override", Override
    "type", Type
    "static", Static
    "val", Val
    "open", Open
    "interface", Interface
    "sealed", Sealed
    "mutable", Mutable
    "literal", Literal
    "module", Module
    
    "null", Null
    "true", True
    "false", False
|]

//| Bool of bool
//    | I1 of int8
//    | U1 of uint8
//    | I2 of int16
//    | U2 of uint16
//    | I4 of int32
//    | U4 of uint32
//    | I8 of int64
//    | U8 of uint64
//    | F4 of single
//    | F8 of double
//    | Char of char
//    | String of string

let opTable = [| for op in ops -> op.Name, Op op |]

let floatingR = 
    let e = "[eE][+-]?[0-9]+"
    @"(([0-9]*\.[0-9]+|[0-9]+\.)(" + e + ")?)|([0-9]+" + e + ")"

let escape s =
    let hex2int c = (int c &&& 15) + (int c >>> 6) * 9
    let rec aux ret = function
        | '\\'::'u'::c1::c2::c3::c4::cs ->
            let c = (hex2int c1 <<< 12) ||| (hex2int c2 <<< 8) ||| (hex2int c3 <<< 4) ||| hex2int c4
            aux (char c::ret) cs

        | '\\'::c::cs ->
            let c =
                match c with
                | 'r' -> '\r'
                | 'n' -> '\n'
                | 't' -> '\t'
                | 'v' -> '\v'
                | c -> c
            aux (c::ret) cs

        | c::cs -> aux (c::ret) cs
        | [] -> List.rev ret

    Seq.toList s |> aux [] |> List.toArray |> System.String

let lexData = {
    trivia = @"\s+|//[^\n]"
    keyword = table "keyword" (Array.append keyword opTable)
    custom =
    [|
        custom "id" @"[a-zA-Z_\p{Ll}\p{Lu}\p{Lt}\p{Lo}\p{Lm}][\w`]*" Id
        table "delimiter" delimiter
        custom "integer" @"0[xX][0-9a-fA-F]+|[+-]?[0-9]+" <| fun s ->
            let integer s style = 
                let mutable i = 0
                if System.Int32.TryParse(s, style, null, &i) then Int32 i
                else Int64 <| System.Int64.Parse(s, style)

            if 2 <= s.Length && s.[0] = '0' && s.[1] = 'x'
            then integer s.[2..] System.Globalization.NumberStyles.AllowHexSpecifier
            else integer s System.Globalization.NumberStyles.None

        custom "floating" floatingR (double >> Float64)
        custom "qstring" """("([^"\\]|\\([rntv\\"']|u[0-9a-fA-F]{4}))*")""" <| fun s ->
            let s = s.[1..s.Length-2]
            if String.forall ((<>) '\\') s then QString s
            else QString <| escape s

        custom "sqstring" """('([^'\\]|\\([rntv\\"']|u[0-9a-fA-F]{4}))*')""" <| fun s ->
            let s = s.[1..s.Length-2]
            if String.forall ((<>) '\\') s then SQString s
            else SQString <| escape s
    |]
}

let lex = lexer lexData

let findOp name = Array.find (fst >> (=) name) opTable |> snd

lex "0xff" = Ok [| Int32 255 |]
lex "type" = Ok [| token.Type |]
lex "typeof" = Ok [| Id "typeof" |]
lex "ldc" = Ok [| Id "ldc" |]
lex "ldc.i4" = Ok [| findOp "ldc.i4" |]
lex "ldc.i4.0" = Ok [| findOp "ldc.i4.0" |]
lex "''" = Ok [| SQString "" |]
lex "'\\t\\'\\u0061'" = Ok [| SQString "\t'a" |]

type Stream<'a> = {
    items: 'a array
    mutable current: int
}
let opt p ({ current = i } as xs) =
    let init = i
    match p xs with
    | Ok x -> Ok <| Some x
    | Error _ ->
        xs.current <- init
        Ok None

let manyRev p xs =
    let rec aux rs =
        let { current = init } = xs
        match p xs with
        | Ok r -> aux (r::rs)
        | Error _ ->
            xs.current <- init
            Ok rs
    aux []

let sepBy1Rev p sep xs =
    match p xs with
    | Error e -> Error e
    | Ok r ->
        let rec aux rs =
            let { current = init } = xs
            match sep xs with
            | Error _ ->
                xs.current <- init
                Ok rs

            | Ok _ ->
                match p xs with
                | Error e ->
                    xs.current <- init
                    Ok rs

                | Ok r -> aux (r::rs)
        aux [r]

let (|>>) p f xs =
    match p xs with
    | Ok x -> Ok <| f x
    | Error e -> Error e

let sepBy1 p sep = sepBy1Rev p sep |>> List.rev

let sepBy p sep = opt (sepBy1 p sep) |>> function None -> [] | Some xs -> xs
let (<|>) p1 p2 ({ current = init } as xs) =
    match p1 xs with
    | Error _ ->
        xs.current <- init
        p2 xs

    | r -> r
    
type ParseErrors<'e> =
    | UserError of 'e
    | RequireEos

let satisfyE e pred =
    let e = Error <| UserError e
    fun { items = items; current = i } ->
        if items.Length <= i then e
        else
            let x = items.[i]
            if pred x then Ok x
            else e

let chooseE e chooser =
    let e = UserError e
    fun { items = items; current = i } ->
        if items.Length <= i then Error e
        else
            let x = items.[i]
            match chooser x with
            | Some x -> Ok x
            | None -> Error e

let (.>>.) p1 p2 xs =
    match p1 xs with
    | Error e -> Error e
    | Ok x1 ->
        match p2 xs with
        | Error e -> Error e
        | Ok x2 -> Ok(x1, x2)

let pipe2 p1 p2 f =
    let f = OptimizedClosures.FSharpFunc<_,_,_>.Adapt f
    fun xs ->
        match p1 xs with
        | Error e -> Error e
        | Ok x1 ->
            match p2 xs with
            | Error e -> Error e
            | Ok x2 -> Ok <| f.Invoke(x1, x2)

let pipe3 p1 p2 p3 f =
    let f = OptimizedClosures.FSharpFunc<_,_,_,_>.Adapt f
    fun xs ->
        match p1 xs with
        | Error e -> Error e
        | Ok x1 ->
            match p2 xs with
            | Error e -> Error e
            | Ok x2 ->
                match p3 xs with
                | Error e -> Error e
                | Ok x3 -> Ok <| f.Invoke(x1, x2, x3)

let pipe5 p1 p2 p3 p4 p5 f =
    let f = OptimizedClosures.FSharpFunc<_,_,_,_,_,_>.Adapt f
    fun xs ->
        match p1 xs with
        | Error e -> Error e
        | Ok x1 ->
            match p2 xs with
            | Error e -> Error e
            | Ok x2 ->
                match p3 xs with
                | Error e -> Error e
                | Ok x3 ->
                    match p4 xs with
                    | Error e -> Error e
                    | Ok x4 ->
                        match p5 xs with
                        | Error e -> Error e
                        | Ok x5 -> Ok <| f.Invoke(x1, x2, x3, x4, x5)

let (.>>) p1 p2 xs =
    match p1 xs with
    | Ok _ as r ->
        match p2 xs with
        | Ok _ -> r
        | Error e -> Error e
    | e -> e

let (>>.) p1 p2 xs =
    match p1 xs with
    | Ok _ -> p2 xs
    | Error e -> Error e

let (>>%) p v xs =
    match p xs with
    | Ok _ -> Ok v
    | Error e -> Error e

let eos { items = items; current = i } =
    if items.Length <= i then Ok()
    else Error RequireEos

let createParserForwardedToRef() =
    let p = ref <| fun xs -> failwith "uninitialized"
    (fun xs -> (!p) xs), p

type Errors =
    | RequireToken of token
    | RequireName
    | RequireTypeKind

let (!) symbol = satisfyE (RequireToken symbol) (fun t -> t = symbol)

/// ex: Int32, List`2, 'type', (->)
let name =
    chooseE RequireName (function Id v | SQString v -> Some v | _ -> None) <|>
    (!LParen .>> !HyphenGreaterThan .>> !RParen >>% "->`2")

let typeKind = chooseE RequireTypeKind <| function 
    | token.Abstract
    | token.Interface
    | token.Open
    | token.Sealed as t ->
        match t with
        | token.Abstract -> TypeKind.Abstract
        | token.Interface -> TypeKind.Interface
        | token.Open -> TypeKind.Open
        | token.Sealed -> TypeKind.Sealed
        | _ -> failwith "unreach"
        |> Some
    | _ -> None

/// ($p, ...)
let tupleLike p = !LParen >>. sepBy p !Comma .>> !RParen
let tupleOrValueLike p = tupleLike p <|> (p |>> List.singleton)
typeof<System.Environment.SpecialFolderOption>.FullName
let assemblyName = !LSBraket >>. name .>> !RSBraket
let namespaceRev = sepBy1Rev name !Dot
let nestersRev = manyRev (!Plus >>. name)
let fullName = pipe3 (opt assemblyName) namespaceRev nestersRev <| fun asmName nsRev nestRev ->
    match nsRev, nestRev with
    | [], [] -> failwith "unreach"
    | [], name::nest -> FullName(name, nest, [], asmName)
    | ns::nsRev, name::nest -> FullName(name, nest @ [ns], nsRev, asmName)
    | name::nsRev, [] -> FullName(name, [], nsRev, asmName)

let typeParams = tupleOrValueLike name >>= fun xs ->
    updateEnv (fun vars -> for x in xs do vars.Add(x, newTypeVar x))

let typeSpec, typeSpecRef = createParserForwardedToRef()
do
    let typeSpec = 
        choice [
            pipe2 fullName (tupleOrValueLike typeSpec) <| fun n vs -> TypeSpec(n, vs)
            pipe2
        ]
    typeSpecRef := typeSpec

let inherits = tupleLike typeSpec <|> (typeSpec |>> List.singleton)

/// ex: type open List`1 (T) = ...
let topTypeDef = pipe5 !Type (opt typeKind) name (opt typeParams) (opt inherits .>>. (!Equals >>. members)) <| fun _ k n ps (is, ms) -> TopTypeDef(n, t)

/// ex: type A =;; module B =;;
let top = sepBy (topTypeDef <|> topModuleDef) !DoubleCoron .>> eos

ResizeArray().ConvertAll()


//let findMethod { mmap = mmap; varMap = varMap; typeArgs = typeArgs } name mTypeArgs argTypes = substTypeArgs varMap typeArgs <| fun _ ->
//    get mmap name
//    |> List.find (function
//        | { mVarMap = TypeVarMap(mTypeParams,_) as mVarMap; m = MethodInfo(MethodHead(pars = pars), _)
//            } ->
//            List.length pars = List.length argTypes &&
//            List.length mTypeParams = List.length mTypeArgs &&
//            substTypeArgs mVarMap mTypeArgs <| fun _ ->
//                List.forall2
//                    (fun (Parameter(_,parType)) argType -> typeSpecEq parType argType)
//                    pars
//                    argTypes
//    )
//    |> fun mi -> { mi with mTypeArgs = mTypeArgs }

//    match solveTypeCore map varMap mVarMap t with
//    | SType t -> t.GetConstructor(B.Public ||| B.NonPublic, null, solveTypes map varMap mVarMap ts, null)
//
//    | SBuilderType { mmap = parentMMap } -> findMethod ts parentMMap
//
//    | SBuilderGeneric(t, genericDef, genericParams) -> failwith "Not implemented yet"
//    | STypeVar(_, _) -> failwith "Not implemented yet"

// class Make`1<int32>::Tuple<string>(!0, !!0)

    // Builder::GetMethod is not implemented

        // type C =
        //     fun M (a) (a): a = ...;
        //     fun M () (string): string = ...;;
        //
        // getMethod C "M" () (string)
        // getMethod C "M" (string) (string)
        // getMethod C "M" (string) (!!0)

    // type Make`1 (T1) =
    //     fun Tuple (T2) (T1, T2) : Tuple(T1, T2) = ...;
    //
    // call Make`1(int32)::Tuple (string) (!0, !!0)

    // type C`1(T) =
    //     fun M () (T) : T = ...;
    //     fun M () (List(T)) : List T = ...;
    //     fun M () (string) : string = ...;
    //
    // call C`1(string)::M () (string) => ok "fun M () (string) : string = ...;"
    // call C`1(string)::M () (!0) => ok "fun M () (!0) : !0 = ...;"
    //
    // [T,List(a)]
    // fun Main(a) () = call C`1(List(a))::() (List(a)) => ok
    // fun Main(a) () = call C`1(a)::() (a) => ok


// call class [mscorlib]System.Tuple`2<!0, !!0> class Make`1<int32>::Tuple<string>(!0, !!0)
let (==?) act exp = 
    if act <> exp then printfn "(==?) {act = %A; exp = %A}" act exp
    else printfn "ok"

let (===?) act exp = fst act ==? exp

let emptyTypeMap = HashMap()
let solveT = solveType emptyTypeMap emptyVarMap  emptyVarMap

open System
open System.Reflection
open System.Reflection.Emit

// type C (a) = fun M (b) (a, b) : b
//
// call C(char)::M (int) (char, int)
// call C(char)::M (int) (char, char) // invalid
// call C(char)::M (int) (int, char) // invalid
// call C(char)::M (int) (int, int) // invalid
//
// call C(char)::M (char) (char, char)
// call C(char)::M (char) (int, char) // invalid
// call C(char)::M (char) (char, int) // invalid
// call C(char)::M (char) (int, int) // invalid
begin
    let ds = [
        type1D "C" "a" <| fun f a ->
            f None [] [
                method1 "M" "b" <| fun f b -> f [paramT a; paramT b] b [ldarg 1; ret]
            ]
    ]
    let name = "test1"
    let a = AppDomain.CurrentDomain.DefineDynamicAssembly(AssemblyName name, AssemblyBuilderAccess.RunAndSave)
    let m = a.DefineDynamicModule(name + ".dll")

    let map = HashMap()
    for d in ds do DefineTypes.topDef m map d
    defineTypeParams map
    defineMembers map

    let charT = typeSpecOf<char>
    let cCharT = TypeSpec(FullName("C", [], [], None), [charT])
    let (ILType.ILConstructedGenericType(_, cCharTI)) = solveTypeCore map emptyVarMap emptyVarMap cCharT
    findMethod cCharTI "M" [intT] [charT; intT]

//    emit map
//    createTypes map
end

begin
    let a = AppDomain.CurrentDomain.DefineDynamicAssembly(AssemblyName "test10", AssemblyBuilderAccess.RunAndSave)
    let m = a.DefineDynamicModule("test10.dll")
    let t = m.DefineType("Ty")

    t.DefineGenericParameters [|"a"|] |> ignore

    let tint = t.MakeGenericType([|typeof<int>|])
    tint.GetType() |> ignore

    let t2 = m.DefineType("Ty2")

    t2.SetParent t
    t2.BaseType
end

solveT typeSpecOf<int> ==? typeof<int>
solveT typeSpecOf<Map<int,Set<string>>> ==? typeof<Map<int,Set<string>>>

IL [
    type0D "EqualsInt" None [typeRefOf<System.IEquatable<int>>] [
        override0 "Equals" [paramT intT] typeSpecOf<bool> [ldc_i4 1; ret]
    ]
]
|> emitDll "test3" ===? ".assembly extern mscorlib
{
  .publickeytoken = (B7 7A 5C 56 19 34 E0 89 )
  .ver 4:0:0:0
}
.assembly test3
{
  .hash algorithm 0x00008004
  .ver 0:0:0:0
}
.module test3.dll
.imagebase 0x00400000
.file alignment 0x00000200
.stackreserve 0x00100000
.subsystem 0x0003
.corflags 0x00000001
.class public auto ansi sealed beforefieldinit EqualsInt
       extends [mscorlib]System.Object
       implements class [mscorlib]System.IEquatable`1<int32>
{
  .method public hidebysig newslot virtual final 
          instance bool  Equals(int32 A_1) cil managed
  {
    .maxstack  1
    IL_0000:  ldc.i4.1
    IL_0001:  ret
  }
  .method public specialname rtspecialname 
          instance void  .ctor() cil managed
  {
    .maxstack  2
    IL_0000:  ldarg.0
    IL_0001:  call       instance void [mscorlib]System.Object::.ctor()
    IL_0006:  ret
  }
}"

//#r @"C:\Users\pc-2\AppData\Local\Temp\test3.dll"

//type abstract `->` (a, b) = abstract `_ _` a : b;;
//
//type Num a =
//    abstract ofInteger Integer : a;
//    abstract `_+_` (a, a) : a;;
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
        f None [] [abstract0 "_ _" [param "param" a] b]

    type1D "Num`1" "a" <| fun f a ->
        f None [] [
            abstract0 "ofInteger" [paramT bigintT] a
            abstract0 "_+_" [paramT a; paramT a] a
        ]
    type0D "#Num(System_Int32)" None [numR intT] [
        override0 "ofInteger" [paramT bigintT] intT [ldc_i4 0; ret]
        override0 "_+_" [paramT intT; paramT intT] intT [ldc_i4 0; ret]
    ]

    type1D "CloSucc2`1" "a" <| fun f a ->
        let numAT = numT a
        let cloSucc2AT = type1 (p"CloSucc2`1") a

        f (Some(a ..-> a)) [] [
            field "item1" numAT

            // new (Num a) = base(); @item1 <- $0;
            ctor [paramT numAT] [
                base_init []
                ldarg 0
                stfld cloSucc2AT "item1"
                ret
            ]

            // override `_ _` a : a = @item1.`_+_`($0, @item1.ofInteger(bigint::One));
            override0 "_ _" [paramT a] a [
                ldfld cloSucc2AT "item1"
                ldarg 0
                ldfld cloSucc2AT "item1"
                ldsfld bigintT "One"
                callvirt numAT "ofInteger" [] [a]
                callvirt numAT "_+_" [] [a; a]
                ret
            ]
        ]
//
//    type1D "CloSucc`1" "a" <| fun f a ->
//        f (Some(a ..-> (a .-> a))) [] [
//            override0 "_ _" [paramT (numT a)] (a .-> a) [
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
          instance !b  '_ _'(!a param) cil managed
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
}
.class public auto ansi sealed beforefieldinit '#Num(System_Int32)'
       extends [mscorlib]System.Object
       implements class Num`1<int32>
{
  .method public hidebysig newslot virtual final 
          instance int32  ofInteger(valuetype [System.Numerics]System.Numerics.BigInteger A_1) cil managed
  {
    .maxstack  1
    IL_0000:  ldc.i4.0
    IL_0001:  ret
  }
  .method public hidebysig newslot virtual final 
          instance int32  '_+_'(int32 A_1,
                                int32 A_2) cil managed
  {
    .maxstack  1
    IL_0000:  ldc.i4.0
    IL_0001:  ret
  }
  .method public specialname rtspecialname 
          instance void  .ctor() cil managed
  {
    .maxstack  2
    IL_0000:  ldarg.0
    IL_0001:  call       instance void [mscorlib]System.Object::.ctor()
    IL_0006:  ret
  }
}"


let __ _ =
//    let d = TopTypeDef {
//            kind = None
//            name = t"Type"
//            typeParams = []
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
            typeParams = []
            parent = None
            impls = []
            members = []
        })
    ]
    |> emitDll "test.dll"