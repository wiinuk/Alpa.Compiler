module ILEmit.Parser
#load "RegexLexer.fsx"
#load "ILEmit.fsx"
#r "./bin/debug/Alpa.Compiler.dll"
open System
open Alpa.ParserCombinator
open Alpa.IO
open ILEmit
open RegexLexer

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
    | Colon
    /// "="
    | Equals
    /// "!"
    | Bang
    /// ","
    | Comma
    /// "."
    | Dot
    /// ";"
    | Semicolon
    /// "+"
    | Plus
    /// "!!"
    | DBang
    /// "::"
    | DColon
    /// ";;"
    | DSemicolon
    /// "<:"
    | LessThanColon

    | Abstract
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
    | New

    | Int8
    | Int16
    | Int32
    | Int64
    | UInt8
    | UInt16
    | UInt32
    | UInt64
    | Float32
    | Float64

    | Void
    | Bool
    | Char
    | String
    | Object

    | Null
    | True
    | False

    | Op of System.Reflection.Emit.OpCode

    | Id of string

    | LInt32 of isDecimal: bool * int32
    | LInt64 of isDecimal: bool * int64
    | LFloat64 of double
    | QString of string
    | SQString of string
    
type PrimNumericTypes =
    | I1
    | I2
    | I4
    | I8
    | U1
    | U2
    | U4
    | U8
    | F4
    | F8

type OperandType =
    | OpNumericType of PrimNumericTypes
    | OpStringType

type Errors =
    | ScanError of index: int

    | RequireToken of token
    | RequireInt32Token
    | RequireLiteralToken
    | RequireIdToken
    | RequireOpToken
    | RequireTypeName
    | RequireTypeSpecifier
    | RequireName
    | RequireTypeKind
    | RequireOperand of OperandType

    | NumericRange
    | OperandTypeMissmatch

let ops =
    typeof<System.Reflection.Emit.OpCodes>.GetFields()
    |> Array.map (fun f -> f.GetValue null |> unbox<System.Reflection.Emit.OpCode>)

let delimiter = [|
    "(", LParen
    ")", RParen
    "[", LSBraket
    "]", RSBraket
    ":", Colon
    "=", Equals
    "!", Bang
    ",", Comma
    ".", Dot
    ";", Semicolon
    "+", Plus
    "!!", DBang
    "::", DColon
    ";;", DSemicolon
    "<:", LessThanColon
|]

let keyword = [|
    "abstract", Abstract
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
    "new", New
    
    "int8", Int8
    "int16", Int16
    "int32", Int32
    "int64", Int64
    "uint8", UInt8
    "uint16", UInt16
    "uint32", UInt32
    "uint64", UInt64
    "float32", Float32
    "float64", Float64

    "void", Void
    "bool", Bool
    "char", Char
    "string", String
    "object", Object

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
    trivia = @"\s+|//[^\n]*"
    keyword = table "keyword" (Array.append keyword opTable)
    custom =
    [|
        custom "id" @"[a-zA-Z_\p{Ll}\p{Lu}\p{Lt}\p{Lo}\p{Lm}][\w`]*" Id
        table "delimiter" delimiter
        custom "floating" floatingR (double >> LFloat64)

        custom "integer" @"0[xX][0-9a-fA-F]+|[+-]?[0-9]+" (
            let format = System.Globalization.NumberFormatInfo.InvariantInfo
            fun s ->
                let integer isDecimal s style = 
                    let mutable i = 0
                    if Int32.TryParse(s, style, format, &i) then LInt32(isDecimal, i)
                    else LInt64(isDecimal, Int64.Parse(s, style))

                if 2 <= s.Length && s.[0] = '0' && (let c = s.[1] in c = 'x' || c = 'X')
                then integer true s.[2..] System.Globalization.NumberStyles.AllowHexSpecifier
                else integer false s System.Globalization.NumberStyles.AllowLeadingSign
        )
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

let (!) symbol = satisfyE ((=) symbol) <| RequireToken symbol

let tInt32 = satisfyMapE (function LInt32 _ -> true | _ -> false) (function LInt32(_,x) -> x | _ -> 0) RequireInt32Token

let tId = satisfyMapE (function Id _ -> true | _ -> false) (function Id x -> x | _ -> "") RequireIdToken

let tOp = satisfyMapE (function Op _ -> true | _ -> false) (function Op x -> x | _ -> Unchecked.defaultof<_>) RequireOpToken

/// ex: Int32, List`2, 'type'
let name =
    satisfyMapE
        (function Id _ | SQString _ -> true | _ -> false)
        (function Id v | SQString v -> v | _ -> "")
        RequireName

let typeKind =
    satisfyMapE
        (function
            | token.Abstract
            | token.Interface
            | token.Open
            | token.Sealed -> true
            | _ -> false
        )
        (function
            | token.Abstract -> TypeKind.Abstract
            | token.Interface -> TypeKind.Interface
            | token.Open -> TypeKind.Open
            | token.Sealed -> TypeKind.Sealed
            | _ -> TypeKind.Sealed
        )
        RequireTypeKind

/// ($p, ...) | ()
let tupleLike0 p = !LParen >>. sepBy p !Comma .>> !RParen
/// ($p, ...)
let tupleLike1 p = !LParen >>. sepBy1 p !Comma .>> !RParen
/// ($p, ...) | $p | ()
let tupleOrValueLike0 p = tupleLike0 p <|> (p |>> List.singleton)
/// ($p, ...) | $p
let tupleOrValueLike1 p = tupleLike1 p <|> (p |>> fun x -> x, [])

let assemblyName = !LSBraket >>. name .>> !RSBraket
let namespaceRev = manyRev (name .>> !Dot)
let nestersRev = manyRev (name .>> !Plus)

/// ex: [mscorlib]System.Diagnostics.Stopwatch+InternalTimers+LowTimer
let fullName = pipe4 (opt assemblyName) namespaceRev nestersRev name <| fun asmName nsRev nestRev name -> FullName(name, nestRev, nsRev, asmName)

open PreDefinedTypes
let preDefinedTypeName =
    satisfyMapE
        (function 
            | Int8
            | Int16
            | Int32
            | Int64
            | UInt8
            | UInt16
            | UInt32
            | UInt64
            | Float32
            | Float64

            | Void
            | Bool
            | Char
            | String
            | Object -> true
            | _ -> false
        )
        (function
            | Int8 -> int8T
            | Int16 -> int16T
            | Int32 -> int32T
            | Int64 -> int64T
            | UInt8 -> uint8T
            | UInt16 -> uint16T
            | UInt32 -> uint32T
            | UInt64 -> uint64T
            | Float32 -> float32T
            | Float64 -> float64T

            | Void -> voidT
            | Bool -> boolT
            | Char -> charT
            | String -> stringT
            | Object -> objectT
            | _ -> voidT
        )
        RequireTypeName

/// ex: (T1), (T1, T2)
let typeParams _ = tupleLike1 name |>> function x,xs -> x::xs

/// ex: "[mscorlib]System.Diagnostics.Stopwatch+Internals+LowTimer`1(T)" "!T" "!0" "!!2"
let typeSpec, typeSpecRef = createParserForwardedToRef()
do
    typeSpecRef := 
        choice [
            preDefinedTypeName
            pipe2 fullName (opt (tupleOrValueLike1 typeSpec)) <| fun n vs -> TypeSpec(n, match vs with None -> [] | Some(v,vs) -> v::vs)
            !Bang >>. tId |>> TypeVar
            !DBang >>. tId |>> MethodTypeVar
            !Bang >>. tInt32 |>> TypeArgRef
            !DBang >>. tInt32 |>> MethodTypeArgRef
        ]

let inherits = !LessThanColon >>. tupleOrValueLike1 typeSpec

#nowarn "9"
let reinterpret<'f,'t when 'f : unmanaged and 't : unmanaged> (x: 'f) =
    let p = NativeInterop.NativePtr.stackalloc 1
    NativeInterop.NativePtr.write p x
    NativeInterop.NativePtr.read<'t>(NativeInterop.NativePtr.ofNativeInt(NativeInterop.NativePtr.toNativeInt p))

let unreachable<'a> : 'a = failwith "unreachable"

let toNumericType = function
    | "i1" -> I1
    | "i2" -> I2
    | "i4" -> I4
    | "i8" -> I8
    | "u1" -> U1
    | "u2" -> U2
    | "u4" -> U4
    | "u8" -> U8
    | "f4" -> F4
    | "f8" -> F8
    | _ -> unreachable
    
/// ex: true, null, 'a', "", 10, 10:i8, 3.14159:f4
let literal =
    let numericValue = satisfyE (function LInt32 _ | LInt64 _ | LFloat64 _ -> true | _ -> false) RequireLiteralToken
    let numericTypeName =
        satisfyMapE
            (function Id("i1"|"i2"|"i4"|"i8"|"u1"|"u2"|"u4"|"u8"|"f4"|"f8") -> true | _ -> false) 
            (function Id s -> toNumericType s |> Some | _ -> None)
            RequireTypeSpecifier
    
    let numericTypeSpecifier = optDefault None (!Colon >>. numericTypeName)

    let int32BitsToSingle x = reinterpret<int32,float32> x

    let convInt32OrRaise isDecimal n = function
        | None -> Literal.I4 n
        | Some t ->
            match t with
            | I1 -> Literal.I1 <| Checked.int8 n
            | I2 -> Literal.I2 <| Checked.int16 n
            | I4 -> Literal.I4 n
            | I8 -> Literal.I8 <| int64 n
            | U1 -> Literal.U1 <| Checked.uint8 n
            | U2 -> Literal.U2 <| Checked.uint16 n
            | U4 -> if isDecimal then Literal.U4 <| Checked.uint32 n else Literal.U4 <| uint32 n
            | U8 -> if isDecimal then Literal.U8 <| Checked.uint64 n else Literal.U8 <| uint64 (uint32 n)

            | F4 -> if isDecimal then raise <| OverflowException() else Literal.F4 <| int32BitsToSingle n
            | F8 -> if isDecimal then raise <| OverflowException() else Literal.F8 <| BitConverter.Int64BitsToDouble(int64 (uint32 n))

    let convInt64OrRaise isDecimal n = function
        | None -> Literal.I8 n
        | Some t ->
            match t with
            | I1 -> Literal.I1 <| Checked.int8 n
            | I2 -> Literal.I2 <| Checked.int16 n
            | I4 -> Literal.I4 <| Checked.int32 n
            | I8 -> Literal.I8 n
            | U1 -> Literal.U1 <| Checked.uint8 n
            | U2 -> Literal.U2 <| Checked.uint16 n
            | U4 -> Literal.U4 <| Checked.uint32 n
            | U8 -> if isDecimal then Literal.U8 <| Checked.uint64 n else Literal.U8 <| uint64 n

            | F4 -> if isDecimal then raise <| OverflowException() else Literal.F4 <| int32BitsToSingle(Checked.int32 n)
            | F8 -> if isDecimal then raise <| OverflowException() else Literal.F8 <| BitConverter.Int64BitsToDouble n

    let convOrRaise v t =
        match v with
        | LInt32(isDecimal, n) -> convInt32OrRaise isDecimal n t
        | LInt64(isDecimal, n) -> convInt64OrRaise isDecimal n t
        | LFloat64 v ->
            match t with
            | None
            | Some F8 -> Literal.F8 v
            | Some F4 -> Literal.F4 <| single v
            | _ -> raise <| OverflowException()

        | _ -> unreachable

    let numericLiteral xs =
        let r1 = numericValue xs
        if r1.Status = Primitives.Ok then
            let r2 = numericTypeSpecifier xs
            if r2.Status = Primitives.Ok then
                try Reply(convOrRaise r1.Value r2.Value) with
                | :? OverflowException -> Reply((), NumericRange)

            else Reply((), r2.Error)
        else Reply((), r1.Error)

    let simpleLiteral =
        satisfyMapE
            (function 
                | QString _ | True | False | Null -> true
                | SQString v -> v.Length = 1
                | _ -> false
            )
            (function
                | QString x -> Literal.String x
                | SQString x -> Literal.Char x.[0]
                | True -> Literal.Bool true
                | False -> Literal.Bool false
                | Null -> Literal.Null
                | _ -> Literal.Null
            )
            RequireLiteralToken

    simpleLiteral <|> numericLiteral


let literalDef = pipe5(!Val, name, typeSpec, !Equals, literal, fun _ n t _ v -> MemberDef.Literal(n, t, v))

let fieldDef = pipe5(!Val, optBool !Static, optBool !Mutable, name, typeSpec, fun _ s m n t -> Field(s, m, n, t))

let parameter =
    (pipe3 name !Colon typeSpec <| fun n _ t -> Parameter(Some n, t)) <|>
    (typeSpec |>> fun t -> Parameter(None, t))

let parameters = tupleLike0 parameter

let methodHead =
    let ret = !Colon >>. typeSpec
    pipe4 name (optDefault [] (typeParams true)) parameters ret <| fun name mTypeParams ps ret -> MethodHead(name, mTypeParams, ps, Parameter(None, ret))

/// ex: abstract AddRange (T) (xs: IEmumerable(T)) : System.Void
let abstractDef = !Abstract >>. methodHead |>> AbstractDef

type OT = System.Reflection.Emit.OperandType

let opInteger t min max ofInt64 =
    satisfyMapE
        (function 
            | LInt32(_,x) -> min <= int64 x && int64 x <= max
            | LInt64(_,x) -> min <= x && x <= max
            | _ -> false
        )
        (function
            | LInt32(_,x) -> ofInt64(int64 x)
            | LInt64(_,x) -> ofInt64 x
            | _ -> OpNone
        )
        (RequireOperand(OpNumericType t))

let opI1 = opInteger I1 (int64 SByte.MinValue) (int64 SByte.MaxValue) (OpI1 << int8)
let opI2 = opInteger I2 (int64 Int16.MinValue) (int64 Int16.MaxValue) (OpI2 << int16)
let opI4 = opInteger I4 (int64 Int32.MinValue) (int64 Int32.MaxValue) (OpI4 << int32)
let opI8 =
    satisfyMapE
        (function LInt32 _ | LInt64 _ -> true | _ -> false)
        (function LInt32(_,x) -> OpI8 <| int64 x | LInt64(_,x) -> OpI8 x | _ -> OpNone)
        (RequireOperand(OpNumericType I8))

let opF4 =
    satisfyMapE
        (function LFloat64 _ -> true | _ -> false)
        (function LFloat64 x -> OpF4(single x) | _ -> OpNone)
        (RequireOperand(OpNumericType F4))

let opF8 =
    satisfyMapE
        (function LFloat64 _ -> true | _ -> false)
        (function LFloat64 x -> OpF8 x | _ -> OpNone)
        (RequireOperand(OpNumericType F8))

let opString =
    satisfyMapE
        (function QString _ -> true | _ -> false)
        (function QString x -> OpString x | _ -> OpNone)
        (RequireOperand OpStringType)

let opType = typeSpec |>> OpType

/// ex: System.Type::Delimiter
let opField = pipe3 typeSpec !DColon name <| fun t _ n -> OpField(t, n)

/// ex: System.Tuple`2(string, char)(!0, !1)
let opCtor = pipe2 typeSpec (tupleLike0 typeSpec) <| fun t args -> OpCtor(t, args)

let opMethod =
    let make parent _ name ts1 ts2 =
        match ts2 with
        | None -> OpMethod(parent, name, [], ts1)
        | Some ts2 -> OpMethod(parent, name, ts1, ts2)
    
    pipe5(typeSpec, !DColon, name, tupleLike0 typeSpec, opt (tupleLike0 typeSpec), make)

let opMethodBase = opMethod <|> opCtor
let instr =
    let label = optDefault "" (tId .>> !Colon)
    let operand t xs =
        match t with
        | OT.InlineNone -> Reply OpNone
        | OT.ShortInlineI -> opI1 xs
        | OT.ShortInlineVar -> opI1 xs
        | OT.InlineVar -> opI2 xs
        | OT.InlineI -> opI4 xs
        | OT.InlineI8 -> opI8 xs
        | OT.ShortInlineR -> opF4 xs
        | OT.InlineR -> opF8 xs
        | OT.InlineString -> opString xs
        | OT.InlineType -> opType xs
        | OT.InlineField -> opField xs
        | OT.InlineMethod -> opMethodBase xs

        | OT.InlineBrTarget
        | OT.ShortInlineBrTarget
        | OT.InlineSwitch
        | OT.InlineSig
        | OT.InlineTok
        | _ -> failwithf "not implemented"

    let p xs =
        let r1 = label xs
        if r1.Status <> Primitives.Ok then Reply((), r1.Error)
        else
            let r2 = tOp xs
            if r2.Status <> Primitives.Ok then Reply((), r2.Error)
            else
                let op = r2.Value
                let r3 = operand op.OperandType xs
                if r3.Status <> Primitives.Ok then Reply((), r3.Error)
                else
                    Reply(Instr(r1.Value, op, r3.Value))
    p

let methodBody = many1 instr |>> fun (x,xs) -> MethodBody(x::xs)
let methodInfo = pipe3 methodHead !Equals methodBody <| fun h _ b -> MethodInfo(h, b)

/// ex: new (x: System.Int32) = ...
let ctorDef = pipe4 !New parameters !Equals methodBody <| fun _ ps _ b -> CtorDef(ps, b)

let methodDef =
    choice [
        pipe2 !Override methodInfo <| fun _ m -> MethodDef(Some Override.Override, m)
        // TODO: BaseMethod
        pipe3 !Fun (optBool !Static) methodInfo <| fun _ isStatic m ->
            if isStatic then StaticMethodDef m
            else MethodDef(None, m)
    ]

let typeMember =
    choice [
        literalDef
        fieldDef
        abstractDef
        ctorDef
        methodDef
    ]
let members = sepBy typeMember !Semicolon

/// ex: type open List`1 (T) <: [mscorlib]System.Object = ...
let typeDef ctor =
    let make _ k n ps (is, ms) =
        let parent, impls =
            match is with
            | None -> None, []
            | Some(x, xs) -> Some x, xs

        let def = {
            kind = k
            typeParams = ps
            parent = parent
            impls = impls
            members = ms
        }
        ctor(n, def)

    pipe5 (!Type, opt typeKind, name, optDefault [] (typeParams false), (opt inherits .>>. (!Equals >>. members)), make)

let moduleModuleDef, moduleDefRef = createParserForwardedToRef()
let moduleMember =
    choice [
        !Fun >>. methodInfo |>> ModuleMethodDef
        typeDef ModuleTypeDef
        moduleModuleDef
        pipe5(!Val, optBool !Mutable, name, !Colon, typeSpec, fun _ m n _ t -> ModuleValDef(m, n, t))
        pipe5(!Val, name, !Colon, typeSpec, (!Equals >>. literal), fun _ n _ t l -> ModuleLiteralDef(n, t, l))
    ]
    
let moduleMembers = sepBy moduleMember !Semicolon

moduleDefRef := pipe5(!Module, name, !Equals, moduleMembers, !DSemicolon, fun _ n _ ms _ -> ModuleModuleDef(n, ms))

let topModuleDef = pipe4 !Module name !Equals moduleMembers <| fun _ n _ ms -> TopModuleDef(n, ms)

/// ex: type A =;; module B =;;
let top = sepBy (typeDef TopTypeDef <|> topModuleDef) !DSemicolon |>> fun ds -> { topDefs = ds }
let initialState = ()

let parseWith p source =
    match lex source with
    | Error i -> Error(ScanError i, None)
    | Ok ts ->
        let ts = Buffer.ofSeq ts
        match runWithState (p .>> eof) initialState ts with
        | Success x -> Ok x
        | Failure(e,_,lastT,_) -> Error(e, lastT)

let parse source = parseWith top source