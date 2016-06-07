module ILEmit.Parser
open System
open Alpa.ParserCombinator
open Alpa.IO
open ILEmit
open ILEmit.Emit
open RegexLexer

type TokenKind =
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
    /// ":>"
    | ColonGreaterThan

    | Abstract
    | Override
    | Type
    | Open
    | Interface
    | Sealed
    | Mutable
    | Literal
    | Module
    | New
    | Let
    | Member

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

type Token = Source<TokenKind>

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

type ScanErrors =
    | IntegerOverflow

type Errors =
    | ScanError of index: int * ScanErrors option

    | RequireToken of TokenKind
    | RequireInt32Token
    | RequireLiteralToken
    | RequireIdToken
    | RequireOpToken
    | RequireTypeName
    | RequireTypeSpecifier
    | RequireName
    | RequireTypeKind
    | RequireOperand of OperandType

    | RequireTypeMember
    | RequireModuleMember
    | RequireTopMember

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
    ":>", ColonGreaterThan
|]

let keyword = [|
    "abstract", Abstract
    "override", Override
    "type", Type
    "open", Open
    "interface", Interface
    "sealed", Sealed
    "mutable", Mutable
    "literal", Literal
    "module", Module
    "new", New
    "let", Let
    "member", Member
    
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
    keyword = makeTokenOfTable "keyword" (Array.append keyword opTable)
    custom =
    [|
        makeToken "id" @"[a-zA-Z_\p{Ll}\p{Lu}\p{Lt}\p{Lo}\p{Lm}][\w`]*" Id
        makeTokenOfTable "delimiter" delimiter
        makeToken "floating" floatingR (double >> LFloat64)
        makeTokenOrError "integer" @"0[xX][0-9a-fA-F]+|[+-]?[0-9]+" (
            let format = System.Globalization.NumberFormatInfo.InvariantInfo
            fun s ->
                let integer isDecimal s style = 
                    let mutable i = 0
                    let mutable n = 0L
                    if Int32.TryParse(s, style, format, &i) then ValueOk <| LInt32(isDecimal, i)
                    elif Int64.TryParse(s, style, format, &n) then ValueOk <| LInt64(isDecimal, n)
                    else ValueError IntegerOverflow

                if 2 <= s.Length && s.[0] = '0' && (let c = s.[1] in c = 'x' || c = 'X')
                then integer true s.[2..] System.Globalization.NumberStyles.AllowHexSpecifier
                else integer false s System.Globalization.NumberStyles.AllowLeadingSign
        )
        makeToken "qstring" """("([^"\\]|\\([rntv\\"']|u[0-9a-fA-F]{4}))*")""" <| fun s ->
            let s = s.[1..s.Length-2]
            if String.forall ((<>) '\\') s then QString s
            else QString <| escape s

        makeToken "sqstring" """('([^'\\]|\\([rntv\\"']|u[0-9a-fA-F]{4}))*')""" <| fun s ->
            let s = s.[1..s.Length-2]
            if String.forall ((<>) '\\') s then SQString s
            else SQString <| escape s
    |]
}

let lex = lexer lexData

module SourceParsers =
    open RegexLexer.Source

    let manyRev1 p = pipe2 p (manyRev (p |>> value)) <| fun x xs -> map (fun x -> x::xs) x
    let many1 p = pipe2 p (many (p |>> value)) <| fun x xs -> map (fun x -> x,xs) x

    let satisfyE p e = satisfyE (value >> p) e
    let satisfyMapE p m e = satisfyMapE (value >> p) (map m) e
    let sepBy p sep = sepBy (p |>> value) (sep |>> value) |>> VirtualSource
    let sepBy1 p sep = sepBy1 (p |>> value) (sep |>> value) |>> VirtualSource
    let pipe2 p1 p2 f =
        let f = OptimizedClosures.FSharpFunc<_,_,_>.Adapt f
        pipe2 p1 p2 <| fun x1 x2 -> range x1 (f.Invoke(value x1, value x2)) x2

    let pipe3 p1 p2 p3 f =
        let f = OptimizedClosures.FSharpFunc<_,_,_,_>.Adapt f
        pipe3 p1 p2 p3 <| fun x1 x2 x3 ->
            let l = startPos x1 <<- startPos x2 <<- startPos x3
            let r = endPos x1 ->> endPos x2 ->> endPos x3
            Source l (f.Invoke(value x1, value x2, value x3)) r

    let pipe4 p1 p2 p3 p4 f =
        let f = OptimizedClosures.FSharpFunc<_,_,_,_,_>.Adapt f
        pipe4 p1 p2 p3 p4 <| fun x1 x2 x3 x4 ->
            let l = startPos x1 <<- startPos x2 <<- startPos x3 <<- startPos x4
            let r = endPos x1 ->> endPos x2 ->> endPos x3 ->> endPos x4
            Source l (f.Invoke(value x1, value x2, value x3, value x4)) r

    let pipe5(p1, p2, p3, p4, p5, f) =
        let f = OptimizedClosures.FSharpFunc<_,_,_,_,_,_>.Adapt f
        pipe5(p1, p2, p3, p4, p5, fun x1 x2 x3 x4 x5 ->
            let l = startPos x1 <<- startPos x2 <<- startPos x3 <<- startPos x4 <<- startPos x5
            let r = endPos x1 ->> endPos x2 ->> endPos x3 ->> endPos x4 ->> endPos x5
            Source l (f.Invoke(value x1, value x2, value x3, value x4, value x5)) r
        )

    let opt p = opt p |>> function None -> VirtualSource None | Some x -> map Some x
    let (|>>) p f = p |>> map f

    let optDefault defaultValue p = optDefault (VirtualSource defaultValue) p
    let optBool p = optMap (VirtualSource false) (fun x -> map (fun _ -> true) x) p

    // deriving parsers

    let (>>.) p1 p2 = pipe2 p1 p2 <| fun _ x -> x
    let (.>>.) p1 p2 = pipe2 p1 p2 <| fun x1 x2 -> x1, x2
    let between openP closeP p = pipe3 openP p closeP <| fun _ x _ -> x
    let manyRev p = opt (manyRev1 p) |>> function None -> [] | Some xs -> xs

    let choiceHead e ps = choiceHead value e ps

open SourceParsers

let (!) symbol = satisfyE ((=) symbol) <| RequireToken symbol

let tInt32 = satisfyMapE (function LInt32 _ -> true | _ -> false) (function LInt32(_,x) -> x | _ -> 0) RequireInt32Token

let tId = satisfyMapE (function Id _ -> true | _ -> false) (function Id x -> x | _ -> "") RequireIdToken

let tOp = satisfyMapE (function Op _ -> true | _ -> false) (function Op x -> x | _ -> O.Nop) RequireOpToken

/// ex: Int32, List`2, 'type'
let name =
    satisfyMapE
        (function Id _ | SQString _ -> true | _ -> false)
        (function Id v | SQString v -> v | _ -> "")
        RequireName

let typeKind =
    satisfyMapE
        (function
            | TokenKind.Abstract
            | TokenKind.Interface
            | TokenKind.Open
            | TokenKind.Sealed -> true
            | _ -> false
        )
        (function
            | TokenKind.Abstract -> TypeKind.Abstract
            | TokenKind.Interface -> TypeKind.Interface
            | TokenKind.Open -> TypeKind.Open
            | TokenKind.Sealed -> TypeKind.Sealed
            | _ -> TypeKind.Sealed
        )
        RequireTypeKind

/// ($p, ...) | ()
let tupleLike0 p = between !LParen !RParen (sepBy p !Comma)
/// ($p, ...)
let tupleLike1 p = between !LParen !RParen (sepBy1 p !Comma)
/// ($p, ...) | $p | ()
let tupleOrValueLike0 p = tupleLike0 p <|> (p |>> List.singleton)
/// ($p, ...) | $p
let tupleOrValueLike1 p = tupleLike1 p <|> (p |>> fun x -> x, [])

let assemblyName = between !LSBraket !RSBraket name
let namespaceRev = manyRev (name .>> !Dot)
let nestersRev = manyRev (name .>> !Plus)

/// ex: [mscorlib]System.Diagnostics.Stopwatch+InternalTimers+LowTimer
let fullName = pipe4 (opt assemblyName) namespaceRev nestersRev name <| fun asmName nsRev nestRev name -> FullName(name, nestRev, nsRev, asmName)

let pathRev = pipe2 namespaceRev name <| fun ns n -> n, ns

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
module Unsafe =
    module P = NativeInterop.NativePtr
    let reinterpret<'f,'t when 'f : unmanaged and 't : unmanaged> (x: 'f) =
        let p = P.stackalloc 1
        P.write p x
        P.read<'t>(P.ofNativeInt(P.toNativeInt p))

let unreachable<'a> : 'a = failwith "unreachable"

/// ex: ": int32"
let typing = !Colon >>. typeSpec

/// ex: true, null, 'a', "", 10, 10 :> int64, 0xFFFFFFFF :> float32
let literal =
    let numericValue = satisfyE (function LInt32 _ | LInt64 _ | LFloat64 _ -> true | _ -> false) RequireLiteralToken

    let numericTypeSpec =
        satisfyMapE
            (function Int8 | Int16 | Int32 | Int64 | UInt8 | UInt16 | UInt32 | UInt64 | Float32 | Float64 -> true | _ -> false)
            (function 
                | Int8 -> I1
                | Int16 -> I2
                | Int32 -> I4
                | Int64 -> I8
                | UInt8 -> U1
                | UInt16 -> U2
                | UInt32 -> U4
                | UInt64 -> U8
                | Float32 -> F4
                | Float64 -> F8
                | _ -> I1
            ) RequireTypeSpecifier

    let typing = opt numericTypeSpec

    let int32BitsToSingle x = Unsafe.reinterpret<int32,float32> x

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
        let r1 = typing xs
        if r1.Status = Primitives.Ok then
            let r2 = numericValue xs
            if r2.Status = Primitives.Ok then
                let r1 = r1.Value
                let r2 = r2.Value
                try Reply(Source.range r1 (convOrRaise (Source.value r2) (Source.value r1)) r2) 
                with :? OverflowException -> Reply((), NumericRange)

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
    
let parameter =
    (pipe2 name typing <| fun n t -> Parameter(Some n, t)) <|>
    (typeSpec |>> fun t -> Parameter(None, t))

let parameters = tupleLike0 parameter

let methodHead =
    pipe4 name (optDefault [] (typeParams true)) parameters typing <| fun name mTypeParams ps ret -> MethodHead(name, mTypeParams, ps, Parameter(None, ret))

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
    let opNone = Reply <| Source.VirtualSource OpNone
    let operand t xs =
        match t with
        | OT.InlineNone -> opNone
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
                let r3 = operand (Source.value op).OperandType xs
                if r3.Status <> Primitives.Ok then Reply((), r3.Error)
                else
                    let r1 = r1.Value
                    let r2 = r2.Value
                    let r3 = r3.Value
                    let l = Source.(<<-) (Source.(<<-) (Source.startPos r1) (Source.startPos r2)) (Source.startPos r3)
                    let r = Source.(->>) (Source.(->>) (Source.endPos r1) (Source.endPos r2)) (Source.endPos r3)

                    let instr = Instr(Source.value r1, Source.value op, Source.value  r3)
                    Reply(Source.Source l instr r)
    p

let methodBody = many1 instr |>> fun (x,xs) -> MethodBody(x::xs)
let methodInfo = pipe3 methodHead !Equals methodBody <| fun h _ b -> MethodInfo(h, b)

let fieldTail make = pipe3 (optBool !Mutable) name typing make
let literalTail make = 
    let defaultType = function
        | Literal.Null -> objectT
        | Literal.String _ -> stringT
        | Literal.Bool _ -> boolT
        | Literal.Char _ -> charT
        | Literal.F4 _ -> float32T
        | Literal.F8 _ -> float64T
        | Literal.I1 _ -> int8T
        | Literal.I2 _ -> int16T
        | Literal.I4 _ -> int32T
        | Literal.I8 _ -> int64T
        | Literal.U1 _ -> uint8T
        | Literal.U2 _ -> uint16T
        | Literal.U4 _ -> uint32T
        | Literal.U8 _ -> uint64T

    pipe4 name (opt typing) !Equals literal (fun n t _ l ->
        let t =
            match t with
            | Some t -> t
            | None -> defaultType l
        make n t l
    )

let staticMemberTail =
    choice [
        fieldTail <| fun m n t -> Field(true, m, n, t)
        literalTail <| fun a b c -> MemberDef.Literal(a, b, c)
        methodInfo |>> StaticMethodDef
    ]
let instanceMemberTail =
    choice [
        methodInfo |>> fun m -> MethodDef(None, m)
        fieldTail <| fun m n t -> Field(false, m, n, t)
    ]
let typeMember =
    choiceHead RequireTypeMember [
        Let, staticMemberTail
        Member, instanceMemberTail
        // ex: new (x: System.Int32) = ...
        New, pipe3 parameters !Equals methodBody <| fun ps _ b -> CtorDef(ps, b)
        
        // ex: abstract AddRange (T) (xs: IEmumerable`1(T)) : void
        Abstract, methodHead |>> AbstractDef

        // TODO: BaseMethod
        Override, methodInfo |>> fun m -> MethodDef(Some Override.Override, m)
    ]
let members = sepBy typeMember !Semicolon

/// ex: type open List`1 (T) <: [mscorlib]System.Object = ...
let typeDefTail name make =
    let make k n ps is ms =
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
        make n def

    pipe5 (
        opt typeKind,
        name,
        optDefault [] (typeParams false),
        opt inherits,
        !Equals >>. members,
        make
    )

let moduleModuleDefTail, moduleModuleDefTailRef = createParserForwardedToRef()

let letTail =
    fieldTail (fun m n t -> ModuleValDef(m, n, t)) <|>
    literalTail (fun n t v -> ModuleLiteralDef(n, t, v))

let moduleMember =
    choiceHead RequireModuleMember [
        Let, methodInfo |>> ModuleMethodDef
        Type, typeDefTail name <| fun n d -> ModuleTypeDef(n, d)
        Module, moduleModuleDefTail
        Let, letTail
    ]
    
let moduleMembers = sepBy moduleMember !Semicolon

moduleModuleDefTailRef := pipe4 name !Equals moduleMembers !DSemicolon <| fun n _ ms _ -> ModuleModuleDef(n, ms)

let topMember =
    choiceHead RequireTopMember [
        Type, typeDefTail pathRev <| fun n d -> TopTypeDef(n, d)
        Module, pipe3 pathRev !Equals moduleMembers <| fun n _ ms -> TopModuleDef(n, ms)
    ]

/// ex: type Ns.A =;; module B =;;
let top = sepBy topMember !DSemicolon |>> fun ds -> { topDefs = ds }
let initialState = ()

let parseWith p source =
    match lex source with
    | Error(i, e, lastT) -> Error(ScanError(i, e), lastT)
    | Ok ts ->
        let ts = Buffer.ofSeq ts
        match runWithState (p .>> eof) initialState ts with
        | Success x -> Ok <| Source.value x
        | Failure(e,_,lastT,_) -> Error(e, lastT)

let parse source = parseWith top source