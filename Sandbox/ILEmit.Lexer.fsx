module ILEmit.Lexer
#load "ILEmit.fsx"
open System
open Alpa.ParserCombinator
open Alpa.IO
open ILEmit
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

open SourceParsers
