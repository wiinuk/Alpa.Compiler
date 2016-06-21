module Alpa.IL.Lexer

open System
open Alpa.Emit
open Alpa.ParserCombinator
open Alpa.RegexLexer

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
    /// ","
    | Comma
    /// "."
    | Dot
    /// ";"
    | Semicolon
    /// "+"
    | Plus
    /// "::"
    | DColon
    /// "`"
    | GraveAccent
    /// "``"
    | DGraveAccent
    /// "->"
    | HyphenGreaterThan
    /// "*"
    | Multiply
    /// "/"
    | Slash

    | Abstract
    | Override
    | Type
    | Open
    | Interface
    | Sealed
    | Mutable
    | Literal
    | New
    | Let
    | Member
    | Static
    | Alias
    | This
    | Base
    | Module
    | Assembly
    | Import

    | Public
    | Internal
    | Protected
    | Private
    | PrivateScope
    | InternalAndProtected
    | InternalOrProtected

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
    | Blob of byte array

type Token = Source<TokenKind>
type State = {
    thisType: TypeSpec option
    baseType: TypeSpec option
    namespaceRev: string list
    nestersRev: string list
}

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
    | RequireContexualKeyword of string
    | RequireInt32Token
    | RequireLiteralToken
    | RequireIdToken
    | RequireOpToken
    | RequireBlobToken
    | RequireType
    | RequireTypeSpecifier
    | RequireName
    | RequireTypeKind
    | RequireOperand of OperandType

    | RequireTypeMember
    | RequireModuleMember
    | RequireTopMember
    | RequireAccess

    | NumericRange
    | OperandTypeMissmatch

    | UnsolvedThisType
    | UnsolvedBaseType

    | DuplicateVersion
    | DuplicatePublicKeyToken
    | DuplicateCulture

    | DuplicatedAccess
    | DuplicatedMethodKind
    | DuplicatedFieldKind

let delimiter() = [|
    "(", LParen
    ")", RParen
    "[", LSBraket
    "]", RSBraket
    ":", Colon
    "=", Equals
    ",", Comma
    ".", Dot
    ";", Semicolon
    "+", Plus
    "::", DColon
    "`", GraveAccent
    "``", DGraveAccent
    "->", HyphenGreaterThan
    "*", Multiply
    "/", Slash
|]

let keyword() = [|
    "abstract", Abstract
    "override", Override
    "type", Type
    "open", Open
    "interface", Interface
    "sealed", Sealed
    "mutable", Mutable
    "literal", Literal
    "new", New
    "let", Let
    "member", Member
    "static", Static
    "alias", Alias
    "this", This
    "base", Base
    "module", Module
    "assembly", Assembly
    "import", Import

    "public", Public
    "internal", Internal
    "protected", Protected
    "private", Private
    "private_scope", PrivateScope
    "internal_and_pretected", InternalAndProtected
    "internal_or_protected", InternalOrProtected
    "protected_and_internal", InternalAndProtected
    "protected_or_internal", InternalOrProtected

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

let opKeyword() =
    typeof<System.Reflection.Emit.OpCodes>.GetFields()
    |> Array.map (fun f ->
        let op =
            f.GetValue null
            |> unbox<System.Reflection.Emit.OpCode>
        op.Name, Op op
    )

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

let lexData() = {
    trivia = @"\s+|//[^\n]*"
    keyword = makeTokenOfTable "keyword" (Array.append (keyword()) (opKeyword()))
    custom =
    [|
        makeToken "blob" @"B""(\s*[0-9a-fA-F]{2})*\s*""" <| fun s ->
            let xs = ResizeArray()
            let rec aux i =
                if s.Length <= i then ()
                else
                    let c1 = s.[i]
                    if Char.IsWhiteSpace c1 || c1 = '"' then aux(i+1)
                    else
                        let hexToInt c = (int<char> c &&& 15) + (int c >>> 6) * 9
                        let c2 = s.[i+1]
                        let v = uint8 ((hexToInt c1 <<< 4) ||| hexToInt c2)
                        xs.Add v
                        aux(i+2)
            aux 2
            Blob <| xs.ToArray()

        makeToken "id" @"[a-zA-Z_\p{Ll}\p{Lu}\p{Lt}\p{Lo}\p{Lm}][\w`]*" Id
        makeTokenOfTable "delimiter" <| delimiter()
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

let lex = lexer <| lexData()

module SourceParsers =
    open Alpa.RegexLexer.Source
    
    let opt p = opt p |>> function None -> VirtualSource None | Some x -> map Some x
    let preturn v = preturn v |>> VirtualSource
    let manyRev1 p =
        let p1 = p |>> map (fun x -> [x])
        many1Fold p1 p <| fun xs x ->
            Source (startPos xs) (value x::value xs) (endPos x)

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

    let tuple3 p1 p2 p3 = pipe3 p1 p2 p3 <| fun x1 x2 x3 -> x1, x2, x3
    let tuple4 p1 p2 p3 p4 = pipe4 p1 p2 p3 p4 <| fun x1 x2 x3 x4 -> x1, x2, x3, x4
    let (>>%) p v = p |>> map (fun _ -> v)
    let (|>>) p f = p |>> map f
    
    let many p = opt (many1 p) |>> function None -> [] | Some(x,xs) -> x::xs
    let optDefault defaultValue p = optDefault (VirtualSource defaultValue) p
    let optBool p = optMap (VirtualSource false) (fun x -> map (fun _ -> true) x) p

    // deriving parsers

    let (>>.) p1 p2 = pipe2 p1 p2 <| fun _ x -> x
    let (.>>.) p1 p2 = pipe2 p1 p2 <| fun x1 x2 -> x1, x2
    let between openP closeP p = pipe3 openP p closeP <| fun _ x _ -> x
    let manyRev p = opt (manyRev1 p) |>> function None -> [] | Some xs -> xs

    let choiceHead e ps = choiceHead value e ps