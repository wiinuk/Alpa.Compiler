module Alpa.Parser.Helpers

#load "./Alpa.Parser.Operator.fsx"

open Alpa
open Alpa.IO
open Alpa.Token
open FSharp.Reflection
open System
open System.Collections
open System.Reflection

type T = FSharpType
type V = FSharpValue

type Diff = Eq | Diff of path: string * Type * obj * obj

let untypeSeqToObjSeq (xs: IEnumerable) = seq {
    let e = xs.GetEnumerator()
    while e.MoveNext() do yield e.Current
}

/// Unit, List<'T>, Record, Union, Tuple, Exception
let fsValueDiff eqDelegate (l: 'a) (r: 'a) =
    let rec eqs ts ps ls rs =
        let xs = Seq.zip3 ts ps (Seq.zip ls rs)
        use e = xs.GetEnumerator()
        let rec aux _ =
            if e.MoveNext() then
                let t,p,(l,r) = e.Current
                match eq t p l r with
                | Eq -> aux()
                | x -> x
            else Eq
        aux()

    and eqsP ts ls rs path = eqs (Seq.map (fun (p: PropertyInfo) -> p.PropertyType) ts) (ts |> Seq.map (fun p -> sprintf "%s.%s" path p.Name)) ls rs
    and eqsM fs vs t l r = eqsP (fs(t, true) |> Array.toSeq) (vs(l, true) |> Array.toSeq) (vs(r, true) |> Array.toSeq)
    and eq t path l r =
        match eqDelegate path t l r with
        | Some x -> x
        | None ->
            if t = typeof<unit> then Eq
            elif t.IsGenericType && t.GetGenericTypeDefinition() = typedefof<list<_>> then listEq t path l r
            elif T.IsRecord(t, true) then eqsM T.GetRecordFields V.GetRecordFields t l r path
            elif T.IsUnion(t, true) then unionEq t path l r
            elif T.IsTuple t then
                let ps = Seq.initInfinite <| fun i -> sprintf "%s.%d" path i
                eqs (T.GetTupleElements t) ps (V.GetTupleFields l) (V.GetTupleFields r)

            elif T.IsExceptionRepresentation(t, true) then eqsM T.GetExceptionFields V.GetExceptionFields t l r path
            else
                // Unchecked.equals l r
                failwith "unionEq"
        
    and listEq t path l r =
        let t' = t.GetGenericArguments().[0]
        let ts = Seq.initInfinite <| fun _ -> t'
        let ps = Seq.initInfinite <| fun i -> sprintf "%s.[%d]" path i
        let ls, rs = untypeSeqToObjSeq(unbox<_> l), untypeSeqToObjSeq(unbox<_> r)
        let ll, rl = Seq.length ls, Seq.length rs
        let minl = min ll rl
        if ll <> rl then Diff(sprintf "%s.Length.[%d..]" path minl, t, l, r)
        else eqs ts ps ls rs

    and unionEq t path l r =
        let lu, ls = V.GetUnionFields(l, t, true)
        let ru, rs = V.GetUnionFields(r, t, true)
        if lu.Tag <> ru.Tag then Diff(path, t, l, r)
        else eqsP (lu.GetFields()) ls rs path

    eq typeof<'a> "x" l r

let tokenValueEq l r =
    if l.Kind <> r.Kind then false
    else
        match l.Kind with
        | TokenKind.D
        | TokenKind.Rid
        | TokenKind.Rop -> l._value = r._value
        | TokenKind.I ->
            match l._value2, r._value2 with
            | null, null -> l._value = r._value
            | null, _ | _, null -> false
            | l, r -> unbox<bigint> l = unbox<bigint> r

        | TokenKind.F ->
            match l._value2, r._value2 with
            | null, null -> l._value = r._value
            | null, _ | _, null -> false
            | l, r ->
                
                // ??? normalization
                unbox<bigint * bigint * bigint> l = unbox<bigint * bigint * bigint> r

        | TokenKind.C -> l._value = r._value

        | TokenKind.S
        | TokenKind.Id
        | TokenKind.Qid
        | TokenKind.Op
        | TokenKind.Qop -> unbox<Symbol> l._value2 = unbox<Symbol> r._value2

let syntaxDiff l r =
    let eq = Some Eq
    let eq path t l r =
        if t = typeof<Token> then
            let l = unbox<Token> l
            let r = unbox<Token> r
            if tokenValueEq l r then eq else Some <| Diff(path, t, l, r)
        else None

    fsValueDiff eq l r

type Character = C16 of char | C32 of int<c32>
type Delimiter =
    | Comma
    | Semicolon
    | LeftSquareBracket
    | RightSquareBracket
    | LeftCurlyBracket
    | RightCurlyBracket
    | LeftParenthesis
    | RightParenthesis

type ReceivedOp =
    | EqualsSign
    | FullStop
    | Colon
    | VerticalLine

    | RightwardsArrow
    | LeftwardsArrow
    | TwoDotLeader
    | Proportion
    | HorizontalEllipsis
    
type ReceivedId =
    | I_

    | Alias
    | Case
    | Class
//    | In
    | Type
    | With
    | Import
    | Module
    | For
    | Where
    | Let

type TokenInfo =
    | D of Delimiter
    | Rid of ReceivedId
    | Rop of ReceivedOp
    | Id of Symbol
    | Qid of Symbol
    | Op of Symbol
    | Qop of Symbol
    | I of bigint
    | F of bigint * bigint * bigint
    | C of Character
    | S of Symbol

let tokenToTokenInfo t =
    let special t = LanguagePrimitives.EnumOfValue<_,Special> (char t._value)
    let toDelimiter = function
        | Special.``D(`` -> LeftParenthesis
        | Special.``D)`` -> RightParenthesis
        | Special.``D,`` -> Comma
        | Special.``D;`` -> Semicolon
        | Special.``D[`` -> LeftSquareBracket
        | Special.``D]`` -> RightSquareBracket
        | Special.``D{`` -> LeftCurlyBracket
        | Special.``D}`` -> RightCurlyBracket
        | _ -> failwith "toDelimiter"

    let toReceivedId = function
        | Special.Alias -> Alias
        | Special.Case -> Case
        | Special.Class -> Class
        | Special.For -> For
        | Special.I_ -> I_
        | Special.Import -> Import
        | Special.Let -> Let
        | Special.Module -> Module
        | Special.Type -> Type
        | Special.Where -> Where
        | Special.With -> With
        | _ -> failwith "toReceivedId"

    let toReceivedOp = function
        | Special.``O=`` -> EqualsSign
        | Special.``O.`` -> FullStop
        | Special.``O:`` -> Colon
        | Special.``O|`` -> VerticalLine

        | Special.``O->`` -> RightwardsArrow
        | Special.``O<-`` -> LeftwardsArrow
        | Special.``O..`` -> TwoDotLeader
        | Special.``O::`` -> Proportion
        | Special.``O...`` -> HorizontalEllipsis
        | _ -> failwith "toReceivedOp"

    match t.Kind with
    | TokenKind.D -> D(toDelimiter <| special t)
    | TokenKind.Rid -> Rid(toReceivedId <| special t)
    | TokenKind.Rop -> Rop(toReceivedOp <| special t)
    | TokenKind.C ->
        let c = t._value * 1<_>
        let c = if CharStream.needSurrogatePair c then C32 c else C16(char t._value)
        C c

    | TokenKind.I -> match t._value2 with :? bigint as x -> I x | _ -> I(bigint t._value)
    | TokenKind.F -> match t._value2 with :? (bigint * bigint * bigint) as x -> F x | _ -> F(bigint t._value, 0I, 0I)
    | TokenKind.Id -> Id(unbox<Symbol> t._value2)
    | TokenKind.Qid -> Qid(unbox<Symbol> t._value2)
    | TokenKind.Op -> Op(unbox<Symbol> t._value2)
    | TokenKind.Qop -> Qop(unbox<Symbol> t._value2)
    | TokenKind.S -> S(unbox<Symbol> t._value2)
    
let tokenInfo (source: string) t =
    let i1, i2 = range t
    kind t, source.[int<int<_>> i1 .. int<int<_>>i2 - 1]

let tokenInfos source rs = Seq.map (tokenInfo source) rs

module Token =
    let zero = {
        TriviaStart = Position()
        Start = Position()
        Kind = TokenKind.I
        _value = 0
        _value2 = null
        End = Position()
    }
    let ident n = { zero with Kind = TokenKind.Id; _value2 = box<Symbol> n }
    let op n = { zero with Kind = TokenKind.Op; _value2 = box<Symbol> n }
    let rop s = { zero with Kind = TokenKind.Rop; _value = int <| LanguagePrimitives.EnumToValue<Special,_> s }
    let delim s = { zero with Kind = TokenKind.D; _value = int <| LanguagePrimitives.EnumToValue<Special,_> s }
    let rid s = { zero with Kind = TokenKind.Rid; _value = int <| LanguagePrimitives.EnumToValue<Special,_> s }
    let ``d=`` = rop Special.``O=``
    let ``,`` = delim Special.``D,``
    let ``;`` = delim Special.``D;``
    let ``module`` = rid Special.Module
    let ``{`` = delim Special.``D{``
    let ``}`` = delim Special.``D}``
    let ``(`` = delim Special.``D(``
    let ``)`` = delim Special.``D)``

let (!) id = Name <| Token.ident id
let (!%) op = Name <| Token.op op
let (~+) var = LongIdentifier([], var)
let (!+) id = + !id
let (!+%) op = + !%op

let (!-) n = NamedType(!+n, [])
let (!-%) n = NamedType(!+%n, [])

let (!!) id = LookupExpression !+id
let (!!%) op = LookupExpression !+%op
let (!@) id = LongIdentifierPattern !+id
let (!@%) op = LongIdentifierPattern !+%op

module Syntax =
    module Constants =
        let unit = ConstantExpression(UnitConstant(Token.``(``, Token.``)``))

    // -- TypeName --

    let typeName name args = TypeName(name, Seq.map TypeArgument args |> Seq.toList)
    let typeName2 name arg1 arg2 = typeName name [arg1; arg2]
    

    // -- Type --

    let tupleType t1 t2 ts = TupleType(t1, Token.``,``, t2, Seq.map (fun t -> Token.``,``, t) ts |> Seq.toList)
    let tupleType2 t1 t2 = tupleType t1 t2 []


    // -- TypeDefinition --

    let abbreviationTypeDefinition typeName type' = AbbreviationTypeDefinition(typeName, Token.``d=``, type')


    // -- Expression --

    let applicationsExpression kind e1 e2 es = ApplicationsExpression(kind, e1, e2, Seq.toList es)
    let apply2 e1 e2 = applicationsExpression IdentifierApply e1 e2 []
    let apply3 e1 e2 e3 = applicationsExpression IdentifierApply e1 e2 [e3]
    let seq' e1 e2 = SequentialExpression(e1, Token.``;``, e2)    
    let infixL l op r = applicationsExpression InfixLeftApply op l [r]
    let infixN l op r = applicationsExpression InfixNoneApply op l [r]
    let infixR l op r = applicationsExpression InfixRightApply op l [r]
    let prefix op e = applicationsExpression PrefixApply op e []
    let postfix e op = applicationsExpression PostfixApply op e []


    // -- ModuleElement --

    let module' name es =
        let es =
            match Seq.tryHead es with
            | None -> None
            | Some e ->
                let es = Seq.tail es
                Some(e, Seq.map (fun e -> Token.``;``, e) es |> Seq.toList)

        ModuleDefinition(Token.``module``, name, Token.``d=``, Token.``{``, es, Token.``}``)

    let moduleLetElement name pats body = ModuleLetElement(LetHeader(!name, pats), Token.``d=``, Token.``{``, body, Token.``}``)
    let moduleVal name body = moduleLetElement name [] body
    let moduleFun2 name pat1 pat2 body = moduleLetElement name [pat1; pat2] body
    let moduleFun3 name pat1 pat2 pat3 body = moduleLetElement name [pat1; pat2; pat3] body


    // -- ImplementationFile --
    let moduleElements e es = e, Seq.map (fun e -> Token.``;``, e) es |> Seq.toList

    let anonymousModule = function
        | [] -> None
        | e::es -> AnonymousModule(moduleElements e es) |> Some    

    let namedModule name = function
        | [] -> None
        | e::es -> NamedModule(Token.``module``, name, moduleElements e es) |> Some