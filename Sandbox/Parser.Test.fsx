#load "./Alpa.Parser.fsx"

open Alpa
open Alpa.IO
open Alpa.Parser
open Alpa.ParserCombinator

let run p xs =
    match CharStream.run Lexer.start xs with
    | None -> Failure(ErrorNone, -1, None, initialState)
    | Some xs -> runWithState p initialState xs
    
let test p xs =
    for a, b in xs do
        match run p a with
        | Success x when x = b -> ()
        | e -> failwithf "%A" e
    printfn "ok"

    
open Alpa.Token
let tokenInfo (source: string) t =
    let i1, i2 = range t
    kind t, source.[int<int<_>> i1 .. int<int<_>>i2 - 1]

let tokenInfos source rs = Seq.map (tokenInfo source) rs

let lex s = CharStream.run Lexer.start s |> Option.map (Buffer.toSeq >> tokenInfos s)

let v n = {
    TriviaStart = Position()
    Start = Position()
    Kind = Id
    _value = 0
    _value2 = box<Symbol> n
    End = Position()
}
let rop s = {
    TriviaStart = Position()
    Start = Position()
    Kind = Rop
    _value = int <| LanguagePrimitives.EnumToValue s
    _value2 = null
    End = Position()
}
let delim s = {
    TriviaStart = Position()
    Start = Position()
    Kind = D
    _value = int <| LanguagePrimitives.EnumToValue s
    _value2 = null
    End = Position()
}
let ``d=`` = rop Special.``O=``
let ``,`` = delim Special.``D,``

open FSharp.Reflection
type T = FSharpType
type V = FSharpValue

/// Unit, List<'T>, Record, Union, Tuple, Exception
let fsValueEq eqDelegate (l: 'a) (r: 'a) =
    let rec eqs ts ls rs = Seq.zip3 ts ls rs |> Seq.forall (fun (t, l, r) -> eq t l r)
    and eqsP ts = eqs <| Seq.map (fun (p: System.Reflection.PropertyInfo) -> p.PropertyType) ts
    and eqsM fs vs t l r = eqsP (fs(t, true)) (vs(l, true)) (vs(r, true))
    and eq t l r =
        match eqDelegate t l r with
        | Some x -> x
        | None ->
            if t = typeof<unit> then true
            elif t.IsGenericType && t.GetGenericTypeDefinition() = typedefof<list<_>> then
                let t' = t.GetGenericArguments().[0]
                let l = unbox<System.Collections.IStructuralEquatable> l
                let r = unbox<System.Collections.IStructuralEquatable> r
                let c = {
                    new System.Collections.IEqualityComparer with
                        override __.Equals(l', r') = eq t' l' r'
                        override __.GetHashCode _ = failwith ""
                }
                l.Equals(r, c)

            elif T.IsRecord(t, true) then eqsM T.GetRecordFields V.GetRecordFields t l r
            elif T.IsUnion(t, true) then unionEq t l r
            elif T.IsTuple t then  eqs (T.GetTupleElements t) (V.GetTupleFields l) (V.GetTupleFields r)
            elif T.IsExceptionRepresentation(t, true) then eqsM T.GetExceptionFields V.GetExceptionFields t l r
            else
                // Unchecked.equals l r
                failwith "unionEq"
        
    and unionEq t l r =
        let lu, ls = V.GetUnionFields(l, t, true)
        let ru, rs = V.GetUnionFields(r, t, true)
        lu.Tag = ru.Tag && eqsP (lu.GetFields()) ls rs

    eq typeof<'a> l r

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

let syntaxEq l r =
    let false' = Some false
    let true' = Some true
    let eq t l r =
        if t = typeof<Token> then
            let l = unbox<Token> l
            let r = unbox<Token> r
            if tokenValueEq l r then true' else false'
        else None

    fsValueEq eq l r

let simpleType n = NamedType(LongIdentifier([], v n), [])

type TokenInfo =
    | D of Special
    | Rid of Special
    | Rop of Special
    | Id of Symbol
    | Qid of Symbol
    | Op of Symbol
    | Qop of Symbol
    | I of bigint
    | F of bigint * bigint * bigint
    | C of int<c32>
    | S of Symbol

let tokenToTokenInfo t =
    match t.Kind with
    | TokenKind.D -> D(LanguagePrimitives.EnumOfValue (char t._value))
    | TokenKind.Rid -> Rid(LanguagePrimitives.EnumOfValue (char t._value))
    | TokenKind.Rop -> Rop(LanguagePrimitives.EnumOfValue (char t._value))
    | TokenKind.C -> C(t._value * 1<_>)
    | TokenKind.I -> match t._value2 with :? bigint as x -> I x | _ -> I(bigint t._value)
    | TokenKind.F -> match t._value2 with :? (bigint * bigint * bigint) as x -> F x | _ -> F(bigint t._value, 0I, 0I)
    | TokenKind.Id -> Id(unbox<Symbol> t._value2)
    | TokenKind.Qid -> Qid(unbox<Symbol> t._value2)
    | TokenKind.Op -> Op(unbox<Symbol> t._value2)
    | TokenKind.Qop -> Qop(unbox<Symbol> t._value2)
    | TokenKind.S -> S(unbox<Symbol> t._value2)

fsi.AddPrintTransformer(box << tokenToTokenInfo)

let l = AbbreviationTypeDefinition(TypeName(v"ValueTuple2", [TypeArgument(v"t1"); TypeArgument(v"t2")]), ``d=``, TupleType(simpleType "t1", ``,``, simpleType "t2", []))
let (Success r) = run typeDefinition "ValueTuple2 t1 t2 = t1, t2"

run type' "(t1, t2)"

run typeDefinitions "type ValueTuple2 t1 t2 = (t1, t2)"

syntaxEq (TypeArgument(v"t1")) (let (Success r) = run typar "t1" in r)

syntaxEq l r

run start "
module A =
    a = ()
    b = ()
x = ()"
                
// module A = a = ()
//            b = ()
// x = ()

// module A = { a = (); b = () }; x = ()

// module A = {
// a = ();
// b = ()
// };
// x = ()

run longIdentifier "a.b.c"

run start "module Alpa

type ValueTuple2 t1 t2 = (t1, t2)
type ValueTuple3 t1 t2 t3 = (t1, t2, t3)
type ValueTuple4 t1 t2 t3 t4 = (t1, t2, t3, t4)
type Slice a = (Pointer a, Int32)
type Position = (Int32, Int32, Int32)
type Symbol = string

type Special = Character
module Specials =
	``D,`` = ','
	``D;`` = ';'
"

let xs = """module Alpa

type ValueTuple2 t1 t2 = (t1, t2)
type ValueTuple3 t1 t2 t3 = (t1, t2, t3)
type ValueTuple4 t1 t2 t3 t4 = (t1, t2, t3, t4)
type Slice a = (Pointer a, Int32)
type Position = (Int32, Int32, Int32)
type Symbol = string

type Special = Character
module Specials =
	``D,`` = ','
	``D;`` = ';'
	``D[`` = '['
	``D]`` = ']'
	``D{`` = '{'
	``D}`` = '}'
	``D(`` = '('
	``D)`` = ')'

	``O=`` = '='
	``O.`` = '.'
	``O:`` = ':'
	``O|`` = '|'

	``O->`` = 'a'
	``O<-`` = 'b'
	``O..`` = 'c'
	``O::`` = 'g'
	``O...`` = 'i'
    
	I_ = '_'

	Alias = 'A'
	Case = 'B'
	Class = 'C'
//    In = 'D'
	Type = 'E'
	With = 'F'
	Import = 'G'
	Module = 'H'
	For = 'I'
	Where = 'J'
	Let = 'K'"""

run start xs

//let path0 = many (attempt (Parser.identifier .>> Delimiters.``.``))
//run path0 "a.b. "
//
//let longIdentifier = path0 .>>.? Parser.identifier 
//run longIdentifier "a.b. "
//
//let p = Parser.identifier >>. many longIdentifier
//run p "a a.b = -10"
//
//let path0 = many (Parser.identifier .>>? Delimiters.``.``)
//let longIdentifier = tuple2 path0 Parser.identifier
//run longIdentifier "a"
//
//run letHeader "a = 10"
//
//let letDefinition = letHeader .>>? Delimiters.``d=`` .>>. expression
//run letDefinition "a = 10"
//run start "a = 10"