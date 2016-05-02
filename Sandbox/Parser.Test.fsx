#load "./Alpa.Parser.Helpers.fsx"

open Alpa
open Alpa.IO
open Alpa.Parser
open Alpa.Parser.Helpers
open Alpa.ParserCombinator

module P = Alpa.Parser
module S = Alpa.Parser.Helpers.Syntax
module C = Alpa.Parser.Helpers.Syntax.Constants

fsi.AddPrintTransformer(box << tokenToTokenInfo)

let parse p xs =
    match CharStream.run Lexer.start xs with
    | None -> Failure(ErrorNone, -1, None, initialState)
    | Some xs -> runWithState p initialState xs
    
let test diff p xs =
    for a, b in xs do
        match parse p a with
        | Success x ->
            match diff x b with
            | Eq -> ()
            | Diff _ as d ->
                printfn "NotEq Act = %A -> %A; Exp = %A; Diff = %A" a b x d

        | Failure _ as r -> printfn "%A" r

let errorTest p xs =
    for a in xs do
        match parse p a with
        | Success x -> printfn "failure %A => %A" a x
        | Failure _ -> ()


let lex s = CharStream.run Lexer.start s |> Option.map (Buffer.toSeq >> tokenInfos s)


parse start "
module X = {
    x = ()
    y = ()
}
"

test syntaxDiff typeDefinition [
    "ValueTuple2 t1 t2 = t1, t2",
        S.abbreviationTypeDefinition (S.typeName2 !"ValueTuple2" !"t1" !"t2") (S.tupleType2 !-"t1" !-"t2")
]

test syntaxDiff moduleElements [
    "a = ()\nb = ()", S.moduleElements (S.moduleVal "a" C.unit) [S.moduleVal "b" C.unit]
]

test syntaxDiff start (
    let exp = S.anonymousModule [S.moduleVal "a" C.unit]
    let exp2 =
        S.anonymousModule [
            S.moduleFun2 "a" !@"x" !@"y" (S.apply3 !!"x" !!%"+" !!"y")
        ]
    let exp3 =
        S.anonymousModule [
            S.module' !"A" [
                S.moduleVal "a" C.unit
                S.moduleVal "b" C.unit
            ]
            S.moduleVal "x" C.unit
        ]
    [
        "module X\na = ()", S.namedModule !+"X" [S.moduleVal "a" C.unit]
        "module X\na = ()\nb = ()", S.namedModule !+"X" [S.moduleVal "a" C.unit; S.moduleVal "b" C.unit]

        "a = ()", exp
        "a\n = ()", exp
        "a =\n ()", exp

        "a x y =\n  x + y", exp2
        "a x y =\n  x +\n  y", exp2
        "a x y =\n  x\n  + y", exp2
        "a x y =\n  x\n  +\n  y", exp2
        "a x y =\n  x\n   +\n   y", exp2

        
        "module A =\n  a = ()\n  b = ()\nx = ()", exp3
        "module A = a = ()\n           b = ()\nx = ()", exp3
        "module A = { a = { () }; b = { () } }; x = ()", exp3
        "module A = {\na = ()\nb = ()\n}\nx = ()", exp3
    ]
)

test syntaxDiff expression [
    "a\nb", S.apply2 !!"a" !!"b"
    "a\n b", S.apply2 !!"a" !!"b"
]

//errorTest (Layout.fileStart >>. expression .>> eof) [
//    "  a\n  b"
//]

test syntaxDiff moduleFunctionOrValueDefinition (
    let exp = S.moduleFun2 "a" !@"x" !@"y" (S.apply2 !!"x" !!"y")
    let exp2 = S.moduleFun2 "apply" !@"f" !@"x" (S.apply2 !!"f" !!"x")
    [
        "a x y = x y", exp
        "a x y =\n  x y", exp
        "a x y =\n  x\n  y", exp
        "a x y =\n  x\n   y", exp

        "apply f x =\n  f x", exp2
        "apply f x =\n  f\n   x", exp2
        "seq unit a =\n  unit;\n  a", S.moduleFun2 "seq" !@"unit" !@"a" (S.seq !!"unit" !!"a")

        "apply2 f x y =\n  f x y", S.moduleFun3 "apply2" !@"f" !@"x" !@"y" (S.apply3 !!"f" !!"x" !!"y")
        "seqApply action x y =\n  action x;\n  y", S.moduleFun3 "seqApply" !@"action" !@"x" !@"y" (S.seq (S.apply2 !!"action" !!"x") !!"y")
        "seq2 unit1 unit2 a =\n  unit1;\n  unit2; a", S.moduleFun3 "seq2" !@"unit1" !@"unit2" !@"a" (S.seq !!"unit1" (S.seq !!"unit2" !!"a"))
        "seqApply unit f x =\n  unit;\n  f x", S.moduleFun3 "seqApply" !@"unit" !@"f" !@"x" (S.seq !!"unit" (S.apply2 !!"f" !!"x"))
    ]
)

parse start "module Alpa

type ValueTuple2 t1 t2 = (t1, t2)
type ValueTuple3 t1 t2 t3 = (t1, t2, t3)
type ValueTuple4 t1 t2 t3 t4 = (t1, t2, t3, t4)
type Slice a = (Pointer a, Int32)
type Position = (Int32, Int32, Int32)
type Symbol = String

type Special = Character
module Specials =
    ``D,`` = ','
    ``D;`` = ';'
"

lex "\n//    In = 'D'\n;"

let xs = """module Alpa

type ValueTuple2 t1 t2 = (t1, t2)
type ValueTuple3 t1 t2 t3 = (t1, t2, t3)
type ValueTuple4 t1 t2 t3 t4 = (t1, t2, t3, t4)
type Slice a = (Pointer a, Int32)
type Position = (Int32, Int32, Int32)
type Symbol = String

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

parse start xs

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
