#load "./Alpa.Parser.Helpers.fsx"

open Alpa
open Alpa.IO
open Alpa.Parser
open Alpa.Parser.Helpers
open Alpa.ParserCombinator

module P = Alpa.Parser
module S = Alpa.Parser.Helpers.Syntax

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
                printfn "NotEq Act = %A; Exp = %A; Diff = %A" b x d

        | Failure _ as r -> printfn "%A" r

let errorTest p xs =
    for a in xs do
        match parse p a with
        | Success x -> printfn "failure %A => %A" a x
        | Failure _ -> ()


let lex s = CharStream.run Lexer.start s |> Option.map (Buffer.toSeq >> tokenInfos s)


test syntaxDiff typeDefinition [
    "ValueTuple2 t1 t2 = t1, t2",
        S.abbreviationTypeDefinition (S.typeName2 !"ValueTuple2" !"t1" !"t2") (S.tupleType2 +"t1" +"t2")
]

test syntaxDiff moduleElements [
    "a = ()\nb = ()", S.moduleElements (S.moduleVal "a" S.cUnit) [S.moduleVal "b" S.cUnit]
]

do
    let a = 'a'
    let
     a = 'a'

    let a
     = 'a'

    let a =
     'a'

    let a x y =
        x
        +
        y

    let a x y =
        x
         +
          y

    let a = 'a'
    ()

test syntaxDiff start (
    let exp = S.anonymousModule [S.moduleVal "a" S.cUnit]
    [
        "module X\na = ()", S.namedModule !~"X" [S.moduleVal "a" S.cUnit]
        "module X\na = ()\nb = ()", S.namedModule !~"X" [S.moduleVal "a" S.cUnit; S.moduleVal "b" S.cUnit]

        "a = ()", exp
        "a\n = ()", exp
        "a =\n ()", exp
        "a x y =\n  x\n  +\n  y", exp
        "a x y =\n  x\n   +\n   y", exp
    ]
)

test syntaxDiff expression [
    "a\nb", S.apply2 !!"a" !!"b"
    "a\n b", S.apply2 !!"a" !!"b"
]

errorTest (Layout.fileStart >>. expression .>> eof) [
    "  a\n  b"
]

test syntaxDiff moduleFunctionOrValueDefinition (
    let exp = S.moduleFun2 "a" !@"x" !@"y" (S.apply2 !!"x" !!"y")
    [
        "a x y = x y", exp
        "a x y =\n  x y", exp
        "a x y =\n  x\n  y", exp
        "a x y =\n  x\n   y", exp
    ]
)

parse (opt (Layout.fileStart >>. anonymousModule)) "
    a = 'a'
    b = 'b'
"

parse start "
module A =
    a = ()
    b = ()
x = ()"            

parse type' "(t1, t2)"

parse typeDefinitions "type ValueTuple2 t1 t2 = (t1, t2)"

//    apply f x =
//        f x
//    
//    apply f x =
//        f
//         x
//    
//    seq unit b =
//        unit;
//        b
//
//    apply2 f x y =
//        f x y
//
//    seqApply action x y =
//        action x;
//        y
//
//    seq2 unit1 unit2 y =
//        unit1;
//        unit2;
//        y
//
//    seqApply unit f x =
//        unit;
//        f x
//
//    opApply c1 (@) c2 =
//        c1 @ c2
//
//    opApply c1 (@) c2 =
//        c1 @
//        c2
//
//    opApply c1 (@) c2 =
//        c1
//        @
//        c2
//
//    opApply c1 (@) c2 =
//        c1
//        @ c2

let e1 f x =
    f
    x

let e2 f x =
    f
    + x

let e3 f x =
    f +
    x

let
    a f
    x
    = f
        x
        x
   
// module A = a = ()
//            b = ()
// x = ()

// module A = { a = (); b = () }; x = ()

// module A = {
// a = ();
// b = ()
// };
// x = ()

parse longIdentifier "a.b.c"

parse start "module Alpa

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