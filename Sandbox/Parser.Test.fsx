#load "./Alpa.Parser.Helpers.fsx"

open Alpa
open Alpa.IO
open Alpa.Parser
open Alpa.ParserCombinator
open Alpa.Parser.Operator
open Alpa.Parser.Helpers

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
        "seq unit a =\n  unit;\n  a", S.moduleFun2 "seq" !@"unit" !@"a" (S.seq' !!"unit" !!"a")

        "apply2 f x y =\n  f x y", S.moduleFun3 "apply2" !@"f" !@"x" !@"y" (S.apply3 !!"f" !!"x" !!"y")
        "seqApply action x y =\n  action x;\n  y", S.moduleFun3 "seqApply" !@"action" !@"x" !@"y" (S.seq' (S.apply2 !!"action" !!"x") !!"y")
        "seq2 unit1 unit2 a =\n  unit1;\n  unit2; a", S.moduleFun3 "seq2" !@"unit1" !@"unit2" !@"a" (S.seq' (S.seq' !!"unit1" !!"unit2") !!"a")
        "seqApply unit f x =\n  unit;\n  f x", S.moduleFun3 "seqApply" !@"unit" !@"f" !@"x" (S.seq' !!"unit" (S.apply2 !!"f" !!"x"))
    ]
)

parse start "

infixl 100 |>
x |> f = f x

f a b c =
    a
        |> b
        |> c
"

parse (Specials.``type`` >>. (choice [abbreviationTypeDefinition; emptyTypeDefinition])) "type Int32"

let xs = """module Alpa

type ``(,)`` t1 t2 = ``(,)`` t1 t2
type ``(,,)`` t1 t2 t3 = ``(,,)`` t1 t2 t3
type ``(,,,)`` t1 t2 t3 t4 = ``(,,,)`` t1 t2 t3 t4
type Int32
type Character
type String

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

// typing

// let (Success(Some file)) = parse start xs

    
// <haskell>
// prec,    left assoc,                 non assoc,                      right assoc
// 9,       (!!),                       (),                             (.)
// 8,       (),                         (),                             (^ ^^ **)
// 7,       (* / div mod rem quot),     (),                             ()
// 6,       (+ -),                      (),                             ()
// 5,       (),                         (),                             (: ++)
// 4,       (),                         (== /= < <= > >= elem notElem), ()
// 3,       (),                         (),                             (&&)
// 2,       (),                         (),                             (||)
// 1,       (>> >>=),                   (),                             ()
// 0,       (),                         (),                             ($ $! seq)
//
// <f#>
// prec,    left assoc,                 non assoc,                      right assoc
// 9,       (),                         (),                             (**#)
// 8,       (*# /# %#),                 (),                             ()
// 7,       (+# -#),                    (),                             ()
// 6,       (),                         (),                             (::)
// 5,       (),                         (),                             (^#)
// 4,       (&&& !!! ^^^ ~~~ <<< >>>),  (),                             ()
// 3,       (<# ># = |# &#),            (),                             ()
// 2,       (& &&),                     (),                             ()
// 1,       (||),                       (),                             ()
// 0,       (),                         (),                             (:=)

let env =
    let makeEnv = List.map (fun (n,op) -> [n], op) >> Env.make
    makeEnv [
        "a", None
        "b", None
        "c", None
        "d", None
        "e", None
        "f", None

        "**", Some(Infix, Right, 80)

        "*", Some(Infix, Left, 70)
        "===", Some(Infix, NonAssoc, 70)
        "***", Some(Infix, Right, 70)
        
        "+", Some(Infix, Left, 60)

        "==", Some(Infix, NonAssoc, 40)

        "!", Some(Prefix, NonAssoc, 0)
        "-", Some(Prefix, NonAssoc, 0)

        "++", Some(Postfix, NonAssoc, 0)
        "--", Some(Postfix, NonAssoc, 0)
    ]

let a, b, c, d, e = !!"a", !!"b", !!"c", !!"d", !!"e"

let (.+), (.*), (.-), (.**), (.***) = !!%"+", !!%"*", !!%"-", !!%"**", !!%"***"
let (@!), (.++), (.--) = !!%"!", !!%"++", !!%"--"
let (.==), (.===) = !!%"==", !!%"==="

let (+.) l r = l @ (.+)::r

let (.+.) l r = S.infix l (.+) r
let (.*.) l r = S.infix l (.*) r
let (.**.) l r = S.infix l (.**) r
let (.***.) l r = S.infix l (.***) r
let (.==.) l r = S.infix l (.==) r
let (.===.) l r = S.infix l (.==) r


//let add a b = a + b
//let (!!) a = -a
//
//add !! 10 !! 5

// postfix -- ++
// prefix - !
//
// infixR 80 **
// infixL 70 *, infixR 70 ***, infixN 70 ===
// infixL 60 + 
// infixN 40 ==
//
// `1 + 2 + 3 * 4 * 5` -> `(1 + 2) + ((3 * 4) * 5)`
// `1 * 2 * 3 + 4 + 5` -> `(((1 * 2) * 3) + 4) + 5`
// `+ - a ++ --` -> `(+(-((a++)--)))`
// `a !b++ -c-- + d` -> `(a (!(b++)) (-(c--))) + d`
//
// `a * b ** c ** d * e` -> `(a * (b ** (c ** d))) * e`
// `a == b + c` -> `a == (b + c)`
//
// `a == b == c` -> error
// `a * b === c` -> error
// `a === b * c` -> error
// `a * b *** c` -> error
// `a *** b * c` -> error
// `a *** b === c` -> error
// `a === b *** c` -> error
//
// `a == b + c == d` -> error

let (==>) l r = l, Some r
let error e = e, None
let testOp src exp =
    let act = parseApplications env src
    match exp with
    | Some exp ->
        if act <> Choice1Of2 exp then
            printfn "source: %A;\nactual: %A;\nexpected: %A;" src act exp

    | None ->
        match act with
        | Choice1Of2 _ -> printfn "source: %A;\nactual: %A" src act
        | _ -> ()

Seq.iter ((<||) testOp) [
    [a; (.+); b] ==> (a .+. b)
    [a; b; (.+); c; d] ==> (S.apply2 a b .+. S.apply2 c d)
    [a; (.+); b; (.+); c; (.*); d; (.*); e] ==> ((a .+. b) .+. ((c .*. d) .*. e))
    [a; (.*); b; (.*); c; (.+); d; (.+); e] ==> ((((a .*. b) .*. c) .+. d) .+. e)
    [(@!); (.-); a; (.++); (.--)] ==> (S.prefix (@!) (S.prefix (.-) (S.postfix (S.postfix a (.++)) (.--))))

    [a; (@!); b; (.++); (.-); c; (.--); (.+); d] ==> ((S.apply3 a (S.prefix (@!) (S.postfix b (.++))) (S.prefix (.-) (S.postfix c (.--))))) .+. d

    [a; (.*); b; (.**); c; (.**); d; (.*); e] ==> ((a .*. (b .**. (c .**. d))) .*. e)
    [a; (.==); b; (.+); c] ==> (a .==. (b .+. c))

    error [a; (.==); b; (.==); c]
    error [a; (.*); b; (.===); c]
    error [a; (.===); b; (.*); c]
    error [a; (.*); b; (.***); c]
    error [a; (.***); b; (.*); c]
    error [a; (.***); b; (.===); c]
    error [a; (.===); b; (.***); c]

    error [a; (.==); b; (.+); c; (.==); d]
]

parseApplications env [a; (.***); b; (.*); c], (a .***. (b .*. c))

let infer = ()



//open System
//open System.Reflection 
//open System.Reflection.Emit
//
//AppDomain.CurrentDomain.DefineDynamicAssembly(.AssemblyName(), )
//
//let emitNamedModule (LongIdentifier(ns, n)) es =
//    es
//
//let emitImplementationFile = function
//    | AnonymousModule _ -> failwithf ""
//    | NamedModule(_,n,xs) -> emitNamedModule n xs