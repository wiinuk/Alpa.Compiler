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
            S.moduleFun2 "a" !@"x" !@"y" (S.apply3Raw !!"x" !!%"+" !!"y")
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
    "a\nb", S.apply2Raw !!"a" !!"b"
    "a\n b", S.apply2Raw !!"a" !!"b"
]

//errorTest (Layout.fileStart >>. expression .>> eof) [
//    "  a\n  b"
//]

test syntaxDiff moduleFunctionOrValueDefinition (
    let exp = S.moduleFun2 "a" !@"x" !@"y" (S.apply2Raw !!"x" !!"y")
    let exp2 = S.moduleFun2 "apply" !@"f" !@"x" (S.apply2Raw !!"f" !!"x")
    [
        "a x y = x y", exp
        "a x y =\n  x y", exp
        "a x y =\n  x\n  y", exp
        "a x y =\n  x\n   y", exp

        "apply f x =\n  f x", exp2
        "apply f x =\n  f\n   x", exp2
        "seq unit a =\n  unit;\n  a", S.moduleFun2 "seq" !@"unit" !@"a" (S.seq' !!"unit" !!"a")

        "apply2 f x y =\n  f x y", S.moduleFun3 "apply2" !@"f" !@"x" !@"y" (S.apply3Raw !!"f" !!"x" !!"y")
        "seqApply action x y =\n  action x;\n  y", S.moduleFun3 "seqApply" !@"action" !@"x" !@"y" (S.seq' (S.apply2Raw !!"action" !!"x") !!"y")
        "seq2 unit1 unit2 a =\n  unit1;\n  unit2; a", S.moduleFun3 "seq2" !@"unit1" !@"unit2" !@"a" (S.seq' (S.seq' !!"unit1" !!"unit2") !!"a")
        "seqApply unit f x =\n  unit;\n  f x", S.moduleFun3 "seqApply" !@"unit" !@"f" !@"x" (S.seq' !!"unit" (S.apply2Raw !!"f" !!"x"))
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


//type dot = Dot of char
//type name = char
//type e = 
//    | Member of e * dot * name
//    | Lookup of (name * dot) list * name
//
//let rec takeMember e dot ls r =
//    match ls with
//    | [] -> Member(e, dot, r)
//    | (ln,ld)::ls -> takeMember (Member(e, dot, ln)) ld ls r
//
//let rec takeLookup env rns rs ms r =
//    match ms with
//    | [] ->
//        let rns' = r::rns
//        if Set.contains (List.rev rns') env then Lookup(List.rev rs, r)
//        else failwithf "error %A %A" (List.rev rs) r
//
//    | (mn,md) as i::ms ->
//        let rns' = mn::rns
//
//        if Set.contains (List.rev rns') env
//        then takeMember (Lookup(List.rev rs, mn)) md ms r
//        else takeLookup env rns' (i::rs) ms r
//
//let take env = takeLookup env [] []
//          
//let env = Set [['A';'a']; ['B';'C';'b']]
//  
//take env ['A', Dot '.'] 'a' = Lookup(['A', Dot '.'], 'a')
//take env ['B', Dot '.'; 'C', Dot '#'; 'b', Dot ','; 'x', Dot ':'] 'y' =
//    Member(Member(Lookup(['B', Dot '.'; 'C', Dot '#'], 'b'), Dot ',', 'x'), Dot ':', 'y')
//
//take env ['A', Dot '.'] 'x'
//take env ['X', Dot '.'; 'A', Dot ','] 'a'
//take env ['B', Dot '.'] 'C'



    
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
    let makeEnv = List.map (fun (n,op) -> [n], op) >> Env.makeVars
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

let (.+.) l r = S.infixL l (.+) r
let (.*.) l r = S.infixL l (.*) r
let (.**.) l r = S.infixR l (.**) r
let (.***.) l r = S.infixR l (.***) r
let (.==.) l r = S.infixN l (.==) r
let (.===.) l r = S.infixN l (.==) r


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
// `- a ! b` -> `-(a(!b))`
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

let testSolveCore diff solve env src exp =
    let act = solve env src
    match exp with
    | Some exp ->
        match diff act (Ok exp) with
        | Diff _ as d -> printfn "source: %A;\nactual: %A;\nexpected: %A; diff: %A" src act exp d
        | _ -> ()

    | None ->
        match act with
        | Ok _ -> printfn "source: %A;\nactual: %A" src act
        | _ -> ()

let testSolveExpr diff = testSolveCore diff <| trySolve solveExpr

let testApps diff env src exp =
    let src =
        match src with
        | [] -> C.unit
        | [l] -> l
        | l::r::rs -> ApplicationsExpression(ApplicationKind.RawApply, l, r, rs)

    testSolveExpr diff env src exp

Seq.iter ((<||) (testApps syntaxDiff env)) [
    [a; (.+); b] ==> (a .+. b)
    [a; b; (.+); c; d] ==> (S.apply2 a b .+. S.apply2 c d)
    [a; (.+); b; (.+); c; (.*); d; (.*); e] ==> ((a .+. b) .+. ((c .*. d) .*. e))
    [a; (.*); b; (.*); c; (.+); d; (.+); e] ==> ((((a .*. b) .*. c) .+. d) .+. e)
    [(@!); (.-); a; (.++); (.--)] ==> (S.prefix (@!) (S.prefix (.-) (S.postfix (S.postfix a (.++)) (.--))))
    [(.-); a; (@!); b] ==> (S.apply2 (S.prefix (.-) a) (S.prefix (@!) b))

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

//let (Success f) = parse start "module A = a = ()"
//solve env f
//
//[a; (@!); b; (.++); (.-); c; (.--); (.+); d] ==>
//    ((S.apply3 a (S.prefix (@!) (S.postfix b (.++))) (S.prefix (.-) (S.postfix c (.--))))) .+. d
//
//ApplicationsExpression(
//    PrefixApply,
//    ApplicationsExpression(
//        PrefixApply,
//        ApplicationsExpression(
//            PostfixApply,
//            (.--),
//            ApplicationsExpression(PostfixApply, (.++), a, []),
//            []
//        ),
//        (.-),
//        []
//    ),
//    (@!),
//    []
//)

module Result =
    let map f = function
        | Ok x -> Ok(f x)
        | Error e -> Error e

let testSolve diff = testSolveCore diff <| fun env src ->
    match parse start src with
    | Failure(e,_,_,_) -> Error e
    | Success f -> solve env f

let solve env src =
    match parse start src with
    | Failure(e,_,_,_) -> Error e
    | Success f -> solve env f

Seq.iter ((<||) (testSolve syntaxDiff Env.empty)) [
    "x = ()\nx = x" ==> (
        S.anonymousModule [
            S.moduleVal "x" C.unit
            S.moduleVal "x" !!"x"
        ],
        [
            ["x"], SymbolInfo.Var
            ["x"], SymbolInfo.Var
        ]
    )

    "module A =\n  a = ()\na = ()" ==> (
        S.anonymousModule [
            S.module' !"A" [
                S.moduleVal "a" C.unit
            ]
            S.moduleVal "a" C.unit
        ],
        [
            ["a"], SymbolInfo.Var
            ["A"], SymbolInfo.Module
            ["A";"a"], SymbolInfo.Var
        ]
    )
]

exception UnifyException of ParseError * Type * Type

let typingModuleInner env (e, es) =
    let e = typingModuleElement env e
    failwith ""

let typingImplementationFile env = function
    | AnonymousModule es -> AnonymousModule(typingModuleInner env es)
    | NamedModule(moduleK, name, es) -> NamedModule(moduleK, name, typingModuleInner env es)


let tryTyping typing env x =
    try typing env x |> Ok with
    | UnifyException(e, t1, t2) -> Error(e, t1, t2)

let typing env f =
    try
        match f with
        | None -> Ok None
        | Some f -> typingImplementationFile env f |> Some |> Ok
    with 
    | UnifyException(e, t1, t2) -> Error(e, t1, t2)



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