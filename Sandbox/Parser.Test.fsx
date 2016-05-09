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
        "seq2 unit1 unit2 a =\n  unit1;\n  unit2; a", S.moduleFun3 "seq2" !@"unit1" !@"unit2" !@"a" (S.seq (S.seq !!"unit1" !!"unit2") !!"a")
        "seqApply unit f x =\n  unit;\n  f x", S.moduleFun3 "seqApply" !@"unit" !@"f" !@"x" (S.seq !!"unit" (S.apply2 !!"f" !!"x"))
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

let (Success(Some f)) = parse start xs

type Fixity =
    | Nonfix
    | Prefix
    | Infix
    | Suffix

type Associativity =
    | NonAssoc
    | Left
    | Right

type sorted_table<'k,'v> = list<'k * list<'v>>
type Operator = Operator of Fixity * Associativity * precedence: int * FullPath: list<Symbol>
type VarInfo = VarInfo of option<Operator> * FullPath: list<Symbol>
type Node<'K,'V when 'K : comparison> =
    | Leaf of 'V
    | Node of Map<'K, Node<'K,'V>>

type Tree<'K,'V when 'K : comparison> = Map<'K, Node<'K,'V>>
type SymbolTree = Tree<Symbol, VarInfo>

type ResolveEnv = {
    InfixOpsTable: sorted_table<int, Operator>
    Vars: SymbolTree
}
module Env =
    let contains n env =
        match Map.tryFind n env.Vars with
        | Some(Leaf _) -> true
        | _ -> false

    let tryFind (LongIdentifier(ls, r)) env =
        let rec aux ls r vars =
            match ls with
            | [] ->
                match Map.tryFind (r._value2 :?> Symbol) vars with
                | Some(Leaf v) -> Some v
                | _ -> None

            | (l, _)::ls ->
                match Map.tryFind (l._value2 :?> Symbol) vars with
                | Some(Node vars) -> aux ls r vars
                | _ -> None

        aux ls r env.Vars

type Result<'a> = NoChange | Update of 'a

let (|Op|_|) env = function
    | LookupExpression(LongIdentifier(ns, n) as name) ->
        match Token.kind n with
        | TokenKind.Id
        | TokenKind.Op
        | TokenKind.Qid ->
            match Env.tryFind name env with
            | Some(VarInfo(Some op, fp)) -> Some(op, name, fp)
            | _ -> None
        | _ -> None
    | _ -> None
    
// prefix --; infixL 10 *; infixL 5 +; infixR 10 **; nonfix 10 ==;
// `1 + 2 + 3 * 4 * 5` -> `(1 + 2) + ((3 * 4) * 5)`
// `1 * 2 * 3 + 4 + 5` -> `(((1 * 2) * 3) + 4) + 5`

let parseApplications env es =
    let parseTerm = function
        | Op env e::_ -> failwithf "parseTerm %A" e
        | e::es -> Some(e, es)
        | [] -> failwith "empty"

    let parseOp infixOps = function
        | Op env (_,name,fp) as e::es ->
            if List.exists (fun (Operator(_,_,_,fp')) -> fp = fp') infixOps
            then Some(name, es)
            else failwithf "parseOp %A" e
        | _ -> failwith "parseOp"

    let rec parseInfixOpTable infixOpTable es =
        match infixOpTable with
        | [] -> parseTerm es
        | (_, infixOps)::infixOpTable ->
            parseInfixOps infixOps infixOpTable es

    and parseInfixOps infixOps infixOpTable es =
        match parseInfixOpTable infixOpTable es with
        | None -> None
        | Some(l, es) ->
            
            let rec parseManyInfixOps l es =
                try parseOp infixOps es with _ -> None

                |> function
                | None -> l, es
                | Some(op, es) ->
                    try parseInfixOpTable infixOpTable es with _ -> None

                    |> function
                    | None -> l, es
                    | Some(r, es) -> parseManyInfixOps (OperatorExpression(InfixOperator(l, op, r))) es

            Some <| parseManyInfixOps l es

    match parseInfixOpTable env.InfixOpsTable es with
    | Some(e, []) -> Some e
    | _ -> None

let add fullPath op env =
    let rec addTree l rs v tree =
        match Map.tryFind l tree, rs with
        | Some(Node ltree), r::rs -> Map.add l (Node(addTree r rs v ltree)) tree
        | _, r::rs -> Map.add l (Node(addTree r rs v Map.empty)) tree
        | _, [] -> Map.add l (Leaf v) tree

    let rec addSortedTable key x = function
        | [] -> [key, [x]]
        | (k,xs) as kxs::table ->
            if key < k then (key,[x])::kxs::table
            elif key = k then (k,x::xs)::table
            else kxs::addSortedTable key x table

    match fullPath with
    | [] -> failwith "empty path"
    | p::ps ->
        let vars = addTree p ps (VarInfo(op, fullPath)) env.Vars
        match op with
        | None -> { env with Vars = vars }
        | Some(Operator(_,_,prec,_) as op) ->
            { env with 
                Vars = vars
                InfixOpsTable = addSortedTable prec op env.InfixOpsTable
            }
            


let make xs =
    let env = { InfixOpsTable = []; Vars = Map.empty }
    Seq.fold (fun env (fullPath, op) ->
        let op = Option.map(fun (f, a, p) -> Operator(f, a, p, fullPath)) op
        add fullPath op env
    ) env xs
    
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
    make [
        ["a"], None
        ["b"], None
        ["c"], None
        ["d"], None
        ["e"], None
        ["+"], Some(Infix, Left, 60)
        ["*"], Some(Infix, Left, 70)
    ]

let infix l op r = OperatorExpression(InfixOperator(l, op, r))

let a, b, c, d, e = !!"a", !!"b", !!"c", !!"d", !!"e"

parseApplications env [a; !!"+"; b] = Some(infix a !+"+" b)
parseApplications env [a; !!"+"; b; !!"+"; c; !!"*"; d; !!"*"; e] =
    Some(infix (infix a !+"+" b) !+"+" (infix (infix c !+"*" d) !+"*" e))

parseApplications env [a; !!"*"; b; !!"*"; c; !!"+"; d; !!"+"; e] =
    Some(infix (infix (infix (infix a !+"*" b) !+"*" c) !+"+" d) !+"+" e)

type Resolved<'a> = Resolved of Fixity * int * 'a
let nonfix x = Resolved(Nonfix, 0, x)

let rec resolveNameOfExpr env e =
    match e with
    | ApplicationsExpression(e1, e2, es) -> 
            

open System
open System.Reflection 
open System.Reflection.Emit

System.AppDomain.CurrentDomain.DefineDynamicAssembly(.AssemblyName(), )

let emitNamedModule (LongIdentifier(ns, n)) es =
    es

let emitImplementationFile = function
    | AnonymousModule _ -> failwithf ""
    | NamedModule(_,n,xs) -> emitNamedModule n xs