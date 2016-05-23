module internal PolyTyping2.Test
#load "PolyTyping2.fsx"
open PolyTyping2

let refId (x: _ ref) = System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode x
fsi.AddPrintTransformer <| fun (x: IndefType) -> box(refId x, x.contents)
let (!=) l r = not (l == r)

let typesign0 t = TypeSign([], t)
let type0 n = Type(n, [])
let type1 n t1 = Type(n, [t1])
let type2 n t1 t2 = Type(n, [t1; t2])

let forall0 t = TypeScheme([], t)
let forall1 f =
    let v1 = newTypeVar()
    TypeScheme([v1], f <| IndefType v1)

let forall2 f =
    let v1, v2 = newTypeVar(), newTypeVar()
    TypeScheme([v1; v2], f (IndefType v1) (IndefType v2))
    
let (!!) = IndefType
let (.->) = lamT
let (.=>) cs t = TypeSign(cs, t)

let simpleT t = forall0([] .=> t)

let (|Type0|Type1|Type2|TypeLt2|) = function
    | Type(n, []) -> Type0 n
    | Type(n, [t1]) -> Type1(n, t1)
    | Type(n, [t1; t2]) -> Type2(n, t1, t2)
    | t -> TypeLt2 t

let rec (|VarT|_|) = function
    | IndefType({ contents = TypeVar } as v) -> Some v
    | IndefType { contents = SomeType(VarT t) } -> Some t
    | _ -> None

let (|LamT|_|) = function Type2("->", l, r) -> Some(l, r) | _ -> None
let (|Lam3T|_|) = function
    | LamT(t1, LamT(t2, t3)) -> Some(t1, t2, t3)
    | _ -> None

let (|IntT|_|) = function Type0 "Int" -> Some() | _ -> None

let stringT = type0 "String"
let refT = type1 "Ref"
let unitT = type0 "()"
let boolT = type0 "Bool"
let intT = type0 "Int"
let floatT = type0 "Float"
let lam3T t1 t2 t3 = lamT t1 (lamT t2 t3)
let lam4T t1 t2 t3 t4 = lamT t1 (lamT t2 (lamT t3 t4))
let tup2T = type2 ","
let listT = type1 "[]"

let listEq eq l r = List.compareWith (fun l r -> if eq l r then 0 else 1) l r = 0
let resultEq eq1 eq2 l r =
    match l, r with
    | Ok l, Ok r -> eq1 l r
    | Error l, Error r -> eq2 l r
    | _ -> false

module Print =
    let wrap p tp t = if tp <= p then sprintf "(%s)" t else t
    let quote q n =
        if not <| Seq.exists (fun c -> c = '\\' || c = q) n then sprintf "%c%s%c" q n q
        else String.collect (function '\\' -> "\\\\" | c when c = q -> "\\" + string q | c -> string c) n

    let printId q n = 
        if 
            Seq.forall System.Char.IsLetter (Seq.truncate 1 n) &&
            Seq.forall System.Char.IsLetterOrDigit n
        then n
        else quote q n

    let printVar map r = 
        match List.tryFind (fun (r',_) -> r = r') map with
        | Some(_, n) -> n, map
        | None ->
            let rec fleshVar i map =
                let n' = sprintf "'t%d" i
                if List.exists (fun (_,n) -> n = n') map then fleshVar (i+1) map
                else n'

            let n = fleshVar 1 map
            n, (r, n)::map

    let rec print map = function
        | Type("()", []) -> 10, map, "()"
        | Type("[]", [t]) ->
            let _, map, t = print map t
            10, map, sprintf "[%s]" t

        | Type("->", [t1; t2]) ->
            let p = 5
            let p1, map, t1 = print map t1
            let p2, map, t2 = print map t2
            p, map, sprintf "%s -> %s" (wrap p p1 t1) (wrap (p-1) p2 t2)

        | Type(",", [t1; t2]) ->
            let p = 4
            let p1, map, t1 = print map t1
            let p2, map, t2 = print map t2
            p, map, sprintf "%s, %s" (wrap p p1 t1) (wrap p p2 t2)

        | Type(",,", [t1; t2; t3]) ->
            let p = 4
            let p1, map, t1 = print map t1
            let p2, map, t2 = print map t2
            let p3, map, t3 = print map t3
            p, map, sprintf "%s, %s, %s" (wrap p p1 t1) (wrap p p2 t2) (wrap p p3 t3)

        | Type(n, ts) ->
            let p = 9
            let n = printId '`' n
            let ts, map =
                ts
                |> Seq.fold (fun (r, map) t ->
                    let p', map, t = print map t
                    r + " " + wrap p p' t, map
                ) ("", map)

            p, map, n + ts

        | IndefType { contents = SomeType t } -> print map t
        | IndefType({ contents = TypeVar _ } as r) ->
            let n, map = printVar map r
            10, map, n

    let printTypeArg map = function
        | { contents = SomeType _ } -> "", map
        | { contents = TypeVar _ } as r -> printVar map r

    let printTypeSign map (TypeSign(cs, t)) =
        let _, map, cs =
            match cs with
            | [] -> 10, map, ""
            | [c] ->
                let _, map, c = print map c
                10, map, c + " => "

            | cs ->
                let p = 4
                let cs, map =
                    Seq.fold (fun (r, map) t ->
                        let p', map, t = print map t
                        r + ", " + wrap p p' t, map
                    ) ("", map) cs

                10, map, sprintf "(%s) => " cs

        let _, map, t = print map t
        10, map, sprintf "%s%s" cs t

    let printTypeScheme (TypeScheme(vs, t)) =
        let _,map,t = printTypeSign [] t

        if List.isEmpty vs then t
        else
            let ts, _ =
                List.fold (fun (r, map) v ->
                    let r', map = printTypeArg map v
                    r + " " + r', map
                ) ("", map) vs

            sprintf "type%s.%s" ts t
      
let sprintType t = Print.printTypeScheme t

let typing e =
    try 
        typingCore Env.empty e 
        |> deref
        |> bind
        |> Ok 
    with
    | TypingException e -> Error e

let (!) = Var
let (->.) var body = Lam(var, body)
let (%.) f x = App(f, x)
let lam2E x1 x2 e = x1 ->. (x2 ->. e)
let appE = (%.)
let app2E f x1 x2 = f %. x1 %. x2
let ifE c t f = !"if" %. c %. t %. f

type Decl =
    | ExtDec of Var * TypeScheme
    | LetDec of Var * Exp
    | RecDec of Var * Exp
    | TypDec of Var * TypeDef
    | InsDec of Var * Type list * (Var * Exp) list
    | AndDec of (Var * Exp) list

let extD var type' = ExtDec(var, type')
let letE var body = LetDec(var, body)
let recE var body = RecDec(var, body)
let typE var typeDef = TypDec(var, typeDef)
let andD = AndDec
let clsE var typeVars methodDefs = typE var (ClassDef(typeVars, methodDefs))
let cls1D var makeDefs =
    let a = newTypeVar()
    clsE var [a] <| makeDefs (IndefType a)

let ins0D name arg impls = InsDec(name, [arg], impls)
let ins1D make =
    let a = newVarT()
    let name, var, impls = make a
    InsDec(name, [var], impls)

let (^.) def cont =
    match def with
    | ExtDec(v, t) -> Ext(v, t, cont)
    | LetDec(v, b) -> Let(v, b, cont)
    | RecDec(v, b) -> LetRec([v,b], cont)
    | TypDec(v, d) -> TypeDef(v, d, cont)
    | InsDec(v, vs, is) -> InstanceDef(v, vs, is, cont)
    | AndDec vds -> LetRec(vds, cont)

let (!!!) = function 
    | ExtDec(x, _) | LetDec(x, _) | RecDec(x, _) | TypDec(x, _) | InsDec(x, _, _) -> !x
    | AndDec _ -> failwithf "AndDec"
    
let mapT = type2 "Map"
let vecT = type1 "Vec"
let numT = type1 "Num"
let eqT = type1 "Eq"

let fractionalT = type1 "Fractional"

let intLitT = forall1 <| fun a -> [numT a] .=> a
let floatLitT = forall1 <| fun a -> [fractionalT a] .=> a
let floatL _ = Lit floatLitT
let intL _ = Lit intLitT
let stringL _ = Lit <| forall0 ([] .=> stringT)

let (=>.) v xs = Mat(v, List.head xs, List.tail xs)
let numP _ = LitPat intLitT
let anyP = AnyPat

let dataD n vs ds = TypDec(n, DataDef(vs, ds))
let data1D n f =
    let t1 = newTypeVar()
    dataD n [t1] <| f (IndefType t1)

let con0P n = ConPat(n, [])
let con1P n p1 = ConPat(n, [p1])
let con2P n p1 p2 = ConPat(n, [p1; p2])

let trueE = Lit <| simpleT boolT
let falseE = Lit <| simpleT boolT
let (~+) (_: int) = Lit <| simpleT intT
let (^^.) l r = !"seq" %. l %. r

let ifD = extD "if" <| forall1 (fun a -> [] .=> lam4T boolT a a a)
let seqD = extD "seq" <| forall1 (fun a -> [] .=> lam3T unitT a a)

let addIntD = extD "Int._+_" <| simpleT (lam3T intT intT intT)
let negateIntD = extD "Int.-_" <| simpleT (intT .-> intT) 
let succIntD = extD "Int.succ" <| simpleT (intT .-> intT)

let addFloatD = extD "Float._+_" <| simpleT (lam3T floatT floatT floatT)
let negateFloatD = extD "Float.-_" <| simpleT (floatT .-> floatT)

let tup2D = extD "," <| forall2 (fun a b -> [] .=> lam3T a b (tup2T a b))

let listEmptyD = extD "List.empty" <| forall1 (fun a -> [] .=> listT a)
let listSingletonD = extD "List.singleton" <| forall1 (fun a -> [] .=> a .-> listT a)
let listConsD = extD "List.cons" <| forall1 (fun a -> [] .=> lam3T a (listT a) (listT a))
let listIsEmptyD = extD "List.isEmpty" <| forall1 (fun a -> [] .=> listT a .-> boolT)
let listTailD = extD "List.tail" <| forall1 (fun a -> [] .=> listT a .-> listT a)
let listHeadD = extD "List.head" <| forall1 (fun a -> [] .=> listT a .-> a)
let listMapD = extD "List.map" <| forall2 (fun a b -> [] .=> lam3T (a .-> b) (listT a) (listT b))

let idD = letE "id" ("x" ->. !"x")
    
let refD = extD "ref" <| forall1 (fun a -> [] .=> a .-> refT a)
let refSetD = extD ":=" <| forall1 (fun a -> [] .=> lam3T (refT a) a unitT)
let refGetD = extD "!" <| forall1 (fun a -> [] .=> refT a .-> a)

let eqD = cls1D "Eq" <| fun a -> ["_==_", simpleT <| lam3T a a boolT]
let numD =
    cls1D "Num" <| fun a ->
        [
        "_-_", simpleT <| lam3T a a a
        "_+_", simpleT <| lam3T a a a
        ]
        
let errorsEq = (=)
let typeSchemeEq l r =
    let TypeScheme(lvs, TypeSign(lcs, l)), TypeScheme(rvs, TypeSign(rcs, r)) = rebind l, rebind r
    List.length lvs = List.length rvs &&
    (
        List.iter2 (fun rv lv -> rv := SomeType(IndefType lv)) rvs lvs
        listEq typeEq lcs rcs &&
        typeEq l r
    )

let assertEq eq l r =
    if eq l r then printfn "ok"
    else printfn "assert (==) %A %A" l r

let (==?) l r = assertEq (resultEq typeSchemeEq errorsEq) l r

let newTypeVar2 f = f (newTypeVar()) (newTypeVar())
let newTypeVar1 f = f <| newTypeVar()

newTypeVar2 <| fun a b ->

    /// free (type a. a -> a -> b -> Int) = (_flesh0 -> _flesh0 -> b -> Int)
    match free <| TypeScheme([a], [] .=> lam4T !!a !!a !!b intT) with
    | TypeSign([], LamT(IndefType a', LamT(IndefType a'', LamT(IndefType b', IntT)))) ->
        a' != a && a'' != a && a' == a'' && b == b' && a' != b'
    | _ -> false

newTypeVar2 <| fun x y ->
    
    /// bind (x -> y -> Int) = (type a b. a -> b -> Int)
    match bind ([] .=> lam3T !!x !!y intT) with
    | TypeScheme([a; b], TypeSign([], LamT(IndefType a', LamT(IndefType b', IntT)))) ->
        x != a && a == a' && y != b && b == b'
    | _ -> false

// f = \x. x in
// if (f true) (f 2) 3

ifD ^.
letE "f" ("x" ->. !"x") ^.
ifE (!"f" %. trueE) (!"f" %. + 2) (+ 3)
|> typing
    ==? Ok(simpleT <| intT)

tup2D ^.
letE "f" ("x" ->. !"x") ^.
app2E !!!tup2D (!"f" %. + 1) (!"f" %. trueE)
|> typing
    ==? Ok(simpleT <| tup2T intT boolT)

typing (tup2D ^. "f" ->. app2E !!!tup2D (!"f" %. + 1) (!"f" %. trueE)) ==?
    Error(TypeMismatch(!"f" %. trueE, intT, boolT))

// TODO: value restriction
listMapD ^.
    idD ^.
    tup2D ^.

    extD "xs" (simpleT <| listT intT) ^.
    extD "xs2" (simpleT <| listT boolT) ^.

    letE "f" (!!!listMapD %. !!!idD) ^.
    app2E !!!tup2D (!"f" %. !"xs") (!"f" %. !"xs2")

    |> typing 
        ==? Ok(simpleT <| tup2T (listT intT) (listT boolT))


// TODO: value restriction
seqD ^.
    refD ^.
    refSetD ^.
    refGetD ^.
    addIntD ^.
    listHeadD ^.
    listEmptyD ^.

    extD "xs" (simpleT <| listT boolT) ^.

    letE "polyref" (!!!refD %. !!!listEmptyD) ^.
    app2E !!!refSetD !"polyref" !"xs" ^^.
    app2E !!!addIntD (+ 123) (!!!listHeadD %. (!!!refGetD %. !"polyref"))

    |> typing 
        ==? Ok(simpleT <| intT)


ifD ^.
    listIsEmptyD ^.
    succIntD ^.
    listTailD ^.
    listConsD ^.
    listEmptyD ^.

    recE "len" ("xs" ->. ifE (!!!listIsEmptyD %. !"xs") (+ 0) (!!!succIntD %. (!"len" %. (!!!listTailD %. !"xs")))) ^.
    !"len" %. (!!!listConsD %. (+ 0) %. !!!listEmptyD)

    |> typing 
        ==? Ok(simpleT <| intT)

let fooD = cls1D "Foo" <| fun a -> ["op", forall1 <| fun b -> [numT b] .=> lam3T a b a]

numD ^.
fooD ^.
!"op"
|> typing
    ==? Ok(forall2 <| fun a b -> [type1 "Foo" a; numT b] .=> lam3T a b a)
    
numD ^.
letE "double" ("x" ->. app2E !"_+_" !"x" !"x") ^.
!"double"
|> typing
    ==? Ok(forall1 <| fun a -> [numT a] .=> a .-> a)

newTypeVar1 <| fun a ->
    match free (TypeScheme([a], [numT !!a] .=> !!a)) with
    | TypeSign([Type1("Num", VarT x)], VarT x') -> a != x && x == x'
    | _ -> false

newTypeVar2 <| fun a b ->
    match free (TypeScheme([a; b], [numT !!a] .=> !!b)) with
    | TypeSign([Type1("Num", VarT x)], VarT y) -> a != x && a != y && b != x && b != y && x != y
    | _ -> false

// TODO: ???
let t' = forall0 ([numT intT] .=> intT)
typeSchemeEq (forall0 <| free t') t'

// type a. Eq a => a -> a
// type a b. (Eq a, Show a, Eq b) => [a] -> [b] -> String
// type f a b. (Eq (f a), Functor f) => (a -> b) -> f a -> f b -> Bool


begin
    let (===?) = assertEq <| resultEq (listEq typeEq) typeEq
    let isError = function Error _ -> printfn "ok" | x -> printfn "isError %A" x

    let a, b = newVarT(), newVarT()
    solveI (mapT a (vecT b)) [forall2 <| fun x y -> [] .=> mapT x y] ===? Ok []
    solveI (mapT a (vecT b)) [forall1 <| fun x -> [] .=> mapT x x] |> isError
    solveI (mapT (vecT a) b) [forall1 <| fun x -> [] .=> mapT x x] |> isError
    solveI (numT a) [forall1 (fun a -> [] .=> numT a)] ===? Ok []
    solveI (mapT a a) [forall2 <| fun x y -> [] .=> mapT x y] ===? Ok []
    solveI (mapT a b) [forall1 <| fun x -> [] .=> mapT x x] |> isError
    solveI (numT (vecT a)) [forall1(fun x -> [eqT x] .=> numT (vecT x)); forall1(fun x -> [] .=> numT x)] ===? Ok [eqT a]
    solveI (numT (vecT a)) [forall1(fun x -> [] .=> numT x); forall1(fun x -> [eqT x] .=> numT (vecT x))] ===? Ok []
    solveI (numT (vecT boolT)) [forall1 <| fun x -> [eqT x] .=> numT (vecT x)] ===? Error(eqT boolT)
    solveI (numT (vecT boolT)) [forall1 (fun x -> [eqT x] .=> numT (vecT x)); simpleT (eqT boolT)] ===? Ok []
    solveI (numT (vecT a)) [forall1 <| fun x -> [eqT x] .=> numT (vecT x)] ===? Ok [eqT a]
end

begin
    let a, b = newVarT(), newVarT()
    let unlift t = lamT <|| unlift t
    let (===?) = assertEq typeEq
    let (====?) = assertEq typeSchemeEq

    unlift ([numT a] .=> a) ===? numT a .-> a
    forall0 ([] .=> unlift ([] .=> intT)) ====? forall1 (fun a -> [] .=> a .-> intT)
    unlift ([numT a; eqT b] .=> tup2T a b) ===? tup2T (eqT b) (numT a) .-> tup2T a b
    unlift ([numT a; eqT b] .=> tup2T a b) ===? unlift ([eqT b; numT a] .=> tup2T a b)
end

ifD ^.
eqD ^.
numD ^.
extD "0" (forall1 <| fun a -> [numT a] .=> a) ^.
extD "1" (forall1 <| fun a -> [numT a] .=> a) ^.
andD [
    "even", "n" ->. ifE (app2E !"_==_" !"n" !"0") trueE (appE !"odd" (app2E !"_-_" !"n" !"1"))
    "odd", "n" ->. ifE (app2E !"_==_" !"n" !"0") falseE (appE !"even" (app2E !"_-_" !"n" !"1"))
] ^.
!"even"
    |> typing ==? Ok(forall1 <| fun a -> [eqT a; numT a] .=> a .-> boolT)

listSingletonD ^.
cls1D "ShowN" (fun a -> ["showN", forall1 <| fun b -> [numT b] .=> lam3T b a stringT]) ^.
ins1D (fun a ->
    "ShowN", listT a,
    [
        "showN", lam2E "a" "b" <| Lit(simpleT stringT)
    ]
) ^.

lam2E "n" "x" (app2E !"showN" !"n" (appE !!!listSingletonD !"x"))
|> typing
    ==? Ok(forall2 <| fun n x -> [numT n] .=> lam3T n x stringT)


addIntD ^.
negateIntD ^.
addFloatD ^.
negateFloatD ^.

tup2D ^.

cls1D "Num" (fun a ->
    [
    "_+_", simpleT <| lam3T a a a
    "negate", simpleT <| a .-> a
    ]) ^.
    
ins0D "Num" intT
    [
    "_+_", lam2E "x" "y" (app2E !!!addIntD !"x" !"y")
    "negate", "x" ->. appE !!!negateIntD !"x"
    ] ^.
    
ins0D "Num" floatT
    [
    "_+_", lam2E "x" "y" (app2E !!!addFloatD !"x" !"y")
    "negate", "x" ->. appE !!!negateFloatD !"x"
    ] ^.
    
app2E !!!tup2D (appE !"_+_" (Lit <| simpleT intT)) (appE !"_+_" (Lit <| simpleT floatT))
|> typing
    ==? Ok(simpleT <| tup2T (intT .-> intT) (floatT .-> floatT))

floatL 1.0 =>. [
    numP 1, stringL "1"
    anyP, stringL "any"
]
|> typing
    ==? Ok(forall1 <| fun a -> [fractionalT a; numT a] .=> stringT)

data1D "Digit" (fun a ->
[
    "Zero", []
    "One", [a]
    "Two", [a; a]
]) ^.

"x" ->.
    (!"x" =>. [
        con0P "Zero", intL 0
        con1P "One" anyP, intL 1
        con2P "Two" anyP anyP, intL 2
    ])
|> typing
    ==? Ok(forall2 <| fun a b -> [numT b] .=> type1 "Digit" a .-> b)

// case e of { alts } = (\v -> case v of { alts }) e
// v は新しい変数
//
// case v of { p[1] match[1];  ... ; p[n] match[n] }
// = case v of { p[1] match[1] ;
//               _  -> ... case v of {
//                          p[n] match[n] ;
//                          _  -> error "No match" }... }
// 各 match[i] は以下の形式をもつ。
// | g[i], m[1] -> ei, m[1] ; ... ; | g[i], m[i] -> e[i], m[i] where { decls[i] }
//
// case v of { p | g[1] -> e[1] ; ...
//               | g[n] -> e[n] where { decls }
//             _        -> e' }
// = case e' of
//  { y ->  (y は新しい変数)
//   case v of {
//         p -> let { decls } in
//                if g[1] then e[1] ... else if g[n] then e[n] else y ;
//         _ -> y }}
//
// case v of { ~p -> e; _ -> e' }
// = (\x[1] ... x[n] -> e ) (case v of { p -> x[1] }) ... (case v of { p -> x[n] })
// x[1], ..., x[n] はすべて p 内の変数
//
// case v of { x@p -> e; _ -> e' }
// = case v of { p -> (\x -> e) v; _ -> e' }
//
// case v of { _ -> e; _ -> e' } = e
