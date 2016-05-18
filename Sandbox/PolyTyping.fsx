type Symbol = string
type Var = string

type Type =
    | Type of Symbol * Type list
    | TypeVar of TypeVar

and TypeVar = Type option ref

type TypeScheme = TypeScheme of TypeVar list * Type

type Expr =
    | Bool of bool
    | Int of int
    | Var of Var
    | Lam of Var * Expr
    | App of Expr * Expr
    | Dec of Var * TypeScheme * Expr
    | Let of Var * Expr * Expr
    | LetRec of (Var * Expr) * (Var * Expr) list * Expr

let newTypeVar() : TypeVar = ref None
let newVarT() = TypeVar(newTypeVar())

let refT t = Type("ref", [t])
let unitT = Type("()", [])
let boolT = Type("Bool", [])
let intT = Type("Int", [])
let funT v e = Type("->", [v; e])
let tup2T t1 t2 = Type(",", [t1; t2])
let listT t = Type("[]", [t])
let (!!) = TypeVar
let (.->) = funT

let (|FunT|_|) = function Type("->", [l; r]) -> Some(l, r) | _ -> None
let (|IntT|_|) = function Type("Int", []) -> Some() | _ -> None

let (==) l r = LanguagePrimitives.PhysicalEquality l r
let (!=) l r = not (l == r)

let free (TypeScheme(vs, t)) =
    let vts = List.map (fun v -> v, newVarT()) vs

    let rec free = function
        | Type(n, ts) -> Type(n, List.map free ts)
        | TypeVar { contents = Some t } -> free t
        | TypeVar({ contents = None } as v) as t ->
            match List.tryFind (fun (v',_) -> v == v') vts with
            | Some(_,t) -> t
            | None -> t
    free t

let bind t =
    let rec collect vs = function
        | Type(_, ts) -> List.fold collect vs ts
        | TypeVar { contents = Some t } -> collect vs t
        | TypeVar({ contents = None } as v) ->
            if List.exists (fun v' -> v == v') vs then vs
            else v::vs

    TypeScheme(collect [] t |> List.rev, t)

type Env = Map<Var, TypeScheme>
exception UnifyException of Expr * Type * Type
exception VarException of Env * Var

let rec occur v = function
    | Type(_, ts) -> List.exists (occur v) ts
    | TypeVar({ contents = a } as v') ->
        v == v' ||
            match a with
            | None -> false
            | Some t -> occur v t

let rec unify e l r =
    match l, r with
    | Type(ln, ls), Type(rn, rs) when ln = rn && List.length ls = List.length rs -> List.iter2 (unify e) ls rs
    | TypeVar l, TypeVar r when l == r -> ()
    | TypeVar { contents = Some l }, _ -> unify e l r
    | _, TypeVar { contents = Some r } -> unify e l r
    | TypeVar({ contents = None } as lv), _ when not <| occur lv r -> lv := Some r
    | _, TypeVar({ contents = None} as rv) when not <| occur rv l -> rv := Some l
    | _ -> raise <| UnifyException(e, l, r)

let rec typingCore env = function
    | Dec(v, t, e) -> typingCore (Map.add v t env) e
    | Bool _ -> boolT
    | Int _ -> intT
    | Var v ->
        try free <| Map.find v env
        with
        | :? System.Collections.Generic.KeyNotFoundException ->
            raise <| VarException(env, v)
        

    | Lam(v, e) ->
        let vt = newVarT()
        let env = Map.add v (TypeScheme([], vt)) env
        let et = typingCore env e
        funT vt et

    | App(f, x) as e ->
        let ft = typingCore env f
        let xt = typingCore env x
        let rt = newVarT()
        unify e ft (funT xt rt)
        rt

    | Let(var, body, cont) as e ->
        let vt = newVarT()
        let bt = typingCore env body
        unify e vt bt
        typingCore (Map.add var (bind vt) env) cont

    | LetRec((var, body), varBodys, cont) ->
        let vt, vbts = newVarT(), List.map (fun vb -> vb, newVarT()) varBodys
        let env = List.fold (fun env ((v,_),vt) -> Map.add v (bind vt) env) (Map.add var (bind vt) env) vbts
        unify body vt (typingCore env body)
        List.iter (fun ((_,b),vt) -> unify b vt (typingCore env b)) vbts
        typingCore env cont

type Result<'T,'E> = Ok of 'T | Error of 'E

let rec deref = function
    | Type(n, ts) -> Type(n, List.map deref ts)
    | TypeVar { contents = None } as t -> t
    | TypeVar({ contents = Some t } as v) ->
        let t = deref t
        v := Some t
        t

type Error = 
    | UnifyError of Expr * Type * Type
    | VarError of Env * Var

let typing e =
    try 
        typingCore Map.empty e 
        |> deref
        |> Ok 
    with
    | UnifyException(e, l, r) -> Error(UnifyError(e, l, r))
    | VarException(env, v) -> Error(VarError(env, v))

let (!) = Var
let (->.) var body = Lam(var, body)
let (%.) f x = App(f, x)
let appE = (%.)
let app2E f x1 x2 = f %. x1 %. x2
let ifE c t f = !"if" %. c %. t %. f

let decE var type' = Choice1Of3(var, type')
let letE var body = Choice2Of3(var, body)
let recE var body = Choice3Of3(var, body)
let (^.) def cont =
    match def with
    | Choice1Of3(v, t) -> Dec(v, t, cont)
    | Choice2Of3(v, b) -> Let(v, b, cont)
    | Choice3Of3 vb -> LetRec(vb, [], cont)

let (!!!) = function
    | Choice1Of3(x, _)
    | Choice2Of3(x, _) 
    | Choice3Of3(x, _) -> !x

let forall0 t = TypeScheme([], t)
let forall1 f =
    let v1 = newTypeVar()
    TypeScheme([v1], f v1)

let forall2 f =
    let v1, v2 = newTypeVar(), newTypeVar()
    TypeScheme([v1; v2], f v1 v2)


let trueE = Bool true
let (~+) = Int
let (^^.) l r = !"seq" %. l %. r

fsi.AddPrintTransformer <| fun (x: TypeVar) -> box(System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode x, x.contents)


// free (type a. a -> a -> b -> Int) = (_flesh0 -> _flesh0 -> b -> Int)
let a, b = newTypeVar(), newTypeVar()
match free (TypeScheme([a], !!a .-> (!!a .-> (!!b .-> intT)))) with
| FunT(TypeVar a', FunT(TypeVar a'', FunT(TypeVar b', IntT))) -> a' != a && a'' != a && a' == a'' && b == b' && a' != b'
| _ -> false

// bind (x -> y -> Int) = (type x y. x -> y -> Int)
let x, y = newTypeVar(), newTypeVar()
match bind (!!x .-> (!!y .-> intT)) with
| TypeScheme([x'; y'], FunT(TypeVar x'', FunT(TypeVar y'', IntT))) ->
    x == x' && x' == x'' &&
    y == y' && y' == y''

| _ -> false

let ifD = decE "if" <| forall1 (fun a -> boolT .-> (!!a .-> (!!a .-> !!a)))
let seqD = decE "seq" <| forall1 (fun a -> unitT .-> (!!a .-> !!a))

let addIntD = decE "_+_" <| forall0 (intT .-> (intT .-> intT))
let succIntD = decE "succ" <| forall0 (intT .-> intT)

let tup2D = decE "," <| forall2 (fun a b -> !!a .-> (!!b .-> tup2T !!a !!b))

let listEmptyD = decE "List.empty" <| forall1 (listT << (!!))
let listConsD = decE "List.cons" <| forall1 (fun a -> !!a .-> (listT !!a .-> listT !!a))
let listIsEmptyD = decE "List.isEmpty" <| forall1 (fun a -> listT !!a .-> boolT)
let listTailD = decE "List.tail" <| forall1 (fun a -> listT !!a .-> listT !!a)
let listHeadD = decE "List.head" <| forall1 (fun a -> listT !!a .-> !!a)
let listMapD = decE "List.map" <| forall2 (fun a b -> (!!a .-> !!b) .-> (listT !!a .-> listT !!b) )

let idD = letE "id" ("x" ->. !"x")
    
let refD = decE "ref" <| forall1 (fun a -> !!a .-> refT !!a)
let refSetD = decE ":=" <| forall1 (fun a -> refT !!a .-> (!!a .-> unitT))
let refGetD = decE "!" <| forall1 (fun a -> refT !!a .-> !!a)

ifD ^.
letE "f" ("x" ->. !"x") ^.
ifE (!"f" %. trueE) (!"f" %. + 2) (+ 3)
|> typing
    = Ok intT

tup2D ^.
letE "f" ("x" ->. !"x") ^.
app2E !!!tup2D (!"f" %. + 1) (!"f" %. trueE)
|> typing
    = Ok(tup2T intT boolT)

typing (tup2D ^. "f" ->. app2E !!!tup2D (!"f" %. + 1) (!"f" %. trueE)) =
    Error(UnifyError(!"f" %. trueE, intT, boolT))

//let f = List.map (fun x -> x)
//f [1; 2; 3], f []

// TODO: value restriction
listMapD ^.
    idD ^.
    tup2D ^.

    decE "xs" (forall0 (listT intT)) ^.
    decE "xs2" (forall0 (listT boolT)) ^.

    letE "f" (!!!listMapD %. !!!idD) ^.
    app2E !!!tup2D (!"f" %. !"xs") (!"f" %. !"xs2")

    |> typing 
        = Ok(tup2T (listT intT) (listT boolT))


// TODO: value restriction
seqD ^.
    refD ^.
    refSetD ^.
    refGetD ^.
    addIntD ^.
    listHeadD ^.
    listEmptyD ^.

    decE "xs" (forall0 (listT boolT)) ^.

    letE "polyref" (!!!refD %. !!!listEmptyD) ^.
    app2E !!!refSetD !"polyref" !"xs" ^^.
    app2E !!!addIntD (+ 123) (!!!listHeadD %. (!!!refGetD %. !"polyref"))

    |> typing 
        = Ok intT


ifD ^.
    listIsEmptyD ^.
    succIntD ^.
    listTailD ^.
    listConsD ^.
    listEmptyD ^.

    recE "len" ("xs" ->. ifE (!!!listIsEmptyD %. !"xs") (+ 0) (!!!succIntD %. (!"len" %. (!!!listTailD %. !"xs")))) ^.
    !"len" %. (!!!listConsD %. (+ 0) %. !!!listEmptyD)

    |> typing 
        = Ok intT