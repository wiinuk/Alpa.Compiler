type Symbol = string
type Var = string

// Int; Map Int (Set Int); Map a b

type Type =
    | Type of Symbol * Type list
    | TypeVar of TypeVarInfo ref

and TypeVarInfo =
    | SomeType of Type
    | TypeArg of Constraint list

and Constraint =
    | IsLabel of label: Symbol * fieldType: Type

type TypeScheme = TypeScheme of TypeVarInfo ref list * Type
type FieldDef = Symbol * Type
type TypeDef =
    | RecordTypeDef of ctor: Symbol * fields: FieldDef list

type Expr =
    | Bool of bool
    | Int of int
    | Var of Var
    | Lam of Var * Expr
    | App of Expr * Expr
    | Def of Var * TypeScheme * Expr
    | Let of Var * Expr * Expr
    | LetRec of (Var * Expr) * (Var * Expr) list * Expr

    | TypeDef of typeName: Symbol * typeArgs: Type list * TypeDef * Expr

    | NewRecord of ctor: Symbol * fields: FieldDef list
    | FieldGet of Expr * Symbol
    //| FieldUpdate of Expr * Symbol
    
fsi.AddPrintTransformer <| fun (x: TypeVarInfo ref) ->
    box(System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode x, x.contents)

let newTypeVar() : TypeVarInfo ref = ref (TypeArg [])
let newVarT() = TypeVar(newTypeVar())

let refT t = Type("Ref", [t])
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
        | TypeVar { contents = SomeType t } -> free t
        | TypeVar({ contents = TypeArg _ } as v) as t ->
            match List.tryFind (fun (v',_) -> v == v') vts with
            | Some(_,t) -> t
            | None -> t
    free t

let bind t =
    let rec collect vs = function
        | Type(_, ts) -> List.fold collect vs ts
        | TypeVar { contents = SomeType t } -> collect vs t
        | TypeVar({ contents = TypeArg _ } as v) ->
            if List.exists (fun v' -> v == v') vs then vs
            else v::vs

    TypeScheme(collect [] t |> List.rev, t)
    
type Env = {
    vars: Map<Var, TypeScheme>
    types : Map<Var, TypeDef>
}
[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Env =
    let empty = { vars = Map.empty; types = Map.empty }

    let add v t ({ vars = vars } as env) = { env with vars = Map.add v t vars }
    let find v { vars = vars } = Map.find v vars

    let addT v t ({ types = types } as env) = { env with types = Map.add v t types }

type Errors =
    | TypeMismatch of Expr * Type * Type
    | VariableNotFound of Env * Var
    //| DuplicatedTypeArgument of Expr * Type list
    | DuplicatedField of Expr * FieldDef list

exception TypingException of Errors

let rec occur v = function
    | Type(_, ts) -> List.exists (occur v) ts
    | TypeVar({ contents = a } as v') ->
        v == v' ||
            match a with
            | TypeArg _ -> false
            | SomeType t -> occur v t

let rec unify e l r =
    match l, r with
    | Type(ln, ls), Type(rn, rs) when ln = rn && List.length ls = List.length rs -> List.iter2 (unify e) ls rs
    | TypeVar l, TypeVar r when l == r -> ()
    | TypeVar { contents = SomeType l }, _ -> unify e l r
    | _, TypeVar { contents = SomeType r } -> unify e l r
    | TypeVar({ contents = TypeArg _ } as lv), _ when not <| occur lv r -> lv := SomeType r
    | _, TypeVar({ contents = TypeArg _ } as rv) when not <| occur rv l -> rv := SomeType l
    | _ -> raise <| TypingException(TypeMismatch(e, l, r))

let typingTypeDef env e n vs d =
    let listIsSet xs = List.distinct xs = xs
    let rec typeArgs rs = function
        | [] -> List.rev rs
        | TypeVar({ contents = TypeArg [] } as r)::xs when List.forall ((!=) r) rs -> typeArgs (r::rs) xs
        | _::xs -> typeArgs rs xs

    let vs = typeArgs [] vs

    let t = Type(n, List.map TypeVar vs)

    match d with
    | RecordTypeDef(ctor, fs) ->
        if not <| listIsSet (List.map fst fs) then raise <| TypingException(DuplicatedField(e, fs))

        let rec ctorT lastT = function
            | [] -> lastT
            | (_,ft)::fs -> ft .-> (ctorT lastT fs)

        let env = Env.add ctor (ctorT t fs |> bind) env
        List.fold (fun env (f, ft) ->
            Env.add f  env

        ) env fs

let rec typingCore env = function
    | Bool _ -> boolT
    | Int _ -> intT
    | Var v ->
        try free <| Env.find v env
        with
        | :? System.Collections.Generic.KeyNotFoundException ->
            raise <| TypingException(VariableNotFound(env, v))
        
    | Lam(v, e) ->
        let vt = newVarT()
        let env = Env.add v (TypeScheme([], vt)) env
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
        typingCore (Env.add var (bind vt) env) cont

    | LetRec((var, body), varBodys, cont) ->
        let vt, vbts = newVarT(), List.map (fun vb -> vb, newVarT()) varBodys
        let env = List.fold (fun env ((v,_),vt) -> Env.add v (bind vt) env) (Env.add var (bind vt) env) vbts
        unify body vt (typingCore env body)
        List.iter (fun ((_,b),vt) -> unify b vt (typingCore env b)) vbts
        typingCore env cont
        
    | Def(v, t, e) -> typingCore (Env.add v t env) e
    | TypeDef(n, vs, d, cont) as e ->
        let env = typingTypeDef env e n vs d
        typingCore (Env.addT n d env) cont

    | FieldGet(r, l) as e ->
        let rt = typingCore env r
        let ft = newVarT()
        unify e rt (TypeVar(ref (TypeArg [IsLabel(l, ft)])))
        ft
        
let rec deref = function
    | Type(n, ts) -> Type(n, List.map deref ts)
    | TypeVar { contents = TypeArg _ } as t -> t
    | TypeVar({ contents = SomeType t } as v) ->
        let t = deref t
        v := SomeType t
        t

let sprintType t =
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

        | TypeVar { contents = SomeType t } -> print map t
        | TypeVar({ contents = TypeArg _ } as r) ->
            let n, map = printVar map r
            10, map, n

    let printTypeArg map = function
        | { contents = SomeType _ } -> "", map
        | { contents = TypeArg _ } as r -> printVar map r

    let printConstraint map rs = function
        | { contents = SomeType _ } -> rs, map
        | { contents = TypeArg cs } as r -> 
            let v, map = printVar map r
            List.fold (fun (rs, map) c ->
                match c with
                | IsLabel(l, t) ->
                    let p = 9
                    let p', map, t = print map t
                    sprintf "(%s { %s : %s })" v (printId '"' l) (wrap p p' t)::rs, map

            ) (rs, map) cs

    let (TypeScheme(vs, t)) = bind t
    let _,map,t = print [] t

    if List.isEmpty vs then t
    else
        let ts, map =
            List.fold (fun (r, map) v ->
                let r', map = printTypeArg map v
                r + " " + r', map
            ) ("", map) vs

        let cs, _ = List.fold (fun (rs, map) v -> printConstraint map rs v) ([], map) vs
        let cs = 
            match cs with
            | [] -> " "
            | [c] -> sprintf " %s => " c
            | _ -> sprintf " (%s) => " <| String.concat ", " cs

        sprintf "type%s.%s%s" ts cs t
        
    
typingCore Env.empty (Lam("x", FieldGet(Var("x"), "X")))
|> sprintType

type Result<'T,'E> = Ok of 'T | Error of 'E

let typing e =
    try 
        typingCore Env.empty e 
        |> deref
        |> Ok 
    with
    | TypingException e -> Error e

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
    | Choice1Of3(v, t) -> Def(v, t, cont)
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
    Error(TypeMismatch(!"f" %. trueE, intT, boolT))

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