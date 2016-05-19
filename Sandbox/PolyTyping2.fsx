module internal PolyTyping2

type Symbol = string
type Var = string
type assoc<'k,'v> = ('k * 'v) list

// Map [a] Int; Char -> b
type Type =
    | Type of Symbol * Type list
    | IndefType of IndefType
    
and IndefTypeInfo =
    | SomeType of Type
    | TypeVar

and IndefType = IndefTypeInfo ref

/// require: function { contents = IndefTypeInfo.TypeVar } -> true | _ -> false
type TypeVar = IndefType

// (Num a, Ord a) => Set a -> Option a
type TypeSign = TypeSign of context: Type list * Type

// type a b. (Eq a, Show b) => [c] -> (c -> a) -> a -> b -> String
type TypeScheme = TypeScheme of TypeVar list * TypeSign
type TypeDef =
    | EmptyTypeDef of typeArgs: TypeVar list
    | ClassDef of typeArgs: TypeVar list * assoc<Var, TypeScheme>

type Expr =
    | Bool of bool
    | Int of int
    | Var of Var
    | Lam of Var * Expr
    | App of Expr * Expr
    | Def of Var * TypeScheme * Expr
    | Let of Var * Expr * Expr
    | LetRec of assoc<Var, Expr> * Expr
    
    | TypeDef of name: Symbol * TypeDef * Expr
    | InstanceDef of name: Symbol * typeArgs: Type list * methodImpls: assoc<Var, Expr> * cont: Expr

type Env = {
    vars: Map<Var, TypeScheme>
    types: Map<Var, TypeDef>
    impls: TypeScheme list
}
[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Env =
    let empty = {
        vars = Map.empty
        types = Map.empty
        impls = []
    }

    let add v t ({ vars = vars } as env) = { env with vars = Map.add v t vars }
    let find v { vars = vars } = Map.find v vars

    let addT v t ({ types = types } as env) = { env with types = Map.add v t types }
    let findT v { types = types } = Map.find v types

    let addI t ({ impls = impls } as env) = { env with impls = t::impls }

type Errors =
    | TypeMismatch of Expr * Type * Type
    | VariableNotFound of Env * Var
    | TypeNotFound of Expr * Env * Symbol
    | InvalidTypeArgments of Expr * TypeVar list
    | DuplicatedMethodDeclare of Expr * assoc<Var, TypeScheme>
    | InvalidInstanceDeclare of Expr
    | MethodNotImplemented of Expr * Symbol
    | MethodMismatch of Expr * Symbol

exception TypingException of Errors

let (==) (l: _ ref) (r: _ ref) = obj.ReferenceEquals(l, r)
let (!=) l r = not (l == r)
let refId (x: _ ref) = System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode x

fsi.AddPrintTransformer <| fun (x: IndefType) -> box(refId x, x.contents)
    
let typesign0 t = TypeSign([], t)
let type0 n = typesign0 <| Type(n, [])
let type1 n (TypeSign(cs1, t1)) = TypeSign(cs1, Type(n, [t1]))
let type2 n (TypeSign(cs1, t1)) (TypeSign(cs2, t2)) = TypeSign(cs1 @ cs2, Type(n, [t1; t2]))

let newTypeVar() : TypeVar = ref TypeVar
let newVarT() = typesign0 <| IndefType(newTypeVar())

let refT = type1 "Ref"
let unitT = type0 "()"
let boolT = type0 "Bool"
let intT = type0 "Int"
let funT = type2 "->"
let tup2T = type2 ","
let listT = type1 "[]"
let (!!) = IndefType
let (.->) = funT

let (|Type0|Type1|Type2|TypeN|) = function
    | Type(n, []) -> Type0 n
    | Type(n, [t1]) -> Type1(n, t1)
    | Type(n, [t1; t2]) -> Type2(n, t1, t2)
    | t -> TypeN t

let (|FunT|_|) = function Type2("->", l, r) -> Some(l, r) | _ -> None
let (|IntT|_|) = function Type0 "Int" -> Some() | _ -> None

let freeVars (TypeScheme(typeVars, TypeSign(cs, t))) =
    let rec collect vs = function
        | Type(_, ts) -> List.fold collect vs ts
        | IndefType { contents = SomeType t } -> collect vs t
        | IndefType({ contents = TypeVar } as v) ->
            if List.exists ((==) v) typeVars || List.exists ((==) v) vs then vs
            else v::vs

    collect (List.fold collect [] cs) t
    |> List.rev

// type a. Eq a => a -> a
// type a b. (Eq a, Show a, Eq b) => [a] -> [b] -> String
// type f a b. (Eq (f a), Functor f) => (a -> b) -> f a -> f b -> Bool

// class Foo a where { op : Num b => a -> b -> a }
// op : type a b. (Foo a, Num b) => a -> b -> a

// double : type a. Num a => a -> a
// double x = x + x 

// free (type a. Num a => a) = Num _flesh0 => _flesh0
// free (type a b. Num b => a) = Num _flesh0 => _flesh1
// free (Num Int => Int) = ???

// free (type (Num a => a) b. (Num a => a) -> b) = ((Num _fresh0 => _fresh0) -> _fresh1o)
// free (type (Num a => a). Num a => a) = ((Num _fresh0 => _fresh0) -> _fresh1o)


let rec substType vts = function
    | Type(n, ts) -> Type(n, List.map (substType vts) ts)
    | IndefType { contents = SomeType t } -> substType vts t
    | IndefType({ contents = TypeVar _ } as v) as t ->
        match List.tryFind (fun (v',_) -> v == v') vts with
        | Some(_,t) -> IndefType t
        | None -> t

let subst vts (TypeSign(cs, t)) = TypeSign(List.map (substType vts) cs, substType vts t)

let newVars vs = 
    List.choose (function
        | { contents = SomeType _ } -> None
        | ({ contents = TypeVar } as v) -> Some(v, newTypeVar())
    ) vs

let free (TypeScheme(vs, t)) = subst (newVars vs) t

let bind t =
    let vts = TypeScheme([], t) |> freeVars |> newVars
    TypeScheme(List.map snd vts, subst vts t)

let rebind = free >> bind

let rec occur v = function
    | Type(_, ts) -> List.exists (occur v) ts
    | IndefType({ contents = a } as v') ->
        v == v' ||
            match a with
            | TypeVar _ -> false
            | SomeType t -> occur v t

let rec unifyT e l r =
    match l, r with
    | Type(ln, ls), Type(rn, rs) when ln = rn && List.length ls = List.length rs -> List.iter2 (unifyT e) ls rs
    | IndefType l, IndefType r when l == r -> ()
    | IndefType { contents = SomeType l }, _ -> unifyT e l r
    | _, IndefType { contents = SomeType r } -> unifyT e l r
    | IndefType({ contents = TypeVar _ } as lv), _ when not <| occur lv r -> lv := SomeType r
    | _, IndefType({ contents = TypeVar _ } as rv) when not <| occur rv l -> rv := SomeType l
    | _ -> raise <| TypingException(TypeMismatch(e, l, r))
    
let unify e (TypeSign(_, l)) (TypeSign(_, r)) = unifyT e l r

let isPureTypeArg = function { contents = TypeVar } -> true | _ -> false
let typeArgEq l r =
    match l, r with
    | IndefType({ contents = TypeVar } as l), IndefType({ contents = TypeVar } as r) -> l == r
    | _ -> true

let isSetWith eq xs =
    let rec check set = function
        | [] -> true
        | x::xs ->
            if List.exists (eq x) set then false
            else check (x::set) xs
    check [] xs

let co _ = () 
let t (_: string) : Type = failwith ""

let rec typingCore env = function
    | Bool _ -> boolT
    | Int _ -> intT
    | Var v ->
        try free <| Env.find v env with
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

    | LetRec(varBodys, cont) ->
        let vbts = List.map (fun vb -> vb, newVarT()) varBodys
        let env = List.fold (fun env ((v,_),vt) -> Env.add v (bind vt) env) env vbts
        List.iter (fun ((_,b),vt) -> unify b vt (typingCore env b)) vbts
        typingCore env cont

    | Def(v, t, e) -> typingCore (Env.add v t env) e

    | TypeDef(name, (EmptyTypeDef vs as td), cont) as e ->
        if List.exists (isPureTypeArg >> not) vs then raise <| TypingException(InvalidTypeArgments(e, vs))
        if not <| isSetWith (==) vs then raise <| TypingException(InvalidTypeArgments(e, vs))

        typingCore (Env.addT name td env) cont

    | TypeDef(name, (ClassDef(vs, ms) as d), cont) as e ->
        if List.exists (isPureTypeArg >> not) vs then raise <| TypingException(InvalidTypeArgments(e, vs))
        if not <| isSetWith (==) vs then raise <| TypingException(InvalidTypeArgments(e, vs))
        if not <| isSetWith (fun l r -> fst l = fst r) ms then raise <| TypingException(DuplicatedMethodDeclare(e, ms))

        let env = Env.addT name d env

        // class Num a where
        //    add: type. a -> a -> a
        //    negate: type. a -> a
        //    zero: type. a

        // add : type a. Num a => a -> a -> a
        // negate : type a. Num a => a -> a
        // zero : type a. Num a => a
        
        let tc = Type(name, List.map IndefType vs)
        let env =   
            List.fold (fun env (n, TypeScheme(mvs, TypeSign(mcs, mt))) ->
                let ft = rebind <| TypeScheme(vs @ mvs, TypeSign(tc::mcs, mt))
                Env.add n ft env
            ) env ms

        typingCore env cont

    | InstanceDef(className, instanceTypeArgs, is, cont) as e ->
        let td =
            try Env.findT className env with
            | :? System.Collections.Generic.KeyNotFoundException ->
                raise <| TypingException(TypeNotFound(e, env, className))

        match td with
        | EmptyTypeDef _ -> raise <| TypingException(InvalidInstanceDeclare e)
        | ClassDef(classTypeVars, methodDefs) ->
            if List.length instanceTypeArgs <> List.length classTypeVars then raise <| TypingException(InvalidInstanceDeclare e)
            if not <| isSetWith (fun l r -> fst l = fst r) is then raise <| TypingException(InvalidInstanceDeclare e)

            List.iter (fun (n,_) -> if not <| List.exists (fun (n',_) -> n = n') is then raise <| TypingException(MethodNotImplemented(e, n))) methodDefs
            List.iter (fun (n,_) -> if not <| List.exists (fun (n',_) -> n = n') methodDefs then raise <| TypingException(MethodMismatch(e, n))) is
            
            // class ShowN a where { showN : type b. Num b => b -> a -> String }
            //
            // instance ShowN (Vec x) where { showN _ _ = "[...]" }
            //
            // ``show::Vec(1)`` : type x. ShowN (Vec x) = {
            //    showN : type y. Num y => y -> Vec x -> String = \ _ _ -> "[...]"
            // }
            
            // classTypeVars :: [`a`]
            // instanceTypeArgs :: [`Vec x`]
            let typeVars = List.map (!) classTypeVars
            List.iter2 (fun classTypeVar instanceTypeArg -> classTypeVar := SomeType instanceTypeArg) classTypeVars instanceTypeArgs

            // classTypeVars :: [`Vec x`]
            co <@ classTypeVars, [t"Vec x"] @>
            co <@ methodDefs, ["showN", t"type b. Num b => b -> Vec x -> String"] @>

            List.iter (fun (methodName, methodType) ->
                co <@ methodType, t"type b. Num b => b -> Vec x -> String" @>

                let _, implBody = List.find (fun (n,_) -> n = methodName) is
                co <@ implBody, (fun xs n -> "[...]") @>

                let implType = typingCore env implBody
                co <@ implType, t"t -> u -> String" @>

                let methodType = free methodType
                co <@ methodType, t"Num v => v -> Vec x -> String" @>

                unify e implType methodType
                co <@ implType, t"Num v => v -> Vec x -> String" @>
            ) methodDefs
 
            List.iter2 (fun classTypeVar typeVar -> classTypeVar := typeVar) classTypeVars typeVars

            let instanceFreeVars = List.collect (fun t -> freeVars <| TypeScheme([], TypeSign([], t))) instanceTypeArgs
            co <@ instanceTypeArgs, [t"x"] @>

            let instanceType = TypeScheme(instanceFreeVars, TypeSign([], Type(className, instanceTypeArgs)))
            typingCore (Env.addI instanceType env) cont


let rec deref = function
    | Type(n, ts) -> Type(n, List.map deref ts)
    | IndefType { contents = TypeVar _ } as t -> t
    | IndefType({ contents = SomeType t } as v) ->
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

        | IndefType { contents = SomeType t } -> print map t
        | IndefType({ contents = TypeVar _ } as r) ->
            let n, map = printVar map r
            10, map, n

    let printTypeArg map = function
        | { contents = SomeType _ } -> "", map
        | { contents = TypeVar _ } as r -> printVar map r

    let printConstraint map rs = function
        | { contents = SomeType _ } -> rs, map
        | { contents = TypeVar } as r -> printVar map r

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
        

//typingCore Env.empty (Lam("x", FieldGet(Var("x"), "X")))
//|> sprintType

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
    | Choice3Of3 vb -> LetRec([vb], cont)

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
| FunT(IndefType a', FunT(IndefType a'', FunT(IndefType b', IntT))) -> a' != a && a'' != a && a' == a'' && b == b' && a' != b'
| _ -> false

// bind (x -> y -> Int) = (type x y. x -> y -> Int)
let x, y = newTypeVar(), newTypeVar()
match bind (!!x .-> (!!y .-> intT)) with
| TypeScheme([x'; y'], FunT(IndefType x'', FunT(IndefType y'', IntT))) ->
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