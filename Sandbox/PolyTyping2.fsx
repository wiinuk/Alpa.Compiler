module internal PolyTyping2

type Symbol = string
type Var = string
type assoc<'k,'v> = ('k * 'v) list

/// ex: Map [a] Int; Char -> b
[<NoComparison>]
type Type =
    | Type of Symbol * Type list
    | IndefType of IndefType
    
and [<NoComparison>] IndefTypeInfo =
    | SomeType of Type
    | TypeVar

and IndefType = IndefTypeInfo ref

/// require: function { contents = IndefTypeInfo.TypeVar } -> true | _ -> false
type TypeVar = IndefType

/// ex: (Num a, Ord a) => Set a -> Option a
[<NoComparison>]
type TypeSign = TypeSign of context: Type list * Type

/// ex: type a b. (Eq a, Show b) => [c] -> (c -> a) -> a -> b -> String
[<NoComparison>]
type TypeScheme = TypeScheme of TypeVar list * TypeSign

[<NoComparison>]
type TypeDef =
    | EmptyTypeDef of typeArgs: TypeVar list
    | ClassDef of typeArgs: TypeVar list * assoc<Var, TypeScheme>

[<NoComparison>]
type Expr =
    | Bool of bool
    | Int of int
    | Var of Var
    | Lam of Var * Expr
    | App of Expr * Expr
    | Ext of Var * TypeScheme * Expr
    | Let of Var * Expr * Expr
    | LetRec of assoc<Var, Expr> * Expr
    
    | TypeDef of name: Symbol * TypeDef * Expr
    | InstanceDef of name: Symbol * typeArgs: Type list * methodImpls: assoc<Var, Expr> * cont: Expr
    
let (==) (l: _ ref) (r: _ ref) = obj.ReferenceEquals(l, r)
let (!=) l r = not (l == r)
let refId (x: _ ref) = System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode x

fsi.AddPrintTransformer <| fun (x: IndefType) -> box(refId x, x.contents)
    
let newTypeVar() : TypeVar = ref TypeVar
let newVarT() = IndefType(newTypeVar())

let freeVars (TypeScheme(typeVars, TypeSign(cs, t))) =
    let rec collect vs = function
        | Type(_, ts) -> List.fold collect vs ts
        | IndefType { contents = SomeType t } -> collect vs t
        | IndefType({ contents = TypeVar } as v) ->
            if List.exists ((==) v) typeVars || List.exists ((==) v) vs then vs
            else v::vs

    collect (List.fold collect [] cs) t
    |> List.rev
    
let rec substType vts = function
    | Type(n, ts) -> Type(n, List.map (substType vts) ts)
    | IndefType { contents = SomeType t } -> substType vts t
    | IndefType({ contents = TypeVar _ } as v) as t ->
        match List.tryFind (fun (v',_) -> v == v') vts with
        | Some(_,t) -> t
        | None -> t

let subst vts (TypeSign(cs, t)) = TypeSign(List.map (substType vts) cs, substType vts t)

let newTypeVars vs = 
    List.choose (function
        | { contents = SomeType _ } -> None
        | ({ contents = TypeVar } as v) -> Some(v, newTypeVar())
    ) vs

let free (TypeScheme(vs, t)) = subst (newTypeVars vs |> List.map (fun (v,t) -> v, IndefType t)) t

let bind t =
    let vts = TypeScheme([], t) |> freeVars |> newTypeVars
    let vts' = List.map (fun (v,t) -> v, IndefType t) vts
    TypeScheme(List.map snd vts, subst vts' t)

/// rebind t"type a. Eq b => (a, b, Int)" = t"type x b. Eq y => (x, y, Int)
let rebind = free >> bind

type Result<'T,'E> = Ok of 'T | Error of 'E

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
    | InstanceNotFound of Expr * Env * main: Type * sub: Type
    | InvalidTypeArgments of Expr * TypeVar list
    | DuplicatedMethodDeclare of Expr * assoc<Var, TypeScheme>
    | DuplicatedLetRecDecrale of Expr * assoc<Var, Expr>
    | InvalidInstanceDeclare of Expr
    | MethodNotImplemented of Expr * Symbol
    | MethodMismatch of Expr * Symbol

exception TypingException of Errors

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
    
let refT = type1 "Ref"
let unitT = type0 "()"
let boolT = type0 "Bool"
let intT = type0 "Int"
let lamT = type2 "->"
let lam3T t1 t2 t3 = lamT t1 (lamT t2 t3)
let lam4T t1 t2 t3 t4 = lamT t1 (lamT t2 (lamT t3 t4))
let tup2T = type2 ","
let tupNT l r rs =
    let n =
        match List.length rs with
        | 0 -> ","
        | 1 -> ",,"
        | 2 -> ",,,"
        | n -> String.replicate n "," + ","

    Type(n, l::r::rs)

let listT = type1 "[]"
let (!!) = IndefType
let (.->) = lamT

let (|Type0|Type1|Type2|TypeN|) = function
    | Type(n, []) -> Type0 n
    | Type(n, [t1]) -> Type1(n, t1)
    | Type(n, [t1; t2]) -> Type2(n, t1, t2)
    | t -> TypeN t

let rec (|VarT|_|) = function
    | IndefType({ contents = TypeVar } as v) -> Some v
    | IndefType { contents = SomeType(VarT t) } -> Some t
    | _ -> None

let (|LamT|_|) = function Type2("->", l, r) -> Some(l, r) | _ -> None
let (|Lam3T|_|) = function
    | LamT(t1, LamT(t2, t3)) -> Some(t1, t2, t3)
    | _ -> None

let (|IntT|_|) = function Type0 "Int" -> Some() | _ -> None

let unionContext l r = l @ r

exception SolveException of Type * Type
let solveTS l (TypeScheme(_, TypeSign(rcs, r))) =
    let rec solveT assigns l r =
        match l, r with
        | Type(ln, ls), Type(rn, rs) ->
            if ln = rn && List.length ls = List.length rs
            then List.fold2 solveT assigns ls rs
            else raise <| SolveException(l, r)

        | IndefType { contents = SomeType l }, _ -> solveT assigns l r
        | _, IndefType { contents = SomeType r } -> solveT assigns l r
        | IndefType({ contents = TypeVar } as lv), IndefType({ contents = TypeVar } as rv) ->
            if lv == rv then assigns
            else
                match List.tryFind (fun (rv',_) -> rv == rv') assigns with
                | None -> (rv,l)::assigns
                | Some(_, IndefType({ contents = TypeVar } as rv')) -> if rv == rv' then assigns else raise <| SolveException(l, r)
                | Some(_, IndefType { contents = SomeType r }) -> solveT assigns l r
                | Some(_, Type _) -> raise <| SolveException(l, r)

        | Type _, IndefType({ contents = TypeVar } as rv) ->
            match List.tryFind (fun (rv',_) -> rv == rv') assigns with
            | None -> (rv, l)::assigns
            | Some(_, IndefType({ contents = TypeVar } as rv')) -> if rv == rv' then assigns else raise <| SolveException(l, r)
            | Some(_, IndefType({ contents = SomeType r })) -> solveT assigns l r
            | Some(_, Type _) -> raise <| SolveException(l, r)

        | IndefType { contents = TypeVar }, Type _ -> raise <| SolveException(l, r)

    try
        let vts = solveT [] l r
        List.map (fun rc -> let (TypeSign(_,rc)) = subst vts (typesign0 rc) in rc) rcs
        |> Ok
    with
    | SolveException(l, r) -> Error(l, r)

let (.=>) cs t = TypeSign(cs, t)

let rec appendRev ls rs =
    match ls with
    | [] -> rs
    | l::ls -> appendRev ls (l::rs)
    
let isFullApply t = freeVars t |> List.isEmpty

let solveI t impls =
    let solveOnce t impls =
        List.tryPick (fun impl ->
            match solveTS t impl with
            | Ok contexts -> Some contexts
            | Error _ -> None
        ) impls
        
    let relaxedHandle t = if isFullApply (forall0 <| typesign0 t) then Error t else Ok [t]
    let rec solveRec errorHandle t =
        match solveOnce t impls with
        | None -> errorHandle t
        | Some cs ->
            let rec collect rs = function
                | [] -> Ok <| List.rev rs
                | c::cs ->
                    match solveRec relaxedHandle c with
                    | Ok ts -> collect (appendRev ts rs) cs
                    | e -> e

            collect [] cs

    solveRec Error t

let rec typeEq l r =
    match l, r with
    | Type(ln, ls), Type(rn, rs) -> ln = rn && List.length ls = List.length rs && List.forall2 typeEq ls rs
    | IndefType { contents = SomeType l }, _ -> typeEq l r
    | _, IndefType { contents = SomeType r } -> typeEq l r
    | IndefType({ contents = TypeVar } as l), IndefType({ contents = TypeVar } as r) -> l == r
    | _ -> false

let listEq eq l r = List.compareWith (fun l r -> if eq l r then 0 else 1) l r = 0
let resultEq eq1 eq2 l r =
    match l, r with
    | Ok l, Ok r -> eq1 l r
    | Error l, Error r -> eq2 l r
    | _ -> false

let solveOrRaise e ({ impls = impls } as env) cs =
    let findOrRaise c =
        match solveI c impls with
        | Error t ->
            if isFullApply (forall0 <| typesign0 t)
            then raise <| TypingException(InstanceNotFound(e, env, c, t))
            else [c]
        | Ok cs -> cs

    List.collect findOrRaise cs

let rec occur v = function
    | Type(_, ts) -> List.exists (occur v) ts
    | IndefType({ contents = a } as v') ->
        v == v' ||
            match a with
            | TypeVar _ -> false
            | SomeType t -> occur v t

let rec unify e l r =
    match l, r with
    | Type(ln, ls), Type(rn, rs) when ln = rn && List.length ls = List.length rs -> List.iter2 (unify e) ls rs
    | IndefType l, IndefType r when l == r -> ()
    | IndefType { contents = SomeType l }, _ -> unify e l r
    | _, IndefType { contents = SomeType r } -> unify e l r
    | IndefType({ contents = TypeVar _ } as lv), _ when not <| occur lv r -> lv := SomeType r
    | _, IndefType({ contents = TypeVar _ } as rv) when not <| occur rv l -> rv := SomeType l
    | _ -> raise <| TypingException(TypeMismatch(e, l, r))
    
let isPureTypeArg = function { contents = TypeVar } -> true | _ -> false

let isSetWith eq xs =
    let rec check set = function
        | [] -> true
        | x::xs ->
            if List.exists (eq x) set then false
            else check (x::set) xs
    check [] xs

let unlift (TypeSign(cs, t)) =
    let mutable i = 0
    let mutable map = []
    let varName v =
        if List.exists (fun (v',_) -> v = v') map then
            let _,n = List.find (fun (v',_) -> v = v') map
            n
        else
            let n = i
            map <- (v,n)::map
            i <- i+1
            n

    let rec compareT l r =
        match l, r with
        | _, IndefType { contents = SomeType r } -> compareT l r
        | IndefType { contents = SomeType l }, _ -> compareT l r
        | Type(ln, ls), Type(rn, rs) ->
            match compare ln rn with
            | 0 -> List.compareWith compareT ls rs
            | c -> c

        | Type _, IndefType { contents = TypeVar } -> -1
        | IndefType { contents = TypeVar }, Type _ -> 1
        | IndefType({ contents = TypeVar } as lv), IndefType({ contents = TypeVar } as rv) ->            compare (varName lv) (varName rv)
            

    match List.sortWith compareT cs with
    | [] -> newVarT(), t
    | [c] -> c, t
    | c1::c2::cs -> tupNT c1 c2 cs, t
            

let rec typingCore env = function
    | Bool _ -> typesign0 boolT
    | Int _ -> typesign0 intT
    | Var v ->
        try free <| Env.find v env with
        | :? System.Collections.Generic.KeyNotFoundException ->
            raise <| TypingException(VariableNotFound(env, v))

    | Lam(v, e) ->
        let vt = newVarT()
        let env = Env.add v (TypeScheme([], TypeSign([], vt))) env
        let (TypeSign(ec, et)) = typingCore env e
        TypeSign(ec, lamT vt et)
        
    | App(f, x) as e ->
        let (TypeSign(fc, ft)) = typingCore env f
        let (TypeSign(xc, xt)) = typingCore env x
        let rt = newVarT()

        unify e ft (lamT xt rt)

        TypeSign(solveOrRaise e env (unionContext fc xc), rt)
        
    | Let(var, body, cont) as e ->
        let vt = newVarT()
        let (TypeSign(bc, bt)) = typingCore env body
        unify e vt bt
        typingCore (Env.add var (bind (bc .=> vt)) env) cont

    | LetRec(varBodies, cont) as e ->
        if not <| isSetWith (fun l r -> fst l = fst r) varBodies then raise <| TypingException(DuplicatedLetRecDecrale(e, varBodies))

        let vbts = List.map (fun vb -> vb, newVarT()) varBodies
        let env = List.fold (fun env ((v,_),vt) -> Env.add v (bind([] .=> vt)) env) env vbts

        let env =
            List.fold (fun env ((v,b),vt) ->
                let (TypeSign(bc, bt)) = typingCore env b
                unify b vt bt
                Env.add v (bind(bc .=> bt)) env
            ) env vbts
        typingCore env cont

    | Ext(v, t, e) -> typingCore (Env.add v t env) e

    | TypeDef(name, (EmptyTypeDef vs as td), cont) as e ->
        if List.exists (isPureTypeArg >> not) vs then raise <| TypingException(InvalidTypeArgments(e, vs))
        if not <| isSetWith (==) vs then raise <| TypingException(InvalidTypeArgments(e, vs))

        typingCore (Env.addT name td env) cont

    | TypeDef(name, (ClassDef(vs, ms) as d), cont) as e ->
        if List.exists (isPureTypeArg >> not) vs then raise <| TypingException(InvalidTypeArgments(e, vs))
        if not <| isSetWith (==) vs then raise <| TypingException(InvalidTypeArgments(e, vs))
        if not <| isSetWith (fun l r -> fst l = fst r) ms then raise <| TypingException(DuplicatedMethodDeclare(e, ms))

        let env = Env.addT name d env
        
        let tc = Type(name, List.map IndefType vs)
        let env =   
            List.fold (fun env (n, TypeScheme(mvs, TypeSign(mcs, mt))) ->
                let ft = rebind <| TypeScheme(vs @ mvs, TypeSign(tc::mcs, mt))
                Env.add n ft env
            ) env ms

        typingCore env cont

    | InstanceDef(className, instanceTypeArgs, impls, cont) as e ->
        let td =
            try Env.findT className env with
            | :? System.Collections.Generic.KeyNotFoundException ->
                raise <| TypingException(TypeNotFound(e, env, className))

        match td with
        | EmptyTypeDef _ -> raise <| TypingException(InvalidInstanceDeclare e)
        | ClassDef(classTypeVars, methodDefs) ->
            if List.length instanceTypeArgs <> List.length classTypeVars then raise <| TypingException(InvalidInstanceDeclare e)
            if not <| isSetWith (fun l r -> fst l = fst r) impls then raise <| TypingException(InvalidInstanceDeclare e)

            List.iter (fun (n,_) -> if not <| List.exists (fun (n',_) -> n = n') impls then raise <| TypingException(MethodNotImplemented(e, n))) methodDefs
            List.iter (fun (n,_) -> if not <| List.exists (fun (n',_) -> n = n') methodDefs then raise <| TypingException(MethodMismatch(e, n))) impls
            
            let typeVars = List.map (!) classTypeVars
            List.iter2 (fun classTypeVar instanceTypeArg -> classTypeVar := SomeType instanceTypeArg) classTypeVars instanceTypeArgs

            List.iter (fun (methodName, methodType) ->
                let _, implBody = List.find (fun (n,_) -> n = methodName) impls
                let implType = typingCore env implBody
                let methodType = free methodType
                unify e (lamT <|| unlift implType) (lamT <|| unlift methodType)
            ) methodDefs
 
            List.iter2 (:=) classTypeVars typeVars

            let instanceFreeVars = List.collect (fun t -> freeVars <| TypeScheme([], TypeSign([], t))) instanceTypeArgs

            let instanceType = TypeScheme(instanceFreeVars, TypeSign([], Type(className, instanceTypeArgs)))
            typingCore (Env.addI instanceType env) cont


let deref (TypeSign(cs, t)) =
    let rec derefT = function
        | Type(n, ts) -> Type(n, List.map derefT ts)
        | IndefType { contents = TypeVar _ } as t -> t
        | IndefType({ contents = SomeType t } as v) ->
            let t = derefT t
            v := SomeType t
            t
    TypeSign(List.map derefT cs, derefT t)

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
let appE = (%.)
let app2E f x1 x2 = f %. x1 %. x2
let ifE c t f = !"if" %. c %. t %. f

type Decl =
    | ExtDec of Var * TypeScheme
    | LetDec of Var * Expr
    | RecDec of Var * Expr
    | AndDec of (Var * Expr) list
    | TypDec of Var * TypeDef

let extD var type' = ExtDec(var, type')
let letE var body = LetDec(var, body)
let recE var body = RecDec(var, body)
let typE var typeDef = TypDec(var, typeDef)
let andD = AndDec
let clsE var typeVars methodDefs = typE var (ClassDef(typeVars, methodDefs))
let cls1E var makeDefs =
    let a = newTypeVar()
    clsE var [a] <| makeDefs (IndefType a)

let (^.) def cont =
    match def with
    | ExtDec(v, t) -> Ext(v, t, cont)
    | LetDec(v, b) -> Let(v, b, cont)
    | RecDec(v, b) -> LetRec([v,b], cont)
    | TypDec(v, d) -> TypeDef(v, d, cont)
    | AndDec vds -> LetRec(vds, cont)

let (!!!) = function 
    | ExtDec(x, _) | LetDec(x, _) | RecDec(x, _) | TypDec(x, _) -> !x
    | AndDec _ -> failwithf "AndDec"

let trueE = Bool true
let falseE = Bool false
let (~+) = Int
let (^^.) l r = !"seq" %. l %. r

let mapT = type2 "Map"
let vecT = type1 "Vec"
let numT = type1 "Num"
let eqT = type1 "Eq"

let ifD = extD "if" <| forall1 (fun a -> [] .=> lam4T boolT a a a)
let seqD = extD "seq" <| forall1 (fun a -> [] .=> lam3T unitT a a)

let addIntD = extD "_+_" <| forall0 ([] .=> lam3T intT intT intT)
let succIntD = extD "succ" <| forall0 ([] .=> intT .-> intT)

let tup2D = extD "," <| forall2 (fun a b -> [] .=> lam3T a b (tup2T a b))

let listEmptyD = extD "List.empty" <| forall1 (fun a -> [] .=> listT a)
let listConsD = extD "List.cons" <| forall1 (fun a -> [] .=> lam3T a (listT a) (listT a))
let listIsEmptyD = extD "List.isEmpty" <| forall1 (fun a -> [] .=> listT a .-> boolT)
let listTailD = extD "List.tail" <| forall1 (fun a -> [] .=> listT a .-> listT a)
let listHeadD = extD "List.head" <| forall1 (fun a -> [] .=> listT a .-> a)
let listMapD = extD "List.map" <| forall2 (fun a b -> [] .=> lam3T (a .-> b) (listT a) (listT b))

let idD = letE "id" ("x" ->. !"x")
    
let refD = extD "ref" <| forall1 (fun a -> [] .=> a .-> refT a)
let refSetD = extD ":=" <| forall1 (fun a -> [] .=> lam3T (refT a) a unitT)
let refGetD = extD "!" <| forall1 (fun a -> [] .=> refT a .-> a)

let eqD = cls1E "Eq" <| fun a -> ["_==_", forall0 ([] .=> lam3T a a boolT)]
let numD =
    cls1E "Num" <| fun a ->
        [
        "_-_", forall0 ([] .=> lam3T a a a)
        "_+_", forall0 ([] .=> lam3T a a a)
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

fun _ ->
    /// free (type a. a -> a -> b -> Int) = (_flesh0 -> _flesh0 -> b -> Int)
    let a, b = newTypeVar(), newTypeVar()
    match free <| TypeScheme([a], [] .=> lam4T !!a !!a !!b intT) with
    | TypeSign([], LamT(IndefType a', LamT(IndefType a'', LamT(IndefType b', IntT)))) ->
        a' != a && a'' != a && a' == a'' && b == b' && a' != b'
    | _ -> false

fun _ ->
    /// bind (x -> y -> Int) = (type a b. a -> b -> Int)
    let x, y = newTypeVar(), newTypeVar()
    match bind ([] .=> lam3T !!x !!y intT) with
    | TypeScheme([a; b], TypeSign([], LamT(IndefType a', LamT(IndefType b', IntT)))) ->
        x != a && a == a' && y != b && b == b'
    | _ -> false

ifD ^.
letE "f" ("x" ->. !"x") ^.
ifE (!"f" %. trueE) (!"f" %. + 2) (+ 3)
|> typing
    ==? Ok(forall0 ([] .=> intT))

tup2D ^.
letE "f" ("x" ->. !"x") ^.
app2E !!!tup2D (!"f" %. + 1) (!"f" %. trueE)
|> typing
    ==? Ok(forall0 ([] .=> tup2T intT boolT))

typing (tup2D ^. "f" ->. app2E !!!tup2D (!"f" %. + 1) (!"f" %. trueE)) ==?
    Error(TypeMismatch(!"f" %. trueE, intT, boolT))

// TODO: value restriction
listMapD ^.
    idD ^.
    tup2D ^.

    extD "xs" (forall0 ([] .=> listT intT)) ^.
    extD "xs2" (forall0 ([] .=> listT boolT)) ^.

    letE "f" (!!!listMapD %. !!!idD) ^.
    app2E !!!tup2D (!"f" %. !"xs") (!"f" %. !"xs2")

    |> typing 
        ==? Ok(forall0 ([] .=> tup2T (listT intT) (listT boolT)))


// TODO: value restriction
seqD ^.
    refD ^.
    refSetD ^.
    refGetD ^.
    addIntD ^.
    listHeadD ^.
    listEmptyD ^.

    extD "xs" (forall0 ([] .=> listT boolT)) ^.

    letE "polyref" (!!!refD %. !!!listEmptyD) ^.
    app2E !!!refSetD !"polyref" !"xs" ^^.
    app2E !!!addIntD (+ 123) (!!!listHeadD %. (!!!refGetD %. !"polyref"))

    |> typing 
        ==? Ok(forall0 ([] .=> intT))


ifD ^.
    listIsEmptyD ^.
    succIntD ^.
    listTailD ^.
    listConsD ^.
    listEmptyD ^.

    recE "len" ("xs" ->. ifE (!!!listIsEmptyD %. !"xs") (+ 0) (!!!succIntD %. (!"len" %. (!!!listTailD %. !"xs")))) ^.
    !"len" %. (!!!listConsD %. (+ 0) %. !!!listEmptyD)

    |> typing 
        ==? Ok(forall0 ([] .=> intT))

let fooD = cls1E "Foo" <| fun a -> ["op", forall1 <| fun b -> [numT b] .=> lam3T a b a]

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

fun _ ->
    let a = newTypeVar()
    match free (TypeScheme([a], [numT !!a] .=> !!a)) with
    | TypeSign([Type1("Num", VarT x)], VarT x') -> a != x && x == x'
    | _ -> false

fun _ ->
    let a, b = newTypeVar(), newTypeVar()
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
    let (===?) l r =
        let eq = resultEq (listEq typeEq) typeEq
        if not <| eq l r then printfn "assert (==) %A %A" l r

    let isError = function Error _ -> () | x -> printfn "isError %A" x

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
    solveI (numT (vecT boolT)) [forall1 (fun x -> [eqT x] .=> numT (vecT x)); forall0([] .=> eqT boolT)] ===? Ok []
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

// type Bool
// True : type. () => Bool
// False : type. () => Bool
// if : type a. () => Bool -> a -> a
//
//
// class Eq a = { (==): a -> a -> Bool }
// class Num a = { (-): a -> a -> a }
//
// (==) : type a. Eq a => a -> a -> Bool
// ``0`` : type a. Num a => a
// ``1`` : type a. Num a => a
// 
// rec even = \n. if (n == 0) True (odd (n - 1))
// and odd = \n. if (n == 0) False (even (n - 1))
// in even

    // class Num a ...
    // succ : type a. Num a => a -> a
    // zero : type. () => Int
    // instance Num Int ...
    //
    // succ zero
    // (succ: Num a => a -> a) zero
    // (succ: Num a => a -> a) (zero: () => Int)
    // ((succ: Num a => a -> a) (zero: () => Int)) : b
    // unify _ (a -> a) (Int -> b)
    // ((succ: Num Int => Int -> Int) (zero: () => Int)) : Int
    // ((succ: Num Int => Int -> Int) (zero: () => Int)) : () => Int
    
    // class Num a = ...
    // zero : type. () => Int
    // instance Num Int ...
    //
    // n: a = 0; n
    // n: a = (0: Num x => x); n
    // unify _ a x
    // n: a = (0: Num a => a); n
    // n: type a. Num a => a = (0: Num a => a); n
    // n: type a. Num a => a = (0: Num a => a); (n: Num x => x)
        // class Num a where
        //    add: type. a -> a -> a
        //    negate: type. a -> a
        //    zero: type. a

        // add : type a. Num a => a -> a -> a
        // negate : type a. Num a => a -> a
        // zero : type a. Num a => a
        
            // class ShowN a where { showN : type b. Num b => b -> a -> String }
            //
            // instance ShowN (Vec x) where { showN _ _ = "[...]" }
            //
            // type ShowN a = {
            //     showN : type b. Num b => b -> a -> String
            // }
            // ``show::Vec(1)`` : type x. ShowN (Vec x) = {
            //    showN : type y. Num y => y -> Vec x -> String = \ _ _ -> "[...]"
            // }

            // type ShowN a = {
            //     showN : type b. Num b => b -> a -> String
            // }
            // ``show::Vec(1)`` : type x. ShowN (Vec x) = {
            //     showN : type y. Num y => y -> Vec x -> String = \ _ _ -> "[...]"
            // }
            