module PolyTyping2

type Result<'T,'E> = Ok of 'T | Error of 'E

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
    | Lit of TypeScheme
    | Var of Var
    | Lam of Var * Expr
    | App of Expr * Expr
    | Ext of Var * TypeScheme * Expr
    | Let of Var * Expr * Expr
    | LetRec of assoc<Var, Expr> * Expr
    
    | TypeDef of name: Symbol * TypeDef * Expr
    | InstanceDef of name: Symbol * typeArgs: Type list * methodImpls: assoc<Var, Expr> * cont: Expr
    
type Env = {
    vars: Map<Var, TypeScheme>
    types: Map<Var, TypeDef>
    impls: TypeScheme list
}
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

let (==) (l: _ ref) (r: _ ref) = obj.ReferenceEquals(l, r)
    
let newTypeVar() : TypeVar = ref TypeVar
let newVarT() = IndefType(newTypeVar())

let rec collectFreeVarsRev knownVars = function
    | Type(_, ts) -> List.fold collectFreeVarsRev knownVars ts
    | IndefType { contents = SomeType t } -> collectFreeVarsRev knownVars t
    | IndefType({ contents = TypeVar } as v) -> if List.exists ((==) v) knownVars then knownVars else v::knownVars

let freeVars t = collectFreeVarsRev [] t |> List.rev
let freeVarsT (TypeSign(cs, t)) = collectFreeVarsRev (List.fold collectFreeVarsRev [] cs) t |> List.rev
    
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
    let vts = freeVarsT t |> newTypeVars
    let vts' = List.map (fun (v,t) -> v, IndefType t) vts
    TypeScheme(List.map snd vts, subst vts' t)

/// rebind t"type a. Eq b => (a, b, Int)" = t"type x b. Eq y => (x, y, Int)
let rebind = free >> bind

let lamT t1 t2 = Type("->", [t1;t2])
let tupNT l r rs =
    let n =
        match List.length rs with
        | 0 -> ","
        | 1 -> ",,"
        | 2 -> ",,,"
        | n -> String.replicate n "," + ","

    Type(n, l::r::rs)
    
/// typeEq t"Num a" t"Num b" = false
let rec typeEq l r =
    match l, r with
    | Type(ln, ls), Type(rn, rs) -> ln = rn && List.length ls = List.length rs && List.forall2 typeEq ls rs
    | IndefType { contents = SomeType l }, _ -> typeEq l r
    | _, IndefType { contents = SomeType r } -> typeEq l r
    | IndefType({ contents = TypeVar } as l), IndefType({ contents = TypeVar } as r) -> l == r
    | _ -> false

let unionContext ls rs =
    let ls = List.filter (fun l -> not <| List.exists (typeEq l) rs) ls
    ls @ rs

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
        List.map (fun rc -> let (TypeSign(_,rc)) = subst vts (TypeSign([], rc)) in rc) rcs
        |> Ok
    with
    | SolveException(l, r) -> Error(l, r)

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
        
    let relaxedHandle t = if isFullApply t then Error t else Ok [t]
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

let solveOrRaise e ({ impls = impls } as env) cs =
    let findOrRaise c =
        match solveI c impls with
        | Error t ->
            if isFullApply t
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
    | Lit t -> free t
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
        typingCore (Env.add var (bind (TypeSign(bc, vt))) env) cont

    | LetRec(varBodies, cont) as e ->
        if not <| isSetWith (fun l r -> fst l = fst r) varBodies then raise <| TypingException(DuplicatedLetRecDecrale(e, varBodies))

        let vbts = List.map (fun vb -> vb, newVarT()) varBodies
        let env = List.fold (fun env ((v,_),vt) -> Env.add v (bind (TypeSign([], vt))) env) env vbts

        let env =
            List.fold (fun env ((v,b),vt) ->
                let (TypeSign(bc, bt)) = typingCore env b
                unify b vt bt
                Env.add v (bind (TypeSign(bc, bt))) env
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

            let instanceFreeVars = List.collect freeVars instanceTypeArgs

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
