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
    | DataDef of typeArgs: TypeVar list * assoc<Var, Type list>
    | ClassDef of typeArgs: TypeVar list * assoc<Var, TypeScheme>

type Pat =
    | AnyPat
    | ConPat of Var * Pat list
    | LitPat of TypeScheme
    | AsPat of Pat * Var

type Lit =
    | IntegerLit of bigint
    | IntLit of int
    | FloatLit of float
    | CharLit of char
    | StringLit of string

[<NoComparison>]
type Exp =
    | Lit of Lit
    | Var of Var
    | Lam of Var * Exp
    | App of Exp * Exp
    | Ext of Var * TypeScheme * Exp
    | Let of Var * Exp * Exp
    | LetRec of assoc<Var, Exp> * Exp
    
    | Mat of Exp * (Pat * Exp) * (Pat * Exp) list

    | TypeDef of name: Symbol * TypeDef * Exp
    | InstanceDef of name: Symbol * typeArgs: Type list * methodImpls: assoc<Var, Exp> * cont: Exp

type Env = {
    vars: Map<Var, TypeScheme>
    pats: Map<Var, TypeScheme>
    types: Map<Var, TypeDef>
    impls: TypeScheme list
}
type Errors =
    | TypeMismatch of Exp * Type * Type

    | VariableNotFound of Env * Var
    | TypeNotFound of Exp * Env * Symbol
    | InstanceNotFound of Exp * Env * main: Type * sub: Type
    | PatternNotFound of Exp * Env * Var

    | DuplicatedMethodDeclare of Exp * assoc<Var, TypeScheme> * Var
    | DuplicatedLetRecDecrale of Exp * assoc<Var, Exp> * Var
    | DuplicatedPatternVariable of Exp * Var
    | DuplicatedTypeArgment of Exp * TypeVar list * TypeVar
    | DuplicatedInstanceImplement of Exp * Var

    | InvalidInstanceDeclare of Exp
    | InvalidTypeArgments of Exp * TypeVar list
    | InvalidConstructorPattern of Exp * TypeScheme * Pat

    | MethodNotImplemented of Exp * Symbol
    | MethodMismatch of Exp * Symbol

exception TypingException of Errors
let raiseTypengExn e = raise <| TypingException e

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Env =
    let empty = {
        vars = Map.empty
        pats = Map.empty
        types = Map.empty
        impls = []
    }

    let add v t ({ vars = vars } as env) = { env with vars = Map.add v t vars }
    let find v { vars = vars } = Map.find v vars

    let addP v t ({ pats = pats } as env) = { env with pats = Map.add v t pats }
    let tryFindP v { pats = pats } = Map.tryFind v pats

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

let primCharT = TypeSign([], Type("Char", []))
let primStringT = TypeSign([], Type("String", []))
let primIntegerT = TypeSign([], Type("Integer", []))
let primIntT = TypeSign([], Type("Int", []))
let primFloatT = TypeSign([], Type("Float", []))

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
            then raiseTypengExn <| InstanceNotFound(e, env, c, t)
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
    | _ -> raiseTypengExn <| TypeMismatch(e, l, r)
    
let isPureTypeArg = function { contents = TypeVar } -> true | _ -> false

let tryGetDuplicated eq xs =
    let rec check set = function
        | [] -> None
        | x::xs ->
            match List.tryFind (fun x' -> eq x x') set with
            | None -> check (x::set) xs
            | x -> x
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

let rec (|LamT|_|) = function
    | Type("->", [t1;t2]) -> Some(t1, t2)
    | IndefType { contents = SomeType t } -> (|LamT|_|) t
    | _ -> None

let rec (|LamNT|_|) = function
    | LamT(t1,LamNT(t2,t3,ts)) -> Some(t1,t2,t3::ts)
    | LamT(t1,t2) -> Some(t1,t2,[])
    | _ -> None

let typingPat e env p =
    let rec aux locals = function 
        | AnyPat -> TypeSign([], newVarT()), locals
        | ConPat(v, ps) as p ->
            match Env.tryFindP v env, ps with
            | None, [] ->
                if List.exists (fst >> (=) v) locals then raiseTypengExn <| DuplicatedPatternVariable(e, v)
                else
                    let t = TypeSign([], newVarT())
                    t, (v, t)::locals

            | None, _::_ -> raiseTypengExn <| PatternNotFound(e, env, v)
            | Some(TypeScheme(_, TypeSign(_, LamNT _)) as t), [] -> raiseTypengExn <| InvalidConstructorPattern(e, t, p)
            | Some t, [] -> free t, locals
            | Some t, _::_ ->
                match free t with
                | TypeSign(tc, LamNT(dt, ft, fts)) ->
                    if List.length ps <> List.length fts + 1 then raiseTypengExn <| InvalidConstructorPattern(e, t, p)
                    let fts = ft::fts
                    let tc, locals =
                        List.fold2 (fun (tc, locals) p ft ->
                            let (TypeSign(pc, pt)), locals = aux locals p
                            unify e ft pt
                            unionContext tc pc, locals
                        ) (tc, locals) ps fts

                    TypeSign(tc, dt), locals

                | _ -> raiseTypengExn <| InvalidConstructorPattern(e, t, p)

        | LitPat t -> free t, locals
        | AsPat(p, v) ->
            let pt, locals = aux locals p
            if List.exists (fst >> (=) v) locals then raiseTypengExn <| DuplicatedPatternVariable(e, v)
            else
                pt, (v, pt)::locals


    let t, locals = aux [] p
    t, List.fold (fun env (v,t) -> Env.add v (TypeScheme([], t)) env) env locals

let typingVar env v = 
    try free <| Env.find v env with
    | :? System.Collections.Generic.KeyNotFoundException ->
        raiseTypengExn <| VariableNotFound(env, v)

let rec typingApp env f x e =
    let (TypeSign(fc, ft)) = typingCore env f
    let (TypeSign(xc, xt)) = typingCore env x
    let rt = newVarT()
    unify e ft (lamT xt rt)
    TypeSign(solveOrRaise e env (unionContext fc xc), rt)

and typingLam env v e =
    let vt = newVarT()
    let env = Env.add v (TypeScheme([], TypeSign([], vt))) env
    let (TypeSign(ec, et)) = typingCore env e
    TypeSign(ec, lamT vt et)

and typingLet env var body cont e =
    let vt = newVarT()
    let (TypeSign(bc, bt)) = typingCore env body
    unify e vt bt
    typingCore (Env.add var (bind (TypeSign(bc, vt))) env) cont

and typingRec env varBodies cont e =
    match tryGetDuplicated (fun l r -> fst l = fst r) varBodies with
    | Some(v, _) -> raiseTypengExn <| DuplicatedLetRecDecrale(e, varBodies, v)
    | _ ->
        let vbts = List.map (fun vb -> vb, newVarT()) varBodies
        let env = List.fold (fun env ((v,_),vt) -> Env.add v (bind (TypeSign([], vt))) env) env vbts

        let env =
            List.fold (fun env ((v,b),vt) ->
                let (TypeSign(bc, bt)) = typingCore env b
                unify b vt bt
                Env.add v (bind (TypeSign(bc, bt))) env
            ) env vbts
        typingCore env cont

and typingMat env v (p, m) pms e =
    let (TypeSign(vc, vt)) = typingCore env v
    let (TypeSign(pc, pt)), env = typingPat e env p
    let (TypeSign(rc, rt)) = typingCore env m

    unify e vt pt

    let vc = unionContext vc pc
    let vc, rc =
        List.fold (fun (vc, rc) (p, m) ->
            let (TypeSign(pc, pt)), env = typingPat e env p
            let (TypeSign(mc, mt)) = typingCore env m
            unify e vt pt
            unify e mt rt
            unionContext vc pc, unionContext rc mc
        ) (vc, rc) pms

    let rc = solveOrRaise e env <| unionContext vc rc
    TypeSign(rc, rt)
    
and typingDataDef env name (td, vs, cs) cont e =
    let rec conType last = function
        | [] -> last
        | t::ts -> lamT t (conType last ts)

    let patType first = function
        | [] -> first
        | t::ts ->
            let rec aux l = function
                | [] -> l
                | r::rs -> lamT l (aux r rs)
            lamT first (aux t ts)

    let typingCon t env (v, ts) =
        let ct = bind <| TypeSign([], conType t ts)
        let pt = bind <| TypeSign([], patType t ts)

        let env = Env.add v ct env
        let env = Env.add (name + "." + v) ct env
        let env = Env.addP v pt env
        let env = Env.addP (name + "." + v) pt env
        env

    match List.exists (isPureTypeArg >> not) vs, tryGetDuplicated (==) vs with
    | true, _ -> raiseTypengExn <| InvalidTypeArgments(e, vs)
    | _, Some v -> raiseTypengExn <| DuplicatedTypeArgment(e, vs, v)
    | _ ->
        let t = Type(name, List.map IndefType vs)
        let env = Env.addT name td env
        let env = List.fold (typingCon t) env cs
        typingCore (Env.addT name td env) cont

and typingClassDef env name (td, vs, ms) cont e =
    if List.exists (isPureTypeArg >> not) vs then raiseTypengExn <| InvalidTypeArgments(e, vs)
    match tryGetDuplicated (==) vs, tryGetDuplicated (fun l r -> fst l = fst r) ms with
    | Some v, _ -> raiseTypengExn <| DuplicatedTypeArgment(e, vs, v)
    | _, Some(v,_) -> raiseTypengExn <| DuplicatedMethodDeclare(e, ms, v)
    | _ ->
        let env = Env.addT name td env
        let tc = Type(name, List.map IndefType vs)
        let env =   
            List.fold (fun env (n, TypeScheme(mvs, TypeSign(mcs, mt))) ->
                let ft = rebind <| TypeScheme(vs @ mvs, TypeSign(tc::mcs, mt))
                Env.add n ft env
            ) env ms

        typingCore env cont


and typingTypeDef env name td cont e =
    match td with
    | DataDef(vs, cs) -> typingDataDef env name (td, vs, cs) cont e
    | ClassDef(vs, ms) -> typingClassDef env name (td, vs, ms) cont e

and typingInsDef env (className, instanceTypeArgs, impls, cont) e =
    let td =
        try Env.findT className env with
        | :? System.Collections.Generic.KeyNotFoundException ->
            raiseTypengExn <| TypeNotFound(e, env, className)

    match td with
    | DataDef _ -> raiseTypengExn <| InvalidInstanceDeclare e
    | ClassDef(classTypeVars, methodDefs) ->
        if List.length instanceTypeArgs <> List.length classTypeVars then raiseTypengExn <| InvalidInstanceDeclare e

        match tryGetDuplicated (fun l r -> fst l = fst r) impls with
        | Some(v,_) -> raiseTypengExn <| DuplicatedInstanceImplement(e, v)
        | _ ->
            List.iter (fun (n,_) -> if not <| List.exists (fun (n',_) -> n = n') impls then raiseTypengExn <| MethodNotImplemented(e, n)) methodDefs
            List.iter (fun (n,_) -> if not <| List.exists (fun (n',_) -> n = n') methodDefs then raiseTypengExn <| MethodMismatch(e, n)) impls
            
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

and typingLit _ = function
    | CharLit _ -> primCharT
    | StringLit _ -> primStringT
    | IntegerLit _ -> primIntegerT
    | IntLit _ -> primIntT
    | FloatLit _ -> primFloatT

and typingCore env = function
    | Lit l -> typingLit env l
    | Var v -> typingVar env v
    | Lam(v, e) -> typingLam env v e
    | App(f, x) as e -> typingApp env f x e
    | Let(var, body, cont) as e -> typingLet env var body cont e
    | LetRec(varBodies, cont) as e -> typingRec env varBodies cont e
    | Mat(v, pm, pms) as e -> typingMat env v pm pms e
    | Ext(v, t, e) -> typingCore (Env.add v t env) e
    | TypeDef(name, td, cont) as e -> typingTypeDef env name td cont e
    | InstanceDef(name, typeArgs, impls, cont) as e -> typingInsDef env (name, typeArgs, impls, cont) e

let deref (TypeSign(cs, t)) =
    let rec derefT = function
        | Type(n, ts) -> Type(n, List.map derefT ts)
        | IndefType { contents = TypeVar _ } as t -> t
        | IndefType({ contents = SomeType t } as v) ->
            let t = derefT t
            v := SomeType t
            t
    TypeSign(List.map derefT cs, derefT t)
