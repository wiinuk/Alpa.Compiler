module PolyTyping2.Typing
#load "PolyTyping2.fsx"
open PolyTyping2
open System.Collections.Generic

type TPat =
    | AnyPat
    | VarPat of Var * TypeSign
    | ConPat of Var * TPat * TPat list
    | LitPat of TypeScheme
    | AsPat of TPat * Var * TypeSign

[<NoComparison>]
type TExp =
    | Lit of Lit
    | Var of Var * TypeSign
    | Lam of Var * TypeSign * TExp
    | App of TExp * TExp
    | Ext of Var * TypeScheme * TExp
    | Let of Var * TypeScheme * TExp * TExp
    | LetRec of assoc<Var, TypeScheme * TExp> * TExp

    | Mat of TExp * (TPat * TExp) * (TPat * TExp) list

    | TypeDef of name: Symbol * TypeDef * TExp
    | InstanceDef of name: Symbol * typeArgs: Type list * methodImpls: assoc<Var, TypeScheme * TExp> * cont: TExp

type P = PolyTyping2.Pat
type E = PolyTyping2.Exp
let (!?) e = raise <| TypingException e

let typingPat e env p =
    let rec aux locals = function 
        | P.AnyPat -> AnyPat, TypeSign([], newVarT()), locals
        | P.ConPat(v, ps) as p ->
            match Env.tryFindP v env, ps with
            | None, [] ->
                if List.exists (fst >> (=) v) locals then !?DuplicatedPatternVariable(e, v)
                else
                    let t = TypeSign([], newVarT())
                    VarPat(v, t), t, (v, t)::locals

            | None, _::_ -> !?PatternNotFound(e, env, v)
            | Some(TypeScheme(_, TypeSign(_, LamNT _)) as t), [] -> !?InvalidConstructorPattern(e, t, p)
            | Some t, [] -> let t = free t in VarPat(v, t), t, locals
            | Some t, _::_ ->
                match free t with
                | TypeSign(tc, LamNT(dt, ft, fts)) ->
                    if List.length ps <> List.length fts + 1 then !?InvalidConstructorPattern(e, t, p)
                    let fts = ft::fts
                    let ps, tc, locals =
                        List.fold2 (fun (ps, tc, locals) p ft ->
                            let p, (TypeSign(pc, pt)), locals = aux locals p
                            unify e ft pt
                            p::ps, unionContext tc pc, locals
                        ) ([], tc, locals) ps fts
                    let ps = List.rev ps

                    let p, ps = List.head ps, List.tail ps
                    ConPat(v, p, ps), TypeSign(tc, dt), locals

                | _ -> !?InvalidConstructorPattern(e, t, p)

        | P.LitPat t -> LitPat t, free t, locals
        | P.AsPat(p, v) ->
            let p, pt, locals = aux locals p
            if List.exists (fst >> (=) v) locals then !?DuplicatedPatternVariable(e, v)
            else
                AsPat(p, v, pt), pt, (v, pt)::locals


    let p, t, locals = aux [] p
    p, t, List.fold (fun env (v,t) -> Env.add v (TypeScheme([], t)) env) env locals

let rec typingApp env f x e =
    let f, TypeSign(fc, ft) = typingCore env f
    let x, TypeSign(xc, xt) = typingCore env x
    let rt = newVarT()
    unify e ft (lamT xt rt)
    App(f, x), TypeSign(solveOrRaise e env (unionContext fc xc), rt)

and typingLam env v e =
    let vt = newVarT()
    let t = TypeSign([], vt)
    let env = Env.add v (TypeScheme([], t)) env
    let e, TypeSign(ec, et) = typingCore env e
    Lam(v, t, e), TypeSign(ec, lamT vt et)

and typingLet env var body cont e =
    let vt = newVarT()
    let body, TypeSign(bc, bt) = typingCore env body
    unify e vt bt
    let varT = bind (TypeSign(bc, vt))
    let cont, ct = typingCore (Env.add var varT env) cont
    Let(var, varT, body, cont), ct

and typingRec env varBodies cont e =
    match tryGetDuplicated (fun l r -> fst l = fst r) varBodies with
    | Some(v, _) -> !?DuplicatedLetRecDecrale(e, varBodies, v)
    | _ ->
        let vbts = List.map (fun vb -> vb, newVarT()) varBodies
        let env = List.fold (fun env ((v,_),vt) -> Env.add v (bind (TypeSign([], vt))) env) env vbts

        let bs, env =
            List.fold (fun (bs, env) ((v,b),vt) ->
                let b', TypeSign(bc, bt) = typingCore env b
                unify b vt bt
                let bt = bind (TypeSign(bc, bt))
                (v,(bt,b'))::bs, Env.add v bt env
            ) ([], env) vbts
        let bs = List.rev bs

        let cont, ct = typingCore env cont
        LetRec(bs, cont), ct

and typingMat env v (p, m) pms e =
    let v, TypeSign(vc, vt) = typingCore env v
    let p, TypeSign(pc, pt), env = typingPat e env p
    let m, TypeSign(rc, rt) = typingCore env m

    unify e vt pt

    let vc = unionContext vc pc
    let pms, vc, rc =
        List.fold (fun (pms, vc, rc) (p, m) ->
            let p, TypeSign(pc, pt), env = typingPat e env p
            let m, TypeSign(mc, mt) = typingCore env m
            unify e vt pt
            unify e mt rt
            (p, m)::pms, unionContext vc pc, unionContext rc mc
        ) ([], vc, rc) pms
    let pms = List.rev pms

    let rc = solveOrRaise e env <| unionContext vc rc
    Mat(v, (p, m), pms), TypeSign(rc, rt)
    
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
    | true, _ -> !?InvalidTypeArgments(e, vs)
    | _, Some v -> !?DuplicatedTypeArgment(e, vs, v)
    | _ ->
        let t = Type(name, List.map IndefType vs)
        let env = Env.addT name td env
        let env = List.fold (typingCon t) env cs
        let cont, ct = typingCore (Env.addT name td env) cont
        TypeDef(name, DataDef(vs, cs), cont), ct

and typingClassDef env name (td, vs, ms) cont e =
    if List.exists (isPureTypeArg >> not) vs then !?InvalidTypeArgments(e, vs)
    match tryGetDuplicated (==) vs, tryGetDuplicated (fun l r -> fst l = fst r) ms with
    | Some v, _ -> !?DuplicatedTypeArgment(e, vs, v)
    | _, Some(v,_) -> !?DuplicatedMethodDeclare(e, ms, v)
    | _ ->
        let env = Env.addT name td env
        
        let tc = Type(name, List.map IndefType vs)
        let env =   
            List.fold (fun env (n, TypeScheme(mvs, TypeSign(mcs, mt))) ->
                let ft = rebind <| TypeScheme(vs @ mvs, TypeSign(tc::mcs, mt))
                Env.add n ft env
            ) env ms

        let cont, ct = typingCore env cont
        TypeDef(name, ClassDef(vs, ms), cont), ct

and typingTypeDef env name td cont e =
    match td with
    | DataDef(vs, cs) -> typingDataDef env name (td, vs, cs) cont e
    | ClassDef(vs, ms) -> typingClassDef env name (td, vs, ms) cont e

and typingInsDef env (className, instanceTypeArgs, impls, cont) e =
    let td =
        try Env.findT className env with
        | :? KeyNotFoundException -> !?TypeNotFound(e, env, className)

    match td with
    | DataDef _ -> !?InvalidInstanceDeclare(e)
    | ClassDef(classTypeVars, methodDefs) ->
        if List.length instanceTypeArgs <> List.length classTypeVars then !?InvalidInstanceDeclare(e)

        match tryGetDuplicated (fun l r -> fst l = fst r) impls with
        | Some(v,_) -> !?DuplicatedInstanceImplement(e, v)
        | _ ->
            List.iter (fun (n,_) ->
                if not <| List.exists (fun (n',_) -> n = n') impls
                then !?MethodNotImplemented(e, n)
            ) methodDefs
            List.iter (fun (n,_) ->
                if not <| List.exists (fun (n',_) -> n = n') methodDefs
                then !?MethodMismatch(e, n)
            ) impls
            
            let typeVars = List.map (!) classTypeVars
            List.iter2 (fun classTypeVar instanceTypeArg -> classTypeVar := SomeType instanceTypeArg) classTypeVars instanceTypeArgs

            let implBodies =
                List.map (fun (methodName, methodType) ->
                    let implVar, implBody = List.find (fun (n,_) -> n = methodName) impls
                    let implBody, implType = typingCore env implBody
                    let methodType = free methodType
                    unify e (lamT <|| unlift implType) (lamT <|| unlift methodType)
                    implVar, (bind implType, implBody)
                ) methodDefs
 
            List.iter2 (:=) classTypeVars typeVars

            let instanceFreeVars = List.collect freeVars instanceTypeArgs

            let instanceType = TypeScheme(instanceFreeVars, TypeSign([], Type(className, instanceTypeArgs)))
            let cont, ct = typingCore (Env.addI instanceType env) cont
            InstanceDef(className, instanceTypeArgs, implBodies, cont), ct

and typingLit _ = function
    | CharLit _ -> primCharT
    | StringLit _ -> primStringT
    | IntegerLit _ -> primIntegerT
    | IntLit _ -> primIntT
    | FloatLit _ -> primFloatT

and typingCore env = function
    | E.Lit l -> Lit l, typingLit env l
    | E.Var v ->
        try
            let t = free <| Env.find v env
            Var(v, t), t
        with
        | :? KeyNotFoundException -> !?VariableNotFound(env, v)

    | E.Lam(v, e) -> typingLam env v e
    | E.App(f, x) as e -> typingApp env f x e
    | E.Let(var, body, cont) as e -> typingLet env var body cont e
    | E.LetRec(varBodies, cont) as e -> typingRec env varBodies cont e
    | E.Mat(v, pm, pms) as e -> typingMat env v pm pms e
    | E.Ext(v, t, e) -> typingCore (Env.add v t env) e
    | E.TypeDef(name, td, cont) as e -> typingTypeDef env name td cont e
    | E.InstanceDef(name, typeArgs, impls, cont) as e -> typingInsDef env (name, typeArgs, impls, cont) e
