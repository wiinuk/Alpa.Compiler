module PolyTyping2.Emit2
#load "PolyTyping2.fsx"

open PolyTyping2
open System.Reflection
open System.Reflection.Emit
open System

type SType =
    | SType of Symbol * SType list
    | SVType of Symbol

type Type = PolyTyping2.Type
type TypeScheme = Type

type Var =
    | SimpleVar of string
    | ContextVar of Type

type Pat =
    | AnyPat 
    | AsPat of Pat * Var * Type
    | ConPat of Var * Type * Pat list
    | LitPat of TypeScheme

and [<NoComparison>] Exp =
    | Lit of Lit
    | Var of Var * Type
    | Lam of Var * Type * Exp
    | App of Exp * Exp
    | Ext of Var * TypeScheme * Exp
    | Let of Var * Type * Exp * Exp
    | LetRec of assoc<Var, TypeScheme * Exp> * Exp
    | Mat of Exp * (Pat * Exp) * (Pat * Exp) list

(*

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

*)

type private E = PolyTyping2.Exp
let typingTypeSign typing (TypeSign(xs, t)) =
    List.fold (fun e c -> App(e, Var(ContextVar c, c))) (typing t) xs

let rec typing env = function
    | E.Lit x -> Lit x
    | E.Var x -> typingTypeSign (fun t -> Var(SimpleVar x, t)) <| typingVar env x
    | E.Lam(v, e) ->
        // \(x: Num a => a): Num b => b -> ofInteger 10I
        // \(x: Num a -> a) ($(Num b): Num b) -> ofInteger $(Num b) 10I
        let t = typingLam env v (typing env e)
        Lam(v, , typing env e)

    | E.App(f, x) -> App(typing env f, typing env x)
    | E.Ext(v, t, e) -> Ext(v, toSType t, typing env e)
    | E.Let(_, _, _) -> failwith "Not implemented yet"
    | E.LetRec(_, _) -> failwith "Not implemented yet"
    | E.Mat(_, _, _) -> failwith "Not implemented yet"
    | E.TypeDef(name, _, _) -> failwith "Not implemented yet"
    | E.InstanceDef(name, typeArgs, methodImpls, cont) -> failwith "Not implemented yet"

//    typingCore Env.empty e 
//    |> deref
//    |> bind
