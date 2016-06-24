module PolyTyping2.Desuger
#load "PolyTyping2.Typing.fsx"
open PolyTyping2
open PolyTyping2.Typing

type E = PolyTyping2.Typing.TExp

type DPat =
    | AnyPat
    | VarPat of Var * Type
    | ConPat of Var * DPat * DPat list
    | LitPat of TypeScheme
    | AsPat of DPat * Var * Type

[<NoComparison>]
type DExp =
    | Lit of Lit
    | Var of Var * Type
    | Lam of Var * Type * DExp
    | App of DExp * DExp

    | Ext of Var * TypeScheme * DExp
    | Let of Var * TypeScheme * DExp * DExp
    | LetRec of assoc<Var, TypeScheme * DExp> * DExp
    
    /// ex: id(x) = x
    | Fun of name: Var * pars: (Var * Type) list * returnType: Type * DExp * DExp
    /// ex: id(10)
    | Call of name: Var * args: DExp list

    | Mat of DExp * (DPat * DExp) * (DPat * DExp) list

    | TypeDef of name: Symbol * TypeDef * DExp
    | InstanceDef of name: Symbol * typeArgs: Type list * methodImpls: assoc<Var, TypeScheme * DExp> * cont: DExp