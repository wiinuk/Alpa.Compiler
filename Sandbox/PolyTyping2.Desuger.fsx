module PolyTyping2.Desuger
#load "PolyTyping2.Typing.fsx"
open PolyTyping2
open PolyTyping2.Typing

type Type =
    | Type of name: Symbol * tvars: Type list
    | TVar of Symbol

type TypeScheme = Type
type Var = Symbol of string | ISymbol of Type

type DPat =
    | AnyPat
    | VarPat of Var * Type
    | ConPat of Var * DPat * DPat list
    | LitPat of TypeScheme
    | AsPat of DPat * Var * Type

type DExp =
    | Lit of Lit
    | Var of Var * Type
    | Lam of Var * Type * DExp
    | App of DExp * DExp

    | Ext of Var * TypeScheme * DExp
    | Let of Var * TypeScheme * DExp * DExp
    | LetRec of assoc<Var, TypeScheme * DExp> * DExp
    
    | Mat of DExp * (DPat * DExp) * (DPat * DExp) list

    | TypeDef of name: Symbol * TypeDef * DExp
    | InstanceDef of name: Symbol * typeArgs: Type list * methodImpls: assoc<Var, TypeScheme * DExp> * cont: DExp

type E = PolyTyping2.Typing.TExp
type P = PolyTyping2.Typing.TPat
type T = PolyTyping2.Type

let rec toType = function
    | T.IndefType({ contents = TypeVar } as v) ->
        System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode v
        |> sprintf "t@%d"
        |> TVar

    | T.IndefType { contents = SomeType t } -> toType t
    | T.Type(n, ts) -> Type(n, List.map toType ts)

let rec desuger = function
    | E.Lit l -> Lit l, []

    // `x: Num a => a` => `x: a`
    | E.Var(v, TypeSign(_, t)) -> Var(Symbol v, toType t), []
    
    // `\(n: Num a => a) : (Num b => b) -> fromInteger 0I` 
    // => `\(#(Num a): Num a) (#(Num b): Num b) (n: a) : b ->
    //     ignore (n + fromInteger 0I #(Num a));
    //     fromInteger 0I #(Num b)`
    //
    // `\(n: Num a => a) : (Num a => a) -> n`
    // => `\(n: a) : a -> n`
    | E.Lam(v, TypeSign(vcs, t), b) ->
        let b, bcs = desuger b
        let t = toType t
        let cs = unionContext vcs bcs
        let f c e =
            let c = toType c
            Lam(ISymbol c, c, e)

        let l = List.foldBack f cs <| Lam(Symbol v, t, b)
        l, cs

    // `(ofInteger: Num a => bigint -> a) (x: Num a => a)`
    // => `ofInteger #(Num a) x`
    | E.App(f, x) ->
        let fcs, f = desuger f
        let xcs, x = desuger x


        failwith "Not implemented yet"
    | E.Ext(_, _, _) -> failwith "Not implemented yet"
    | E.Let(_, _, _, _) -> failwith "Not implemented yet"
    | E.LetRec(_, _) -> failwith "Not implemented yet"
    | E.Mat(_, _, _) -> failwith "Not implemented yet"
    | E.TypeDef(name, _, _) -> failwith "Not implemented yet"
    | E.InstanceDef(name, typeArgs, methodImpls, cont) -> failwith "Not implemented yet"
