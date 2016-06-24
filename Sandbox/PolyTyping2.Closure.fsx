module PolyTyping2.ILEmit
#load "PolyTyping2.Typing.fsx"

open PolyTyping2
open PolyTyping2.Typing

type Type =
    | Type of name: Symbol * tvars: Type list
    | TVar of Symbol

type TypeScheme = Type

type Symbol = Symbol of Var | ISymbol of Type
type GlobalName = GlobalName of Symbol
type CPat =
    | AnyPat
    | VarPat of Symbol * Type
    | ConPat of Symbol * CPat * CPat list
    | LitPat of Type
    | AsPat of CPat * Symbol * Type

type CExp =
    | Lit of Lit
    | Var of Symbol * Type

    | Lam of Symbol * Type * CExp
    | App of CExp * CExp
    | Ext of Symbol * TypeScheme * CExp
    | Let of Symbol * TypeScheme * CExp * CExp
    | LetRec of assoc<Symbol, TypeScheme * CExp> * CExp
    
    | Mat of CExp * (CPat * CExp) * (CPat * CExp) list

    // `a = 10; map (\x -> x + a) xs` -> `a = 10; map (new Clo(a) xs`
    | MakeClosure of (Symbol * Type) list * cloName: GlobalName * env: CExp list * CExp
    | AppClosure of CExp * CExp

    | TypeDef of name: Symbol * TypeDef * CExp

type Program =
    | CloDef of
        name: Symbol *
        arg: Symbol *
        argT: Type *
        retT: Type *
        body: CExp

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

let funT a b = Type("->", [a; b])

let rec go env = function
    | E.Lit l -> Lit l, []

    // `x: Num a => a` => `x: a`
    | E.Var(v, TypeSign(_, t)) -> Var(Symbol v, toType t), []

    | E.Lam(v, TypeSign(vcs, t), b) ->
        // `\(n: Num a => a) : (Num b => b) -> fromInteger 0I` 
        // => `\(#(Num a): Num a) (#(Num b): Num b) (n: a) : b ->
        //     ignore (n + fromInteger 0I #(Num a));
        //     fromInteger 0I #(Num b)`
        //
        // `\(n: Num a => a) : (Num a => a) -> n`
        // => `\(n: a) : a -> n`
        let b, bcs = go env b
        let t = toType t
        let cs = unionContext vcs bcs
        let f c e =
            let c = toType c
            Lam(ISymbol c, c, e)

        let l = List.foldBack f cs <| Lam(Symbol v, t, b)
        l, cs

    | E.App(_, _) -> failwith "Not implemented yet"
    | E.Ext(_, _, _) -> failwith "Not implemented yet"
    | E.Let(_, _, _, _) -> failwith "Not implemented yet"
    | E.LetRec(_, _) -> failwith "Not implemented yet"
    | E.Mat(_, _, _) -> failwith "Not implemented yet"
    | E.TypeDef(name, _, _) -> failwith "Not implemented yet"
    | E.InstanceDef(name, typeArgs, methodImpls, cont) -> failwith "Not implemented yet"