module Alpa.Parser.Operator
#load "./Alpa.Parser.fsx"

open Alpa

type FullPath = list<Symbol>
type Operator = {
    Fixity: Fixity
    Associativity: Associativity
    Precedence: int
    FullPath: FullPath
}
type VarInfo = VarInfo of option<Operator> * FullPath: FullPath
type Node<'K,'V when 'K : comparison> =
    | Leaf of 'V
    | Node of Map<'K, Node<'K,'V>>

type Tree<'K,'V when 'K : comparison> = Map<'K, Node<'K,'V>>
type SymbolTree = Map<list<Symbol>, VarInfo>

type OperatorTable = {
    PrecedenceKey: int
    AssocLOps: list<Operator>
    AssocNOps: list<Operator>
    AssocROps: list<Operator>
}
type ResolveEnv = {
    InfixOpTables: list<OperatorTable>
    PostfixOps: list<Operator>
    PrefixOps: list<Operator>
    Vars: SymbolTree
}
module OpTable =
    let empty = {
        PrecedenceKey = 0
        AssocLOps = []
        AssocNOps = []
        AssocROps = []
    }
    let add x xs =
        match x.Associativity with
        | NonAssoc -> { xs with AssocNOps = x::xs.AssocNOps }
        | Left -> { xs with AssocLOps = x::xs.AssocLOps }
        | Right -> { xs with AssocROps = x::xs.AssocLOps }

    let singleton x =
        match x.Associativity with
        | NonAssoc -> { empty with PrecedenceKey = x.Precedence; AssocNOps = [x] }
        | Left -> { empty with PrecedenceKey = x.Precedence; AssocLOps = [x] }
        | Right -> { empty with PrecedenceKey = x.Precedence; AssocROps = [x] }
    
module Env =
    let tryFind (LongIdentifier(ls, r)) env =
        let rec aux ls r vars =
            match ls with
            | [] ->
                match Map.tryFind (r._value2 :?> Symbol) vars with
                | Some(Leaf v) -> Some v
                | _ -> None

            | (l, _)::ls ->
                match Map.tryFind (l._value2 :?> Symbol) vars with
                | Some(Node vars) -> aux ls r vars
                | _ -> None

        let path =
            match ls with
            | [] ->
                let r = r._value2 :?> Symbol
                [r]

            | [l,_] ->
                let l, r = l._value2 :?> Symbol, r._value2 :?> Symbol
                [l;r]

            | _ ->
                let r = r._value2 :?> Symbol
                List.map (fun (n,_) -> n._value2 :?> Symbol) ls @ [r]

        Map.tryFind path env.Vars
        
    let rec addTree l rs v tree =
        match Map.tryFind l tree, rs with
        | Some(Node ltree), r::rs -> Map.add l (Node(addTree r rs v ltree)) tree
        | _, r::rs -> Map.add l (Node(addTree r rs v Map.empty)) tree
        | _, [] -> Map.add l (Leaf v) tree

    let rec addOpTables x = function
        | [] -> [OpTable.singleton x]
        | { PrecedenceKey = k } as kxs::table ->
            let key = x.Precedence

            if key < k then OpTable.singleton x::kxs::table
            elif key = k then OpTable.add x kxs::table
            else kxs::addOpTables x table

    let add fullPath op env =
        let vars = Map.add fullPath (VarInfo(op, fullPath)) env.Vars
        match op with
        | None -> { env with Vars = vars }
        | Some({ Fixity = Infix } as op) ->
            { env with 
                Vars = vars
                InfixOpTables = addOpTables op env.InfixOpTables }

        | Some({ Fixity = Postfix } as op) ->
            { env with
                Vars = vars
                PostfixOps = op::env.PostfixOps }

        | Some({ Fixity = Prefix } as op) ->
            { env with
                Vars = vars
                PrefixOps = op::env.PrefixOps }
            
    let make xs =
        let empty = {
            Vars = Map.empty
            InfixOpTables = []
            PostfixOps = []
            PrefixOps = []
        }
        Seq.fold (fun env (fullPath, op) ->
            let op = Option.map(fun (f, a, p) -> { Fixity = f; Associativity = a; Precedence = p; FullPath = fullPath }) op
            add fullPath op env
        ) empty xs

let (|Op|_|) env = function
    | LookupExpression(LongIdentifier(_, n) as name) as e ->
        match Token.kind n with
        | TokenKind.Id
        | TokenKind.Op
        | TokenKind.Qop ->
            match Env.tryFind name env with
            | Some(VarInfo(Some op, fp)) -> Some(op, e, fp)
            | _ -> None
        | _ -> None
    | _ -> None
    
type Reply<'a> = Succ of 'a * Expression list | Fail of ParseError

let parseNonOp env = function
    | Op env _ as e::_ -> Fail(RequireNonOperatorExpression e)
    | e::es -> Succ(e, es)
    | [] -> Fail RequireAnyExpression
        
let parseOp env ops = function
    | Op env (op, name, fp) as e::es ->
        if List.exists (fun { FullPath = fp' } -> fp = fp') ops
        then Succ((name, op), es)
        else Fail(UnknownOperator e)

    | e::_ -> Fail(RequireOperatorExpression e)
    | [] -> Fail RequireAnyExpression

let parseOps env ops es =
    let rec aux ns es =
        match parseOp env ops es with
        | Fail _ -> ns, es
        | Succ((op, _), es) -> aux (op::ns) es
    aux [] es

let parsePrefixPostOps env es =
    let prefixOps, es = parseOps env env.PrefixOps es
    match parseNonOp env es with
    | Fail _ as r -> r
    | Succ(e, es) ->
        let postfixOps, es = parseOps env env.PostfixOps es
        match prefixOps, postfixOps with
        | [], [] -> Succ(e, es)
        | _ ->
            let e = List.foldBack (fun op e -> PostfixApplicationExpression(e, op)) postfixOps e
            let e = List.fold (fun e op -> PrefixApplicationExpression(op, e)) e prefixOps
            Succ(e, es)
                
let parsePrimApplications env es =
    match parsePrefixPostOps env es with
    | Fail e -> Fail e
    | Succ(e, es) ->
        let rec aux rs es =
            match parsePrefixPostOps env es with
            | Fail _ -> List.rev rs, es
            | Succ(e, es) -> aux (e::rs) es

        let rs, es = aux [] es
        match rs with
        | [] -> Succ(e, es)
        | r::rs -> Succ(ApplicationsExpression(e, r, rs), es)

let rec parseInfixOpTable env infixOpTable es =
    match infixOpTable with
    | [] -> parsePrimApplications env es
    | infixOps::infixOpTable -> parseSamePrecedenceInfixOps env infixOps infixOpTable es
        
and parseAssocR env infixROps infixOpTable l es =
    match parseOp env infixROps es with
    | Fail e -> Fail e
    | Succ((opE, _), es) ->
        match parseInfixOpTable env infixOpTable es with
        | Fail e -> Fail e
        | Succ(r, es) ->
            let r, es =
                match parseAssocR env infixROps infixOpTable r es with
                | Fail _ -> r, es
                | Succ(r, es) -> r, es

            Succ(InfixApplicationExpression(l, opE, r), es)
            
and parseAssocN env { AssocLOps = infixLOps; AssocNOps = infixNOps; AssocROps = infixROps } infixOpTable l es =
    let assoc { Associativity = a } = a

    match parseOp env infixNOps es with
    | Fail e -> Fail e
    | Succ((opE, op), es) ->
        match parseInfixOpTable env infixOpTable es with
        | Fail e -> Fail e
        | Succ(r, es) ->
            match parseOp env infixNOps es with
            | Succ((opE',op'), _) -> Fail(AmbiguousAssociativeOperator(opE, assoc op, opE', assoc op'))
            | Fail _ ->
                match parseOp env infixROps es with
                | Succ((opE',op'), _) -> Fail(AmbiguousAssociativeOperator(opE, assoc op, opE', assoc op'))
                | Fail _ ->
                    match parseOp env infixLOps es with
                    | Succ((opE',op'), _) -> Fail(AmbiguousAssociativeOperator(opE, assoc op, opE', assoc op'))
                    | Fail _ -> Succ(InfixApplicationExpression(l, opE, r), es)

and parseAssocL env infixLOps infixOpTable l es =
    match parseOp env infixLOps es with
    | Fail e -> Fail e
    | Succ((opE, _), es) ->
        match parseInfixOpTable env infixOpTable es with
        | Fail e -> Fail e
        | Succ(r, es) ->
            let l = InfixApplicationExpression(l, opE, r)
            match parseAssocL env infixLOps infixOpTable l es with
            | Fail _ -> Succ(l, es)
            | r -> r

// a * b *** c
// a == b == c
// a *** b * c
and parseSamePrecedenceInfixOps env infixOps infixOpTable es =
    let { AssocLOps = infixLOps; AssocROps = infixROps } = infixOps

    match parseInfixOpTable env infixOpTable es with
    | Fail e -> Fail e
    | Succ(l, es) as l' ->
        match parseAssocL env infixLOps infixOpTable l es with
        | Succ _ as r -> r
        | Fail _ ->
            match parseAssocR env infixROps infixOpTable l es with
            | Succ _ as r -> r
            | Fail _ ->
                match parseAssocN env infixOps infixOpTable l es with
                | Succ _ as r -> r
                | Fail _ -> l'

let parseApplications env es =
    match parseInfixOpTable env env.InfixOpTables es with
    | Succ(e, []) -> Choice1Of2 e
    | Succ _ -> Choice2Of2 RequireExpressionsEnd
    | Fail e -> Choice2Of2 e