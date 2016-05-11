module Alpa.Parser.Operator
#load "./Alpa.Parser.fsx"

open Alpa

type Result<'T,'E> = Ok of 'T | Error of 'E

type PathRev = list<Symbol>
type Operator = {
    Fixity: Fixity
    Associativity: Associativity
    Precedence: int
    //FullPath: PathRev
}
type SymbolKind = Module | Var | Type
type SymbolInfo = {
    Kind: SymbolKind
    OperatorInfo: option<Operator>
    //FullPath: PathRev
}
type Node<'K,'V when 'K : comparison> =
    | Leaf of 'V
    | Node of Map<'K, Node<'K,'V>>

type Tree<'K,'V when 'K : comparison> = Map<'K, Node<'K,'V>>
type SymbolTree = Map<PathRev, SymbolInfo>
type OperatorMap = Map<PathRev, Operator>

type OperatorTable = {
    PrecedenceKey: int
    AssocLOps: OperatorMap
    AssocNOps: OperatorMap
    AssocROps: OperatorMap
}
type ResolveEnv = {
    InfixOpTables: list<OperatorTable>
    PostfixOps: OperatorMap
    PrefixOps: OperatorMap
    Vars: SymbolTree
}
module OpTable =
    let empty = {
        PrecedenceKey = 0
        AssocLOps = Map.empty
        AssocNOps = Map.empty
        AssocROps = Map.empty
    }
    let add path x xs =
        match x.Associativity with
        | NonAssoc -> { xs with AssocNOps = Map.add path x xs.AssocNOps }
        | Left -> { xs with AssocLOps = Map.add path x xs.AssocLOps }
        | Right -> { xs with AssocROps = Map.add path x xs.AssocROps }

    let singleton path x =
        match x.Associativity with
        | NonAssoc -> { empty with PrecedenceKey = x.Precedence; AssocNOps = Map [path, x] }
        | Left -> { empty with PrecedenceKey = x.Precedence; AssocLOps = Map [path, x] }
        | Right -> { empty with PrecedenceKey = x.Precedence; AssocROps = Map [path, x] }
    
module Ident =
    let symbol = function
        | Name r
        | ParenthesizedIdentifier(_,r,_) -> r._value2 :?> Symbol

module LongId =
    let rec appendRev ls rs =
        match ls with
        | [] -> rs
        | (l,_)::ls -> appendRev ls (Ident.symbol l::rs)

    let path (LongIdentifier(ls, r)) =
        match ls with
        | [] -> [Ident.symbol r]
        | [l,_] -> [Ident.symbol r; Ident.symbol l]
        | _ -> Ident.symbol r::appendRev ls []
        
    let kind (LongIdentifier(_,n)) =
        match n with
        | Name n
        | ParenthesizedIdentifier(_,n,_) -> Token.kind n

module List =
    /// appendRev [1;2] [3;4] = [2;1;3;4]
    let rec appendRev ls rs =
        match ls with
        | [] -> rs
        | l::ls -> appendRev ls (l::rs)

module Env =
    let tryFind n env = Map.tryFind (LongId.path n) env.Vars
        
    let containsOp name env =
        match Map.tryFind (LongId.path name) env.Vars with
        | Some { OperatorInfo = Some _ } -> true
        | _ -> false

    let rec addTree l rs v tree =
        match Map.tryFind l tree, rs with
        | Some(Node ltree), r::rs -> Map.add l (Node(addTree r rs v ltree)) tree
        | _, r::rs -> Map.add l (Node(addTree r rs v Map.empty)) tree
        | _, [] -> Map.add l (Leaf v) tree

    let rec addOpTables path x = function
        | [] -> [OpTable.singleton path x]
        | { PrecedenceKey = k } as kxs::table ->
            let key = x.Precedence

            if key < k then OpTable.singleton path x::kxs::table
            elif key = k then OpTable.add path x kxs::table
            else kxs::addOpTables path x table

    let add path symbolInfo env =
        let vars = Map.add path symbolInfo env.Vars
        match symbolInfo.OperatorInfo with
        | None -> { env with Vars = vars }
        | Some({ Fixity = Infix } as op) ->
            { env with 
                Vars = vars
                InfixOpTables = addOpTables path op env.InfixOpTables }

        | Some({ Fixity = Postfix } as op) ->
            { env with
                Vars = vars
                PostfixOps = Map.add path op env.PostfixOps }

        | Some({ Fixity = Prefix } as op) ->
            { env with
                Vars = vars
                PrefixOps = Map.add path op env.PrefixOps }
            
    //let fullPath (LongIdentifier(ls,r)) env = Ident.symbol r::LongId.appendRev ls env.Current

    let addModule path env =
        add path {
            // FullPath = fullPath ident env
            Kind = SymbolKind.Module
            OperatorInfo = None
        } env

//    let pushCurrent ident env = { env with Current = Ident.symbol ident::env.Current }
//    let pushCurrents n env = { env with Current = fullPath n env }
//    let popCurrent env =
//        match env.Current with
//        | [] -> env
//        | _::current -> { env with Current = current }

    let make xs =
        let empty = {
            Vars = Map.empty
            InfixOpTables = []
            PostfixOps = Map.empty
            PrefixOps = Map.empty
//            Current = []
        }
        Seq.fold (fun env (path, op) ->
            let op = Option.map (fun (f, a, p) -> { Fixity = f; Associativity = a; Precedence = p; (* FullPath = fullPath *) }) op
            add path { Kind = Var; OperatorInfo = op; (* FullPath = path *) } env
        ) empty xs
        
type Reply<'a> = Succ of 'a * Expression list | Fail of ParseError

let parseOp ops = function
    | LookupExpression name as e::es ->
        match LongId.kind name with
        | TokenKind.Id
        | TokenKind.Op
        | TokenKind.Qop ->
            match Map.tryFind (LongId.path name) ops with
            | Some op -> Succ((e, op), es) // Some(op, e, fp)
            | _ -> Fail(UnknownOperator e)
        | _ -> Fail(RequireOperatorExpression e)
    | _ -> Fail RequireAnyExpression
    
let parseNonOp env = function
    | LookupExpression name as e::es ->
        match LongId.kind name with
        | TokenKind.Id
        | TokenKind.Op
        | TokenKind.Qop ->
            if Env.containsOp name env then Fail(RequireNonOperatorExpression e)
            else Succ(e, es)
        | _ -> Succ(e, es)
    | e::es -> Succ(e, es)
    | [] -> Fail RequireAnyExpression
        
let parseOps env ops es =
    let rec aux ns es =
        match parseOp ops es with
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
            // postfix apply
            let e = List.foldBack (fun op e -> ApplicationsExpression(PostfixApply, op, e, [])) postfixOps e

            // prefix apply
            let e = List.fold (fun e op -> ApplicationsExpression(PrefixApply, op, e, [])) e prefixOps
            Succ(e, es)
                
let parseIdApplications env es =
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
        | r::rs ->
            
            // id apply
            Succ(ApplicationsExpression(IdentifierApply, e, r, rs), es)

let rec parseInfixOpTable env infixOpTable es =
    match infixOpTable with
    | [] -> parseIdApplications env es
    | infixOps::infixOpTable -> parseSamePrecedenceInfixOps env infixOps infixOpTable es
        
and parseAssocR env infixROps infixOpTable l es =
    match parseOp infixROps es with
    | Fail e -> Fail e
    | Succ((opE, _), es) ->
        match parseInfixOpTable env infixOpTable es with
        | Fail e -> Fail e
        | Succ(r, es) ->
            let r, es =
                match parseAssocR env infixROps infixOpTable r es with
                | Fail _ -> r, es
                | Succ(r, es) -> r, es
                
            // infix right apply
            Succ(ApplicationsExpression(InfixRightApply, opE, l, [r]), es)
            
and parseAssocN env { AssocLOps = infixLOps; AssocNOps = infixNOps; AssocROps = infixROps } infixOpTable l es =
    let assoc { Associativity = a } = a

    match parseOp infixNOps es with
    | Fail e -> Fail e
    | Succ((opE, op), es) ->
        match parseInfixOpTable env infixOpTable es with
        | Fail e -> Fail e
        | Succ(r, es) ->
            match parseOp infixNOps es with
            | Succ((opE',op'), _) -> Fail(AmbiguousAssociativeOperator(opE, assoc op, opE', assoc op'))
            | Fail _ ->
                match parseOp infixROps es with
                | Succ((opE',op'), _) -> Fail(AmbiguousAssociativeOperator(opE, assoc op, opE', assoc op'))
                | Fail _ ->
                    match parseOp infixLOps es with
                    | Succ((opE',op'), _) -> Fail(AmbiguousAssociativeOperator(opE, assoc op, opE', assoc op'))
                    | Fail _ ->
                        
                        // infix none apply
                        Succ(ApplicationsExpression(InfixNoneApply, opE, l, [r]), es)

and parseAssocL env infixLOps infixOpTable l es =
    match parseOp infixLOps es with
    | Fail e -> Fail e
    | Succ((opE, _), es) ->
        match parseInfixOpTable env infixOpTable es with
        | Fail e -> Fail e
        | Succ(r, es) ->
            
            // infix left apply
            let l = ApplicationsExpression(InfixLeftApply, opE, l, [r])
            match parseAssocL env infixLOps infixOpTable l es with
            | Fail _ -> Succ(l, es)
            | r -> r

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

let parseLookupExpression env (LongIdentifier(ls, r)) =
    let rec takeMember left leftDelimiter names rightName =
        match names with
        | [] -> DotLookupExpression(left, leftDelimiter, rightName)
        | (name, delimiter)::names -> takeMember (DotLookupExpression(left, leftDelimiter, name)) delimiter names rightName

    let rec takeLookup readedNames names rightName =
        match names with
        | [] ->
            let path = LongIdentifier(List.rev readedNames, rightName)
            match Env.tryFind path env with
            | Some { Kind = SymbolKind.Var } -> Ok(LookupExpression path)
            | _ -> Error(LookupError path)

        | (name, delimiter) as n::names ->
            let readedNames' = n::readedNames
            let path = LongIdentifier(List.rev readedNames', name)

            match Env.tryFind path env with
            | Some { Kind = SymbolKind.Var } ->
                Ok <| takeMember (LookupExpression path) delimiter names rightName

            | _ -> takeLookup readedNames' names rightName

    takeLookup [] ls r

let parseApplicationsExpression env es =
    match parseInfixOpTable env env.InfixOpTables es with
    | Succ(e, []) -> Ok e
    | Succ _ -> Error RequireExpressionsEnd
    | Fail e -> Error e

type ResolveResult<'T,'E> =
    | Updated of 'T
    | Resolved
    | ResolveFailure of 'E

let mapValue f = function
    | Updated x -> Updated(f x)
    | Resolved -> Resolved
    | ResolveFailure e -> ResolveFailure e 

//let mapEnv f = function
//    | Updated e -> Updated(e, f env)
//    | Resolved env -> Resolved(f env)
//    | e -> e
//
//let resolveChain resolve env es =
//    let rec map env result = function
//        | [] -> List.rev result, env
//        | e::es ->
//            let env = resolve env e
//
//            match  with
//            | Ok(e, env) -> map env (e::result) es
//            | Error e -> Error e
//
//    map env [] es

let resolvePat env pat = failwith "Not implemented yet"
let resolveType env t = failwith "Not implemented yet"
let resolveExpr env e = failwith "Not implemented yet"

module M =
    
    module X =
        let mx0 = 0

        // mx0
        let mx1 = 1

    // X.mx0; X.mx1
    let m0 = 0

    // X.mx0; X.mx1
    let m1 = 1

let resolveTypeDefinition env = failwith "Not implemented yet"
// function
//    | AbbreviationTypeDefinition(TypeName(n, targs),eq,ty) ->
//        let env =
//            List.fold (fun env ta ->
//                match ta with
//                | TypeArgument a -> Env.addType a env
//                | TypeArgumentHole _ -> env
//            ) env targs
//
//        resolveType env ty


// <haskell>
// prec,    left assoc,                 non assoc,                      right assoc
// 9,       (!!),                       (),                             (.)
// 8,       (),                         (),                             (^ ^^ **)
// 7,       (* / div mod rem quot),     (),                             ()
// 6,       (+ -),                      (),                             ()
// 5,       (),                         (),                             (: ++)
// 4,       (),                         (== /= < <= > >= elem notElem), ()
// 3,       (),                         (),                             (&&)
// 2,       (),                         (),                             (||)
// 1,       (>> >>=),                   (),                             ()
// 0,       (),                         (),                             ($ $! seq)
//
// <f#>
// prec,    left assoc,                 non assoc,                      right assoc
// 9,       (),                         (),                             (**#)
// 8,       (*# /# %#),                 (),                             ()
// 7,       (+# -#),                    (),                             ()
// 6,       (),                         (),                             (::)
// 5,       (),                         (),                             (^#)
// 4,       (&&& !!! ^^^ ~~~ <<< >>>),  (),                             ()
// 3,       (<# ># = |# &#),            (),                             ()
// 2,       (& &&),                     (),                             ()
// 1,       (||),                       (),                             ()
// 0,       (),                         (),                             (:=)


let assocR80 = { Associativity = Right; Fixity = Infix; Precedence = 80 }
let assocL70 = { Associativity = Left; Fixity = Infix; Precedence = 70 }
let assocL60 = { Associativity = Left; Fixity = Infix; Precedence = 60 }
let assocL40 = { Associativity = Left; Fixity = Infix; Precedence = 40 }
let assocL30 = { Associativity = Left; Fixity = Infix; Precedence = 30 }
let assocL20 = { Associativity = Left; Fixity = Infix; Precedence = 20 }
let defaultOp1 = function
    | '*'
    | '/'
    | '%' -> assocL70
    | '+'
    | '-' -> assocL60
    | '='
    | '<'
    | '>'
    | '|'
    | '&' -> assocL40
    | _ -> assocL60

let defaultOp (s: Symbol) =
    match s with
    | "&&" -> assocL30
    | "||" -> assocL20
    | _ ->
        if 2 <= s.Length then
            match s.[0], s.[1] with
            | '*', '*' -> assocR80
            | '/', '=' -> assocL40
            | _ -> defaultOp1 s.[0]

        elif 1 <= s.Length then defaultOp1 s.[0]
        else
            assocL60

let rec resolveModuleElement env = function
    | ModuleDefinition(_,n,_,_,None,_) as e ->
        e, Ident.symbol n, { Kind = Module; OperatorInfo = None }, []

    | ModuleDefinition(moduleK,n,eq,blockBegin,Some es,blockEnd) ->
        let es, exports = resolveModuleElements env es
        let exports = List.map (fun exportPathRev -> Ident.symbol n::exportPathRev) exports
        let e = ModuleDefinition(moduleK,n,eq,blockBegin,Some es,blockEnd)
        let si = { Kind = Module; OperatorInfo = None }
        e, Ident.symbol n, si, exports

    | ModuleLetElement(LetHeader(name, pats), eq, blockBegin, body, blockEnd) ->
        let pats = List.map (fun p -> resolvePat env p) pats
        let pats, locals = List.unzip pats
        let env =
            List.fold (fun env local ->
                Env.add local { // FullPath = [local];
                          Kind = SymbolKind.Var
                          OperatorInfo = None } env
            ) env locals

        let body = resolveExpr env body
        let e = ModuleLetElement(LetHeader(name, pats), eq, blockBegin, body, blockEnd)


        let op =
            match name with
            | ParenthesizedIdentifier(_,t,_) ->
                let s = t._value2 :?> Symbol
                Some <| defaultOp s

            | Name t ->
                match t.Kind with
                | TokenKind.Op
                | TokenKind.Qop ->
                    let s = t._value2 :?> Symbol
                    Some <| defaultOp s

                // or, and
                | TokenKind.Id -> None
                | _ -> None

        let si = { Kind = Var; OperatorInfo = op }
        e, Ident.symbol name, si, []
        
    | ModuleTypeDefinition(typeK, td) -> resolveTypeDefinition env typeK td

and resolveModuleElements env (e, es) =
    let resolveTail env e = function
        | [] -> e, [], env
        | _ ->
            let r env (sp, e) =
                resolveModuleElement env e
                |> mapValue (fun e -> (sp, e))

            resolveMany r env es
            |> mapValue (fun es -> e, es)
    
    let e, si, exports = resolveModuleElement env e
    let exports = si::List.map (fun exportPathRev -> n::exportPathRev) exports
    let env =
        List.fold (fun env (exportsPathRev, info) -> Env.add exportsPathRev info env) env exports
    ()

let resolve env = function
    | AnonymousModule es -> resolveModuleElements env es |> mapValue AnonymousModule
    | NamedModule(m, n, es) ->
        let env = Env.pushCurrents n env
        resolveModuleElements env es
        |> mapValue (fun es -> NamedModule(m, n, es))
        |> mapEnv (Env.popCurrent >> Env.addModule n)