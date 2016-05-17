module Alpa.Parser.Operator
#load "./Alpa.Parser.fsx"

open Alpa

type Result<'T,'E> = Ok of 'T | Error of 'E

type Operator = {
    fixity: Fixity
    associativity: Associativity
    precedence: int
    //fullPath: PathRev
}
type SymbolKind = Module | Var | Type | Pattern

type SymbolInfo = 
    | Module
    | Var of TypeRef
    | VarOp of TypeRef * Operator
    | Type of TypeRef * list<PathRev * SymbolInfo>
    | TypeOp of TypeRef * Operator * list<PathRev * SymbolInfo>
    | Pattern

type Node<'K,'V when 'K : comparison> =
    | Leaf of 'V
    | Node of Map<'K, Node<'K,'V>>

type Tree<'K,'V when 'K : comparison> = Map<'K, Node<'K,'V>>
type Assoc<'k,'v> = list<'k * 'v>
type OperatorMap = Assoc<PathRev * SymbolKind, Operator>
type SymbolTree = Map<PathRev * SymbolKind, SymbolInfo>

type OperatorTable = {
    precedenceKey: int
    assocLOps: OperatorMap
    assocNOps: OperatorMap
    assocROps: OperatorMap
}
type Reply<'a,'c,'e> = Succ of 'a * list<'c> | Fail of 'e
type SolveEnv = {
    infixOpTables: list<OperatorTable>
    postfixOps: OperatorMap
    prefixOps: OperatorMap
    symbols: SymbolTree
    current: PathRev
}
type ExprParser<'a> = {
    operatorParser: OperatorMap -> list<'a> -> Reply<'a * Operator, 'a, ParseError>
    termParser: SolveEnv -> list<'a> -> Reply<'a, 'a, ParseError>
    prefix: 'a -> 'a -> 'a
    postfix: 'a -> 'a -> 'a
    infix: Associativity -> 'a -> 'a -> 'a -> 'a
    functionApply: 'a -> 'a -> list<'a> -> 'a
    getToken: 'a -> Token

    env: SolveEnv
}
module Assoc =
    let empty = []
    let make1 k v = [k, v]
    let rec tryFind k = function
        | [] -> None
        | (k',v)::kvs ->
            match compare k k' with
            | 0 -> Some v
            | c when c < 0 -> None
            | _ -> tryFind k kvs

    let rec add k v = function
        | [] -> [k,v]
        | (k',_) as kv::kvs ->
            match compare k k' with
            | 0 -> (k,v)::kvs
            | c when c < 0 -> (k,v)::kv::kvs
            | _ -> kv::add k v kvs

module OpTable =
    let empty = {
        precedenceKey = 0
        assocLOps = Assoc.empty
        assocNOps = Assoc.empty
        assocROps = Assoc.empty
    }
    let add path ({ associativity = assoc } as x) ({ assocNOps = ns; assocLOps = ls; assocROps = rs } as xs) =
        match assoc with
        | NonAssoc -> { xs with assocNOps = Assoc.add path x ns }
        | Left -> { xs with assocLOps = Assoc.add path x ls }
        | Right -> { xs with assocROps = Assoc.add  path x rs }

    let singleton path ({ associativity = assoc; precedence = prec } as x) =
        match assoc with
        | NonAssoc -> { empty with precedenceKey = prec; assocNOps = Assoc.make1 path x }
        | Left -> { empty with precedenceKey = prec; assocLOps = Assoc.make1 path x }
        | Right -> { empty with precedenceKey = prec; assocROps = Assoc.make1 path x }
    
module Ident =
    let symbol = function
        | Name r
        | ParenthesizedIdentifier(_,r,_) -> 
            let { _value2 = v } = r 
            v :?> Symbol

    let startToken (Name t | ParenthesizedIdentifier(t,_,_)) = t
    let endToken (Name t | ParenthesizedIdentifier(_,_,t)) = t

module LongId =
    let rec appendRev ls rs =
        match ls with
        | [] -> rs
        | (l,_)::ls -> appendRev ls (Ident.symbol l::rs)

    let pathRev (LongIdentifier(ls, r)) =
        match ls with
        | [] -> [Ident.symbol r]
        | [l,_] -> [Ident.symbol r; Ident.symbol l]
        | _ -> Ident.symbol r::appendRev ls []
        
    let kind (LongIdentifier(_,n)) =
        match n with
        | Name n
        | ParenthesizedIdentifier(_,n,_) -> Token.kind n

    let startToken (LongIdentifier([], e) | LongIdentifier((e,_)::_, _)) = Ident.startToken e
    let endToken (LongIdentifier(_, e)) = Ident.endToken e

module List =
    /// appendRev [1;2] [3;4] = [2;1;3;4]
    let rec appendRev ls rs =
        match ls with
        | [] -> rs
        | l::ls -> appendRev ls (l::rs)

module Env =
    let contains path { symbols = syms } = Map.containsKey path syms
    let tryFind path { symbols = syms } = Map.tryFind path syms
    let find path env = Map.find path env.symbols
    let tryFindVar path env = tryFind (LongId.pathRev path, SymbolKind.Var) env
        
    let containsVarOp path env =
        match tryFindVar path env with
        | Some (VarOp _ | TypeOp _) -> true
        | _ -> false

    let containsVar path env = contains (LongId.pathRev path, SymbolKind.Var) env
    let containsPat path env = contains (LongId.pathRev path, SymbolKind.Pattern) env

    let rec addTree l rs v tree =
        match Map.tryFind l tree, rs with
        | Some(Node ltree), r::rs -> Map.add l (Node(addTree r rs v ltree)) tree
        | _, r::rs -> Map.add l (Node(addTree r rs v Map.empty)) tree
        | _, [] -> Map.add l (Leaf v) tree

    let rec addOpTables path ({ precedence = precedence } as x) = function
        | [] -> [OpTable.singleton path x]
        | { precedenceKey = k } as kxs::table ->
            if precedence < k then OpTable.singleton path x::kxs::table
            elif precedence = k then OpTable.add path x kxs::table
            else kxs::addOpTables path x table

    let add path symbolInfo env =
        let {
                symbols = symbols
                infixOpTables = infixOps
                postfixOps = postfixOps
                prefixOps = prefixOps
            } = env

        let symbolKind = function
            | Type _
            | TypeOp _ -> SymbolKind.Type
            | Var _
            | VarOp _ -> SymbolKind.Var
            | Pattern -> SymbolKind.Pattern
            | Module -> SymbolKind.Module

        let path = path, symbolKind symbolInfo
        let symbols = Map.add path symbolInfo symbols

        match symbolInfo with
        | VarOp(_, op)
        | TypeOp(_, op, _) ->
            match op with
            | { fixity = Infix } ->
                { env with 
                    symbols = symbols
                    infixOpTables = addOpTables path op infixOps }

            | { fixity = Postfix } ->
                { env with
                    symbols = symbols
                    postfixOps = Assoc.add path op postfixOps }

            | { fixity = Prefix } ->
                { env with
                    symbols = symbols
                    prefixOps = Assoc.add path op prefixOps }
        
        | Type _
        | Var _
        | Pattern
        | Module -> { env with symbols = symbols }
            
    let fullPath name { current = current } = name::current
    let enter name ({ current = current } as env) = { env with current = name::current }

    let addModule path env = add path Module env

//    let pushCurrent ident env = { env with Current = Ident.symbol ident::env.Current }
//    let pushCurrents n env = { env with Current = fullPath n env }
//    let popCurrent env =
//        match env.Current with
//        | [] -> env
//        | _::current -> { env with Current = current }

    let empty = {
        symbols = Map.empty
        infixOpTables = []
        postfixOps = Assoc.empty
        prefixOps = Assoc.empty
        current = []
    }
    let makeVars xs =
        Seq.fold (fun env (path, op, ty) ->
            match op with
            | None -> add path (Var(TypeRef ty)) env
            | Some(f, a, p) ->
                let op = { fixity = f; associativity = a; precedence = p }
                add path (VarOp(TypeRef ty, op)) env
        ) empty xs

let expressionsParser =
    let idToken (Name t | ParenthesizedIdentifier(_,t,_)) = t
    let longIdToken (LongIdentifier(_, n)) = idToken n

    let parseOp ops = function
        | LookupExpression name as e::es ->
            match LongId.kind name with
            | TokenKind.Id
            | TokenKind.Op
            | TokenKind.Qop ->
                let path = LongId.pathRev name
                match Assoc.tryFind (path, SymbolKind.Var) ops with
                | Some op -> Succ((e, op), es) // Some(op, e, fp)
                | _ -> Fail(UnsolvedIdentifier(path, LongId.startToken name, LongId.endToken name))

            | _ -> Fail(RequireOperator(longIdToken name))
        | _ -> Fail RequireAnyExpression
    
    let rec getToken = function
        | LookupExpression name -> longIdToken name
        | ConstantExpression(Constant t | UnitConstant(t,_)) -> t

        | DotLookupExpression(e, _, _)
        | BlockExpression(_, e, _)
        | ApplicationsExpression(_, e, _, _)
        | SequentialExpression(e, _, _) -> getToken e

        | LetExpression(header = LetHeader(fixity = Some(FixityDeclaration(t, _)))) -> t
        | LetExpression(header = LetHeader(None, n, _)) -> idToken n

    let parseNonOp env = function
        | LookupExpression name as e::es ->
            match LongId.kind name with
            | TokenKind.Id
            | TokenKind.Op
            | TokenKind.Qop ->
                if Env.containsVarOp name env then Fail(RequireNonOperator(longIdToken name))
                else Succ(e, es)
            | _ -> Succ(e, es)
        | e::es -> Succ(e, es)
        | [] -> Fail RequireAnyExpression

    let prefix op e = ApplicationsExpression(PrefixApply, op, e, [])
    let postfix e op = ApplicationsExpression(PostfixApply, op, e, [])
    let funapp l r rs = ApplicationsExpression(IdentifierApply, l, r, rs)
    let infix assoc l op r =
        let assoc =
            match assoc with
            | Left -> InfixLeftApply
            | Right -> InfixRightApply
            | NonAssoc -> InfixNoneApply

        ApplicationsExpression(assoc, op, l, [r])

    {
        operatorParser = parseOp
        termParser = parseNonOp
        prefix = prefix
        postfix = postfix
        infix = infix
        functionApply = funapp
        getToken = getToken
        env = Env.empty
    }

let parseOp { operatorParser = operatorParser } ops es = operatorParser ops es
let parseNonOp { termParser = termParser; env = env } es = termParser env es
let postfix { postfix = postfix } e op = postfix e op
let prefix { prefix = prefix } op e = prefix op e
let funapp { functionApply = functionApply } l r rs = functionApply l r rs
let infix { infix = infix } assoc l op r = infix assoc l op r
let getToken { getToken = getToken } x = getToken x

let parseOps env ops es =
    let rec aux ns es =
        match parseOp env ops es with
        | Fail _ -> ns, es
        | Succ((op, _), es) -> aux (op::ns) es
    aux [] es

let parsePrefixPostOps ({ env = { prefixOps = prefixOps; postfixOps = postfixOps } } as parser) es =
    let prefixOps, es = parseOps parser prefixOps es
    match parseNonOp parser es with
    | Fail _ as r -> r
    | Succ(e, es) ->
        let postfixOps, es = parseOps parser postfixOps es
        match prefixOps, postfixOps with
        | [], [] -> Succ(e, es)
        | _ ->
            // postfix apply
            let e = List.foldBack (fun op e -> postfix parser e op) postfixOps e

            // prefix apply
            let e = List.fold (fun e op -> prefix parser op e) e prefixOps
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
            Succ(funapp env e r rs, es)

let rec parseInfixOpTable env infixOpTable es =
    match infixOpTable with
    | [] -> parseIdApplications env es
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
                
            // infix right apply
            Succ(infix env Right l opE r, es)
            
and parseAssocN env { assocLOps = infixLOps; assocNOps = infixNOps; assocROps = infixROps } infixOpTable l es =
    let assoc { associativity = a } = a

    match parseOp env infixNOps es with
    | Fail e -> Fail e
    | Succ((opE, op), es) ->
        match parseInfixOpTable env infixOpTable es with
        | Fail e -> Fail e
        | Succ(r, es) ->
            match parseOp env infixNOps es with
            | Succ((opE',op'), _) -> Fail(AmbiguousAssociativeOperator(getToken env opE, assoc op, getToken env opE', assoc op'))
            | Fail _ ->
                match parseOp env infixROps es with
                | Succ((opE',op'), _) -> Fail(AmbiguousAssociativeOperator(getToken env opE, assoc op, getToken env opE', assoc op'))
                | Fail _ ->
                    match parseOp env infixLOps es with
                    | Succ((opE',op'), _) -> Fail(AmbiguousAssociativeOperator(getToken env opE, assoc op, getToken env opE', assoc op'))
                    | Fail _ ->
                        
                        // infix none apply
                        Succ(infix env NonAssoc l opE r, es)

and parseAssocL env infixLOps infixOpTable l es =
    match parseOp env infixLOps es with
    | Fail e -> Fail e
    | Succ((opE, _), es) ->
        match parseInfixOpTable env infixOpTable es with
        | Fail e -> Fail e
        | Succ(r, es) ->
            
            // infix left apply
            let l = infix env Left l opE r
            match parseAssocL env infixLOps infixOpTable l es with
            | Fail _ -> Succ(l, es)
            | r -> r

and parseSamePrecedenceInfixOps env infixOps infixOpTable es =
    let { assocLOps = infixLOps; assocROps = infixROps } = infixOps

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
                
exception SolveException of ParseError

let makeSolveException path =
    UnsolvedIdentifier(
        LongId.pathRev path, 
        LongId.startToken path,
        LongId.endToken path
    )
    |> SolveException

let parseLookupExpression env (LongIdentifier(ls, r)) =
    let rec takeMember left leftDelimiter names rightName =
        match names with
        | [] -> DotLookupExpression(left, leftDelimiter, rightName)
        | (name, delimiter)::names -> takeMember (DotLookupExpression(left, leftDelimiter, name)) delimiter names rightName

    let rec takeLookup readedNames names rightName =
        match names with
        | [] ->
            let path = LongIdentifier(List.rev readedNames, rightName)
            match Env.tryFindVar path env with
            | Some(Var _) -> LookupExpression path
            | _ -> raise <| makeSolveException path

        | (name, delimiter) as n::names ->
            let readedNames' = n::readedNames
            let path = LongIdentifier(List.rev readedNames', name)

            match Env.tryFindVar path env with
            | Some(Var _) -> takeMember (LookupExpression path) delimiter names rightName
            | _ -> takeLookup readedNames' names rightName

    takeLookup [] ls r

let parseApplicationsExpression ({ env = { infixOpTables = infixOpTables } } as parser) es =
    match parseInfixOpTable parser infixOpTables es with
    | Succ(e, []) -> e
    | Succ _ -> raise <| SolveException RequireExpressionsEnd
    | Fail e -> raise <| SolveException e

            
// id (a, a) = a // error
// id (a | a) = a // ok
// id (xs | (a::xs)) = xs // error


let rec solvePat env = function
    | WildcardPattern _ as p -> p, []
    | ParenthesizedPattern(beginP, p, endP) ->
        let p, locals = solvePat env p
        ParenthesizedPattern(beginP, p, endP), locals

    // var | constant | Enum Like Constructor Pat
    | LongIdentifierPattern path as p ->
        if Env.containsVar path env || Env.containsPat path env then
            
            // constant pattern | enum like constructor pattern
            p, []

        else
            // var
            match path with
            | LongIdentifier([], local) -> p, [local]
            | _ -> raise <| makeSolveException path

let addLocals locals env =
    List.fold (fun env (local, t) -> Env.add [Ident.symbol local] (Var t) env) env locals

let solvePats env pats =
    let duplicateIfRaise localSet locals =
        let dup = List.tryPick (fun x -> List.tryFind (fun y -> x = y) locals) localSet
        match dup with
        | Some dup -> raise <| SolveException(DuplicatedArgument dup)
        | None -> ()

    let foldPats env (localSet, pats) pat =
        let pat, locals = solvePat env pat
        duplicateIfRaise localSet locals
        List.appendRev locals localSet, pat::pats

    let locals, pats = List.fold (foldPats env) ([], []) pats
    List.rev pats, addLocals locals env
            
let notContainsIfRaise env name type' =
    if not <| Env.contains (name, SymbolKind.Type) env then
        raise <| SolveException(UnsolvedType(name, type'))

let rec solveType env = function
    | FunctionType(l,arrow,r) as t ->
        let name = ["->"]
        
        notContainsIfRaise env name t

        let l, _ = solveType env l
        let r, _ = solveType env r
        FunctionType(l, arrow, r), name

    | UnitType _ as t ->
        let name = ["()"]
        notContainsIfRaise env name t
        t, name

    | ParenthesizedType(beginP, t, endP) ->
        let t, path = solveType env t
        ParenthesizedType(beginP, t, endP), path

    | TupleType(t1, d, t2, tds) as t ->
        let name =
            match tds with
            | [] -> [","]
            | _ -> [List.fold (fun s _ -> s + ",") "," tds]
            
        notContainsIfRaise env name t

        let t1, _ = solveType env t1
        let t2, _ = solveType env t2
        let tds =
            match tds with
            | [] -> tds
            | _ -> List.map (fun (d, t) -> let t, _ = solveType env t in d, t) tds

        TupleType(t1, d, t2, tds), name

    | ListType(openP, t, closeP) as t' ->
        let name = ["[]"]
        
        notContainsIfRaise env name t'
        
        let t, _ = solveType env t
        ListType(openP, t, closeP), name

    | NamedType(path, targs) as t ->
        let name = LongId.pathRev path

        if not <| Env.contains (name, SymbolKind.Type) env then
            raise <| SolveException(UnsolvedType(name, t))
        else
            let targs = List.map (fun t -> let t, _ = solveType env t in t) targs
            NamedType(path, targs), name
            
let assocR80 = { fixity = Infix; associativity = Right; precedence = 80 }
let assocL70 = { fixity = Infix; associativity = Left; precedence = 70 }
let assocL60 = { fixity = Infix; associativity = Left; precedence = 60 }
let assocL40 = { fixity = Infix; associativity = Left; precedence = 40 }
let assocL30 = { fixity = Infix; associativity = Left; precedence = 30 }
let assocL20 = { fixity = Infix; associativity = Left; precedence = 20 }
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
        if 2 <= String.length s then
            match s.[0], s.[1] with
            | '*', '*' -> assocR80
            | '/', '=' -> assocL40
            | _ -> defaultOp1 s.[0]

        elif 1 <= s.Length then defaultOp1 s.[0]
        else
            assocL60

// a + b = ()
// (+) a b = ()
// a `div` b = ()
// ``test`` a b = ()

let symbolInfoOfName = function
    | ParenthesizedIdentifier(_,{ _value2 = v2 },_) ->
        v2
        :?> Symbol
        |> defaultOp
        |> VarOp

    | Name { Kind = kind; _value2 = v2 } ->
        match kind with
        | TokenKind.Op
        | TokenKind.Qop ->
            v2
            :?> Symbol
            |> defaultOp
            |> VarOp

        // or, and
        | TokenKind.Id -> Var
        | _ -> Var

module Types =
    let unitType =
        UnitType(
            Tokens.makeS TokenKind.D Special.``D(``,
            Tokens.makeS TokenKind.D Special.``D)``
        )
    let characterType = []

let symbolInfo fixity name type' =
    match fixity with
    | Some(FixityDeclaration({ Kind = TokenKind.Rid; _value = v }, { Kind = TokenKind.I; _value = i1; _value2 = i2 })) ->
        let prec =
            match i2 with
            | null -> i1
            | _ -> int <| unbox<bigint> i2

        let c = LanguagePrimitives.EnumOfValue<_,Special>(char<int> v)
        match c with
        | Special.Prefix -> VarOp(type', { fixity = Prefix; associativity = NonAssoc; precedence = prec })
        | Special.Infixl -> VarOp(type', { fixity = Infix; associativity = Left; precedence = prec })
        | Special.Infix -> VarOp(type', { fixity = Infix; associativity = NonAssoc; precedence = prec })
        | Special.Infixr -> VarOp(type', { fixity = Infix; associativity = Right; precedence = prec })
        | Special.Postfix -> VarOp(type', { fixity = Postfix; associativity = NonAssoc; precedence = prec })
        | _ -> symbolInfoOfName name type'
    | _ -> symbolInfoOfName name type'

let rec occur var = function
    | TypeRef(_, ts) -> List.exists (occur var) ts
    | TypeVar v when obj.ReferenceEquals(var, v) -> true
    | TypeVar { contents = None } -> false
    | TypeVar { contents = Some v } -> occur var v

let rec unify l r =
    match l, r with
    | TypeRef(l, ls), TypeRef(r, rs) when l = r && List.length ls = List.length rs ->
        List.iter2 unify ls rs

    | TypeVar l, TypeVar r when obj.ReferenceEquals(l, r) -> ()
    | TypeVar { contents = Some l }, _ -> unify l r
    | _, TypeVar { contents = Some r } -> unify l r
    | TypeVar({ contents = None } as lv), _ ->
        if occur lv r then raise <| SolveException(UnifyFailure(l, r))
        lv := Some r

    | _, TypeVar({ contents = None} as rv) ->
        if occur rv l then raise <| SolveException(UnifyFailure(l, r))
        rv := Some l

    | _ -> raise <| SolveException(UnifyFailure(l, r))
        

let solveNamedType env name startToken endToken =
    match Env.tryFind (name, SymbolKind.Type) env with
    | Some(SymbolInfo.Type(tr, _))
    | Some(SymbolInfo.TypeOp(tr, _, _)) -> tr
    | _ -> raise <| SolveException(UnsolvedTypeOfSource(name, startToken, endToken))

let solveConstant env = function
        
    // TODO: IsUnit a => a
    | UnitConstant(startP, endP) ->
        let name = ["()"]
        let tr = solveNamedType env name startP endP
        if not <| Env.contains (name, SymbolKind.Var) env then
            raise <| SolveException(UnsolvedIdentifier(name, startP, endP))
        else
            tr

    | Constant({ Kind = k } as t) ->
        match k with

        // TODO: IsCharacterLiteral a => a
        | TokenKind.C -> solveNamedType env ["Character"] t t

        // TODO: IsFloatLiteral a => a
        | TokenKind.F -> solveNamedType env ["Float"] t t

        // TODO: IsIntegerLiteral a => a
        | TokenKind.I -> solveNamedType env ["Int"] t t
        
        // TODO: IsStringLiteral a => a
        | TokenKind.S -> solveNamedType env ["String"] t t

        // unreachable
        | _ -> solveNamedType env ["()"] t t

let rec solveExpr env = function
    | ConstantExpression c as e -> e, solveConstant env c
    | DotLookupExpression(e, dotD, name) ->
        
        // TODO: DotLookupExpression(solveExpr env e, dotD, name)
        failwith "not implemented"

    | BlockExpression(openD, e, closeD) ->
        let e, et = solveExpr env e
        BlockExpression(openD, e, closeD), et

    | SequentialExpression(l, d, r) ->
        let l, lt = solveExpr env l
        let r, rt = solveExpr env r
        
        // TODO: (startToken l) (endToken r)
        let tr = solveNamedType env ["()"] d d
        unify lt tr
        SequentialExpression(l, d, r), rt

    | LetExpression(LetHeader(fixity, name, []), TypeScheme([], type'), eqD, value, d, body) ->
        let value, vt = solveExpr env value
        unify type' vt

        let env = Env.add [Ident.symbol name] (symbolInfo fixity name t) env
        let body = solveExpr env body
        LetExpression(LetHeader(fixity, name, pats), type', eqD, value, d, body)

//    | LetExpression(LetHeader(fixity, name, pats), type', eqD, value, d, body) ->
//        
//        let pats, env' = solvePats env pats
//        let value = solveExpr env' value
//        let env = Env.add [Ident.symbol name] (symbolInfo fixity name) env
//        let body = solveExpr env body
//        LetExpression(LetHeader(fixity, name, pats), type', eqD, value, d, body)

    | LookupExpression name -> parseLookupExpression env name
    | ApplicationsExpression(_, l, r, rs) ->
        let p = { expressionsParser with env = env }
        parseApplicationsExpression p (l::r::rs)

let solveTypeDefinition env = function
    | EmptyTypeDefinition(TypeName(name, _)) as d ->
        let name = Ident.symbol name
        d, name, Type(Env.fullPath name env, []), []

    // type Bool = true | false
    // // type Bool, Bool.true, Bool.false, true, false
    //
    // type B = Bool
    // // type Bool, Bool.true, Bool.false, true, false, type B, B.true, B.false
    | AbbreviationTypeDefinition(TypeName(name, args) as typeName, eqD, typeValue) ->
        let env =
            List.fold (fun env targ ->
                match targ with
                | TypeArgument a ->
                    let path = [Ident.symbol a]
                    Env.add path (Type(path, [])) env

                | TypeArgumentHole _ -> env
            ) env args
        
        let typeValue, path = solveType env typeValue

        let exports =
            match Env.find (path, SymbolKind.Type) env with
            | Type(_, exports)
            | TypeOp(_, _, exports) -> exports
            | _ -> []

        let d = AbbreviationTypeDefinition(typeName, eqD, typeValue)
        let name = Ident.symbol name
        d, name, Type(Env.fullPath name env, exports), exports

//module M =
//    module X =
//        mx0 = 0
//
//        // mx0
//        mx1 = 1
//
//    // X.mx0; X.mx1
//    m0 = 0
//
//    // X.mx0; X.mx1
//    m1 = 1

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

type SymbolRose = SymbolRose of SymbolInfo * list<Symbol * SymbolRose>
type Exports = Symbol * SymbolRose

let addExports path si exports =
    if List.exists (fun (pathRev, si) -> pathRev = path) exports then exports
    else
        (path, si)::List.map (fun (pathRev, si) -> List.appendRev path pathRev, si) exports

let addScope env path si exports =
    let exports = addExports path si exports
    let env = List.fold (fun env (pathRev, si) -> Env.add pathRev si env) env exports
    exports, env

let rec solveModuleElement env = function
    | ModuleDefinition(_,n,_,_,None,_) as e -> e, Ident.symbol n, Module, []
    | ModuleDefinition(moduleK,n,eq,blockBegin,Some es,blockEnd) ->
        let env = Env.enter (Ident.symbol n) env
        let es, exports = solveModuleInner env es
        ModuleDefinition(moduleK, n, eq, blockBegin, Some es, blockEnd),
            Ident.symbol n,
            Module,
            exports

    | ModuleLetElement(LetHeader(fixity, name, pats), type', eq, blockBegin, value, blockEnd) ->
        let pats, env = solvePats env pats
        let value = solveExpr env value
        //let value, valueType = solveExpr env value
        //unify type' valueType

        ModuleLetElement(LetHeader(fixity, name, pats), type', eq, blockBegin, value, blockEnd),
            Ident.symbol name,
            symbolInfo fixity name,
            []

    | ModuleTypeDefinition(typeK, def) ->
        let def, n, si, exports = solveTypeDefinition env def
        ModuleTypeDefinition(typeK, def), n, si, exports

and solveModuleInner env (e, es) =
    let e, name, si, exports' = solveModuleElement env e
    let exports, env = addScope env [name] si exports'
    
    let rec solveTail env rs exports = function
        | [] -> List.rev rs, exports
        | (d,e)::es ->
            let e, name, si, exports' = solveModuleElement env e
            let exports', env = addScope env [name] si exports'
            solveTail env ((d,e)::rs) (List.appendRev exports' exports) es

    let es, exports = solveTail env [] exports es
    (e, es), exports
    
let solveImplementationFile env = function
    | AnonymousModule es ->
        let es, exports = solveModuleInner env es
        AnonymousModule es, exports

    | NamedModule(moduleK, name, es) ->
        let env = { env with current = LongId.pathRev name }

        let es, exports = solveModuleInner env es
        let exports = addExports (LongId.pathRev name) Module exports
        NamedModule(moduleK, name, es), exports

let trySolve solve env f =
    try solve env f |> Ok with
    | SolveException e -> Error e

let solve env f =
    try 
        match f with
        | None -> Ok(None, [])
        | Some f ->
            let f, es = solveImplementationFile env f
            Ok(Some f, es)
    with
    | SolveException e -> Error e