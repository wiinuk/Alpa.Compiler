module internal Alpa.Parser.Operator
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
type SymbolKind = Module | Var | Type | Pattern
type SymbolInfo = 
    | Module
    | Var
    | VarOp of Operator
    | Type of list<PathRev * SymbolInfo>
    | TypeOp of Operator * list<PathRev * SymbolInfo>
    | Pattern

type Node<'K,'V when 'K : comparison> =
    | Leaf of 'V
    | Node of Map<'K, Node<'K,'V>>

type Tree<'K,'V when 'K : comparison> = Map<'K, Node<'K,'V>>
type Assoc<'k,'v> = list<'k * 'v>
type OperatorMap = Assoc<PathRev * SymbolKind, Operator>
type SymbolTree = Map<PathRev * SymbolKind, SymbolInfo>

type OperatorTable = {
    PrecedenceKey: int
    AssocLOps: OperatorMap
    AssocNOps: OperatorMap
    AssocROps: OperatorMap
}
type Reply<'a,'c,'e> = Succ of 'a * list<'c> | Fail of 'e
type SolveEnv = {
    InfixOpTables: list<OperatorTable>
    PostfixOps: OperatorMap
    PrefixOps: OperatorMap
    Symbols: SymbolTree
}
type ExprParser<'a> = {
    OpParser: OperatorMap -> list<'a> -> Reply<'a * Operator, 'a, ParseError>
    TermParser: SolveEnv -> list<'a> -> Reply<'a, 'a, ParseError>
    Prefix: 'a -> 'a -> 'a
    Postfix: 'a -> 'a -> 'a
    Infix: Associativity -> 'a -> 'a -> 'a -> 'a
    FunctionApply: 'a -> 'a -> list<'a> -> 'a
    GetToken: 'a -> Token

    Env: SolveEnv
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
        PrecedenceKey = 0
        AssocLOps = Assoc.empty
        AssocNOps = Assoc.empty
        AssocROps = Assoc.empty
    }
    let add path x xs =
        match x.Associativity with
        | NonAssoc -> { xs with AssocNOps = Assoc.add path x xs.AssocNOps }
        | Left -> { xs with AssocLOps = Assoc.add path x xs.AssocLOps }
        | Right -> { xs with AssocROps = Assoc.add  path x xs.AssocROps }

    let singleton path x =
        match x.Associativity with
        | NonAssoc -> { empty with PrecedenceKey = x.Precedence; AssocNOps = Assoc.make1 path x }
        | Left -> { empty with PrecedenceKey = x.Precedence; AssocLOps = Assoc.make1 path x }
        | Right -> { empty with PrecedenceKey = x.Precedence; AssocROps = Assoc.make1 path x }
    
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
    let contains path env = Map.containsKey path env.Symbols
    let tryFind path env = Map.tryFind path env.Symbols
    let find path env = Map.find path env.Symbols
    let tryFindVar path env = tryFind (LongId.path path, SymbolKind.Var) env
        
    let containsVarOp path env =
        match tryFindVar path env with
        | Some (VarOp _ | TypeOp _) -> true
        | _ -> false

    let containsVar path env = contains (LongId.path path, SymbolKind.Var) env
    let containsPat path env = contains (LongId.path path, SymbolKind.Pattern) env

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
        let symbolKind = function
            | Type _
            | TypeOp _ -> SymbolKind.Type
            | Var
            | VarOp _ -> SymbolKind.Var
            | Pattern -> SymbolKind.Pattern
            | Module -> SymbolKind.Module

        let path = path, symbolKind symbolInfo
        let symbols = Map.add path symbolInfo env.Symbols

        match symbolInfo with
        | VarOp op
        | TypeOp(op, _) ->
            match op with
            | { Fixity = Infix } ->
                { env with 
                    Symbols = symbols
                    InfixOpTables = addOpTables path op env.InfixOpTables }

            | { Fixity = Postfix } ->
                { env with
                    Symbols = symbols
                    PostfixOps = Assoc.add path op env.PostfixOps }

            | { Fixity = Prefix } ->
                { env with
                    Symbols = symbols
                    PrefixOps = Assoc.add path op env.PrefixOps }
        
        | Type _
        | Var
        | Pattern
        | Module -> env
            
    //let fullPath (LongIdentifier(ls,r)) env = Ident.symbol r::LongId.appendRev ls env.Current

    let addModule path env = add path Module env

//    let pushCurrent ident env = { env with Current = Ident.symbol ident::env.Current }
//    let pushCurrents n env = { env with Current = fullPath n env }
//    let popCurrent env =
//        match env.Current with
//        | [] -> env
//        | _::current -> { env with Current = current }

    let empty = {
        Symbols = Map.empty
        InfixOpTables = []
        PostfixOps = Assoc.empty
        PrefixOps = Assoc.empty
//            Current = []
    }
    let makeVars xs =
        Seq.fold (fun env (path, op) ->
            match op with
            | None -> add path Var env
            | Some(f, a, p) ->
                let op = { Fixity = f; Associativity = a; Precedence = p }
                add path (VarOp op) env
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
                match Assoc.tryFind (LongId.path name, SymbolKind.Var) ops with
                | Some op -> Succ((e, op), es) // Some(op, e, fp)
                | _ -> Fail(UnsolvedIdentifier name)

            | _ -> Fail(RequireOperator(longIdToken name))
        | _ -> Fail RequireAnyExpression
    
    let rec getToken = function
        | LookupExpression name -> longIdToken name
        | ConstantExpression(Constant t | UnitConstant(t,_)) -> t

        | DotLookupExpression(e, _, _)
        | BlockExpression(_, e, _)
        | ApplicationsExpression(_, e, _, _)
        | SequentialExpression(e, _, _) -> getToken e

        | LetExpression(LetHeader(Some(FixityDeclaration(t, _)), _, _), _, _, _, _) -> t
        | LetExpression(LetHeader(None, n, _), _, _, _, _) -> idToken n

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
        OpParser = parseOp
        TermParser = parseNonOp
        Prefix = prefix
        Postfix = postfix
        Infix = infix
        FunctionApply = funapp
        GetToken = getToken
        Env = Env.empty
    }

let parseOp env ops es = env.OpParser ops es
let parseNonOp env es = env.TermParser env.Env es
let postfix env e op = env.Postfix e op
let prefix env op e = env.Prefix e op
let funapp env l r rs = env.FunctionApply l r rs
let infix env assoc l op r = env.Infix assoc l op r
let getToken env x = env.GetToken x

let parseOps env ops es =
    let rec aux ns es =
        match parseOp env ops es with
        | Fail _ -> ns, es
        | Succ((op, _), es) -> aux (op::ns) es
    aux [] es

let parsePrefixPostOps env es =
    let prefixOps, es = parseOps env env.Env.PrefixOps es
    match parseNonOp env es with
    | Fail _ as r -> r
    | Succ(e, es) ->
        let postfixOps, es = parseOps env env.Env.PostfixOps es
        match prefixOps, postfixOps with
        | [], [] -> Succ(e, es)
        | _ ->
            // postfix apply
            let e = List.foldBack (fun op e -> postfix env e op) postfixOps e

            // prefix apply
            let e = List.fold (fun e op -> prefix env op e) e prefixOps
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
            
and parseAssocN env { AssocLOps = infixLOps; AssocNOps = infixNOps; AssocROps = infixROps } infixOpTable l es =
    let assoc { Associativity = a } = a

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
                
exception SolveException of ParseError

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
            | Some Var -> LookupExpression path
            | _ -> raise <| SolveException(UnsolvedIdentifier path)

        | (name, delimiter) as n::names ->
            let readedNames' = n::readedNames
            let path = LongIdentifier(List.rev readedNames', name)

            match Env.tryFindVar path env with
            | Some Var -> takeMember (LookupExpression path) delimiter names rightName
            | _ -> takeLookup readedNames' names rightName

    takeLookup [] ls r

let parseApplicationsExpression env es =
    match parseInfixOpTable env env.Env.InfixOpTables es with
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
            | _ -> raise <| SolveException(UnsolvedIdentifier path)

let addLocals locals env = List.fold (fun env local -> Env.add [Ident.symbol local] Var env) env locals

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
            
let emptyExportsType = Type []
let notContainsIfRaise env name token =
    if not <| Env.contains (name, SymbolKind.Type) env then
        raise <| SolveException(UnsolvedType(name, token))

let rec solveType env = function
    | FunctionType(l,arrow,r) ->
        let name = ["->"]

        notContainsIfRaise env name arrow

        let l, _ = solveType env l
        let r, _ = solveType env r
        FunctionType(l, arrow, r), name

    | ParenthesizedType(beginP, t, endP) ->
        let t, path = solveType env t
        ParenthesizedType(beginP, t, endP), path

    | TupleType(t1, d, t2, tds) ->
        let name =
            match tds with
            | [] -> [","]
            | _ -> [List.fold (fun s _ -> s + ",") "," tds]
            
        notContainsIfRaise env name d

        let t1, _ = solveType env t1
        let t2, _ = solveType env t2
        let tds =
            match tds with
            | [] -> tds
            | _ -> List.map (fun (d, t) -> let t, _ = solveType env t in d, t) tds

        TupleType(t1, d, t2, tds), name

    | ListType(openP, t, closeP) ->
        let name = ["[]"]
        
        notContainsIfRaise env name openP
        
        let t, _ = solveType env t
        ListType(openP, t, closeP), name

    | NamedType(path, targs) ->
        let name = LongId.path path

        if not <| Env.contains (name, SymbolKind.Type) env then
            raise <| SolveException(UnsolvedIdentifier path)
        else
            let targs = List.map (fun t -> let t, _ = solveType env t in t) targs
            NamedType(path, targs), name
            
let assocR80 = { Fixity = Infix; Associativity = Right; Precedence = 80 }
let assocL70 = { Fixity = Infix; Associativity = Left; Precedence = 70 }
let assocL60 = { Fixity = Infix; Associativity = Left; Precedence = 60 }
let assocL40 = { Fixity = Infix; Associativity = Left; Precedence = 40 }
let assocL30 = { Fixity = Infix; Associativity = Left; Precedence = 30 }
let assocL20 = { Fixity = Infix; Associativity = Left; Precedence = 20 }
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

// a + b = ()
// (+) a b = ()
// a `div` b = ()
// ``test`` a b = ()

let symbolInfoOfName = function
    | ParenthesizedIdentifier(_,t,_) ->
        t._value2
        :?> Symbol
        |> defaultOp
        |> VarOp

    | Name t ->
        match t.Kind with
        | TokenKind.Op
        | TokenKind.Qop ->
            t._value2
            :?> Symbol
            |> defaultOp
            |> VarOp

        // or, and
        | TokenKind.Id -> Var
        | _ -> Var


let symbolInfo fixity name =
    match fixity with
    | Some(FixityDeclaration({ Kind = TokenKind.Rid; _value = v }, { Kind = TokenKind.I; _value = i1; _value2 = i2 })) ->
        let prec =
            match i2 with
            | null -> i1
            | _ -> int <| unbox<bigint> i2

        let c = LanguagePrimitives.EnumOfValue<_,Special>(char<int> v)
        match c with
        | Special.Prefix -> VarOp { Fixity = Prefix; Associativity = NonAssoc; Precedence = prec }
        | Special.Infixl -> VarOp { Fixity = Infix; Associativity = Left; Precedence = prec }
        | Special.Infix -> VarOp { Fixity = Infix; Associativity = NonAssoc; Precedence = prec }
        | Special.Infixr -> VarOp { Fixity = Infix; Associativity = Right; Precedence = prec }
        | Special.Postfix -> VarOp { Fixity = Postfix; Associativity = NonAssoc; Precedence = prec }
        | _ -> symbolInfoOfName name
    | _ -> symbolInfoOfName name

let rec solveExpr env = function
| ConstantExpression _ as e -> e

| DotLookupExpression(e, dotD, name) -> DotLookupExpression(solveExpr env e, dotD, name)
| BlockExpression(openD, e, closeD) -> BlockExpression(openD, solveExpr env e, closeD)
| SequentialExpression(l, d, r) -> SequentialExpression(solveExpr env l, d, solveExpr env r)

| LetExpression(LetHeader(fixity, name, pats), eqD, value, d, body) ->
    let pats, env' = solvePats env pats
    let value = solveExpr env' value
    let env = Env.add [Ident.symbol name] (symbolInfo fixity name) env
    let body = solveExpr env body
    LetExpression(LetHeader(fixity, name, pats), eqD, value, d, body)

| LookupExpression name -> parseLookupExpression env name
| ApplicationsExpression(_, l, r, rs) ->
    let p = { expressionsParser with Env = env }
    parseApplicationsExpression p (l::r::rs)

let solveTypeDefinition env = function
    | EmptyTypeDefinition(TypeName(name, args)) as d ->
        d, Ident.symbol name, emptyExportsType, []

    // type Bool = true | false
    // // type Bool, Bool.true, Bool.false, true, false
    //
    // type B = Bool
    // // type Bool, Bool.true, Bool.false, true, false, type B, B.true, B.false
    | AbbreviationTypeDefinition(TypeName(name, args) as typeName, eqD, typeValue) ->
        let env =
            List.fold (fun env targ ->
                match targ with
                | TypeArgument a -> Env.add [Ident.symbol a] emptyExportsType env
                | TypeArgumentHole _ -> env
            ) env args
        
        let typeValue, path = solveType env typeValue

        let exports =
            match Env.find (path, SymbolKind.Type) env with
            | Type exports
            | TypeOp(_, exports) -> exports
            | _ -> []

        let d = AbbreviationTypeDefinition(typeName, eqD, typeValue)
        d, Ident.symbol name, Type exports, exports

module M =
    
    module X =
        let mx0 = 0

        // mx0
        let mx1 = 1

    // X.mx0; X.mx1
    let m0 = 0

    // X.mx0; X.mx1
    let m1 = 1

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
    (path, si)::List.map (fun (pathRev, si) -> List.appendRev path pathRev, si) exports

let addScope env path si exports =
    let exports = addExports path si exports
    let env = List.fold (fun env (pathRev, si) -> Env.add pathRev si env) env exports
    exports, env


let solveModuleLetElement env (LetHeader(fixity, name, pats), eq, blockBegin, body, blockEnd) =
    let pats, env = solvePats env pats
    let body = solveExpr env body
    let e = ModuleLetElement(LetHeader(fixity, name, pats), eq, blockBegin, body, blockEnd)
    e, Ident.symbol name, symbolInfo fixity name, []

let rec solveModuleElement env = function
    | ModuleDefinition(_,n,_,_,None,_) as e -> e, Ident.symbol n, Module, []
    | ModuleDefinition(moduleK,n,eq,blockBegin,Some es,blockEnd) ->
        let es, exports = solveModuleInner env es
        let exports = List.map (fun (pathRev, si) -> (Ident.symbol n::pathRev), si) exports
        let e = ModuleDefinition(moduleK,n,eq,blockBegin,Some es,blockEnd)
        e, Ident.symbol n, Module, exports

    | ModuleLetElement(head, eq, blockBegin, body, blockEnd) -> solveModuleLetElement env (head, eq, blockBegin, body, blockEnd)
    | ModuleTypeDefinition(typeK, def) ->
        let def, n, si, exports = solveTypeDefinition env def
        ModuleTypeDefinition(typeK, def), n, si, exports

and solveModuleInner env (e, es) =
    let e, name, si, exports = solveModuleElement env e
    let exports, env = addScope env [name] si exports

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
        let es, exports = solveModuleInner env es
        let exports = addExports (LongId.path name) Module exports
        NamedModule(moduleK, name, es), exports

let solve env f =
    try Option.map (solveImplementationFile env) f |> Ok
    with
    | SolveException e -> Error e