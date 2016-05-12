module Alpa.Parser
#load "./Alpa.Parser.Types.fsx"

open Alpa.IO
open Alpa.IO.Stream
open Alpa.Token
open Alpa.ParserCombinator

type State = ValueTuple3<Position, list<Position>, unit>
let initialState: State = ValueTuple3(Item1 = Position(0<_>, 1<_>, 1<_>), Item2 = [], Item3 = ())

type Fixity =
    | Prefix
    | Infix
    | Postfix

type Associativity =
    | NonAssoc
    | Left
    | Right

type ParseError =
    | ErrorNone

    | RequireSpecialToken of Special
    | RequireIdentiferToken
    | RequireOperatorToken

    /// Char, Int, Float, String
    | RequireLiteralToken
    | RequireLineSeparator
    | RequireBlockBegin
    | RequireBlockEnd
    | RequireFileStart
    | RequireApplicationSeparator
    
    | RequireAnyExpression
    | RequireExpressionsEnd
    | RequireOperator of Token
    | RequireNonOperator of Token
    | AmbiguousAssociativeOperator of prevOp: Token * prevAssoc: Associativity * nowOp: Token * nowAssoc: Associativity

    | UnsolvedIdentifier of LongIdentifier
    | UnsolvedType of list<Symbol> * Token

    | DuplicatedArgument of Identifier

type Parser<'a> = Parser<Token, State, ParseError, 'a>
let (|Parser|) (p: Parser<_>) = p
let (|Stream|) (xs: Stream<_,State>) = xs

let rParser s = satisfyE (isR s) (RequireSpecialToken s)

module Specials =
    let ``(`` = rParser Special.``D(``
    let ``)`` = rParser Special.``D)``
    let ``;`` = rParser Special.``D;``
    let ``,`` = rParser Special.``D,``
    let ``[`` = rParser Special.``D[``
    let ``]`` = rParser Special.``D]``
    let ``{`` = rParser Special.``D{``
    let ``}`` = rParser Special.``D}``

    let ``d=`` = rParser Special.``O=``
    let ``.`` = rParser Special.``O.``
    let ``->`` = rParser Special.``O->``

    let ``_`` = rParser Special.I_
    let ``module`` = rParser Special.Module
    let ``type`` = rParser Special.Type
//    let ``let`` = RParser Special.Let
//    let ``in`` = RParser Special.In

module Layout =
    let lineSeparatorToken =
        {
            TriviaStart = Position()
            Start = Position()
            Kind = D
            _value = int (LanguagePrimitives.EnumToValue Special.``D;``)
            _value2 = null
            End = Position()
        }

    let blockBeginLayoutToken =
        {
            TriviaStart = Position()
            Start = Position()
            Kind = D
            _value = int (LanguagePrimitives.EnumToValue Special.``D{``)
            _value2 = null
            End = Position()
        }

    let blockEndLayoutToken =
        {
            TriviaStart = Position()
            Start = Position()
            Kind = D
            _value = int (LanguagePrimitives.EnumToValue Special.``D}``)
            _value2 = null
            End = Position()
        }

    let lineSeparator (Stream xs) =
        if canRead xs then Reply((), RequireLineSeparator)
        else
            let offside = xs.UserState.Item1
            let p = (get xs 0).Start
            if not (offside.Line < p.Line && offside.Column = p.Column) then Reply((), RequireLineSeparator)
            else
                xs.UserState.Item1 <- p
                Reply lineSeparatorToken

    let applicationSeparator (Stream xs) =
        if canRead xs then Reply((), RequireApplicationSeparator)
        else
            let offside = xs.UserState.Item1
            let p = (get xs 0).Start
            if not (offside.Line <= p.Line && offside.Column <= p.Column) then Reply((), RequireBlockBegin)
            else
                Reply(())

    let blockBegin (Stream xs) =
        if canRead xs then Reply((), RequireBlockBegin)
        else
            let offside = xs.UserState.Item1
            let p = (get xs 0).Start
            if not (offside.Line <= p.Line && offside.Column < p.Column) then Reply((), RequireBlockBegin)
            else
                let offsideStack = xs.UserState.Item2
                xs.UserState.Item1 <- p
                xs.UserState.Item2 <- offside::offsideStack
                Reply blockBeginLayoutToken

    let blockEnd (Stream xs) =
        match xs.UserState.Item2 with
        | [] -> Reply((), RequireBlockEnd)
        | offside::offsideStack ->
            xs.UserState.Item1 <- offside
            xs.UserState.Item2 <- offsideStack
            Reply blockEndLayoutToken

    let fileStart (Stream xs) =
        if canRead xs then Reply((), RequireFileStart)
        else
            match xs.UserState.Item2 with
            | _::_ -> Reply((), RequireFileStart)
            | [] ->
                xs.UserState.Item1 <- (get xs 0).Start
                Reply(())

module S = Specials
let lineSeparator = S.``;`` <|> Layout.lineSeparator
let block p f = pipe3 S.``{`` p S.``}`` f <|> pipe3 Layout.blockBegin p Layout.blockEnd f

// ++, `div`
let operator = satisfyE isOp RequireOperatorToken

/// id, Id, ``i d``, (+), (`div`)
let identifier =
    (satisfyE isId RequireIdentiferToken |>> Name) <|>
    (pipe3 S.``(`` operator S.``)`` <| fun a b c -> ParenthesizedIdentifier(a, b, c))

let identifierOrOperator = identifier <|> (operator |>> Name)

let path0 = many (identifier .>>. S.``.``)

let longIdentifier = pipe2 path0 identifier <| fun xs x -> LongIdentifier(xs, x)
let longIdentifierOrOperator = pipe2 path0 identifierOrOperator <| fun xs x -> LongIdentifier(xs, x)

let constant =
    (satisfyE (fun t -> match t.Kind with I | F | C | S -> true | _ -> false) RequireLiteralToken |>> Constant) <|>
    pipe2 S.``(`` S.``)`` (fun a b -> UnitConstant(a, b))

let pattern, _pattern = createParserForwardedToRef()

let atomicPattern =
    choice [
//        ``const``
        S.``_`` |>> WildcardPattern
        pipe3 S.``(`` pattern S.``)`` <| fun a b c -> ParenthesizedPattern(a, b, c)
        longIdentifier |>> LongIdentifierPattern
//        listPattern
//        recordPattern
//        arrayPattern
//        D.``:?`` atomicType
//        K.``null``
    ]

_pattern :=
    choice [
        S.``_`` |>> WildcardPattern
        pipe3 S.``(`` pattern S.``)`` <| fun a b c -> ParenthesizedPattern(a, b, c)
        longIdentifier |>> LongIdentifierPattern // pat-paramopt patopt -- named pattern
//        const -- constant pattern
//        pat as ident -- "as" pattern
//        pat '|' pat -- disjunctive pattern
//        pat '&' pat -- conjunctive pattern
//        pat :: pat -- "cons" pattern
//        pat : type -- pattern with type constraint
//        pat,...,pat -- tuple pattern
//        list-pat -- list pattern
//        array-pat -- array pattern
//        record-pat -- record pattern
//        :? atomic-type -- dynamic type test pattern
//        :? atomic-type as ident -- dynamic type test pattern
//        null -- null-test pattern
//        attributes pat -- pattern with attributes
    ]

let letHeader =
    let opHead = pipe4 atomicPattern operator atomicPattern (many atomicPattern) <| fun p1 n p2 ps -> LetHeader(Name n, p1::p2::ps)
    let idHead = pipe2 identifier (many atomicPattern) <| fun n ps -> LetHeader(n, ps)
    opHead <|> idHead

let expression, _expression = createParserForwardedToRef()

_expression := (
//        begin expr end -- block expression
//        expr(expr) -- high precedence application
//        expr<types> -- type application expression
//        expr infix-op expr -- infix application expression
//        prefix-op expr -- prefix application expression
//        expr.[expr] -- indexed lookup expression
//        expr.[slice-ranges] -- slice expression
//        expr <- expr -- assignment expression
//        expr , ... , expr -- tuple expression
//        new type expr -- simple object expression
//        { new base-call object-members interface-impls } -- object expression
//        { field-initializers } -- record expression
//        { expr with field-initializers } -- record cloning expression
//        [ expr ; ... ; expr ] -- list expression
//        [| expr ; ... ; expr |] -- array expression
//        expr { comp-or-range-expr } -- computation expression
//        [ comp-or-range-expr] -- computed list expression
//        [| comp-or-range-expr |] -- computed array expression
//        lazy expr -- delayed expression
//        null -- the "null" value for a reference type
//        expr : type -- type annotation
//        expr :> type -- static upcast coercion
//        expr :? type -- dynamic type test
//        expr :?> type -- dynamic downcast coercion
//        upcast expr -- static upcast expression
//        downcast expr -- dynamic downcast expression
//        let value-defn in expr –- value definition expression
//        let rec function-or-value-defns in expr -- recursive definition expression
//        use ident = expr in expr –- deterministic disposal expression
//        fun argument-pats -> expr -- function expression
//        function rules -- matching function expression
//        match expr with rules -- match expression
//        try expr with rules -- try/with expression
//        try expr finally expr -- try/finally expression
//        if expr then expr elif-branchesopt else-branchopt -- conditional expression
//        while expr do expr done -- while loop
//        for ident = expr to expr do expr done -- simple for loop
//        for pat in expr-or-range-expr do expr done -- enumerable for loop
//        assert expr -- assert expression
//        <@ expr @> -- quoted expression
//        <@@ expr @@> -- quoted expression
//        %expr -- expression splice
//        %%expr -- weakly typed expression splice
//        (static-typars : (member-sig) expr) -– static member invocation
    let primitiveExpression =
        choice [
            constant |>> ConstantExpression // -- a constant value
            pipe3 S.``(`` expression S.``)`` <| fun a b c -> BlockExpression(a, b, c)
            longIdentifierOrOperator |>> LookupExpression
        ]

    let p = primitiveExpression
    let p = pipe2 p (many (S.``.`` .>>. identifier)) <| fun e ns -> // -- dot lookup expression
        match ns with 
        | [] -> e 
        | _ -> List.fold (fun e (d, n) -> DotLookupExpression(e, d, n)) e ns

    let p = sepBy1 p Layout.applicationSeparator |>> function e, [] -> e | e1, e2::es -> ApplicationsExpression(RawApply, e1, e2, es)
    
    let p =
        let pipe a b c d e = LetExpression(a, b, c, d, e)
        let letExpression = pipe5(letHeader, S.``d=``, primitiveExpression, lineSeparator, p, pipe) // –- function definition expression
        letExpression <|> p

    let p = chainL1 p lineSeparator <| fun l op r -> SequentialExpression(l, op, r) // -- sequential execution expression
    p
)

let moduleFunctionOrValueDefinition =
    choice [
        pipe3 letHeader S.``d=`` (block expression (fun a b c -> a, b, c)) <| fun a b (c,d,e) -> ModuleLetElement(a, b, c, d, e)
//        doExpression
    ]

let typar = (S.``_`` |>> TypeArgumentHole) <|> (identifier |>> TypeArgument)
let typarDefinition = (* attributesopt *) typar
let typeName =
    let idTypeName = pipe2 (* attributes opt access opt *) identifier (many typarDefinition) <| fun a b -> TypeName(a, b)
    let opTypeName = pipe3 typarDefinition operator (many1 typarDefinition) <| fun l op (r, rs) -> TypeName(Name op, l::r::rs)
    idTypeName <|> opTypeName

let type', _type' = createParserForwardedToRef()
_type' := (    
    let primitiveType = 
        choice [
            pipe3 S.``(`` type' S.``)`` <| fun a b c -> ParenthesizedType(a, b, c)
            pipe3 S.``[`` type' S.``]`` <| fun a b c -> ListType(a, b, c)
            longIdentifier |>> fun x -> NamedType(x, [])

            // typar -- variable type
            // type[ , ... , ] -- array type
            // type typar-defns -- type with constraints
            // typar :> type -- variable type with subtype constraint
            // #type -- anonymous type with subtype constraint
        ]

    let p = primitiveType
    let p = pipe2 longIdentifier (many1 p) (fun a (x, xs) -> NamedType(a, x::xs)) <|> p
    let p = chainL1 p S.``->`` <| fun l op r -> FunctionType(l, op, r)
    let p = pipe2 p (many (S.``,`` .>>. p)) <| fun a -> function [] -> a | (b, c)::xs -> TupleType(a, b, c, xs)
    p
)

let abbreviationTypeDefinition = pipe3 typeName S.``d=`` type' <| fun a b c -> AbbreviationTypeDefinition(a, b, c)
let emptyTypeDefinition = typeName |>> EmptyTypeDefinition
let typeDefinition =
    choice [
        abbreviationTypeDefinition
//        record-type-defn
//        union-type-defn
//        anon-type-defn
//        class-type-defn
//        struct-type-defn
//        interface-type-defn
//        enum-type-defn
//        delegate-type-defn
//        type-extension
        emptyTypeDefinition
    ]

let typeDefinitions = pipe2 S.``type`` typeDefinition <| fun a b -> ModuleTypeDefinition(a, b)

let moduleElement, _moduleElement = createParserForwardedToRef()
let moduleElements = separateBy1 moduleElement lineSeparator
let moduleDefinitionBody = block (opt moduleElements) <| fun a b c -> a, b, c
let moduleDefinition = pipe4 (* attributes opt *) S.``module`` (* access opt *) identifier S.``d=`` moduleDefinitionBody <| fun a b c (d,e,f) -> ModuleDefinition(a, b, c, d, e, f)

_moduleElement :=
    choice [
        moduleFunctionOrValueDefinition
        typeDefinitions
        moduleDefinition
        // module-abbrev -- module abbreviations
        // import-decl -- import declarations
        // compiler-directive-decl
    ]

let anonymousModule = moduleElements |>> AnonymousModule
let module' = pipe3 S.``module`` longIdentifier moduleElements <| fun a b c -> NamedModule(a, b, c)

let implementationFile =
    choice [
//        many namespaceDeclGroup
        module'
        anonymousModule
    ]

let (Parser start) = opt (Layout.fileStart >>. implementationFile) .>> eof