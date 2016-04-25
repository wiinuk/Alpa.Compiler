module Alpa.Parser
#load "./Alpa.ParserCombinator.fsx"

open Alpa.IO
open Alpa.Token
open Alpa.ParserCombinator

    
type State = Position
let initialState = Position(0<_>, 1<_>, 1<_>)

type Error =
    | ErrorNone
    | RequireR of Special
    | RequireIdentifer
    | RequireOperator
    | RequireIntegerLiteral
    | RequireFloatLiteral
    | RequireCharLiteral
    | RequireStringLiteral
    | RequireLineSeparator of Position

type Parser<'a> = Parser<Token, State, Error, 'a>
let (|Parser|) (p: Parser<_>) = p

let rParser s = satisfyE (isR s) (RequireR s)
module Delimiters =
    let ``d=`` = rParser Special.``O=``
    let ``(`` = rParser Special.``D(``
    let ``)`` = rParser Special.``D)``
    let ``.`` = rParser Special.``O.``
    let ``;`` = rParser Special.``D;``

module Keywords =
    let ``_`` = rParser Special.I_
//    let ``let`` = RParser Special.Let
//    let ``in`` = RParser Special.In

module D = Delimiters
module K = Keywords

let identifier = satisfyE isId RequireIdentifer
let operator = satisfyE isOp RequireOperator

let path0 = many (identifier .>> D.``.``)

let longIdentifier = pipe2 path0 identifier <| fun xs x -> LongIdentifier(xs, x)
let longIdentifierOrOperator = pipe2 path0 (identifier <|> operator) <| fun xs x -> LongIdentifier(xs, x)

let constInt = satisfyE isI RequireIntegerLiteral
let constFloat = satisfyE isF RequireFloatLiteral
let constChar = satisfyE isC RequireCharLiteral
let constString = satisfyE isS RequireStringLiteral
let const' =
    choice [
        constInt
        constFloat
        constChar
        constString
    ]

let pattern, _pattern = createParserForwardedToRef()

let atomicPattern =
    choice [
//        ``const``
        longIdentifier |>> LongIdentifierPattern
//        listPattern
//        recordPattern
//        arrayPattern
        between D.``(`` D.``)`` pattern
//        D.``:?`` atomicType
//        K.``null``
        K.``_`` >>% WildcardPattern
    ]

_pattern :=
    choice [
//        const -- constant pattern
        longIdentifier |>> LongIdentifierPattern // pat-paramopt patopt -- named pattern
        K.``_`` >>% WildcardPattern
//        pat as ident -- "as" pattern
//        pat '|' pat -- disjunctive pattern
//        pat '&' pat -- conjunctive pattern
//        pat :: pat -- "cons" pattern
//        pat : type -- pattern with type constraint
//        pat,...,pat -- tuple pattern
        between D.``(`` D.``)`` pattern
//        list-pat -- list pattern
//        array-pat -- array pattern
//        record-pat -- record pattern
//        :? atomic-type -- dynamic type test pattern
//        :? atomic-type as ident -- dynamic type test pattern
//        null -- null-test pattern
//        attributes pat -- pattern with attributes
    ]

let letHeader =
    let opHead = pipe4 atomicPattern operator atomicPattern (many atomicPattern) <| fun p1 n p2 ps -> LetHeader(n, p1::p2::ps)
    let idHead = pipe2 identifier (many atomicPattern) <| fun n ps -> LetHeader(n, ps)
    opHead <|> idHead

let expression, _expression = createParserForwardedToRef()
let letDefinition = letHeader .>> D.``d=`` .>>. expression

_expression :=
    choice [
        const' |>> ConstExpression // -- a constant value
        between D.``(`` D.``)`` expression |>> BlockExpression // -- block expression
//        begin expr end -- block expression
        longIdentifierOrOperator |>> LookupExpression // -- lookup expression
        pipe3 expression D.``.`` longIdentifierOrOperator <| fun e _ n -> DotLookupExpression(e, n) // -- dot lookup expression
        pipe3 expression expression (many expression) <| fun e1 e2 es -> ApplicationsExpression(e1, e2, es)
//        expr expr -- application expression

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
        pipe3 letDefinition D.``;`` expression <| fun (h, v) _ e -> LetExpression(h, v, e) // –- function definition expression
//        let value-defn in expr –- value definition expression
//        let rec function-or-value-defns in expr -- recursive definition expression
//        use ident = expr in expr –- deterministic disposal expression
//        fun argument-pats -> expr -- function expression
//        function rules -- matching function expression
        pipe3 expression D.``;`` expression <| fun l _ r -> SequentialExpression(l, r) // -- sequential execution expression
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
]

let moduleFunctionOrValueDefinition =
    choice [
        letDefinition
//        doExpression
    ]

let moduleElement =
    choice [
        moduleFunctionOrValueDefinition
        // typeDefinitions -- type definitions
        // moduleDefinition -- module definitions
        // module-abbrev -- module abbreviations
        // import-decl -- import declarations
        // compiler-directive-decl
    ]

let lineSeparator =
    let p xs =
        let p: Position = xs.UserState
        if xs.Items.size <= xs.Index then Reply((), RequireLineSeparator p)
        else
            let x: Token = xs.Items.items.[xs.Index]
            if not (p.Line < x.Start.Line && p.Column = x.Start.Column) then Reply((), RequireLineSeparator p)
            else
                xs.UserState <- x.Start
                Reply(())
    p

let moduleElements = sepBy1 moduleElement lineSeparator
let anonymousModule = moduleElements

let implementationFile =
    choice [
//        many namespaceDeclGroup
//        namedModule
        anonymousModule
    ]

let (Parser start) = opt implementationFile .>> eof