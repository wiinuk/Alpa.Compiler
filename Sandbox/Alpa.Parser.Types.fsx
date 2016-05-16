namespace Alpa
#r "./bin/debug/Alpa.Compiler.dll"

type PathRev = list<Symbol>

type TypeRef =
    | TypeRef of fullPath: PathRev * typeArgs: list<TypeRef>
    | TypeVar of ref<option<TypeRef>>

type Fixity =
    | Prefix
    | Infix
    | Postfix

type Associativity =
    | NonAssoc
    | Left
    | Right

type Identifier = 
    | Name of idOrOp: Token
    | ParenthesizedIdentifier of ``(``: Token * op: Token * ``)``: Token

type LongIdentifier = LongIdentifier of (Identifier * Token) list * Identifier
type FixityDeclaration = FixityDeclaration of fixityKeyword: Token * precedenceInteger: Token

type Type = 
    | UnitType of ``(``: Token * ``)``: Token
    | ParenthesizedType of ``(``: Token * Type * ``)``: Token
    | FunctionType of Type * ``->``: Token * Type
    | TupleType of Type * ``,``: Token * Type * ``(, Type)*``: (Token * Type) list
    | ListType of ``[``: Token * Type * ``]``: Token
    | NamedType of LongIdentifier * typeArguments: Type list

type Pattern =
    | WildcardPattern of ``_``: Token
    | ParenthesizedPattern of ``(``: Token * Pattern * ``)``: Token
    | LongIdentifierPattern of LongIdentifier

type LetHeader = LetHeader of fixity: option<FixityDeclaration> * Identifier * Pattern list

type Constant =
    | UnitConstant of ``(``: Token * ``)``: Token
    | Constant of Token

type ApplicationKind = RawApply | PrefixApply | InfixLeftApply | InfixNoneApply | InfixRightApply | PostfixApply | IdentifierApply
type Expression =
    | ConstantExpression of Constant

    // reduce to (LookupExpression and DotLookupExpression)
    | LookupExpression of LongIdentifier

    | DotLookupExpression of Expression * ``.``: Token * Identifier

    | ApplicationsExpression of ApplicationKind * Expression * Expression * Expression list

    | BlockExpression of ``(``: Token * Expression * ``)``: Token
    | SequentialExpression of Expression * ``;``: Token * Expression
    | LetExpression of header: LetHeader * TypeRef * ``=``: Token * Expression * ``;``: Token * Expression

type TypeArgument = 
    | TypeArgumentHole of ``_``: Token
    | TypeArgument of identifier: Identifier

type TypeName = TypeName of Identifier * TypeArgument list

type TypeDefinition =
    | AbbreviationTypeDefinition of TypeName * ``=``: Token * Type
    | EmptyTypeDefinition of TypeName

type ModuleElement =
    | ModuleDefinition of ``module``: Token * Identifier * ``=``: Token * blockBegin: Token * option<ModuleElements<ModuleElement>> * blockEnd: Token
    | ModuleLetElement of LetHeader * TypeRef * ``=``: Token * blockBegin: Token * Expression * blockEnd: Token
    | ModuleTypeDefinition of ``type``: Token * TypeDefinition

and ModuleElements<'M> = 'M * list<Token * 'M>

type ImplementationFile<'M> =
    | NamedModule of ``module``: Token * LongIdentifier * ModuleElements<'M>
    | AnonymousModule of ModuleElements<'M>