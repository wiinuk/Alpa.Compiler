﻿namespace Alpa
#r "./bin/debug/Alpa.Compiler.dll"

type Identifier = Token
type LongIdentifier = LongIdentifier of Identifier list * Identifier

type Pattern =
    | WildcardPattern of ``_``: Token
    | ParenthesizedPattern of ``(``: Token * Pattern * ``)``: Token
    | LongIdentifierPattern of LongIdentifier

type LetHeader = LetHeader of Identifier * Pattern list
type Constant =
    | UnitConstant of ``(``: Token * ``)``: Token
    | Constant of Token

type Expression =
    | ConstantExpression of Constant
    | LookupExpression of LongIdentifier
    | DotLookupExpression of Expression * ``.``: Token * LongIdentifier
    | ApplicationsExpression of Expression * Expression * Expression list
    | BlockExpression of ``(``: Token * Expression * ``)``: Token
    | SequentialExpression of Expression * ``;``: Token * Expression
    | LetExpression of LetHeader * ``=``: Token * Expression * ``;``: Token * Expression


type Type = 
    | ParenthesizedType of ``(``: Token * Type * ``)``: Token
    | FunctionType of Type * ``->``: Token * Type
    | TupleType of Type * ``,``: Token * Type * ``(, Type)*``: (Token * Type) list
    | ListType of ``[``: Token * Type * ``]``: Token
    | NamedType of LongIdentifier * typeArguments: Type list
    
type TypeArgument = TypeArgument of _OrIdentifier: Token
type TypeName = TypeName of identifier: Token * TypeArgument list

type TypeDefinition =
    | AbbreviationTypeDefinition of TypeName * ``=``: Token * Type

type ModuleElement = 
    | ModuleDefinition of ``module``: Token * Identifier * ``=``: Token * blockBegin: Token * option<ModuleElements> * blockEnd: Token
    | ModuleLetElement of LetHeader * ``=``: Token * blockBegin: Token * Expression * blockEnd: Token
    | ModuleTypeDefinition of ``type``: Token * TypeDefinition

and ModuleElements = ModuleElement * list<Token * ModuleElement>

type ImplementationFile =
    | NamedModule of ``module``: Token * LongIdentifier * ModuleElements
    | AnonymousModule of ModuleElements

