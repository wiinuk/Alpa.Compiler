namespace Alpa.Emit

open System
open System.Collections.Generic
open System.Reflection.Emit

type FullName = FullName of name: string * nestersRev: string list * namespaceRev: string list * assemblyName: string option

type TypeVar = string
and TypeSpec =
    /// ex: [mscorlib]System.Tuple(..., ...)
    | TypeSpec of pathRev: FullName * TypeSpec list
    /// ex: `T1
    | TypeVar of TypeVar
    /// ex: ``T1
    | MethodTypeVar of TypeVar
    /// ex: `0
    | TypeArgRef of int
    /// ex: ``0
    | MethodTypeArgRef of int

type MethodName = string
type MethodTypeAnnotation =
    | MethodTypeAnnotation of typeArgs: TypeSpec list * argTypes: TypeSpec list * returnType: TypeSpec option
type Operand =
    | OpNone
    | OpI1 of int8
    | OpI2 of int16
    | OpI4 of int
    | OpI8 of int64
    | OpF4 of single
    | OpF8 of double
    | OpString of string
    | OpType of TypeSpec
    | OpField of thisType: TypeSpec * name: string
    | OpCtor of thisType: TypeSpec * argTypes: TypeSpec list
    | OpMethod of thisType: TypeSpec * name: MethodName * MethodTypeAnnotation option

type Macro =
    | BaseInit of TypeSpec list

type Instr = 
    | Instr of string * OpCode * Operand

type Override =
    | Override
    | BaseMethod of baseMethod: (TypeSpec * MethodName)

type Parameter = Parameter of name: string option * TypeSpec
type MethodBody = MethodBody of Instr list
type MethodHead = MethodHead of name: MethodName * typeParams: TypeVar list * pars: Parameter list * ret: Parameter
type MethodInfo = MethodInfo of MethodHead * MethodBody
type StaticMethodInfo = MethodInfo

type Literal =
    | Bool of bool
    | I1 of int8
    | U1 of uint8
    | I2 of int16
    | U2 of uint16
    | I4 of int32
    | U4 of uint32
    | I8 of int64
    | U8 of uint64
    | F4 of single
    | F8 of double
    | Char of char
    | String of string
    | Null

type MemberDef =
    | Literal of name: string * TypeSpec * Literal
    | Field of isStatic: bool * isMutable: bool * name: string * TypeSpec
    | AbstractDef of MethodHead
    | CtorDef of pars: Parameter list * MethodBody
    | CCtorDef of MethodBody
    | MethodDef of Override option * MethodInfo
    | StaticMethodDef of StaticMethodInfo

type TypeKind = Abstract | Interface | Open | Sealed

type AliasSign = string
type AliasDef = {
    aTypeParams: TypeVar list
    entity: TypeSpec
}
type TypeDef = {
    kind: TypeKind option
    typeParams: TypeVar list
    parent: TypeSpec option
    impls: TypeSpec list
    members: MemberDef list
}
type ModuleDef = {
    mMembers: ModuleMember list
}
and ModuleMember =
    | ModuleMethodDef of StaticMethodInfo
    | ModuleTypeDef of name: string * TypeDef
    | ModuleCCtorDef of MethodBody
    | ModuleModuleDef of name: string * ModuleDef
    | ModuleValDef of isMutable: bool * name: string * TypeSpec
    | ModuleLiteralDef of name: string * TypeSpec * Literal

type TopDef =
    | TopAliasDef of name: AliasSign * AliasDef
    | TopTypeDef of pathRev: (string * string list) * TypeDef
    | TopModuleDef of pathRev: (string * string list) * ModuleDef

type AssemblyDef = string
type IL = { topDefs: TopDef list }

[<Sealed; AllowNullLiteral>]
type HashMap<'k,'v when 'k : equality> =
    inherit Dictionary<'k,'v>
    new () = {}
    new (elements) as x =
        { inherit Dictionary<_,_>() }
        then
            for k, v in elements do x.Add(k, v)

/// typeParams.Length = typeParamBuilders.Length
type TypeVarMap = (TypeVar * GenericTypeParameterBuilder) list
type MethodSign = MethodName
type FieldSign = string

type Env = {
    amap: AliasMap
    map: TypeMap
}
and ILTypeBuilder = {
    env: Env

    d: Choice<TypeDef, ModuleDef>
    t: TypeBuilder
    path: FullName
    mutable varMap: TypeVarMap

    mutable cctor: ILMethodBuilder option

    mmap: MethodMap
    cmap: CtorMap
    fmap: FieldMap
}

and ILMethodBuilder = {
    /// DeclaringType
    dt: ILTypeBuilder
    mb: Choice<MethodBuilder,ConstructorBuilder>
    mVarMap: TypeVarMap
    m: MethodInfo
}
and AliasMap = HashMap<AliasSign, AliasDef>
and MethodMap = HashMap<MethodSign, ILMethodBuilder list>
and FieldMap = HashMap<FieldSign, FieldBuilder>
and TypeMap = HashMap<FullName, ILTypeBuilder>
and CtorMap = ResizeArray<ILMethodBuilder>

type SolvedType =
    | RuntimeType of Type
    | Builder of ILTypeBuilder
    | InstantiationType of closeType: Type * openType: ILTypeBuilder option
    | TypeParam of TypeVar * GenericTypeParameterBuilder

type SolveEnv = {
    senv: Env
    sVarMap: TypeVarMap
    sMVarMap: TypeVarMap
    typeArgs: SolvedType list
    mTypeArgs: SolvedType list
}
type IsMethodBase<'m> = {
    getMTypeParams: 'm -> SolvedType list
    getParameters: 'm -> SolvedType list
}
type IsMethodInfo<'m,'i,'b> = {
    baseClass: IsMethodBase<'b>
    toBase: 'm -> 'b
    getSystemMethod: 'm -> 'i
}
type IsType<'t,'m,'c> = {
    getMethodsOfName: string -> 't -> 'm seq
    getCtors: 't -> 'c seq
    getTypeParams: 't -> SolvedType list
}

type EmitErrors =
    | DuplicatedAliasTypeParameter of TypeVar
    | UnownedAliasTypeParameter of TypeVar
    | UnownedAliasTypeParameterRef of int
    | UnsolvedType of TypeSpec
    | DuplicatedAliasName of AliasSign * AliasDef * Choice<TypeDef,ModuleDef>
    | RecursiveAlias of AliasSign
    | AliasKindError of AliasSign * appliedTypes: TypeSpec list * target: AliasDef

exception EmitException of EmitErrors
