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

type MethodRef = 
    | MethodRef of 
        thisType: TypeSpec *
        name: MethodName *
        anntation: MethodTypeAnnotation option

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
    | OpMethod of MethodRef

type Macro =
    | BaseInit of TypeSpec list

type Instr = 
    | Instr of string * OpCode * Operand

type Override = Override of baseMethods: MethodRef list

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

type TypeAccess =
    | Public

    /// C# internal
    | Private

type NestedAccess =
    | Public

    /// C# internal
    | Private
    | Family
    | Assembly
    | FamilyAndAssembly
    | FamilyOrAssembly

type MemberAccess =
    | Public
    /// C# private
    | Private
    /// C# protected
    | Family
    
    /// C# internal
    | Assembly
    | FamilyAndAssembly
    | FamilyOrAssembly

    | PrivateScope

type TypeKind = | Interface | Abstract | Open | Sealed | Static
type MethodKind = | Open

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
and MemberDef =
    | Literal of MemberAccess option * name: string * TypeSpec * Literal
    | Field of MemberAccess option * isStatic: bool * isMutable: bool * name: string * TypeSpec
    | AbstractDef of MemberAccess option * MethodHead
    | CtorDef of MemberAccess option * pars: Parameter list * MethodBody
    | CCtorDef of MethodBody
    | MethodDef of MemberAccess option * Override option * MethodKind option * MethodInfo
    | StaticMethodDef of MemberAccess option * MethodInfo
    | NestedType of NestedAccess option * name: string * TypeDef

type TopDef =
    | TopAliasDef of name: AliasSign * AliasDef
    | TopTypeDef of TypeAccess option * pathRev: (string * string list) * TypeDef

type AssemblyDef = AssemblyDef of string

type Version = Version2 of int * int | Version3 of int * int * int | Version4 of int * int * int * int
type AssemblyRef = AssemblyRef of name: string * publicKeyToken: byte list option * version: Version option
type IL = {
    assembly: AssemblyDef
    imports: AssemblyRef list
    moduleDef: string option
    topDefs: TopDef list
}

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

    d: TypeDef
    t: TypeBuilder
    path: FullName
    mutable varMap: TypeVarMap

    mmap: MethodMap
    fmap: FieldMap
}

and ILMethodBuilder = {
    /// DeclaringType
    dt: ILTypeBuilder
    ov: Override option
    mb: Choice<MethodBuilder,ConstructorBuilder>
    mVarMap: TypeVarMap
    h: MethodHead
    b: MethodBody option
}
and AliasMap = HashMap<AliasSign, AliasDef>
and MethodMap = HashMap<MethodSign, ILMethodBuilder list>
and FieldMap = HashMap<FieldSign, FieldBuilder>
and TypeMap = HashMap<FullName, ILTypeBuilder>

type SolvedType =
    | RuntimeType of Type
    | Builder of ILTypeBuilder
    | InstantiationType of closeType: Type * openType: ILTypeBuilder option * typeParams: SolvedType list
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
    | DuplicatedAliasName of AliasSign * AliasDef * TypeDef
    | RecursiveAlias of AliasSign
    | AliasKindError of AliasSign * appliedTypes: TypeSpec list * target: AliasDef

    | ConstructorIsNotOverride of MethodRef

exception EmitException of EmitErrors
