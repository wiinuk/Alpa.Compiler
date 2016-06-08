namespace Alpa.Emit

open System
open System.Collections.Generic
open System.Reflection.Emit

module List =
    let tryIter2 action ls rs =
        let rec aux ls rs =
            match ls, rs with
            | l::ls, r::rs -> action l r; aux ls rs
            | [], [] -> true
            | _ -> false
        aux ls rs

type FullName = FullName of name: string * nestersRev: string list * namespaceRev: string list * assemblyName: string option

type TypeVar = string
and TypeSpec =
    /// ex: [mscorlib]System.Tuple(..., ...)
    | TypeSpec of pathRev: FullName * TypeSpec list
    /// ex: !T1
    | TypeVar of TypeVar
    /// ex: !!T1
    | MethodTypeVar of TypeVar
    /// ex: !0
    | TypeArgRef of int
    /// ex: !!0
    | MethodTypeArgRef of int

type MethodName = string
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
    | OpMethod of thisType: TypeSpec * name: MethodName * typeArgs: TypeSpec list * argTypes: TypeSpec list

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

type TypeDef = {
    kind: TypeKind option
    typeParams: TypeVar list
    inherits: TypeSpec list
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
    | TopAliasDef of name: string * typeParams: string list * entity: TypeSpec
    | TopTypeDef of pathRev: (string * string list) * TypeDef
    | TopModuleDef of pathRev: (string * string list) * ModuleDef

type AssemblyDef = string
type IL = { topDefs: TopDef list }

[<Sealed; AllowNullLiteral>]
type HashMap<'k,'v when 'k : equality>() = inherit Dictionary<'k,'v>()

/// typeParams.Length = typeParamBuilders.Length
type TypeVarMap = TypeVarMap of typeParams: TypeVar list * typeParamBuilders: GenericTypeParameterBuilder list
type MethodSign = MethodName
type FieldSign = string

type ILTypeBuilder = {
    d: Choice<TypeDef, ModuleDef>
    t: TypeBuilder

    path: FullName
    
    map: TypeMap
    mutable varMap: TypeVarMap

    mutable cctor: ILCtorBuilder option
    mmap: MethodMap
    cmap: CtorMap
    fmap: FieldMap
}

and ILMethodBuilder = {
    /// DeclaringType
    dt: ILTypeBuilder
    mb: MethodBuilder
    mVarMap: TypeVarMap
    m: MethodInfo
}
and ILCtorBuilder = {
    /// DeclaringType
    dt: ILTypeBuilder
    cb: ConstructorBuilder
    pars: Parameter list
    body: MethodBody
}
and MethodMap = HashMap<MethodSign, ILMethodBuilder list>
and FieldMap = HashMap<FieldSign, FieldBuilder>
and TypeMap = HashMap<FullName, ILTypeBuilder>
and CtorMap = ResizeArray<ILCtorBuilder>

type SolvedTypeParam =
    | RuntimeTypeParam of Type
    | TypeParamBuilder of GenericTypeParameterBuilder

type SolvedType =
    | RuntimeType of Type
    | Builder of ILTypeBuilder
    | InstantiationType of closeType: Type * openType: ILTypeBuilder option
    | TypeParam of TypeVar * SolvedTypeParam

type SolveEnv = {
    tmap: TypeMap
    varMap: (TypeVar * SolvedTypeParam) list
    mVarMap: (TypeVar * SolvedTypeParam) list
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