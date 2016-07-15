namespace Alpa.Emit

open System
open System.Collections.Generic
open System.Reflection.Emit

type FullName = FullName of name: string * nestersRev: string list * namespaceRev: string list * assemblyName: string option

type TypeVar = string
and TypeSpec =
    /// ex: T*
    | Pointer of TypeSpec
    /// ex: T&
    | Byref of TypeSpec
    /// ex: T[]
    | Array of TypeSpec

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
        annotation: MethodTypeAnnotation option

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

type Instr = 
    | Instr of string * OpCode * Operand

type ILLit =
    | LitB of bool
    | LitI1 of int8
    | LitI2 of int16
    | LitI4 of int32
    | LitI8 of int64
    | LitU1 of uint8
    | LitU2 of uint16
    | LitU4 of uint32
    | LitU8 of uint64
    | LitC of char
    | LitF4 of single
    | LitF8 of double
    /// ex: null; "abc"
    | LitS of string
    | LitNull of TypeSpec

type ILExp =
    /// ex: 10i; 'c'; "test"; null[string]
    | Lit of ILLit
    /// ex: a
    | NVar of string
    /// ex: $0
    | AVar of int
    /// ex: a: string in x
    | LetZero of string * TypeSpec * ILExp
    /// ex: a <- "" in x
    | Let of string * ILExp * ILExp
    /// ex: a; b
    | Next of ILExp * ILExp

    /// ex: 'a'.[object::ToString]()
    | VCall of ILExp * MethodRef * ILExp list
    /// ex: object::ReferenceEquals(x, y);
    ///     string::Equals(string, string)(a, b);
    ///     "".Equals(string)(null)
    | ICall of Choice<ILExp, TypeSpec> * Choice<string, MethodRef> * ILExp list

    /// ex: x.Value; String.Empty
    | FieldAccess of Choice<ILExp, TypeSpec> * fieldName: string

    /// ex: &e
    | NVarRef of string
    /// ex: &$0
    | AVarRef of int
    /// ex: x.&F; T.&F
    | FieldRef of Choice<ILExp, TypeSpec> * fieldName: string
    /// ex: x.&[n]
    | ArrayElemRef of ILExp * index: ILExp

    /// ex: upcast "" IEquatable`1(string)
    | Upcast of ILExp * TypeSpec

    /// ex: [1; 2; 3]
    | NewArray of ILExp * ILExp list
    /// ex: xs.[i]
    | ArrayIndex of ILExp * ILExp
    /// ex: []: int array
    | NewEmptyArray of TypeSpec

    /// ex: *r
    | RefRead of ILExp
    /// ex: r *<- 10; 0
    | MRefWrite of ref: ILExp * value: ILExp * cont: ILExp

    /// ex: initobj &a: 10;
    | Initobj of ILExp * ILExp
    /// ex: newobj string('a', 10i)
    | Newobj of Choice<TypeSpec, MethodRef> * ILExp list


type Local = Local of isPinned: bool * TypeSpec
type Locals = Locals of initLocals: bool * locals: Local list
type MethodBody = MethodBody of Locals option * Instr list | MethodExpr of ILExp
type Parameter = Parameter of name: string option * TypeSpec
type MethodHead = MethodHead of name: MethodName * typeParams: TypeVar list * pars: Parameter list * ret: Parameter
type MethodInfo = MethodInfo of MethodHead * MethodBody
type Override = Override of baseMethods: MethodRef list
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
type AssemblyRef = 
    {
        name: string
        version: Version option
        culture: string option
        publicKeyToken: byte array option
    }
type AssemblyImport = AssemblyImport of AssemblyRef * string option
type IL = {
    assembly: AssemblyDef
    imports: AssemblyImport list
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
    imap: HashMap<string, AssemblyRef>
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
    mb: Choice<MethodBuilder, ConstructorBuilder>
    mVarMap: TypeVarMap
    h: MethodHead
    b: MethodBody option
}
and AliasMap = HashMap<AliasSign, AliasDef>
and MethodMap = HashMap<MethodSign, ILMethodBuilder list>
and FieldMap = HashMap<FieldSign, FieldBuilder>
and TypeMap = HashMap<FullName, ILTypeBuilder>

type SolvedType =
    | PointerType of element: SolvedType
    | ByrefType of element: SolvedType
    | ArrayType of element: SolvedType

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

    | DuplicatedAssemblyAlias of string

exception EmitException of EmitErrors
