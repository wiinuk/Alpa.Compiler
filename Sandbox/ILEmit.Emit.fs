module ILEmit.Emit

// (1) type name definition
// type IOrd`1 ... = ...;;
// type IMap`2 ... = ...;;
// type IntMap`1 ... = ...;;
// module Module =
//     type X = ...;
//     ...;;
//
// (2) type param definition
// type IOrd`1 a = ...;;
// type IMap`2(k <: IOrd, v) = ...;;
// type IntMap`1 v = ...;;
// module Module =
//     type X = ...;
//     ...;;
//
// (3) member definition
// type IOrd`1 a =
//     abstract CompareTo a : int;;
// type IMap`2(k <: IOrd, v) =
//     abstract Add(k, v) : void;;
// type IntMap`1 v <: object, IMap(int32, v) =
//     override Add(int32, v) : void = ...;;
// module Module =
//     type X = fun Member (a <: IOrd b, b) (a) : void = ...;
//     fun main () : void = ...;;
//
// (4) emit method body
// type IOrd`1 a =
//     abstract CompareTo a : int;;
// type IMap`2(k <: IOrd, v) =
//     abstract Add(k, v) : void;;
// type IntMap`1 v <: object, IMap(int32, v) =
//     override Add(int32, v) : void = ret;;
// module Module =
//     type X = fun Member (a <: IOrd b, b) (a) : void = ret;
//     fun main () : void = ret;;

open System
open System.Collections.Generic
open System.Reflection.Emit

type B = System.Reflection.BindingFlags
type CC = System.Reflection.CallingConventions
type T = System.Reflection.TypeAttributes
type M = System.Reflection.MethodAttributes
type P = System.Reflection.ParameterAttributes
type F = System.Reflection.FieldAttributes
type O = System.Reflection.Emit.OpCodes

let init() = Array.zeroCreate 4
let asArray items size =
    if Array.length items = size then items
    else Array.sub items 0 size
    
let extend items size =
    let ys = Array.zeroCreate(min 2146435071 (Array.length items * 2))
    Array.Copy(items, 0, ys, 0, size)
    ys

let put items size x =
    let items = if Array.length items = size then extend items size else items
    items.[size] <- x
    items

module List =
    let mapToArray map xs =
        let rec aux items size = function
            | [] -> asArray items size
            | x::xs -> aux (put items size (map x)) (size + 1) xs

        aux (init()) 0 xs

module Array =
    let filterMap pred map xs =
        let rec aux items size i =
            if Array.length xs <= i then asArray items size
            else
                let x = xs.[i]
                if pred x then aux (put items size (map x)) (size + 1) (i + 1)
                else aux items size (i + 1)

        aux (init()) 0 0
        

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
    | MethodDef of Override option * MethodInfo
    | StaticMethodDef of StaticMethodInfo

type TypeKind = Abstract | Interface | Open | Sealed

type TypeDef = {
    kind: TypeKind option
    typeParams: TypeVar list
    parent: TypeSpec option
    /// Implement Interfaces
    impls: TypeSpec list
    members: MemberDef list
}
type ModuleMember =
    | ModuleMethodDef of StaticMethodInfo
    | ModuleTypeDef of name: string * TypeDef
    | ModuleModuleDef of name: string * ModuleMember list
    | ModuleValDef of isMutable: bool * name: string * TypeSpec
    | ModuleLiteralDef of name: string * TypeSpec * Literal

type TopDef =
    | TopTypeDef of pathRev: (string * string list) * TypeDef
    | TopModuleDef of pathRev: (string * string list) * ModuleMember list

type AssemblyDef = string
type IL = { topDefs: TopDef list }

type HashMap<'k,'v when 'k : equality> = Dictionary<'k,'v>
let add (map: HashMap<_,_>) k v = map.Add(k, v)
let assign (map: HashMap<_,_>) k v = map.[k] <- v
let get (map: HashMap<_,_>) k = map.[k]
let tryGet (map: HashMap<_,_>) k (v: _ byref) = map.TryGetValue(k, &v)
let values (map: HashMap<_,_>) = map.Values

type MethodSign = MethodName
type FieldSign = string
let emptyVarMap = []
let notimpl<'a> : 'a = raise <| System.NotImplementedException()

[<AbstractClass>]
type ILTypeSkeleton(t: Type) =
    inherit System.Type()

    // from virtual System.Type
    override __.IsGenericType = t.IsGenericType
    override __.GetGenericArguments() = t.GetGenericArguments()
    override __.GetGenericTypeDefinition() = t.GetGenericTypeDefinition()

    // from abstract System.Type
    override __.GetConstructors _ = notimpl
    //override __.GetConstructorImpl(_,_,_,_,_) = notimpl
    override __.GetMethods _ = notimpl
    //override __.GetMethodImpl(_,_,_,_,_,_) = notimpl
    override __.GetField(_,_) = notimpl
    override __.GetFields _ = notimpl
    override __.GetEvent(_,_) = notimpl
    override __.GetEvents _ = notimpl
    override __.GetInterface(_,_) = notimpl
    override __.GetInterfaces() = notimpl
    override __.GetPropertyImpl(_,_,_,_,_,_) = notimpl
    override __.GetProperties _ = notimpl
    override __.GetNestedTypes _ = notimpl
    override __.GetNestedType(_,_) = notimpl
    override __.GetMembers _ = notimpl
    override __.GetAttributeFlagsImpl() = if isNull t then notimpl else t.Attributes
    override __.IsArrayImpl() = if isNull t then notimpl else t.IsArray
    override __.IsByRefImpl() = if isNull t then notimpl else t.IsByRef
    override __.IsPointerImpl() = if isNull t then notimpl else t.IsPointer
    override __.IsPrimitiveImpl() = if isNull t then notimpl else t.IsPrimitive
    override __.IsCOMObjectImpl() = if isNull t then notimpl else t.IsCOMObject
    override __.GetElementType() = if isNull t then notimpl else t.GetElementType()
    override __.HasElementTypeImpl() = if isNull t then notimpl else t.HasElementType
    override __.UnderlyingSystemType = if isNull t then notimpl else t

    override __.GUID = if isNull t then notimpl else t.GUID
    override __.Assembly = if isNull t then notimpl else t.Assembly
    override __.Module = if isNull t then notimpl else t.Module
    override __.Namespace = if isNull t then notimpl else t.Namespace
    override __.FullName = if isNull t then notimpl else t.FullName
    override __.AssemblyQualifiedName = if isNull t then notimpl else t.AssemblyQualifiedName
    override __.BaseType = notimpl

    override __.InvokeMember(_,_,_,_,_,_,_,_) = notimpl

    // from System.Reflection.MemberInfo
    override __.GetCustomAttributes _ = notimpl
    override __.GetCustomAttributes(_,_) = notimpl
    override __.IsDefined(_,_) = notimpl
    override __.Name = if isNull t then notimpl else t.Name

    // from System.Object
    override l.Equals(r: obj) = obj.ReferenceEquals(l, r)
    override __.GetHashCode() = 0

[<Sealed>]
type ILTypeParameter(definition: TypeVar, builder: GenericTypeParameterBuilder) =
    inherit ILTypeSkeleton(builder)
    member val IL = definition
    member val Builder = builder
    override __.GetConstructorImpl(_,_,_,_,_) = notimpl
    override __.GetMethodImpl(_,_,_,_,_,_) = notimpl

type TypeVarMap = ILTypeParameter list

type SolveEnv = {
    tmap: TypeMap
    varMap: ILTypeParameter list
    mVarMap: ILTypeParameter list
    typeArgs: Type list
    mTypeArgs: Type list
}

and TypeMap = HashMap<FullName, ILType>

and [<Sealed>] ILType(definition: Choice<TypeDef, ModuleMember list>, builder: TypeBuilder, map: TypeMap) =
    inherit ILTypeSkeleton(builder)

    member __.IL = definition
    member __.Builder = builder
    member __.TypeMap = map
    member val VarMap = emptyVarMap with get, set
    member val MethodMap = HashMap<MethodSign, ILMethod list>()
    member val ConstructorMap = ResizeArray<ILConstructor>()
    member val FieldMap = HashMap<FieldSign, FieldBuilder>()

    override ti.MakeGenericType ts = upcast ILInstantiationType(builder.MakeGenericType ts, Some ti)
    override t.GetField(name, _) = upcast get t.FieldMap name
    override t.GetMethodImpl(name, bindingAttr, binder, _, types, modifiers) =
        let binder = match binder with null -> Type.DefaultBinder | b -> b
        downcast binder.SelectMethod(
            bindingAttr,
            List.mapToArray (fun m -> upcast m) (get t.MethodMap name),
            types,
            modifiers
        )

    override t.GetConstructorImpl(bindingAttr, binder, _, types, modifiers) =
        let binder = match binder with null -> Type.DefaultBinder | b -> b
        downcast binder.SelectMethod(
            bindingAttr,
            [| for m in t.ConstructorMap -> upcast m |],
            types,
            modifiers
        )
        
and [<Sealed>] ILInstantiationType(closeType: Type, openType: ILType option) =
    inherit ILTypeSkeleton(closeType)

    let openType' =
        match openType with 
        | None -> closeType.GetGenericTypeDefinition()
        | Some t -> upcast t
        
    member val OpenType = openType
    override __.GetField(name, b) = TypeBuilder.GetField(closeType, openType'.GetField(name, b))

    override __.GetMethodImpl(name, bindingAttr, binder, _, types, modifiers) =
        let binder = match binder with null -> Type.DefaultBinder | b -> b
        let openMethodsOfOpenType =
            match openType' with
            | :? ILType as t -> List.mapToArray (fun m -> m :> Reflection.MethodBase) <| get t.MethodMap name
            | _ -> openType'.GetMethods bindingAttr |> Array.filterMap (fun m -> m.Name = name) (fun m -> upcast m)

        TypeBuilder.GetMethod(
            closeType,
            downcast binder.SelectMethod(bindingAttr, openMethodsOfOpenType, types, modifiers)
        )

    override __.GetConstructorImpl(bindingAttr, binder, _, types, modifiers) =
        let binder = match binder with null -> Type.DefaultBinder | b -> b
        let methodsOfOpenType =
            match openType' with
            | :? ILType as t -> [|for m in t.ConstructorMap -> m :> Reflection.MethodBase|]
            | _ -> openType'.GetConstructors bindingAttr |> Array.map (fun m -> upcast m)

        TypeBuilder.GetConstructor(
            closeType,
            downcast binder.SelectMethod(bindingAttr, methodsOfOpenType, types, modifiers)
        )

and IILMethodBase =
    abstract MethodVarMap: TypeVarMap
    abstract Parameters: Parameter list

and [<Sealed>] ILMethod(definition: MethodInfo, declaringType: ILType, builder: MethodBuilder, methodTypeVars: TypeVarMap) =
    inherit System.Reflection.MethodInfo()
    member val IL = definition
    member val ILDeclaringType = declaringType
    member val Builder = builder
    member val MethodVarMap = methodTypeVars
    interface IILMethodBase with
        override __.MethodVarMap = methodTypeVars
        override __.Parameters = let (MethodInfo(MethodHead(pars=pars),_)) = definition in pars

    // from MethodInfo
    override __.ReturnTypeCustomAttributes = notimpl
    override __.GetBaseDefinition() = notimpl

    // from MethodBase
    override __.GetParameters() = notimpl
    override __.GetMethodImplementationFlags() = notimpl
    override __.Attributes = notimpl
    override __.MethodHandle = notimpl
    override __.Invoke(_,_,_,_,_) = notimpl

    // from MemberInfo
    override __.ReflectedType = notimpl
    override __.DeclaringType = notimpl
    override __.GetCustomAttributes _ = notimpl
    override __.GetCustomAttributes(_,_) = notimpl
    override __.IsDefined(_,_) = notimpl
    override __.Name = notimpl

    // from System.Object
    override __.Equals(_: obj): bool = notimpl
    override __.GetHashCode() = notimpl
    override x.ToString() = sprintf "%A" x

and [<Sealed>] ILConstructor(declaringType: ILType, builder: ConstructorBuilder, parameters: Parameter list, body: MethodBody) =
    inherit System.Reflection.ConstructorInfo()
    member val ILDeclaringType = declaringType
    member val Builder = builder
    member val Body = body

    interface IILMethodBase with
        override __.MethodVarMap = emptyVarMap
        override __.Parameters = parameters
    
    // from ConstructorInfo
    override __.Invoke(_,_,_,_) = notimpl

    // from MethodBase
    override __.GetParameters() = notimpl
    override __.GetMethodImplementationFlags() = notimpl
    override __.Attributes = notimpl
    override __.MethodHandle = notimpl
    override __.Invoke(_,_,_,_,_) = notimpl

    // from MemberInfo
    override __.ReflectedType = notimpl
    override __.DeclaringType = notimpl
    override __.GetCustomAttributes _ = notimpl
    override __.GetCustomAttributes(_,_) = notimpl
    override __.IsDefined(_,_) = notimpl
    override __.Name = notimpl

    // from System.Object
    override __.Equals(_: obj): bool = notimpl
    override __.GetHashCode() = notimpl
    override x.ToString() = sprintf "%A" x

type ILSymbolType (symbol) =
    inherit ILTypeSkeleton(null)
    member val Symbol = symbol
    override __.GetMethodImpl(_,_,_,_,_,_) = notimpl
    override __.GetConstructorImpl(_,_,_,_,_) = notimpl

type ILTypeArgumentIndex(index) =
    inherit ILTypeSkeleton(null)
    member val Index = index
    override __.GetMethodImpl(_,_,_,_,_,_) = notimpl
    override __.GetConstructorImpl(_,_,_,_,_) = notimpl

type ILMethodTypeArgumentIndex(index) =
    inherit ILTypeSkeleton(null)
    member val Index = index
    override __.GetMethodImpl(_,_,_,_,_,_) = notimpl
    override __.GetConstructorImpl(_,_,_,_,_) = notimpl
    
/// require: closeType.GetType().Name = "RuntimeType" && closeType.IsGenericType
let getMemberOfRuntimeOpenType getMembers resolveMember (closeType: Type) (memberOfOpenType: Reflection.MemberInfo) =
    let openTypeParemeters = closeType.GetGenericTypeDefinition().GetGenericArguments()
    let methodGerenicArgs =
        match memberOfOpenType with 
        | :? Reflection.MethodBase as m when m.IsGenericMethod -> m.GetGenericArguments()
        | _ -> Type.EmptyTypes

    let mOpenTypeMd = memberOfOpenType.MetadataToken
    getMembers closeType (B.DeclaredOnly ||| B.Public ||| B.NonPublic ||| B.Instance ||| B.Static)
    |> Seq.find (fun (m: #Reflection.MemberInfo) ->
        m.Name = memberOfOpenType.Name &&
        let m' : Reflection.MemberInfo = resolveMember m.Module m.MetadataToken openTypeParemeters methodGerenicArgs
        m'.MetadataToken = mOpenTypeMd
    )

let getMethodOfRuntimeOpenType closeType (methodOfOpenType: Reflection.MethodInfo) =
    getMemberOfRuntimeOpenType
        (fun t b -> t.GetMethods b)
        (fun m md tps mtps -> upcast m.ResolveMethod(md, tps, mtps))
        closeType methodOfOpenType

let getCtorOfRuntimeOpenType closeType (ctorOfOpenType: Reflection.ConstructorInfo) =
    getMemberOfRuntimeOpenType
        (fun t b -> t.GetConstructors b)
        (fun m md tps mtps -> upcast m.ResolveMethod(md, tps, mtps))
        closeType ctorOfOpenType

type ILRuntimeGenericType(t: System.Type) =
    inherit ILTypeSkeleton(t)

    let openType = t.GetGenericTypeDefinition()
    override __.GetGenericTypeDefinition() = openType
    override __.GetMethodImpl(name, bindingAttr, binder, callConvention, types, modifiers) =
        openType.GetMethod(name, bindingAttr, binder, callConvention, types, modifiers)
        |> getMethodOfRuntimeOpenType t

    override __.GetConstructorImpl(bindingAttr, binder, callConvention, types, modifiers) =
        openType.GetConstructor(bindingAttr, binder, callConvention, types, modifiers)
        |> getCtorOfRuntimeOpenType t

let paramType (Parameter(_,t)) = t
    
let toTypeName = function
//    | FullName(name, [], [], None) -> name
//    | FullName(name, [], [], Some asmName) -> name + ", " + asmName
//    | FullName(name, [], [ns1], None) -> ns1 + "." + name
//    | FullName(name, [], [ns1], Some asmName) -> ns1 + "." + name + ", " + asmName
    | FullName(name, nestersRev, nsRev, asmName) ->
        let b = System.Text.StringBuilder name
        let d = Type.Delimiter
        for nester in nestersRev do b.Insert(0, '+').Insert(0, nester) |> ignore
        for ns in nsRev do b.Insert(0, d).Insert(0, ns) |> ignore
        match asmName with
        | Some n -> b.Append(", ").Append(n) |> ignore
        | None -> ()

        b.ToString()
        
let solveTypeVarMap vs v = let t = List.find (fun (p: ILTypeParameter) -> String.Equals(p.IL, v)) vs in t.Builder
let rec solveType ({ tmap = map; varMap = varMap; mVarMap = mVarMap; typeArgs = typeArgs; mTypeArgs = mTypeArgs } as env) t =
    let getGenericTypeDef map pathRev =
        let mutable ti = Unchecked.defaultof<_>
        if not <| tryGet map pathRev &ti then Type.GetType(toTypeName pathRev, true)
        else upcast ti
        
    let rec aux (t: Type) =
        match t with
        | :? ILSymbolType as t ->
            match t.Symbol with
            | TypeSpec(pathRev, []) -> getGenericTypeDef map pathRev
            | TypeSpec(pathRev, ts) ->
                let ts = List.mapToArray (fun t -> ILSymbolType t :> Type |> solveType env) ts
                match getGenericTypeDef map pathRev with
                | :? ILType as ti -> ti.MakeGenericType ts
                | t ->
                    let t = t.MakeGenericType ts

                    let isDynamicType : Type -> _ = function 
                        | :? GenericTypeParameterBuilder
                        | :? TypeBuilder
                        | :? ILInstantiationType
                        | :? ILType 
                        | :? ILTypeParameter -> false
                        | _ -> true

                    if Array.forall isDynamicType ts then upcast ILRuntimeGenericType t
                    else upcast ILInstantiationType(t, None)

            | TypeVar v -> upcast solveTypeVarMap varMap v
            | MethodTypeVar v -> upcast solveTypeVarMap mVarMap v
            | TypeArgRef i ->
                match List.tryItem i typeArgs with
                | None -> upcast ILTypeArgumentIndex i
                | Some t -> t

            | MethodTypeArgRef i ->
                match List.tryItem i mTypeArgs with
                | None -> upcast ILMethodTypeArgumentIndex i
                | Some t -> t

        | :? ILTypeArgumentIndex as t -> List.item t.Index typeArgs
        | :? ILMethodTypeArgumentIndex as t -> List.item t.Index mTypeArgs
        | t -> t

    aux t

let solveTypeOfSymbol env t = solveType env <| ILSymbolType t
let rec getSystemType : Type -> _ = function
    | :? ILInstantiationType
    | :? ILRuntimeGenericType
    | :? ILType
    | :? ILTypeParameter as t ->
        let t = t.UnderlyingSystemType
        if t.IsGenericType then
            t.GetGenericTypeDefinition().MakeGenericType(t.GetGenericArguments() |> Array.map getSystemType)
        else t
    | t -> t

let solveSystemTypeOfSymbol env t = solveTypeOfSymbol env t |> getSystemType
let solveSystemTypeOfParams env pars = List.mapToArray (paramType >> solveSystemTypeOfSymbol env) pars

let defineVarMap typeParams defineGenericParameters =
    match typeParams with
    | [] -> []
    | _ ->
        List.toArray typeParams
        |> defineGenericParameters
        |> List.ofArray
        |> List.map2 (fun p p' -> ILTypeParameter(p, p')) typeParams

let mDefineGP (m: MethodBuilder) xs = m.DefineGenericParameters xs
let tDefineGP (t: TypeBuilder) xs = t.DefineGenericParameters xs

let addTypeName (FullName(name, nestersRev, nsRev, asmName)) typeName =
    FullName(typeName, name::nestersRev, nsRev, asmName)

let ofTypeName (typeName, nsRev) = FullName(typeName, [], nsRev, None)
let getName (FullName(name=name)) = name

module DefineTypes =
    let rec module'(defineType, toName, a, fullName, map, ms) =
        let a = a ||| T.Abstract ||| T.Sealed
        let t = defineType(toName fullName, a)
        add map fullName <| ILType(Choice2Of2 ms, t, map)
        for m in ms do moduleMember fullName t map m

    and type'(defineType, toName, a, fullName, map, ({ kind = kind; members = members } as d)) =
        let isInterfaceMember = function 
            | Literal _
            | Field _
            | MethodDef _
            | StaticMethodDef _
            | CtorDef _ -> false
            | AbstractDef _ -> true

        let kind =
            match kind with
            | Some k -> k
            | None ->
                match members with
                | [] -> Sealed
                | _ when List.forall isInterfaceMember members -> Interface
                | _ -> Sealed

        let a = 
            match kind with
            | Interface -> T.Abstract ||| T.Interface
            | Abstract -> T.Abstract
            | Sealed -> T.Sealed
            | Open -> T.Class
            ||| a
            ||| T.BeforeFieldInit

        let t = defineType(toName fullName, a)
        add map fullName <| ILType(Choice1Of2 d, t, map)

    and moduleMember path (t: TypeBuilder) map = function
        | ModuleMethodDef _
        | ModuleValDef _ 
        | ModuleLiteralDef _ -> ()
        | ModuleModuleDef(name, ms) -> module'(t.DefineNestedType, getName, T.NestedPublic, addTypeName path name, map, ms)
        | ModuleTypeDef(name, td) -> type'(t.DefineNestedType, getName, T.NestedPublic, addTypeName path name, map, td)

    let topDef (m: ModuleBuilder) map = function
        | TopModuleDef(path, ms) -> module'(m.DefineType, toTypeName, T.Public, ofTypeName path, map, ms)
        | TopTypeDef(name, td) -> type'(m.DefineType, toTypeName, T.Public, ofTypeName name, map, td)

let defineTypeParams map =
    for ti: ILType in values map do
        match ti.IL with
        | Choice2Of2 _ -> ()
        | Choice1Of2 { typeParams = typeParams } ->
            ti.VarMap <- defineVarMap typeParams <| tDefineGP ti.Builder

let toSign (MethodHead(name=name)) = name

let addMethod mmap head m =
    let sign = toSign head
    let mutable ms = Unchecked.defaultof<_>
    if tryGet mmap sign &ms then assign mmap sign (m::ms)
    else add mmap sign [m]

let addCtor (cmap: _ ResizeArray) c = cmap.Add c

let defineParam defineParameter i (Parameter(n, _)) = defineParameter(i, P.None, Option.toObj n) |> ignore
let defineParams defineParameter pars = List.iteri (fun i a -> defineParam defineParameter (i + 1) a) pars

let envOfTypeBuilder mVarMap (ti: ILType) = {
    tmap = ti.TypeMap
    varMap = ti.VarMap
    mVarMap = mVarMap
    typeArgs = []
    mTypeArgs = []
}

let defineMethodHead (ti: ILType) attr callconv (MethodHead(name,typeParams,pars,ret)) =
    let t = ti.Builder
    let m = t.DefineMethod(name, attr, callconv)
    let mVarMap = defineVarMap typeParams <| mDefineGP m

    let env = envOfTypeBuilder mVarMap ti
    m.SetReturnType(solveSystemTypeOfSymbol env <| paramType ret)
    m.SetParameters(solveSystemTypeOfParams env pars)

    defineParam m.DefineParameter 0 ret
    defineParams m.DefineParameter pars

    m, mVarMap

let defineMethod (dt: ILType) a c (MethodInfo(head, _) as m) =
    let mmap = dt.MethodMap
    let mb, mVarMap = defineMethodHead dt a c head
    addMethod mmap head <| ILMethod(m, dt, mb, mVarMap)

let defineMethodDef dt ov m =
    match ov with
    | None -> defineMethod dt (M.Public ||| M.Final ||| M.HideBySig) CC.Standard m
    | Some Override -> defineMethod dt (M.Public ||| M.Final ||| M.HideBySig ||| M.NewSlot ||| M.Virtual) CC.HasThis m
    | Some(BaseMethod _) -> defineMethod dt (M.Private ||| M.Final ||| M.HideBySig ||| M.NewSlot ||| M.Virtual) CC.HasThis m
    // TODO: last path
//                        let bt = solveType map varMap <| typeRefToType baseType
//                        let pts = solveParamTypes map varMap pars
//                        let bm = bt.GetMethod(baseMethodName, pts)
//                        t.DefineMethodOverride(bm, m)
    
let defineField (ti: ILType) (isStatic, isMutable, name, ft) =
    let t, fmap = ti.Builder, ti.FieldMap

    let a = F.Public
    let a = if isStatic then a ||| F.Static else a
    let a = if isMutable then a else a ||| F.InitOnly
    let ft = solveSystemTypeOfSymbol (envOfTypeBuilder emptyVarMap ti)  ft
    let f = t.DefineField(name, ft, a)
    add fmap name f

let defineLiteral (ti: ILType) name ft fv =
    let t, fmap = ti.Builder, ti.FieldMap

    let a = F.Public ||| F.Static ||| F.Literal
    let ft = solveSystemTypeOfSymbol (envOfTypeBuilder emptyVarMap ti) ft
    let f = t.DefineField(name, ft, a)
    let literalValue = function
        | I1 v -> box v
        | U1 v -> box v
        | I2 v -> box v
        | U2 v -> box v
        | I4 v -> box v
        | U4 v -> box v
        | I8 v -> box v
        | U8 v -> box v
        | Bool v -> box v
        | F4 v -> box v
        | F8 v -> box v
        | Char v -> box v
        | String v -> box v
        | Null -> null

    f.SetConstant <| literalValue fv
    add fmap name f

let defineCtor (dt: ILType) pars body =
    let t, cmap = dt.Builder, dt.ConstructorMap 

    let pts = solveSystemTypeOfParams (envOfTypeBuilder emptyVarMap dt) pars
    let c = t.DefineConstructor(M.SpecialName ||| M.RTSpecialName ||| M.Public, CC.HasThis, pts)
    defineParams c.DefineParameter pars
    addCtor cmap <| ILConstructor(dt, c, pars, body)
    
let defineStaticMethod (dt: ILType) (MethodInfo(head, _) as m) =
    let mmap = dt.MethodMap
    let mb, mVarMap = defineMethodHead dt (M.Public ||| M.Static) CC.Standard head
    addMethod mmap head <| ILMethod(m, dt, mb, mVarMap)

let defineMember dt = function
    | Field(isStatic, isMutable, n, ft) -> defineField dt (isStatic, isMutable, n, ft)
    | Literal(n, t, l) -> defineLiteral dt n t l
    | MethodDef(ov, m) -> defineMethodDef dt ov m
    | StaticMethodDef m -> defineStaticMethod dt m
    | CtorDef(pars, body) -> defineCtor dt pars body
    | AbstractDef head ->
        let a = M.Public ||| M.HideBySig ||| M.NewSlot ||| M.Abstract ||| M.Virtual
        defineMethodHead dt a CC.HasThis head
        |> ignore

let defineTypeDef (ti: ILType) { parent = parent; impls = impls; members = members } =
    let t = ti.Builder
    match parent with
    | Some parent -> t.SetParent <| solveSystemTypeOfSymbol (envOfTypeBuilder emptyVarMap ti) parent
    | _ -> ()

    for impl in impls do
        t.AddInterfaceImplementation <| solveSystemTypeOfSymbol (envOfTypeBuilder emptyVarMap ti) impl
    for m in members do defineMember ti m

let defineModuleMember dt = function
    | ModuleTypeDef _
    | ModuleModuleDef _ -> ()
    | ModuleValDef(isMutable, name, ft) -> defineField dt (true, isMutable, name, ft)
    | ModuleLiteralDef(name, ft, v) -> defineLiteral dt name ft v
    | ModuleMethodDef m -> defineStaticMethod dt m

let defineMembers map =
    for ti: ILType in values map do
        let d = ti.IL
        match d with
        | Choice1Of2 td -> defineTypeDef ti td
        | Choice2Of2 members -> for m in members do defineModuleMember ti m

let sysTypeValidate (t: Type) =
    if t.IsNested then failwithf "%A is GenericParameter." t
    if t.IsGenericParameter then failwithf "%A is GenericParameter." t

let getPath t =
    sysTypeValidate t
    let nsRev =
        t.Namespace.Split Type.Delimiter
        |> Seq.rev
        |> Seq.toList

    FullName(t.Name, [], nsRev, Some(t.Assembly.GetName().Name))

let rec typeOfT t =
    let rec typeOfTypeArgs (t: Type) = 
        if not t.IsGenericType then []
        else t.GetGenericArguments() |> Seq.map typeOfT |> Seq.toList

    TypeSpec(getPath t, typeOfTypeArgs t)

[<RequiresExplicitTypeArguments>]
let typeOf<'a> = typeOfT typeof<'a>

let ilBinder env mTypeArgs = { new Reflection.Binder() with
    override __.SelectMethod(_, methods, argTypes, _) =
        let pred (m: IILMethodBase) =
            let mVarMap = m.MethodVarMap
            let pars = m.Parameters
            List.length mVarMap = List.length mTypeArgs &&
            List.length pars = Array.length argTypes &&
            let env = { env with mTypeArgs = m.MethodVarMap |> List.map (fun t -> upcast t) }
            Seq.forall2
                (fun (Parameter(_,parT)) argT ->
                    solveType env (ILSymbolType parT) = solveType env argT
                ) pars argTypes

        let filter : Reflection.MethodBase -> _ = function
            | :? ILMethod as m -> pred m
            | :? ILConstructor as m -> pred m
            | m ->
                let mTypeParams = if m.IsGenericMethod then m.GetGenericArguments() else Type.EmptyTypes
                Array.length mTypeParams = List.length mTypeArgs &&
                let parameters = m.GetParameters()
                Array.length parameters = Array.length argTypes &&
                let env = { env with mTypeArgs = List.ofArray mTypeParams }
                Seq.forall2
                    (fun (par: Reflection.ParameterInfo) argT ->
                        par.ParameterType = solveType env argT
                    )
                    parameters
                    argTypes
        methods
        |> Seq.filter filter
        |> Seq.exactlyOne

    override __.SelectProperty(_, _, _, _, _) = notimpl
    override __.BindToMethod(_, _, _, _, _, _, _) = notimpl
    override __.BindToField(_, _, _, _) = notimpl
    override __.ChangeType(_, _, _) = notimpl
    override __.ReorderArgumentArray(_, _) = notimpl
}

let getField env parent name =
    let parent = solveType env <| ILSymbolType parent
    parent.GetField(name, B.DeclaredOnly ||| B.Static ||| B.Instance ||| B.Public ||| B.NonPublic)

let getMethod env parent name mTypeArgs argTypes =
    let parent = solveType env <| ILSymbolType parent
    let env =
        if parent.IsGenericType then
            { env with typeArgs = List.ofArray <| parent.GetGenericTypeDefinition().GetGenericArguments() }
        else env

    let env' =
        match parent with
        | :? ILType as parent ->
            { env with varMap = parent.VarMap }
        | :? ILInstantiationType as parent ->
            match parent.OpenType with
            | None -> env
            | Some openParent -> { env with varMap = openParent.VarMap }
        | _ -> env

    let binder = ilBinder env' mTypeArgs
    let openMethod =
        parent.GetMethod(
            name,
            B.DeclaredOnly ||| B.Static ||| B.Instance ||| B.Public ||| B.NonPublic,
            binder,
            CC.Any,
            List.mapToArray (ILSymbolType >> solveType env) argTypes,
            null
        )
    if openMethod.IsGenericMethodDefinition then
        let mTypeArgs = List.mapToArray (ILSymbolType >> solveType env) mTypeArgs
        openMethod.MakeGenericMethod mTypeArgs
    else
        openMethod

    |> function
        | :? ILMethod as m -> m.Builder :> Reflection.MethodInfo
        | m -> m

let getCtor env parent argTypes =
    let parent = solveType env <| ILSymbolType parent
    let env = if parent.IsGenericType then { env with typeArgs = List.ofArray <| parent.GetGenericTypeDefinition().GetGenericArguments() } else env

    let binder = ilBinder env emptyVarMap
    parent.GetConstructor(
        B.DeclaredOnly ||| B.Public ||| B.NonPublic ||| B.Instance,
        binder,
        CC.HasThis,
        List.mapToArray (ILSymbolType >> solveType env) argTypes,
        null
    )
    |> function
        | :? ILConstructor as m -> m.Builder :> Reflection.ConstructorInfo
        | m -> m

let emitInstr (g: ILGenerator) mVarMap dt (Instr(label, op, operand)) =
    match operand with
    | OpNone -> g.Emit op
    | OpI1 n -> g.Emit(op, n)
    | OpI2 n -> g.Emit(op, n)
    | OpI4 n -> g.Emit(op, n)
    | OpI8 n -> g.Emit(op, n)
    | OpF4 n -> g.Emit(op, n)
    | OpF8 n -> g.Emit(op, n)
    | OpString s -> g.Emit(op, s)
    | OpType t -> g.Emit(op, solveSystemTypeOfSymbol (envOfTypeBuilder mVarMap dt) t)
    | OpField(parent, name) -> g.Emit(op, getField (envOfTypeBuilder mVarMap dt) parent name)
    | OpMethod(parent, name, mTypeArgs, argTypes) -> g.Emit(op, getMethod (envOfTypeBuilder mVarMap dt) parent name mTypeArgs argTypes)
    | OpCtor(parent, argTypes) -> g.Emit(op, getCtor (envOfTypeBuilder mVarMap dt) parent argTypes)

let emitMethod g mVarMap dt (MethodBody instrs) =
    for instr in instrs do emitInstr g mVarMap dt instr

let emit map =
    for t: ILType in values map do
        let mmap, cmap = t.MethodMap, t.ConstructorMap
        for mis in values mmap do
            for m: ILMethod in mis do
                let mb, mVarMap, dt, MethodInfo(_, b) = m.Builder, m.MethodVarMap, m.ILDeclaringType, m.IL
                emitMethod (mb.GetILGenerator()) mVarMap dt b

        for m: ILConstructor in cmap do
            let cb, dt, body = m.Builder, m.ILDeclaringType, m.Body
            emitMethod (cb.GetILGenerator()) emptyVarMap dt body

let createTypes map = for t: ILType in values map do t.Builder.CreateType() |> ignore

let emitIL m { topDefs = ds } =
    let map = HashMap()
    for d in ds do DefineTypes.topDef m map d
    defineTypeParams map
    defineMembers map
    emit map
    createTypes map

module PreDefinedTypes =
    let int8T = typeOf<int8>
    let int16T = typeOf<int16>
    let int32T = typeOf<int32>
    let int64T = typeOf<int64>
    
    let uint8T = typeOf<uint8>
    let uint16T = typeOf<uint16>
    let uint32T = typeOf<uint32>
    let uint64T = typeOf<uint64>
    
    let float32T = typeOf<single>
    let float64T = typeOf<double>

    let voidT = typeOfT typeof<System.Void>
    let boolT = typeOf<bool>
    let charT = typeOf<Char>
    let stringT = typeOf<string>
    let objectT = typeOf<obj>
