namespace Alpa.Emit
open System

[<AutoOpen>]
module internal InternalShortNames =
    type B = System.Reflection.BindingFlags
    type CC = System.Reflection.CallingConventions
    type T = System.Reflection.TypeAttributes
    type M = System.Reflection.MethodAttributes
    type P = System.Reflection.ParameterAttributes
    type F = System.Reflection.FieldAttributes
    type O = System.Reflection.Emit.OpCodes

module List =
    let tryIter2 action ls rs =
        let rec aux ls rs =
            match ls, rs with
            | l::ls, r::rs -> action l r; aux ls rs
            | [], [] -> true
            | _ -> false
        aux ls rs

    let tryGetDuplicate xs =
        let rec aux set = function
            | [] -> None
            | x::_ when List.contains x set -> Some x
            | x::xs -> aux (x::set) xs
        aux [] xs

module HashMap =
    open System.Collections.Generic

    let contines (map: HashMap<_,_>) k = map.ContainsKey k
    let add (map: HashMap<_,_>) k v = map.Add(k, v)
    let assign (map: HashMap<_,_>) k v = map.[k] <- v
    let get (map: HashMap<_,_>) k = 
        try map.[k]
        with
        | :? KeyNotFoundException as e ->
            raise <| KeyNotFoundException(sprintf "%s: %A" e.Message k)

    let tryGet (map: HashMap<_,_>) k (v: _ byref) = map.TryGetValue(k, &v)
    let values (map: HashMap<_,_>) = map.Values

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module TypeVarMap =
    let emptyVarMap = []
    let typeParams xs = Seq.map fst xs
    let typeVarMapToSolvedType xs = Seq.map TypeParam xs
    
[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module AssemblyRef =
    open System.Reflection
    open System.Globalization

    let toAssemblyName
        {
            name = name
            publicKeyToken = publicKeyToken
            culture = culture
            version = version
        }
        =
        let n = AssemblyName name
        match publicKeyToken with
        | None -> ()
        | Some k -> n.SetPublicKeyToken(Array.copy k)

        match version with
        | None -> ()
        | Some v ->
            let v =
                match v with
                | Version2(v1, v2) -> Version(v1,v2)
                | Version3(v1, v2, v3) -> Version(v1,v2,v3)
                | Version4(v1, v2, v3, v4) -> Version(v1,v2,v3,v4)

            n.Version <- v

        match culture with
        | None -> ()
        | Some x ->
            n.CultureInfo <-
                if x = "neutral"
                then CultureInfo.InvariantCulture
                else CultureInfo.GetCultureInfo x
        n

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module FullName =
    let toTypeName { imap = imap } = function
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
            | Some n ->
                b.Append(", ") |> ignore
                match n with
                | "mscorlib" -> b.Append(n)
                | _ ->
                    let mutable r = Unchecked.defaultof<_>
                    if HashMap.tryGet imap n &r then
                        let n = AssemblyRef.toAssemblyName r
                        b.Append n
                    else
                        b.Append n

                |> ignore
            | None -> ()

            b.ToString()

    let addTypeName (FullName(name, nestersRev, nsRev, asmName)) typeName =
        FullName(typeName, name::nestersRev, nsRev, asmName)

    let ofTypeName (typeName, nsRev) = FullName(typeName, [], nsRev, None)
    let getName (FullName(name=name)) = name

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module SolveEnv =   
    let envOfTypeBuilder mVarMap { env = env; varMap = varMap } = {
        senv = env
        sVarMap = varMap
        sMVarMap = mVarMap
        typeArgs = []
        mTypeArgs = []
    }
    let envOfMethodBuilder { mVarMap = mVarMap; dt = dt } = envOfTypeBuilder mVarMap dt

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module SolvedType =
    let rec getUnderlyingSystemType = function
        | RuntimeType t
        | InstantiationType(closeType = t) -> t
        | TypeParam(_, t) -> upcast t
        | Builder { t = t } -> upcast t

        | PointerType t -> getUnderlyingSystemType(t).MakePointerType()
        | ByrefType t -> getUnderlyingSystemType(t).MakeByRefType()
        | ArrayType t -> getUnderlyingSystemType(t).MakeArrayType()

    let rec typeEq l r =
        match l, r with
        | RuntimeType l, RuntimeType r -> l = r
        | InstantiationType(closeType=lc;typeParams=ls), InstantiationType(closeType=rc;typeParams=rs) -> lc.GetGenericTypeDefinition() = rc.GetGenericTypeDefinition() && List.forall2 typeEq ls rs
        | TypeParam(_, l), TypeParam(_, r) -> l = r
        | Builder { t = l }, Builder { t = r } -> l = r
        | _ -> false

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module EmitException =
    let raiseEmitExn e = raise <| EmitException e
    
[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module TypeSpec =
    open HashMap

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

    type private C = System.TypeCode
    let getTypeCode = function
        | TypeSpec(FullName(n, [], ["System"], Some "mscorlib"), []) ->
            match n with
            | "Boolean" -> C.Boolean
            | "Byte" ->  C.Byte
            | "Char" -> C.Char
            | "DBNull" -> C.DBNull
            | "DateTime" -> C.DateTime
            | "Decimal" -> C.Decimal
            | "Double" -> C.Double
            | "Int16" -> C.Int16
            | "Int32" -> C.Int32
            | "Int64" -> C.Int64
            | "SByte" -> C.SByte
            | "Single" -> C.Single
            | "String" -> C.String
            | "UInt16" -> C.UInt16
            | "UInt32" -> C.UInt32
            | "UInt64" -> C.UInt64
            | _ -> C.Object
        | _ -> C.Object

    let rec getReplacedType subst = function
        | TypeSpec(n, ts) -> TypeSpec(n, List.map (getReplacedType subst) ts)
        | TypeVar v as t ->
            match List.tryFind (fun (v',_) -> v = v') subst with
            | Some(_,t) -> getReplacedType subst t
            | None -> t

        | t -> t

    let applyType n ({ aTypeParams = ps; entity = t } as v) ts =
        if List.length ps <> List.length ts then EmitException.raiseEmitExn <| AliasKindError(n, ts, v)
        let rec eval = function
            | TypeSpec(n, ts) -> TypeSpec(n, List.map eval ts)
            | TypeVar v -> List.item (List.findIndex ((=) v) ps) ts
            | TypeArgRef i -> List.item i ts
            | _ -> failwith "unreach"
        eval t

    let solveTypeVarMap xs v = List.find (fst >> (=) v) xs |> snd
    let rec solveTypeCore ({ senv = { map = map; amap = amap } as senv; sVarMap = varMap; sMVarMap = mVarMap; typeArgs = typeArgs; mTypeArgs = mTypeArgs } as env) t =
        let getTypeDef map name =
            let mutable ti = Unchecked.defaultof<_>
            if tryGet map name &ti then Builder ti
            else RuntimeType <| Type.GetType(FullName.toTypeName senv name, true)

        let rec aux t =
            let mutable ad = Unchecked.defaultof<_>
            match t with
            | Pointer t -> PointerType (aux t)
            | Byref t -> ByrefType (aux t)
            | Array t -> ArrayType (aux t)

            | TypeSpec(FullName(name, [], [], None), ts) when tryGet amap name &ad ->
                solveTypeCore env (applyType name ad ts)
                
            | TypeSpec(pathRev, []) -> getTypeDef map pathRev
            | TypeSpec(pathRev, ts) ->
                let vs = List.map (solveTypeCore env) ts
                let ts = Seq.map SolvedType.getUnderlyingSystemType vs |> Seq.toArray
                match getTypeDef map pathRev with
                | Builder({ t = t } as ti) -> InstantiationType(t.MakeGenericType ts, Some ti, vs)
                | RuntimeType t ->
                    let t = t.MakeGenericType ts
                    if List.forall (function RuntimeType _ -> true | _ -> false) vs then RuntimeType t
                    else InstantiationType(t, None, vs)

                | _ -> failwith "unreach"

            | TypeVar v -> TypeParam(v, solveTypeVarMap varMap v)
            | MethodTypeVar v -> TypeParam(v, solveTypeVarMap mVarMap v)
            | TypeArgRef i -> List.item i typeArgs
            | MethodTypeArgRef i -> List.item i mTypeArgs
        aux t

    let solveType env t = solveTypeCore env t |> SolvedType.getUnderlyingSystemType
    let solveTypes env ts = Seq.map (solveType env) ts |> Seq.toArray
    let solveParamTypes env pars = Seq.map (fun (Parameter(_,t)) -> solveType env t) pars |> Seq.toArray

module PreDefinedTypes =
    open TypeSpec

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

open PreDefinedTypes
    
[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Parameter =
    let paramType (Parameter(_,t)) = t
    let voidParam = Parameter(None, PreDefinedTypes.voidT)

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module MethodHead =
    let cctorHead = MethodHead(".cctor", [], [], Parameter.voidParam)
    let ctorHead pars = MethodHead(".ctor", [], pars, Parameter.voidParam)
    let defaultCtorHead = ctorHead []
    
[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module MethodBody =
    let defaultConstructerBody baseType =
        let bc = MethodRef(baseType, ".ctor", Some(MethodTypeAnnotation([],[], None)))
        MethodBody(None,
            [
                Instr("", O.Ldarg_0, OpNone)
                Instr("", O.Call, OpMethod bc)
                Instr("", O.Ret, OpNone)
            ]
        )

    let defaultConstructerBodyOfObject = defaultConstructerBody objectT

module Member =
    open System.Reflection
    let metadataToken (m: MemberInfo) = m.MetadataToken
    let name (m: MemberInfo) = m.Name
    let getGenericArguments (m: MemberInfo) =
        match m with 
        | :? Reflection.MethodBase as m when m.IsGenericMethod -> m.GetGenericArguments()
        | _ -> Type.EmptyTypes

module Type =
    type MT = Reflection.MemberTypes
    let isGeneric (t: Type) = t.IsGenericType
    let getOpenType t = if isGeneric t then t.GetGenericTypeDefinition() else t
    let getTypeParams t = if isGeneric t then t.GetGenericTypeDefinition().GetGenericArguments() else Type.EmptyTypes

    let getAllMethodBases (t: Type) =
        t.GetMember(
            "*",
            MT.Constructor ||| MT.Method,
            B.DeclaredOnly ||| B.Public ||| B.NonPublic ||| B.Static ||| B.Instance
        )
        |> box
        |> unbox<Reflection.MethodBase array>

    let getMethodBases name (t: Type) =
        t.FindMembers(
            MT.Constructor ||| MT.Method,
            B.DeclaredOnly ||| B.Public ||| B.NonPublic ||| B.Static ||| B.Instance,
            Reflection.MemberFilter(fun m _ -> m.Name = name),
            null
        )
        |> Seq.map (fun m -> m :?> Reflection.MethodBase)

    let getConstructors (t: Type) = t.GetConstructors(B.DeclaredOnly ||| B.Public ||| B.NonPublic ||| B.Instance)
    
    let ctorsToMethodBasesArray (xs: Reflection.ConstructorInfo array) = box xs |> unbox<Reflection.MethodBase array>

module Method =
    open System.Reflection
    let getTypeParams (m: MethodInfo) = if m.IsGenericMethod then m.GetGenericMethodDefinition().GetGenericArguments() else [||]

module MethodBase =
    open System.Reflection
    let getTypeParams : MethodBase -> _ = function
        | :? MethodInfo as m -> Method.getTypeParams m
        | _ -> Type.EmptyTypes

    let getParemeterTypes (m: MethodBase) = m.GetParameters() |> Seq.map (fun p -> p.ParameterType)

    let getReturnType (m: MethodBase) =
        match m with
        | :? MethodInfo as m -> m.ReturnType
        | _ -> typeof<Void>
        
    let makeCloseMethod openMethod mTypeArgs =
        if Seq.isEmpty mTypeArgs then openMethod
        else
            let m = (openMethod: MethodBase) :?> Reflection.MethodInfo
            upcast m.MakeGenericMethod(Seq.toArray mTypeArgs)

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module ILMethodBuilder =
    open Parameter
    open SolvedType

    let getUnderlyingSystemMethod { mb = m } =
        match m with
        | Choice1Of2 m -> m :> Reflection.MethodBase
        | Choice2Of2 m -> upcast m

    let getTypeParams { ILMethodBuilder.mVarMap = mVarMap } = mVarMap
    let getParemeterTypes { h = MethodHead(pars=pars) } = Seq.map paramType pars
    let getReturnType { h = MethodHead(ret=ret) } = paramType ret
    let makeCloseMethod m mTypeArgs =
        Seq.map getUnderlyingSystemType mTypeArgs
        |> MethodBase.makeCloseMethod (getUnderlyingSystemMethod m)

    let getILGenerator { mb = mb } =
        match mb with
        | Choice1Of2 m -> m.GetILGenerator()
        | Choice2Of2 m -> m.GetILGenerator()

    let setInitLocals { mb = mb } x =
        match mb with
        | Choice2Of2 m -> m.InitLocals <- x
        | Choice1Of2 m ->
            if not m.IsGenericMethod || m.IsGenericMethodDefinition then
                m.InitLocals <- x
            else ()

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module ILTypeBuilder =
    open HashMap

    let addMethodOfSign { mmap = mmap } sign m =
        let mutable ms = Unchecked.defaultof<_>
        if tryGet mmap sign &ms then assign mmap sign (m::ms)
        else add mmap sign [m]

    let addMethod dt (MethodHead(name=sign)) m = addMethodOfSign dt sign m

    let addCtor dt c = addMethodOfSign dt ".ctor" c
    
    let newILTypeBuilder d t path env = {
        d = d
        t = t
        path = path
        varMap = TypeVarMap.emptyVarMap
        env = env
        mmap = HashMap()
        fmap = HashMap()
    }
    let getMethods name { mmap = mmap } = get mmap name |> List.toSeq
    let getConstructors dt = getMethods ".ctor" dt
    let getTypeParams { varMap = varMap } = varMap

module Access =
    let nestedAccess = function
        | None -> T.NestedPublic
        | Some a ->
            match a with
            | NestedAccess.Public -> T.NestedPublic
            | NestedAccess.Assembly -> T.NestedAssembly
            | NestedAccess.Private ->T.NestedPrivate
            | NestedAccess.Family -> T.NestedFamily
            | NestedAccess.FamilyAndAssembly -> T.NestedFamANDAssem
            | NestedAccess.FamilyOrAssembly -> T.NestedFamORAssem

    let typeAccess = function
        | None -> T.Public
        | Some a ->
            match a with
            | TypeAccess.Public -> T.Public
            | TypeAccess.Private -> T.NotPublic
        
    let fieldAccess = function
        | None -> F.Public
        | Some x ->
            match x with
            | MemberAccess.Assembly -> F.Assembly
            | MemberAccess.Public -> F.Public
            | MemberAccess.Private -> F.Private
            | MemberAccess.Family -> F.Family
            | MemberAccess.FamilyAndAssembly -> F.FamANDAssem
            | MemberAccess.FamilyOrAssembly -> F.FamORAssem
            | MemberAccess.PrivateScope -> F.PrivateScope

    let methodAccess a = fieldAccess a |> int |> enum<M>
