module Alpa.Emit.ILEmitExpr
open System
open Alpa.Emit.TypeSpec
open Alpa.Emit.PreDefinedTypes

let inRange l h x = l <= x && x <= h
let ldcI4 = function
    | -1 -> Instr("", O.Ldc_I4_M1, OpNone)
    | 0 -> Instr("", O.Ldc_I4_0, OpNone)
    | 1 -> Instr("", O.Ldc_I4_1, OpNone)
    | 2 -> Instr("", O.Ldc_I4_2, OpNone)
    | 3 -> Instr("", O.Ldc_I4_3, OpNone)
    | 4 -> Instr("", O.Ldc_I4_4, OpNone)
    | 5 -> Instr("", O.Ldc_I4_5, OpNone)
    | 6 -> Instr("", O.Ldc_I4_6, OpNone)
    | 7 -> Instr("", O.Ldc_I4_7, OpNone)
    | 8 -> Instr("", O.Ldc_I4_8, OpNone)
    | n when inRange (int32 SByte.MinValue) (int32 SByte.MaxValue) n ->
        Instr("", O.Ldc_I4_S, OpI1(int8 n))
    | n -> Instr("", O.Ldc_I4, OpI4 n)

let ldarg = function
    | 0s -> Instr("", O.Ldarg_0, OpNone)
    | 1s -> Instr("", O.Ldarg_1, OpNone)
    | 2s -> Instr("", O.Ldarg_2, OpNone)
    | 3s -> Instr("", O.Ldarg_3, OpNone)
    | n when inRange (int16 SByte.MinValue) (int16 SByte.MaxValue) n ->
        Instr("", O.Ldarg_S, OpI1(int8 n))
        
    | n -> Instr("", O.Ldarg, OpI2 n)

let ldloc = function
    | 0s -> Instr("", O.Ldloc_0, OpNone)
    | 1s -> Instr("", O.Ldloc_1, OpNone)
    | 2s -> Instr("", O.Ldloc_2, OpNone)
    | 3s -> Instr("", O.Ldloc_3, OpNone)
    | n when inRange (int16 SByte.MinValue) (int16 SByte.MaxValue) n ->
        Instr("", O.Ldloc_S, OpI1(int8 n))
    | n -> Instr("", O.Ldloc, OpI2 n)

let stloc = function
    | 0s -> Instr("", O.Stloc_0, OpNone)
    | 1s -> Instr("", O.Stloc_1, OpNone)
    | 2s -> Instr("", O.Stloc_2, OpNone)
    | 3s -> Instr("", O.Stloc_3, OpNone)
    | n when inRange (int16 SByte.MinValue) (int16 SByte.MaxValue) n ->
        Instr("", O.Stloc_S, OpI1(int8 n))
    | n -> Instr("", O.Stloc, OpI2 n)

let ldloca n =
    if inRange (int16 SByte.MinValue) (int16 SByte.MaxValue) n then Instr("", O.Ldloca_S, OpI1(int8 n))
    else Instr("", O.Ldloca, OpI2 n)

let ldarga n =
    if inRange (int16 SByte.MinValue) (int16 SByte.MaxValue) n then Instr("", O.Ldarga_S, OpI1(int8 n))
    else Instr("", O.Ldarga, OpI2 n)
    
type C = System.TypeCode

let ldind env = function
    | TypeSpec.Pointer _ -> Instr("", O.Ldind_I, OpNone)
    | TypeSpec.Array _ -> Instr("", O.Ldind_Ref, OpNone)
    | t ->
        match getTypeCode t with
        | C.SByte -> Instr("", O.Ldind_I1, OpNone)
        | C.Int16 -> Instr("", O.Ldind_I2, OpNone)
        | C.Int32 -> Instr("", O.Ldind_I4, OpNone)
        | C.Int64 -> Instr("", O.Ldind_I8, OpNone)
        | C.Single -> Instr("", O.Ldind_R4, OpNone)
        | C.Double -> Instr("", O.Ldind_R8, OpNone)
        | C.Byte -> Instr("", O.Ldind_U1, OpNone)
        | C.UInt16 -> Instr("", O.Ldind_U2, OpNone)
        | C.UInt32 -> Instr("", O.Ldind_U4, OpNone)
        | _ ->
            let t' = solveType env t
            if t' = typeof<nativeint> || t' = typeof<unativeint> then Instr("", O.Ldind_I, OpNone)
            elif t'.IsValueType || t'.IsGenericParameter then Instr("", O.Ldobj, OpType t)
            else Instr("", O.Ldind_Ref, OpNone)

let stind env = function
    | TypeSpec.Pointer _ -> Instr("", O.Stind_I, OpNone)
    | TypeSpec.Array _ -> Instr("", O.Stind_Ref, OpNone)
    | t ->
        match getTypeCode t with
        | C.SByte -> Instr("", O.Stind_I1, OpNone)
        | C.Int16 -> Instr("", O.Stind_I2, OpNone)
        | C.Int32 -> Instr("", O.Stind_I4, OpNone)
        | C.Int64 -> Instr("", O.Stind_I8, OpNone)
        | C.Single -> Instr("", O.Stind_R4, OpNone)
        | C.Double -> Instr("", O.Stind_R8, OpNone)
        | _ ->
            let t' = solveType env t
            if t' = typeof<nativeint> || t' = typeof<unativeint> then Instr("", O.Stind_I, OpNone)
            elif t'.IsValueType || t'.IsGenericParameter then Instr("", O.Stobj, OpType t)
            else Instr("", O.Stind_Ref, OpNone)

let ldelem env = function
    | TypeSpec.Pointer _ -> Instr("", O.Ldelem_I, OpNone)
    | TypeSpec.Array _ -> Instr("", O.Ldelem_Ref, OpNone)
    | t ->
        match getTypeCode t with
        | C.SByte -> Instr("", O.Ldelem_I1, OpNone)
        | C.Int16 -> Instr("", O.Ldelem_I2, OpNone)
        | C.Int32 -> Instr("", O.Ldelem_I4, OpNone)
        | C.Int64 -> Instr("", O.Ldelem_I8, OpNone)
        | C.Single -> Instr("", O.Ldelem_R4, OpNone)
        | C.Double -> Instr("", O.Ldelem_R8, OpNone)
        | C.Byte -> Instr("", O.Ldelem_U1, OpNone)
        | C.UInt16 -> Instr("", O.Ldelem_U2, OpNone)
        | C.UInt32 -> Instr("", O.Ldelem_U4, OpNone)
        | _ ->
            let t' = solveType env t
            if t' = typeof<nativeint> || t' = typeof<unativeint> then Instr("", O.Ldelem_I, OpNone)
            elif t'.IsValueType || t'.IsGenericParameter then Instr("", O.Ldelem, OpType t)
            else Instr("", O.Ldelem_Ref, OpNone)

let stelem env = function
    | TypeSpec.Pointer _ -> Instr("", O.Stelem_I, OpNone)
    | TypeSpec.Array _ -> Instr("", O.Stelem_Ref, OpNone)
    | t ->
        match getTypeCode t with
        | C.SByte -> Instr("", O.Stelem_I1, OpNone)
        | C.Int16 -> Instr("", O.Stelem_I2, OpNone)
        | C.Int32 -> Instr("", O.Stelem_I4, OpNone)
        | C.Int64 -> Instr("", O.Stelem_I8, OpNone)
        | C.Single -> Instr("", O.Stelem_R4, OpNone)
        | C.Double -> Instr("", O.Stelem_R8, OpNone)
        | _ ->
            let t' = solveType env t
            if t' = typeof<nativeint> || t' = typeof<unativeint> then Instr("", O.Stelem_I, OpNone)
            elif t'.IsValueType || t'.IsGenericParameter then Instr("", O.Stelem, OpType t)
            else Instr("", O.Stelem_Ref, OpNone)

let emitLit = function
    | LitB x when x -> Instr("", O.Ldc_I4_1, OpNone), boolT
    | LitB _ -> Instr("", O.Ldc_I4_0, OpNone), boolT
    | LitI1 x -> ldcI4(int32 x), int8T
    | LitI2 x -> ldcI4(int32 x), int16T
    | LitI4 x -> ldcI4 x, int32T
    | LitI8 x -> Instr("", O.Ldc_I8, OpI8 x), int64T
    | LitU1 x -> ldcI4(int32 x), uint8T
    | LitU2 x -> ldcI4(int32 x), uint16T
    | LitU4 x -> ldcI4(int32 x), uint32T
    | LitU8 x -> Instr("", O.Ldc_I8, OpI8(int64 x)), uint64T
    | LitC x -> ldcI4(int32 x), charT
    | LitF4 x -> Instr("", O.Ldc_R4, OpF4 x), float32T
    | LitF8 x -> Instr("", O.Ldc_R8, OpF8 x), float64T
    | LitS null -> Instr("", O.Ldnull, OpNone), stringT
    | LitS x -> Instr("", O.Ldstr, OpString x), stringT
    | LitNull t -> Instr("", O.Ldnull, OpNone), t

type LocalInfo = { i: int16; t: TypeSpec; using: bool }
let LocalInfo(i, t, u) = { i = i; t = t; using = u }

let rec appendRev ls rs =
    match ls with
    | [] -> rs
    | l::ls -> appendRev ls (l::rs)

type Env = {
    locals: Map<string, LocalInfo>
    pars: Parameter list
    menv: SolveEnv
}
let updateLocals ({ locals = locals } as env) (ls: ResizeArray<_>) v vt =
    let l = 
        let i = ls.FindIndex(fun { t = t; using = using } -> not using && t = vt)
        if 0 <= i then
            let l = LocalInfo(int16 i, vt, true)
            ls.[i] <- l
            l
        else
            let l = LocalInfo(int16 locals.Count, vt, true)
            ls.Add l
            l

    l, { env with locals = Map.add v l locals }


let findNVar { pars = pars; locals = locals } v =
    match Map.tryFind v locals with
    | Some { i = i; t = t } -> true, i, t
    | None ->
        let rec findi i = function
            | Parameter(Some n, t)::_ when n = v -> false, i, t
            | _::xs -> findi (i+1s) xs
            | [] -> failwithf "not found NVar(%A)" v
        findi 0s pars

let (<<|) (xs: ResizeArray<_>) x = xs.Add x

let emitNVarRef env _ rs v =
    let isLoc, i, t = findNVar env v
    rs <<| if isLoc then ldloca i else ldarga i
    TypeSpec.Byref t

let emitAVarRef { pars = pars } _ rs i =
    let (Parameter(_,t)) = List.item i pars
    rs <<| ldarga (int16 i)
    TypeSpec.Byref t

let emitNVar env _ rs v =
    // `$0.[1].F <- 2` =
    // `
    // ldloca 0
    // ldc.i4.1
    // ldelema ...
    // ldc.i4.2
    // stfld ...::F
    // `
    let isLoc, i, t = findNVar env v
    rs <<| if isLoc then ldloc i else ldarg i
    t

let emitAVar { pars = pars } _ rs i =
    let (Parameter(_,t)) = List.item i pars
    rs <<| ldarg (int16 i)
    t

let rec emit env ls rs = function
    | Lit x -> let i, t = emitLit x in rs <<| i; t
    | NVar v -> emitNVar env ls rs v
    | AVar i -> emitAVar env ls rs i
    | LetZero(v, vt, e) -> emitLetZero env ls rs (v, vt, e)
    | Let(v, init, e) ->
        let vt = emit env ls rs init
        let { i = i } as l, env = updateLocals env ls v vt
        rs.Add <| stloc i
        let t = emit env ls rs e
        ls.[int32 i] <- { l with using = false }
        t

    | Next(l, r) ->
        let t = emit env ls rs l
        if t <> voidT then rs <<| Instr("", O.Pop, OpNone)
        emit env ls rs r

    | VCall(this, m, args) -> emitVCall env ls rs (this, m, args)
    | ICall(this, m, args) -> emitICall env ls rs (this, m, args)
    | Upcast(x, t) -> emit env ls rs x |> ignore; t
    | NewArray(x, xs) -> emitNewArray env ls rs (x, xs)
    | NewEmptyArray t ->
        rs <<| ldcI4 0
        rs <<| Instr("", O.Newarr, OpType t)
        TypeSpec.Array t

    | NVarRef v -> emitNVarRef env ls rs v
    | AVarRef i -> emitAVarRef env ls rs i
    | FieldRef(this, fieldName) -> emitFieldRef env ls rs (this, fieldName)
    | ArrayElemRef(array, index) ->
        let elemT =
            match emit env ls rs array with
            | TypeSpec.Array t -> t
            | _ -> failwith "ArrayIndex"

        if emit env ls rs index <> int32T then failwith "ArrayIndex"

        rs <<| Instr("", O.Ldelema, OpType elemT)
        TypeSpec.Byref elemT

    | RefRead e -> emitRefRead env ls rs e
    | Initobj(ref, e) ->
        let refT = emit env ls rs ref
        let t =
            match refT with
            | TypeSpec.Byref t -> t
            | _ -> failwith "Initobj"

        rs <<| Instr("", O.Initobj, OpType t)
        emit env ls rs e

    | Newobj(this, args) ->
        let argTs = List.map (fun arg -> emit env ls rs arg) args
        let MethodRef(thisType=thisT) as m =
            match this with
            | Choice1Of2 thisT -> MethodRef(thisT, ".ctor", Some(MethodTypeAnnotation([], argTs, None)))
            | Choice2Of2 ctor -> ctor

        rs <<| Instr("", O.Newobj, OpMethod m)
        thisT

    | FieldAccess(this, fieldName) -> emitFieldAccess env ls rs (this, fieldName)
    | ArrayIndex(array, index) -> emitArrayIndex env ls rs (array, index)
    | MRefWrite(ref, value, cont) -> emitMRefWrite env ls rs (ref, value, cont)

and emitLetZero env ls rs (v, vt, e) =
    let { i = i } as l, env = updateLocals env ls v vt
    let t = emit env ls rs e
    ls.[int32 i] <- { l with using = false }
    t

and emitArrayIndexRef env ls rs (array, i) =
    let arrayT = emit env ls rs array
    emit env ls rs i |> ignore
    rs <<| Instr("", O.Ldelema, OpNone)
    match arrayT with
    | TypeSpec.Array t -> TypeSpec.Byref t
    | _ -> failwithf "emitArrayIndexRef %A" arrayT

and emitSFieldRef { menv = menv } _ rs (thisT, name) =
    rs <<| Instr("", O.Ldsflda, OpField(thisT, name))
    let field = Solve.getField menv thisT name
    let fieldT = typeOfT field.FieldType
    TypeSpec.Byref fieldT

and emitIFieldRef { menv = menv } env ls rs (this, name) =
    (*
    `S::new().F` ->
    `
        ldloca 0
        initobj S::.ctor()
        ldloc.0
        stloc.1
        ldloca 1
        ldflda S::F
    `
    *)
    let thisT = emit env ls rs this
    rs.Add <| Instr("", O.Ldflda, OpField(thisT, name))
    let field = Solve.getField menv thisT name
    let fieldT = typeOfT field.FieldType
    TypeSpec.Byref fieldT

and emitVCall env ls rs (this, m, args) =
    emit env ls rs this |> ignore
    for arg in args do emit env ls rs arg |> ignore
    rs <<| Instr("", O.Callvirt, OpMethod m)
    match m with
    | MethodRef(_, _, Some(MethodTypeAnnotation(returnType=Some r))) -> r
    | _ ->
        match Solve.getMethodBase env.menv m with
        | :? System.Reflection.MethodInfo as m ->
            // TODO: typeparam
            typeOfT m.ReturnType

        | _ -> failwithf ""

and emitICall env ls rs (this, m, args) =
    let thisT =
        match this with
        | Choice1Of2 this -> emit env ls rs this
        | Choice2Of2 thisT -> thisT

    let argsT = [for arg in args -> emit env ls rs arg]

    let m =
        match m with
        | Choice2Of2 m -> m
        | Choice1Of2 name -> MethodRef(thisT, name, Some(MethodTypeAnnotation([], argsT, None)))

    rs <<| Instr("", O.Call, OpMethod m)

    match m with
    | MethodRef(_, _, Some(MethodTypeAnnotation(returnType=Some r))) -> r
    | _ ->
        match Solve.getMethodBase env.menv m with
        | :? System.Reflection.MethodInfo as m ->
            // TODO: typeparam
            typeOfT m.ReturnType

        | _ -> failwithf ""

and emitNewArray ({ menv = menv } as env) ls rs (x, xs) =
    let rs' = ResizeArray()
    let t = emit env ls rs' x
    rs.Add <| ldcI4 (List.length xs + 1)
    rs.Add <| Instr("", O.Newarr, OpType t)
    rs.Add <| Instr("", O.Dup, OpNone)
    rs.Add <| ldcI4 0
    rs.AddRange rs'
    let stElem = stelem menv t
    rs.Add stElem

    List.iteri (fun i x ->
        rs.Add <| Instr("", O.Dup, OpNone)
        rs.Add <| ldcI4 (i + 1)
        let t' = emit env ls rs x
        if t <> t' then failwithf "NewArray: %A <> %A" t t'
        rs.Add stElem
    ) xs

    TypeSpec.Array t

and emitFieldRef ({ menv = menv } as env) ls rs (this, fieldName) =
    let thisT, op =
        match this with
        | Choice1Of2 this -> emit env ls rs this, O.Ldflda
        | Choice2Of2 thisT -> thisT, O.Ldsflda

    rs <<| Instr("", op, OpField(thisT, fieldName))
    let f = Solve.getField menv thisT fieldName
    TypeSpec.Byref <| typeOfT f.FieldType

and emitRefRead ({ menv = menv } as env) ls rs e =
    let byrefT = emit env ls rs e
    let elemT =
        match byrefT with 
        | TypeSpec.Byref t -> t
        | _ -> failwithf "MRefRead(%A : %A)" e byrefT

    rs <<| ldind menv elemT
    elemT

and emitFieldAccess ({ menv = menv } as env) ls rs (this, fieldName) =
    // `.&` ... IFieldRef = O.Ldflda
    // `&.&` ... RFieldRef = O.Ldflda
    // `&.` ... RField = O.Ldfld
    // `.` ... IField

    // x.F.G.H
    // x.&F&.&G&.H

    let thisT, op =
        match this with
        | Choice1Of2 this -> emit env ls rs this, O.Ldfld
        | Choice2Of2 thisT -> thisT, O.Ldsfld

    rs <<| Instr("", op, OpField(thisT, fieldName))
    let f = Solve.getField menv thisT fieldName
    typeOfT f.FieldType

and emitArrayIndex ({ menv = menv } as env) ls rs (array, index) =
    let elemT =
        match emit env ls rs array with
        | TypeSpec.Array t -> t
        | _ -> failwith "ArrayIndex"
        
    if emit env ls rs index <> int32T then failwith "ArrayIndex"

    rs <<| ldelem menv elemT
    elemT

and emitMRefWrite ({ menv = menv } as env) ls rs (ref, value, cont) =
    let elemT =
        match emit env ls rs ref with
        | TypeSpec.Byref t -> t
        | _ -> failwith "MRefWrite"

    let valueT = emit env ls rs value
    if elemT <> valueT then failwith "MRefWrite"
    rs <<| stind menv valueT
    emit env ls rs cont