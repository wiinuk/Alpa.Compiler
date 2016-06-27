module PolyTyping2.ILEmit
#load "PolyTyping2.Typing.fsx"
#r "./bin/debug/Alpa.Compiler.dll"
open Alpa.Emit
open Alpa.Emit.TypeSpec
open Alpa.Emit.PreDefinedTypes
open PolyTyping2
open PolyTyping2.Typing
open System.Reflection.Emit
open System

type E = PolyTyping2.Typing.TExp

type Type = TypeSpec
type LocalName = Var

type CLit =
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
    | LitNull of Type


let opMap = Map.empty

OpCodes.Calli
OpCodes.Call
OpCodes.Callvirt
OpCodes.Ret
OpCodes.Newobj
Seq.filter (fun (KeyValue(k,v: OpCode)) -> v.StackBehaviourPop = StackBehaviour.Varpop || v.StackBehaviourPush = StackBehaviour.Varpush) opMap
|> Seq.toArray

StackBehaviour.Pop0
StackBehaviour.Pop1
StackBehaviour.Pop1_pop1
StackBehaviour.Popi
StackBehaviour.Popi_pop1
StackBehaviour.Popi_popi
StackBehaviour.Popi_popi8
StackBehaviour.Popi_popi_popi
StackBehaviour.Popi_popr4
StackBehaviour.Popi_popr8
StackBehaviour.Popref
StackBehaviour.Popref_pop1
StackBehaviour.Popref_popi
StackBehaviour.Popref_popi_pop1
StackBehaviour.Popref_popi_popi
StackBehaviour.Popref_popi_popi8
StackBehaviour.Popref_popi_popr4
StackBehaviour.Popref_popi_popr8
StackBehaviour.Popref_popi_popref
StackBehaviour.Varpop

StackBehaviour.Push0
StackBehaviour.Push1
StackBehaviour.Push1_push1
StackBehaviour.Pushi
StackBehaviour.Pushi8
StackBehaviour.Pushr4
StackBehaviour.Pushr8
StackBehaviour.Pushref
StackBehaviour.Varpush

// OpCodeType.Annotation
OpCodeType.Macro
OpCodeType.Nternal
OpCodeType.Objmodel
OpCodeType.Prefix
OpCodeType.Primitive

FlowControl.Branch
FlowControl.Break
FlowControl.Call
FlowControl.Cond_Branch
FlowControl.Meta
FlowControl.Next
// FlowControl.Phi
FlowControl.Return
FlowControl.Throw

OperandType.ShortInlineVar
OperandType.InlineVar

type CExp =
    /// ex: 10i; 'c'; "test"; null[string]
    | Lit of CLit
    /// ex: a
    | LVar of LocalName
    /// ex: a: string in x
    | LetZero of LocalName * Type * CExp
    /// ex: a <- "" in x
    | Let of LocalName * CExp * CExp
    /// ex: a; b
    | Next of CExp * CExp

    /// ex: 'a'.[object::ToString]()
    | VCall of CExp * MethodRef * CExp list
    /// ex: object::ReferenceEquals(x, y);
    ///     string::Equals(string, string)();
    ///     "".Equals(string)(null)
    | ICall of CExp * Choice<string, MethodRef> * CExp list

    /// ex: upcast "" IEquatable`1(string)
    | Upcast of CExp * Type

    /// ex: [1; 2; 3]
    | NewArray of CExp * CExp list
    /// ex: []: int array
    | NewEmptyArray of Type

    /// ex: &a
    | Ref of CExp
    /// ex: *a
    | Deref of CExp

    /// ex: initobj &a
    | Initobj of CExp
    /// ex: newobj string('a', 10i)
    | Newobj of MethodRef * CExp list

type O = System.Reflection.Emit.OpCodes

let inRange l h x = l <= x && x <= h
let macroLdcI4 = function
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

let macroLdloc = function
    | 0s -> Instr("", O.Ldloc_0, OpNone)
    | 1s -> Instr("", O.Ldloc_1, OpNone)
    | 2s -> Instr("", O.Ldloc_2, OpNone)
    | 3s -> Instr("", O.Ldloc_3, OpNone)
    | n when inRange (int16 SByte.MinValue) (int16 SByte.MaxValue) n ->
        Instr("", O.Ldloc_S, OpI1(int8 n))
    | n -> Instr("", O.Ldloc, OpI2 n)

let macroStloc = function
    | 0s -> Instr("", O.Stloc_0, OpNone)
    | 1s -> Instr("", O.Stloc_1, OpNone)
    | 2s -> Instr("", O.Stloc_2, OpNone)
    | 3s -> Instr("", O.Stloc_3, OpNone)
    | n when inRange (int16 SByte.MinValue) (int16 SByte.MaxValue) n ->
        Instr("", O.Stloc_S, OpI1(int8 n))
    | n -> Instr("", O.Stloc, OpI2 n)

type C = System.TypeCode
let macroStelem = function
    | Array t ->
        Instr("", O.Ste)
    match getTypeCode t with
    | C.Boolean -> Instr("", O.stele)

let emitLit = function
    | LitB x ->
        if x then Instr("", O.Ldc_I4_1, OpNone), boolT
        else Instr("", O.Ldc_I4_0, OpNone), boolT

    | LitI1 x -> macroLdcI4(int32 x), int8T
    | LitI2 x -> macroLdcI4(int32 x), int16T
    | LitI4 x -> macroLdcI4 x, int32T
    | LitI8 x -> Instr("", O.Ldc_I8, OpI8 x), int64T

    | LitU1 x -> macroLdcI4(int32 x), uint8T
    | LitU2 x -> macroLdcI4(int32 x), uint16T
    | LitU4 x -> macroLdcI4(int32 x), uint32T
    | LitU8 x -> Instr("", O.Ldc_I8, OpI8(int64 x)), uint64T
    | LitC x -> macroLdcI4(int32 x), charT
    | LitF4 x -> Instr("", O.Ldc_R4, OpF4 x), float32T
    | LitF8 x -> Instr("", O.Ldc_R8, OpF8 x), float64T
    | LitS null -> Instr("", O.Ldnull, OpNone), stringT
    | LitS x -> Instr("", O.Ldstr, OpString x), stringT
    | LitNull t -> Instr("", O.Ldnull, OpNone), t

type LocalInfo = { i: int16; t: Type; using: bool }
let LocalInfo(i, t, u) = { i = i; t = t; using = u }

let rec appendRev ls rs =
    match ls with
    | [] -> rs
    | l::ls -> appendRev ls (l::rs)

type Env = {
    locals: Map<string, LocalInfo>
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

let rec go env ls (rs: ResizeArray<_>) = function
    | Lit x -> let i, t = emitLit x in rs.Add i; t
    | LVar v ->
        let { i = i; t = t } = Map.find v env.locals
        rs.Add <| macroLdloc i
        t

    | LetZero(v, vt, e) ->
        let { i = i } as l, env = updateLocals env ls v vt
        let t = go env ls rs e
        ls.[int32 i] <- { l with using = false }
        t

    | Let(v, init, e) ->
        let vt = go env ls rs init
        let { i = i } as l, env = updateLocals env ls v vt
        rs.Add <| macroStloc i
        let t = go env ls rs e
        ls.[int32 i] <- { l with using = false }
        t

    | Next(l, r) ->
        let t = go env ls rs l
        if t <> voidT then rs.Add <| Instr("", O.Pop, OpNone)
        go env ls rs r

    | VCall(this, m, args) ->
        go env ls rs this |> ignore
        for arg in args do go env ls rs arg |> ignore
        rs.Add <| Instr("", O.Callvirt, OpMethod m)
        match m with
        | MethodRef(_, _, Some(MethodTypeAnnotation(returnType=Some r))) -> r
        | _ ->
            match Solve.getMethodBase env.menv m with
            | :? System.Reflection.MethodInfo as m ->
                // TODO: typeparam
                typeOfT m.ReturnType

            | _ -> failwithf ""

    | ICall(this, m, args) ->
        let thisT = go env ls rs this
        let argsT = [for arg in args -> go env ls rs arg]

        let m =
            match m with
            | Choice2Of2 m -> m
            | Choice1Of2 name -> MethodRef(thisT, name, Some(MethodTypeAnnotation([], argsT, None)))

        rs.Add <| Instr("", O.Call, OpMethod m)

        match m with
        | MethodRef(_, _, Some(MethodTypeAnnotation(returnType=Some r))) -> r
        | _ ->
            match Solve.getMethodBase env.menv m with
            | :? System.Reflection.MethodInfo as m ->
                // TODO: typeparam
                typeOfT m.ReturnType

            | _ -> failwithf ""

    | Upcast(x, t) ->
        go env ls rs x |> ignore
        t

    | NewArray(x, xs) ->
        let rs' = ResizeArray()
        let t = go env ls rs' x
        let stElem = macroStelem t
        rs.Add <| Instr("", O.Newarr, OpType t)
        rs.Add <| Instr("", O.Dup, OpNone)
        rs.Add <| macroLdcI4 0
        rs.AddRange rs'
        rs.Add stElem

        for x in xs do
            rs.Add <| Instr("", O.Dup, OpNone)
            rs.Add <| macroLdcI4 (i + 1)
            let t' = go env ls rs x
            if t <> t' then failwith "NewArray"
            rs.Add stElem

        arrayT t

    | NewEmptyArray()

    | Ref(_) -> failwith "Not implemented yet"
    | Deref(_) -> failwith "Not implemented yet"
    | Initobj(_) -> failwith "Not implemented yet"
    | Newobj(_, _) -> failwith "Not implemented yet"

//let emitI4 = function
//    | -1 -> Instr("", O.Ldc_I4_M1, OpNone)
//    | 0 -> Instr("", O.Ldc_I4_0, OpNone)
//    | 1 -> Instr("", O.Ldc_I4_1, OpNone)
//    | 2 -> Instr("", O.Ldc_I4_2, OpNone)
//    | 3 -> Instr("", O.Ldc_I4_3, OpNone)
//    | 4 -> Instr("", O.Ldc_I4_4, OpNone)
//    | 5 -> Instr("", O.Ldc_I4_5, OpNone)
//    | 6 -> Instr("", O.Ldc_I4_6, OpNone)
//    | 7 -> Instr("", O.Ldc_I4_7, OpNone)
//    | 8 -> Instr("", O.Ldc_I4_8, OpNone)
//    | n when int System.SByte.MinValue <= n && n <= int System.SByte.MaxValue -> Instr("", O.Ldc_I4_S, OpI1 <| int8 n)
//    | n -> Instr("", O.Ldc_I4, OpI4 n)

type C = System.TypeCode

let emitDefault env t =
    match getTypeCode t with
    | C.Boolean -> Lit <| LitB false
    | C.Byte -> Lit <| LitU1 0uy
    | C.Char -> Lit <| LitC '\000'
    | C.Double -> Lit <| LitF8 0.0
    | C.Int16 -> Lit <| LitI2 0s
    | C.Int32 -> Lit <| LitI4 0
    | C.Int64 -> Lit <| LitI8 0L
    | C.SByte -> Lit <| LitI1 0y
    | C.Single -> Lit <| LitF4 0.0f
    | C.String -> Lit <| LitS null
    | C.UInt16 -> Lit <| LitU2 0us
    | C.UInt32 -> Lit <| LitU4 0u
    | C.UInt64 -> Lit <| LitU8 0UL
    | _ ->
        if (let t = solveType env t in t.IsValueType || t.IsGenericParameter)
        then LetZero("a", t, Next(Initobj(Ref(LVar "a")), Deref(LVar "a")))
        else Lit <| LitNull t

let bigintT = typeOf<bigint>
let rec tryPick (|Pick|_|) = function
    | Pick x -> Some x
    | Quotations.ExprShape.ShapeCombination(_,es) -> List.tryPick (tryPick (|Pick|_|)) es
    | Quotations.ExprShape.ShapeLambda(_,e) -> tryPick (|Pick|_|) e
    | Quotations.ExprShape.ShapeVar _ -> None

let tryFindMethodBase e =
    tryPick (function 
        | Quotations.Patterns.Call(_,m,_) -> Some(m :> System.Reflection.MethodBase)
        | Quotations.Patterns.NewObject(m,_) -> Some(m :> _)
        | _ -> None
    ) e

let methodOf e =
    match tryFindMethodBase e with
    | None -> failwithf "%A" e
    | Some m ->
        let mTypeArgs = if m.IsGenericMethod then [for t in m.GetGenericArguments() -> typeOfT t] else []
        let argTypes = [for p in m.GetParameters() -> typeOfT p.ParameterType]
        let at = MethodTypeAnnotation(mTypeArgs, argTypes, None)
        MethodRef(typeOfT m.DeclaringType, m.Name, Some at)

let inRange l h x = l <= x && x <= h
let int32Min = bigint(System.Int32.MinValue)
let int32Max = bigint(System.Int32.MaxValue)
let int64Min = bigint(System.Int64.MinValue)
let int64Max = bigint(System.Int64.MaxValue)
let uint64Min = bigint(System.UInt64.MinValue)
let uint64Max = bigint(System.UInt64.MaxValue)

let emitBigint env (n: bigint) = 
    if n.IsZero then emitDefault env bigintT
    elif n.IsOne then Call(methodOf <@ bigint.get_One @>, [])
    elif n = bigint.MinusOne then Call(methodOf <@ bigint.get_MinusOne @>, [])
    elif inRange int32Min int32Max n then
        Newobj(methodOf <@ bigint : int32 -> _ @>, [Lit <| LitI4(int32 n)])

    elif inRange int64Min int64Max n then
        Newobj(methodOf <@ bigint : int64 -> _ @>, [Lit <| LitI8(int64 n)])

    elif inRange uint64Min uint64Max n then
        Newobj(methodOf <@ bigint : uint64 -> _ @>, [Lit <| LitU8(uint64 n)])

    else
        let xs = NewArray [for x in n.ToByteArray() -> Lit(LitU1 x)]
        Newobj(methodOf <@ bigint : byte array -> _ @>, [xs])

let emitLit env = function
    | CharLit n -> Lit(LitC n)
    | IntegerLit n -> emitBigint env n
    | IntLit n -> Lit(LitI4 n)
    | FloatLit n -> Lit(LitF8 n)
    | StringLit s -> Lit(LitS s)

(*
a = 10;
f a =
    \() -> _ = a; ""
*)

let mutable ident = 0
let fleshId() = ident <- ident + 1; ident
let lambdaT x r = TypeSpec(FullName("Lambda`2", [], [], None), [x; r])
let emit = function
    | E.Lit l -> emitLit l

    // map (\x -> x + a) xs
    // type Closure@123 : Lambda`2(int32, int32) =
    //     let a: int32
    //     new (int32) => base(); this::a <- $0
    //     override Apply(int32): int32 => $0 + this::a
    // ;
    // map(int)().Apply[Lambda`2(Lambda`2(int32,int32),Lambda`2(List`1(int32),List`1(int32)))](new Closure@123(a)).Apply[Lambda`2(List`1(int32),List`1(int32))](xs)
    | E.Var(v, _) -> LVar v
    | E.Lam(v, vt, b) ->
        // closure = tuple, func
        let lamType tps =
            let name =
                match tps with
                | [] -> sprintf "Closure@%d" (fleshId())
                | _ -> sprintf "Closure@%d`%d" (fleshId()) (List.length tps)

            TopTypeDef(
                Some TypeAccess.Private,
                (name, []),
                {
                    kind = None
                    typeParams = tps
                    parent = Some <| lambdaT vt rt
                    impls = []
                    members = [
                        
                    ]
                }
            )

        Newobj()

    | E.App(_, _) -> failwith "Not implemented yet"
    | E.Ext(_, _, _) -> failwith "Not implemented yet"
    | E.Let(_, _, _, _) -> failwith "Not implemented yet"
    | E.LetRec(_, _) -> failwith "Not implemented yet"
    | E.Mat(_, _, _) -> failwith "Not implemented yet"
    | E.TypeDef(name, _, _) -> failwith "Not implemented yet"
    | E.InstanceDef(name, typeArgs, methodImpls, cont) -> failwith "Not implemented yet"