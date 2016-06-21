module Alpa.IL.Parser

open System
open Alpa.Emit
open Alpa.ParserCombinator
open Alpa.RegexLexer
open Alpa.IO
open Alpa.IL.Lexer
open Alpa.IL.Lexer.SourceParsers

type internal OT = System.Reflection.Emit.OperandType

[<AutoOpen>]
module Specials =
    let d symbol = satisfyE ((=) symbol) <| RequireToken symbol
    let ``(`` = d LParen
    let ``)`` = d RParen
    let ``[`` = d LSBraket
    let ``]`` = d RSBraket
    let ``,`` = d Comma
    let ``.`` = d Dot
    let ``:`` = d Colon
    let ``+`` = d Plus
    let ``d=`` = d Equals
    let ``;``= d Semicolon
    let ``::`` = d DColon
    let graveAccent = d GraveAccent
    let dGraveAccent = d DGraveAccent
    let ``->`` = d HyphenGreaterThan
    let ``*`` = d Multiply
    let ``/`` = d Slash

    let ``mutable`` = d Mutable
    let ``new`` = d New
    let ``static`` = d Static
    let ``open`` = d Open
    let assembly = d Assembly
    let import = d Import
    let this = d This
    let ``module`` = d Module
    let ``as`` = d As
    let ``let`` = d Let
    let pinned = d Pinned

module K = Specials

/// ($p, ...) | ()
let tupleLike0 p = between ``(`` ``)`` (sepBy p ``,``)
/// ($p, ...)
let tupleLike1 p = between ``(`` ``)`` (sepBy1 p ``,``)
/// ($p, ...) | $p | ()
let tupleOrValueLike0 p = tupleLike0 p <|> (p |>> List.singleton)
/// ($p, ...) | $p
let tupleOrValueLike1 p = tupleLike1 p <|> (p |>> fun x -> x, [])

type PropKind = 
    /// p
    | Once
    /// p?
    | Optional
    /// p*
    | Many0
    /// p+
    | Many1

let isValidProp n = function
    | Once -> n = 1
    | Optional -> 0 <= n && n <= 1
    | Many0 -> true
    | Many1 -> 0 < n

let props reduce value props =
    let p = List.mapi (fun i (_,_,p) -> p |>> fun x -> x, i) props |> choice
    let map = Seq.map (fun (k,_,_) -> k, ref 0) props |> Seq.toArray
    let rec aux s map xs =
        let i' = xs.Index
        let u' = xs.UserState

        let r = p xs
        if r.Status = Primitives.Ok && i' < xs.Index then
            let r = r.Value
            let x, i = Source.value r
            let k, n = Array.get map i
            if isValidProp (!n+1) k then
                incr n
                let s = reduce (Source.value s) x
                aux (Source.VirtualSource s) map xs
            else
                let _,e,_ = List.item i props
                Reply((), e)
        else
            xs.Index <- i'
            xs.UserState <- u'
            let f (k, n) = isValidProp !n k |> not
            let i = Array.tryFindIndex f map
            match i with
            | None -> Reply s
            | Some i -> let _,e,_ = List.item i props in Reply((), e)

    fun xs ->
        let r = aux (Source.VirtualSource value) map xs
        for _,n in map do n := 0
        r


let tInt32 = satisfyMapE (function LInt32 _ -> true | _ -> false) (function LInt32(_,x) -> x | _ -> 0) RequireInt32Token

let tOp = satisfyMapE (function Op _ -> true | _ -> false) (function Op x -> x | _ -> O.Nop) RequireOpToken
let tBlob = satisfyMapE (function Blob _ -> true | _ -> false) (function Blob x -> x | _ -> null) RequireBlobToken

/// ex: Int32, List`2, 'type'
let name =
    satisfyMapE
        (function Id _ | SQString _ -> true | _ -> false)
        (function Id v | SQString v -> v | _ -> "")
        RequireName

let typeKind =
    satisfyMapE
        (function
            | TokenKind.Abstract
            | TokenKind.Interface
            | TokenKind.Open
            | TokenKind.Sealed -> true
            | _ -> false
        )
        (function
            | TokenKind.Abstract -> TypeKind.Abstract
            | TokenKind.Interface -> TypeKind.Interface
            | TokenKind.Open -> TypeKind.Open
            | TokenKind.Sealed -> TypeKind.Sealed
            | _ -> TypeKind.Sealed
        )
        RequireTypeKind
let typeKindOpt = opt typeKind

let namespaceRev = manyRev (name .>> ``.``)
let pathRev = pipe2 namespaceRev name <| fun ns n -> n, ns
let nestersRev = manyRev (name .>> ``/``)
let assemblyName = between ``[`` ``]`` pathRev |>> fun (x,xs) ->  List.rev (x::xs) |> String.concat "."

/// ex: [mscorlib]System.Diagnostics.Stopwatch+InternalTimers+LowTimer
let fullName = pipe4 (opt assemblyName) namespaceRev nestersRev name <| fun asmName nsRev nestRev name -> FullName(name, nestRev, nsRev, asmName)

open PreDefinedTypes

/// ex: (``T1), (``'t.1', ``'t.2')
let mTypeParams = tupleLike1(dGraveAccent >>. name) |>> function x,xs -> x::xs

/// ex: (`T1), (`'t.1', `'t.2')
let typeParams = tupleLike1(graveAccent >>. name) |>> function x,xs -> x::xs

/// ex: "[mscorlib]System.Diagnostics.Stopwatch+Internals+LowTimer`1(int32)" "`T" "`0" "``2" "base" "this"
let typeSpec, typeSpecRef = createParserForwardedToRef()
do
    let namedType = pipe2 fullName (opt (tupleLike1 typeSpec)) <| fun n vs -> TypeSpec(n, match vs with None -> [] | Some(v,vs) -> v::vs)

    let primType = 
        choiceHead RequireType [
            LParen, typeSpec .>> ``)``
            Int8, preturn int8T
            Int16, preturn int16T
            Int32, preturn int32T
            Int64, preturn int64T
            UInt8, preturn uint8T
            UInt16, preturn uint16T
            UInt32, preturn uint32T
            UInt64, preturn uint64T
            Float32, preturn float32T
            Float64, preturn float64T
            
            Void, preturn voidT
            Bool, preturn boolT
            Char, preturn charT
            String, preturn stringT
            Object, preturn objectT
            This, fun xs ->
                let { thisType = t } = xs.UserState
                match t with
                | Some t -> Reply(Source.VirtualSource t)
                | None -> Reply((), Errors.UnsolvedThisType)

            Base, fun xs ->
                let { baseType = t } = xs.UserState
                match t with
                | Some t -> Reply(Source.VirtualSource t)
                | None -> Reply((), Errors.UnsolvedBaseType)

            GraveAccent, ((name |>> TypeVar) <|> (tInt32 |>> TypeArgRef))
            DGraveAccent, ((name |>> MethodTypeVar) <|> (tInt32 |>> MethodTypeArgRef))
        ] <|> namedType

    let tupleType =
        let tuple2Name = FullName("*`2", [], [], None)
        let tuple3Name = FullName("**`3", [], [], None)
        let tuple4Name = FullName("***`4", [], [], None)
        let tuple5Name = FullName("****`5", [], [], None)
        let tuple6Name = FullName("*****`6", [], [], None)
        let tuple7Name = FullName("******`7", [], [], None)
        sepBy1 primType ``*`` |>> function
            | x, [] -> x
            | t, ts ->
                let ts = t::ts
                let name =
                    match List.length ts with
                    | 2 -> tuple2Name
                    | 3 -> tuple3Name
                    | 4 -> tuple4Name
                    | 5 -> tuple5Name
                    | 6 -> tuple6Name
                    | 7 -> tuple7Name
                    | n -> FullName(sprintf "%s`%d" (String.replicate (n-1) "*") n, [], [], None)
                TypeSpec(name, ts)

    let arrowType =
        let arrowName = FullName("->`2", [], [], None)
        let foldArrow = function
            | x, [] -> x
            | x, xs ->
                let rec aux l = function
                    | [] -> l
                    | r::rs -> TypeSpec(arrowName, [l; aux r rs])
                aux x xs

        sepBy1 tupleType ``->`` |>> foldArrow

    typeSpecRef := arrowType

#nowarn "9"
module Unsafe =
    module P = NativeInterop.NativePtr
    let reinterpret<'f,'t when 'f : unmanaged and 't : unmanaged> (x: 'f) =
        let p = P.stackalloc 1
        P.write p x
        P.read<'t>(P.ofNativeInt(P.toNativeInt p))

let unreachable<'a> : 'a = failwith "unreachable"

/// ex: ": int32"
let typing = ``:`` >>. typeSpec

/// ex: true, null, 'a', "", 10, 10 :> int64, 0xFFFFFFFF :> float32
let literal =
    let numericValue = satisfyE (function LInt32 _ | LInt64 _ | LFloat64 _ -> true | _ -> false) RequireLiteralToken

    let numericTypeSpec =
        satisfyMapE
            (function Int8 | Int16 | Int32 | Int64 | UInt8 | UInt16 | UInt32 | UInt64 | Float32 | Float64 -> true | _ -> false)
            (function 
                | Int8 -> I1
                | Int16 -> I2
                | Int32 -> I4
                | Int64 -> I8
                | UInt8 -> U1
                | UInt16 -> U2
                | UInt32 -> U4
                | UInt64 -> U8
                | Float32 -> F4
                | Float64 -> F8
                | _ -> I1
            ) RequireTypeSpecifier

    let typing = opt numericTypeSpec

    let int32BitsToSingle x = Unsafe.reinterpret<int32,float32> x

    let convInt32OrRaise isDecimal n = function
        | None -> Literal.I4 n
        | Some t ->
            match t with
            | I1 -> Literal.I1 <| Checked.int8 n
            | I2 -> Literal.I2 <| Checked.int16 n
            | I4 -> Literal.I4 n
            | I8 -> Literal.I8 <| int64 n
            | U1 -> Literal.U1 <| Checked.uint8 n
            | U2 -> Literal.U2 <| Checked.uint16 n
            | U4 -> if isDecimal then Literal.U4 <| Checked.uint32 n else Literal.U4 <| uint32 n
            | U8 -> if isDecimal then Literal.U8 <| Checked.uint64 n else Literal.U8 <| uint64 (uint32 n)

            | F4 -> if isDecimal then raise <| OverflowException() else Literal.F4 <| int32BitsToSingle n
            | F8 -> if isDecimal then raise <| OverflowException() else Literal.F8 <| BitConverter.Int64BitsToDouble(int64 (uint32 n))

    let convInt64OrRaise isDecimal n = function
        | None -> Literal.I8 n
        | Some t ->
            match t with
            | I1 -> Literal.I1 <| Checked.int8 n
            | I2 -> Literal.I2 <| Checked.int16 n
            | I4 -> Literal.I4 <| Checked.int32 n
            | I8 -> Literal.I8 n
            | U1 -> Literal.U1 <| Checked.uint8 n
            | U2 -> Literal.U2 <| Checked.uint16 n
            | U4 -> Literal.U4 <| Checked.uint32 n
            | U8 -> if isDecimal then Literal.U8 <| Checked.uint64 n else Literal.U8 <| uint64 n

            | F4 -> if isDecimal then raise <| OverflowException() else Literal.F4 <| int32BitsToSingle(Checked.int32 n)
            | F8 -> if isDecimal then raise <| OverflowException() else Literal.F8 <| BitConverter.Int64BitsToDouble n

    let convOrRaise v t =
        match v with
        | LInt32(isDecimal, n) -> convInt32OrRaise isDecimal n t
        | LInt64(isDecimal, n) -> convInt64OrRaise isDecimal n t
        | LFloat64 v ->
            match t with
            | None
            | Some F8 -> Literal.F8 v
            | Some F4 -> Literal.F4 <| single v
            | _ -> raise <| OverflowException()

        | _ -> unreachable

    let numericLiteral xs =
        let r1 = typing xs
        if r1.Status = Primitives.Ok then
            let r2 = numericValue xs
            if r2.Status = Primitives.Ok then
                let r1 = r1.Value
                let r2 = r2.Value
                try Reply(Source.range r1 (convOrRaise (Source.value r2) (Source.value r1)) r2) 
                with :? OverflowException -> Reply((), NumericRange)

            else Reply((), r2.Error)
        else Reply((), r1.Error)

    let simpleLiteral =
        satisfyMapE
            (function 
                | QString _ | True | False | Null -> true
                | SQString v -> v.Length = 1
                | _ -> false
            )
            (function
                | QString x -> Literal.String x
                | SQString x -> Literal.Char x.[0]
                | True -> Literal.Bool true
                | False -> Literal.Bool false
                | Null -> Literal.Null
                | _ -> Literal.Null
            )
            RequireLiteralToken

    simpleLiteral <|> numericLiteral
    
let parameter =
    (pipe2 name typing <| fun n t -> Parameter(Some n, t)) <|>
    (typeSpec |>> fun t -> Parameter(None, t))

let parameters = tupleLike0 parameter

let methodHead =
    pipe4 name (optDefault [] mTypeParams) parameters typing <| fun name mTypeParams ps ret -> MethodHead(name, mTypeParams, ps, Parameter(None, ret))

let opInteger t min max ofInt64 =
    satisfyMapE
        (function 
            | LInt32(_,x) -> min <= int64 x && int64 x <= max
            | LInt64(_,x) -> min <= x && x <= max
            | _ -> false
        )
        (function
            | LInt32(_,x) -> ofInt64(int64 x)
            | LInt64(_,x) -> ofInt64 x
            | _ -> OpNone
        )
        (RequireOperand(OpNumericType t))

let opI1 = opInteger I1 (int64 SByte.MinValue) (int64 SByte.MaxValue) (OpI1 << int8)
let opI2 = opInteger I2 (int64 Int16.MinValue) (int64 Int16.MaxValue) (OpI2 << int16)
let opI4 = opInteger I4 (int64 Int32.MinValue) (int64 Int32.MaxValue) (OpI4 << int32)
let opI8 =
    satisfyMapE
        (function LInt32 _ | LInt64 _ -> true | _ -> false)
        (function LInt32(_,x) -> OpI8 <| int64 x | LInt64(_,x) -> OpI8 x | _ -> OpNone)
        (RequireOperand(OpNumericType I8))

let opF4 =
    satisfyMapE
        (function LFloat64 _ -> true | _ -> false)
        (function LFloat64 x -> OpF4(single x) | _ -> OpNone)
        (RequireOperand(OpNumericType F4))

let opF8 =
    satisfyMapE
        (function LFloat64 _ -> true | _ -> false)
        (function LFloat64 x -> OpF8 x | _ -> OpNone)
        (RequireOperand(OpNumericType F8))

let opString =
    satisfyMapE
        (function QString _ -> true | _ -> false)
        (function QString x -> OpString x | _ -> OpNone)
        (RequireOperand OpStringType)

let opType = typeSpec |>> OpType

/// ex: System.Type::Delimiter
let opField = pipe3 typeSpec ``::`` name <| fun t _ n -> OpField(t, n)

let methodRef =
    let methodName = 
        choice [
            K.``new`` >>% ".ctor"
            K.``static`` >>. K.``new`` >>% ".cctor"
            name
        ]
    let signAnnot = pipe3 (tupleLike0 typeSpec) (opt (tupleLike0 typeSpec)) (opt typing) <| fun ts1 ts2 ret ->
        match ts2 with
        | None -> MethodTypeAnnotation([], ts1, ret)
        | Some ts2 -> MethodTypeAnnotation(ts1, ts2, ret)

    pipe4 typeSpec ``::`` methodName (opt signAnnot) <| fun parent _ name t -> MethodRef(parent, name, t)

let opMethod = methodRef |>> OpMethod

let instr =
    let label = optDefault "" (name .>> ``:``)
    let opNone = Reply <| Source.VirtualSource OpNone
    let operand t xs =
        match t with
        | OT.InlineNone -> opNone
        | OT.ShortInlineI -> opI1 xs
        | OT.ShortInlineVar -> opI1 xs
        | OT.InlineVar -> opI2 xs
        | OT.InlineI -> opI4 xs
        | OT.InlineI8 -> opI8 xs
        | OT.ShortInlineR -> opF4 xs
        | OT.InlineR -> opF8 xs
        | OT.InlineString -> opString xs
        | OT.InlineType -> opType xs
        | OT.InlineField -> opField xs
        | OT.InlineMethod -> opMethod xs

        | OT.InlineBrTarget
        | OT.ShortInlineBrTarget
        | OT.InlineSwitch
        | OT.InlineSig
        | OT.InlineTok
        | _ -> failwithf "not implemented"

    let p xs =
        let r1 = label xs
        if r1.Status <> Primitives.Ok then Reply((), r1.Error)
        else
            let r2 = tOp xs
            if r2.Status <> Primitives.Ok then Reply((), r2.Error)
            else
                let op = r2.Value
                let r3 = operand (Source.value op).OperandType xs
                if r3.Status <> Primitives.Ok then Reply((), r3.Error)
                else
                    let r1 = r1.Value
                    let r2 = r2.Value
                    let r3 = r3.Value
                    let l = Source.(<<-) (Source.(<<-) (Source.startPos r1) (Source.startPos r2)) (Source.startPos r3)
                    let r = Source.(->>) (Source.(->>) (Source.endPos r1) (Source.endPos r2)) (Source.endPos r3)

                    let instr = Instr(Source.value r1, Source.value op, Source.value  r3)
                    Reply(Source.Source l instr r)
    p
let typeAccess =
    satisfyMapE
        (function
            | Public
            | Private -> true
            | _ -> false
        )
        (function
            | Public -> TypeAccess.Public
            | Private -> TypeAccess.Private
            | _ -> TypeAccess.Public
        )
        RequireAccess

let typeAccessOpt = opt typeAccess

let nestedAccess =
    satisfyMapE
        (function
            | Public
            | Private
            
            | Internal
            | Protected
            | InternalAndProtected
            | InternalOrProtected -> true
            | _ -> false
        )
        (function
            | Public -> NestedAccess.Public
            | Private -> NestedAccess.Private
            
            | Internal -> NestedAccess.Assembly
            | Protected -> NestedAccess.Family
            | InternalAndProtected -> NestedAccess.FamilyAndAssembly
            | InternalOrProtected -> NestedAccess.FamilyOrAssembly
            | _ -> NestedAccess.Public
        )
        RequireAccess

let nestedAccessOpt = opt nestedAccess

let memberAccess =
    satisfyMapE
        (function
            | Public
            | Private
            
            | Internal
            | Protected
            | InternalAndProtected
            | InternalOrProtected 
            | PrivateScope -> true
            | _ -> false
        )
        (function
            | Public -> MemberAccess.Public
            | Private -> MemberAccess.Private
            
            | Internal -> MemberAccess.Assembly
            | Protected -> MemberAccess.Family
            | InternalAndProtected -> MemberAccess.FamilyAndAssembly
            | InternalOrProtected -> MemberAccess.FamilyOrAssembly
            | PrivateScope -> MemberAccess.PrivateScope
            | _ -> MemberAccess.Public
        )
        RequireAccess

let memberAccessOpt = opt memberAccess

let methodKind = K.``open`` >>% MethodKind.Open

let local = pipe2 (optBool K.pinned) typeSpec <| fun p s -> Local(p, s)
/// ex: let default (int32, pinned void*)
let locals = pipe3 K.``let`` tupleOrValueLike0 local
let methodBody = pipe2 locals (many1 instr) <| fun ls (x,xs) -> MethodBody(ls, x::xs)
let methodAttrs =
    props
        (fun (k, a) -> function Choice1Of2 k -> Some k, a | Choice2Of2 a -> k, Some a)
        (None, None)
        [
            Optional, DuplicatedAccess, memberAccess |>> Choice1Of2
            Optional, DuplicatedMethodKind, methodKind |>> Choice2Of2
        ]

let methodInfo = pipe3 methodHead ``d=`` methodBody <| fun h _ b -> MethodInfo(h, b)

let baseMethods = tupleLike0 methodRef
let baseMethodsOpt = optDefault [] baseMethods

let fieldAttrs =
    props
        (fun (m, a) -> function Choice1Of2 m -> m, a | Choice2Of2 a -> m, Some a)
        (false, None)
        [
            Optional, DuplicatedFieldKind, K.``mutable`` |>> (let x = Choice1Of2 true in fun _ -> x)
            Optional, DuplicatedAccess, memberAccess |>> Choice2Of2
        ]
let fieldTail make = pipe3 fieldAttrs name typing make
let literalTail make = 
    let defaultType = function
        | Literal.Null -> objectT
        | Literal.String _ -> stringT
        | Literal.Bool _ -> boolT
        | Literal.Char _ -> charT
        | Literal.F4 _ -> float32T
        | Literal.F8 _ -> float64T
        | Literal.I1 _ -> int8T
        | Literal.I2 _ -> int16T
        | Literal.I4 _ -> int32T
        | Literal.I8 _ -> int64T
        | Literal.U1 _ -> uint8T
        | Literal.U2 _ -> uint16T
        | Literal.U4 _ -> uint32T
        | Literal.U8 _ -> uint64T

    pipe5(memberAccessOpt, name, opt typing, ``d=``, literal, (fun a n t _ l ->
        let t =
            match t with
            | Some t -> t
            | None -> defaultType l
        make a n t l
    ))

let staticMemberTail =
    choice [
        fieldTail <| fun (m, a) n t -> Field(a, true, m, n, t)
        literalTail <| fun a n b c -> MemberDef.Literal(a, n, b, c)
        pipe2 memberAccessOpt methodInfo <| fun a m -> StaticMethodDef(a, m)
    ]
let instanceMemberTail =
    choice [
        pipe2 methodAttrs methodInfo <| fun (a, k) m -> MethodDef(a, None, k, m)
        fieldTail <| fun (m, a) n t -> Field(a, false, m, n, t)
    ]
let typeMember, typeMemberRef = createParserForwardedToRef()
let members = many typeMember

let extends = ``:`` >>. typeSpec
let implements = ``+`` >>. typeSpec

/// ex: type open MyLib.List`1 (T) : object + [mscorlib]System.IEquatable`1(T) = ...
let typeDefTail(access, kind, name, enterType, leaveType, make) =
    let make a k (n, ps, p) is ms =
        make a n {
            kind = k
            typeParams = ps
            parent = p
            impls = is
            members = ms
        }

    let enterType x s = enterType (Source.value x) s

    pipe5(
        access,
        kind,
        updateStateWith (tuple3 name (optDefault [] typeParams) (opt extends)) enterType,
        many implements,
        ``d=`` >>. members .>> updateState leaveType .>> ``;``,
        make
    )

let nestedTypeTail kind =
    let enter (n, ts, p) ({ nestersRev = nestRev; namespaceRev = nsRev } as s) =
        let name = FullName(n, nestRev, nsRev, None)
        { s with
            thisType = Some(TypeSpec(name, List.map TypeVar ts))
            baseType = match p with None -> Some objectT | p -> p
            nestersRev = n::nestRev
        }
    let leave ({ nestersRev = nestersRev } as s) =
        { s with
            thisType = None
            baseType = None
            nestersRev = match nestersRev with [] -> [] | _::ns -> ns
        }
    typeDefTail(nestedAccessOpt, kind, name, enter, leave, (fun a n t -> NestedType(a, n, t)))
    
do
    typeMemberRef :=
        choiceHead RequireTypeMember [
            Let, staticMemberTail
            Member, instanceMemberTail

            // ex: new (x: System.Int32) = ...
            New, pipe4 memberAccessOpt parameters ``d=`` methodBody <| fun a ps _ b -> CtorDef(a, ps, b)

            // ex: abstract AddRange (T) (xs: IEmumerable`1(T)) : void
            Abstract, pipe2 memberAccessOpt methodHead <| fun a m -> AbstractDef(a, m)

            Override, pipe3 baseMethodsOpt methodAttrs methodInfo <| fun ms (a, k) m ->
                MethodDef(a, Some(Override.Override ms), k, m)

            Type, nestedTypeTail typeKindOpt
            Module, nestedTypeTail (preturn (Some TypeKind.Static))

            Static, pipe5(K.``new``, ``(``, ``)``, ``d=``, methodBody, fun _ _ _ _ b -> CCtorDef b)
        ]
let typeName =
    let typeArg = graveAccent >>. name
    choice [
        pipe2 name (opt (tupleOrValueLike1 typeArg)) <| fun n vs ->
            n, match vs with None -> [] | Some(v,vs) -> v::vs

        sepBy1 typeArg ``*`` |>> function
            | x, [] -> x, []
            | t, ts ->
                let ts = t::ts
                let name =
                    match List.length ts with
                    | 2 -> "*`2"
                    | 3 -> "**`3"
                    | 4 -> "***`4"
                    | 5 -> "****`5"
                    | 6 -> "*****`6"
                    | 7 -> "******`7"
                    | n -> sprintf "%s`%d" (String.replicate (n-1) "*") n
                name, ts

        pipe3 typeArg ``->`` typeArg <| fun l _ r -> "->`2", [l;r]
    ]

/// integer = [System.Numerics]System.Numerics.BigInteger;;
/// `a -> `b = Fun`2(`a, `b);;
/// `a * `b = [mscorlib]System.Tuple`2(`a, `b)
let aliasTail = pipe3 typeName ``d=`` typeSpec <| fun (n,ts) _ td -> TopAliasDef(n,{ aTypeParams = ts; entity = td })

let topMember =
    let enterType ((name, nsRev), typeParams, parent) _ =
        let path = FullName(name, [], nsRev, None)
        {
            thisType = Some(TypeSpec(path, List.map TypeVar typeParams))
            baseType = match parent with None -> Some objectT | p -> p
            nestersRev = [name]
            namespaceRev = nsRev
        }
    let leaveType _ =
        {
            thisType = None
            baseType = None
            nestersRev = []
            namespaceRev = []
        }
    choiceHead RequireTopMember [
        Alias, aliasTail
        Type, typeDefTail(typeAccessOpt, typeKindOpt, pathRev, enterType, leaveType, (fun a n d -> TopTypeDef(a, n, d)))
        Module, typeDefTail(typeAccessOpt, preturn <| Some TypeKind.Static, pathRev, enterType, leaveType, (fun a n d -> TopTypeDef(a, n, d)))
    ]

// import [mscorlib] =
//     version = 4.0.0.0
//     public_key_token = b(b7 7a 5c 56 19 34 e0 89)

let path = pathRev |>> fun (x,xs) -> List.rev(x::xs) |> String.concat "."
let assembly = pipe2 K.assembly assemblyName <| fun _ n -> AssemblyDef n

let (!!) k =
    satisfyMapE
        (function Id t -> t = k | _ -> false)
        (function Id t -> t | _ -> "")
        <| RequireContexualKeyword k

let version = pipe5(!!"version", ``d=`` >>. tInt32 .>> ``,``, tInt32 .>> ``,``, tInt32 .>> ``,``, tInt32, (fun _ v1 v2 v3 v4 -> Version4(v1, v2, v3, v4)))
let publicKeyToken = pipe3 !!"public_key_token" ``d=`` tBlob <| fun _ _ blob -> blob

let culture = pipe3 !!"culture" ``d=`` name <| fun _ _ s -> s

let assemblyRefDecls =
    let reduce r = function
        | Choice1Of3 v -> { r with version = Some v }
        | Choice2Of3 t -> { r with publicKeyToken = Some t }
        | Choice3Of3 c -> { r with culture = Some c }

    let init = { name = ""; version = None; culture = None; publicKeyToken = None }
    props reduce init [
        Optional, DuplicateVersion, version |>> Choice1Of3
        Optional, DuplicatePublicKeyToken, publicKeyToken |>> Choice2Of3
        Optional, DuplicateCulture, culture |>> Choice3Of3
    ]

/// ex: import [System.Numerics] version = 4,0,0,0 public_key_token = B"b77a5c561934e089" as [numerics]
let assemblyImport =
    pipe4
        K.import
        assemblyName
        assemblyRefDecls
        (opt (!!"as" >>. assemblyName))
        (fun _ n r a -> AssemblyImport({ r with name = n }, a))

let moduleDef = pipe3 K.this K.``module`` path <| fun _ _ n -> n

/// ex: assembly MyAsm type Ns.A =; module B =; type T =;
let top = pipe4 assembly (many assemblyImport) (opt moduleDef) (many topMember) <| fun a rs m ds -> { assembly = a; imports = rs; moduleDef = m; topDefs = ds }

let initialState = {
    namespaceRev = []
    nestersRev = []
    thisType = None
    baseType = None
}
let parseWith p source =
    match lex source with
    | Error(i, e, lastT) -> Error(ScanError(i, e), lastT)
    | Ok ts ->
        let ts = Buffer.ofSeq ts
        match runWithState (p .>> eof) initialState ts with
        | Success x -> Ok <| Source.value x
        | Failure(e,_,lastT,_) -> Error(e, lastT)

let parse source = parseWith top source