open System.Reflection
open System.Reflection.Emit
open System.Collections.Generic
open System
open Microsoft.FSharp.Quotations

type O = System.Reflection.Emit.OperandType

type MEnv = {
    Module : Module
    BaseModule : Module
    TypeArgs : Type array
    MethodTypeArgs : Type array
    Handlers : ExceptionHandlingClause array
}

type Stream = {
    mutable index : int
    items : byte array
}

let makeStream xs = {
    index = 0
    items = Seq.toArray xs
}

let canRead s = s.index < s.items.Length

let readU1 s = 
    let x = s.index
    s.index <- x + 1
    s.items.[x]

let readI1 s = readU1 s |> int8
let readI2 s = int16 (readU1 s) ||| (int16 (readU1 s) <<< 8)

let readI4 s = 
    let read s n = int (readU1 s) <<< n
    read s 0 ||| read s 8 ||| read s 16 ||| read s 24

let readI8 s = int64 (readI4 s) ||| (int64 (readI4 s) <<< 32)
let readF8 s = readI8 s |> BitConverter.Int64BitsToDouble
let readF4 s = BitConverter.ToSingle(readI4 s |> BitConverter.GetBytes, 0)


let envOfMethodBase (m : MethodBase) = 
    let t = m.DeclaringType
    {
        Module = m.Module
        BaseModule = t.BaseType.Module
        TypeArgs = 
            if t.IsGenericType then t.GetGenericArguments()
            else null

        MethodTypeArgs = 
            if m.IsGenericMethod then m.GetGenericArguments()
            else null

        Handlers = Seq.toArray <| m.GetMethodBody().ExceptionHandlingClauses
    }

let opMap = 
    let xs = 
        typeof<OpCodes>.GetFields()
        |> Seq.map (fun f -> f.GetValue null)
        |> Seq.choose (function :? OpCode as x -> Some x | _ -> None)
        |> Seq.map (fun x -> x.Value, x)
        |> dict
    Dictionary xs


let printTupleLike print (xs: #seq<_>) =
    use e = xs.GetEnumerator()
    printf "("
    if e.MoveNext() then
        print e.Current
        while e.MoveNext() do
            printf ", "
            print e.Current 
    printf ")"
    
let printString q x = 
    printf "%c" q
    for x in x do
        if x = q then printf "\\%c" q
        elif Char.IsLetterOrDigit x then printf "%c" x
        else printf "\\u%04x" <| int16 x
    printf "%c" q

let isIdStartOrContinue = function '_' | '`' -> true | c -> Char.IsLetterOrDigit c
let isIdStart = function '_' -> true | c -> Char.IsLetter c

let printId = function
    | "" -> printf "''"
    | s when isIdStart s.[0] && String.forall isIdStartOrContinue s -> printf "%s" s
    | s -> printString '\'' s

let rec printType (x: Type) = 
    printId x.Name
    if x.IsGenericType then printTupleLike printType <| x.GetGenericArguments()

let printMethod (m : MethodBase) = 
    printType m.DeclaringType
    printf "::"
    printId m.Name
    if m.IsGenericMethod then printTupleLike printType <| m.GetGenericArguments()
    else ()

    m.GetParameters() |> printTupleLike (fun p -> printType p.ParameterType)

    printf " : "
    let ret = 
        match m with
        | :? MethodInfo as x -> x.ReturnType
        | _ -> typeof<Void>
    printType ret

let printField (x: FieldInfo) = 
    printType x.DeclaringType
    printf "::"
    printId x.Name
    printf " : "
    printType x.FieldType

let printBr x = printf "@x%04X" x

let printOperand env s = 
    function 
    | O.InlineBrTarget -> printBr <| readI4 s + s.index
    | O.InlineField -> printField <| env.Module.ResolveField(readI4 s, env.TypeArgs, env.MethodTypeArgs)
    | O.InlineI -> printf "%d" <| readI4 s
    | O.InlineI8 -> printf "%dL" <| readI8 s
    | O.InlineMethod -> 
        let md = readI4 s
        try 
            env.Module.ResolveMethod(md, env.TypeArgs, env.MethodTypeArgs)
        with _ -> env.BaseModule.ResolveMethod(md, env.TypeArgs, env.MethodTypeArgs)
        |> printMethod
    | O.InlineNone -> ()
    | O.InlineR -> printf "%f" <| readF8 s
    | O.InlineSig -> printf "signature (%A)" <| env.Module.ResolveSignature(readI4 s)
    | O.InlineString -> printString '"' <| env.Module.ResolveString(readI4 s)
    | O.InlineSwitch -> 
        let count = readI4 s
        let offset = s.index + count * 4

        Seq.init count (fun _ -> offset + readI4 s)
        |> printTupleLike printBr

    | O.InlineTok -> 
        let tok = readI4 s
        env.Module.ResolveMember(tok, env.TypeArgs, env.MethodTypeArgs) |> function 
        | :? FieldInfo as x -> printField x
        | :? MethodBase as x -> printMethod x
        | :? Type as x -> printType x
        | _ -> printf "member(%06X)" tok

    | O.InlineType -> printType <| env.Module.ResolveType(readI4 s, env.TypeArgs, env.MethodTypeArgs)
    | O.InlineVar -> printf "%d" <| int32 (readI2 s)
    | O.ShortInlineBrTarget -> printBr <| int (readI1 s) + s.index
    | O.ShortInlineI -> printf "%dy" <| readI1 s
    | O.ShortInlineR -> printf "%ff" <| readF4 s
    | O.ShortInlineVar -> printf "%d" <| int32 (readU1 s)
    | _ -> failwith ""

let readOpValue s = 
    match readU1 s with
    | 0xFEuy -> (0xFEs <<< 8) ||| int16 (readU1 s)
    | v -> int16 v

type C = System.Reflection.ExceptionHandlingClauseOptions

let printIndent i = for _ in 1..i do printf "    "

let printBlockStart i { Handlers = hs } offset =
    let h =
        hs 
        |> Seq.tryFind (fun h ->
            h.TryOffset = offset ||
            h.HandlerOffset = offset ||
            (h.Flags = C.Filter && h.FilterOffset = offset)
        )
    match h with
    | None -> i
    | Some h when h.TryOffset = offset -> 
        printIndent i
        printfn "try"
        i + 1

    | Some h when h.HandlerOffset = offset -> 
        printIndent i
        match h.Flags with
        | C.Finally -> printfn "finally"
        | C.Fault -> printfn "fault"
        | C.Clause -> 
            printf "catch "
            printType h.CatchType
            printfn ""
        | C.Filter -> printfn "then"
        | _ -> failwith ""
        i + 1

    | Some _ -> 
        printIndent i
        printfn "filter"
        i + 1

let printBlockEnd i { Handlers = hs } offset = 
    let h =
        hs 
        |> Seq.tryFind (fun h -> 
           h.TryOffset + h.TryLength = offset ||
           h.HandlerOffset + h.HandlerLength = offset ||
           (h.Flags = C.Filter && h.HandlerOffset = offset)
        )
    match h with
    | None -> i
    | Some h when offset = h.HandlerOffset -> i - 1
    | Some _ -> 
        let i = i - 1
        printfn ""
        printIndent i
        printf ";"
        i

let printInstr i env s = 
    let offset = s.index
    let op = opMap.[readOpValue s]
    let i = printBlockStart i env offset
    printIndent i
    printBr offset
    printf " %s " op.Name
    printOperand env s op.OperandType
    printBlockEnd i env s.index

let printIL env s = 
    if not <| canRead s then ()
    else 
        let i = printInstr 0 env s
        
        let rec aux i = 
            if not <| canRead s then ()
            else 
                printfn ""
                let i = printInstr i env s
                aux i
        aux i

let printLocals (b: MethodBody) = 
    let vs = Seq.toArray b.LocalVariables
    match vs with
    | null | [||] -> ()
    | _ -> 
        printf "let "
        if not b.InitLocals then printf "noinit "
        vs
        |> printTupleLike (fun v ->
            if v.IsPinned then printf "pinned " else ()
            printType v.LocalType
        ) 
        printfn ""

let printMethodBase m = 
    let env = envOfMethodBase m
    let b = m.GetMethodBody()
    let xs = b.GetILAsByteArray()
    printLocals b
    printIL env (makeStream xs)

let rec tryPick (|Pick|_|) = 
    function 
    | Pick x -> Some x
    | ExprShape.ShapeCombination(_, xs) -> List.tryPick (tryPick (|Pick|_|)) xs
    | ExprShape.ShapeLambda(_, x) -> tryPick (|Pick|_|) x
    | ExprShape.ShapeVar _ -> None

let getMethod e = 
    tryPick (function 
        | Patterns.Call(_, m, _) -> m :> MethodBase |> Some
        | Patterns.NewObject(m, _) -> m :> MethodBase |> Some
        | Patterns.PropertyGet(_, p, _) -> p.GetGetMethod() :> MethodBase |> Some
        | Patterns.PropertySet(_, p, _, _) -> p.GetSetMethod() :> MethodBase |> Some
        | _ -> None
    ) e
    |> Option.get

let print e = getMethod e |> printMethodBase; printfn ""
let x() = [|20n; 30n|]
let app f x = f x

let tryf() = try 1 / 0 with :? DivideByZeroException -> 0

// print <@ let mutable x = ResizeArray.Enumerator() in x.MoveNext() @>


let y() = [|1s;2s|]
print <@ y @>

try print <@ tryf @>
with e -> printfn "%A" e


type Pair<'a,'b> = struct
    val mutable Key: 'a
    val mutable Value: 'b
end
type T =
    static member F(x: Pair<_,_> byref) =
        let v = &x.Value
        v

printMethodBase <| typeof<T>.GetMethod("F")

open System.Linq.Expressions
type B = System.Linq.Expressions.MemberBindingType
type N = System.Linq.Expressions.ExpressionType
type E = System.Linq.Expressions.Expression

let rec memberBindingExpressions (m: MemberBinding) =
    match m.BindingType with
    | B.Assignment -> let m = m :?> MemberAssignment in Seq.singleton m.Expression
    | B.MemberBinding -> let m = m :?> MemberMemberBinding in Seq.collect memberBindingExpressions m.Bindings
    | B.ListBinding -> let m = m :?> MemberListBinding in m.Initializers |> Seq.collect (fun i -> i.Arguments)
    | _ -> Seq.empty

let paramExprsToExprs (xs: ParameterExpression seq) : Expression seq = unbox(box xs)
let objToSeq = function null -> Seq.empty | x -> upcast [|x|]
let staticOrInstance this xs = if isNull this then xs else seq { yield this; yield! xs }

let (|Parameter|Lambda|Combination|) (e: Expression) =
    match e.NodeType with
    | N.Add
    | N.AddChecked
    | N.And
    | N.AndAlso
    | N.ArrayIndex
    | N.Coalesce
    | N.Divide
    | N.Equal
    | N.ExclusiveOr
    | N.GreaterThan
    | N.GreaterThanOrEqual
    | N.LeftShift
    | N.LessThan
    | N.LessThanOrEqual
    | N.Modulo
    | N.Multiply
    | N.MultiplyChecked
    | N.NotEqual
    | N.Or
    | N.OrElse
    | N.Power
    | N.RightShift
    | N.Subtract
    | N.SubtractChecked
    | N.Assign
    | N.AddAssign
    | N.AndAssign
    | N.DivideAssign
    | N.ExclusiveOrAssign
    | N.LeftShiftAssign
    | N.ModuloAssign
    | N.MultiplyAssign
    | N.OrAssign
    | N.PowerAssign
    | N.RightShiftAssign
    | N.SubtractAssign
    | N.AddAssignChecked
    | N.MultiplyAssignChecked
    | N.SubtractAssignChecked ->
        let e = e :?> BinaryExpression
        Combination(box e, [|e.Left; e.Right|] :> _ seq)

    | N.ArrayLength
    | N.Convert
    | N.ConvertChecked
    | N.Negate
    | N.UnaryPlus
    | N.NegateChecked
    | N.Not
    | N.Quote
    | N.TypeAs
    | N.Decrement
    | N.Increment
    | N.Throw
    | N.Unbox
    | N.PreIncrementAssign
    | N.PreDecrementAssign
    | N.PostIncrementAssign
    | N.PostDecrementAssign
    | N.OnesComplement
    | N.IsTrue
    | N.IsFalse ->
        let e = e :?> UnaryExpression
        Combination(box e, upcast [|e.Operand|])

    | N.Call ->
        let e = e :?> MethodCallExpression
        Combination(box e, staticOrInstance e.Object e.Arguments)

    | N.Conditional ->
        let ce = e :?> ConditionalExpression
        Combination(box ce, upcast [|ce.Test; ce.IfTrue; ce.IfFalse|])

    | N.Constant
    | N.DebugInfo
    | N.Default
    | N.Extension -> Combination(box e, Seq.empty)
    
    | N.Parameter -> Parameter(e :?> ParameterExpression)
    | N.Invoke ->
        let e = e :?> InvocationExpression
        Combination(box e, seq { yield e.Expression; yield! e.Arguments })

    | N.Lambda -> Lambda(e :?> LambdaExpression)
    | N.ListInit ->
        let e = e :?> ListInitExpression
        let xs = seq {
            yield e.NewExpression :> E
            for i in e.Initializers do yield! i.Arguments
        }
        Combination(box e, xs)

    | N.MemberAccess ->
        let e = e :?> MemberExpression
        Combination(box e, upcast [| e.Expression |])

    | N.MemberInit ->
        let e = e :?> MemberInitExpression
        let xs = seq {
            yield e.NewExpression :> E
            for b in e.Bindings do yield! memberBindingExpressions b
        }
        Combination(box e, xs)

    | N.New ->
        let e = e :?> NewExpression
        Combination(box e, upcast e.Arguments)

    | N.NewArrayInit
    | N.NewArrayBounds ->
        let e = e :?> NewArrayExpression
        Combination(box e, upcast e.Expressions)

    | N.TypeIs
    | N.TypeEqual ->
        let e = e :?> TypeBinaryExpression
        Combination(box e, upcast [| e.Expression |])

    | N.Block ->
        let e = e :?> BlockExpression
        let xs = seq {
            yield! paramExprsToExprs e.Variables
            yield! e.Expressions
            yield e.Result
        }
        Combination(box e, xs)

    | N.Dynamic ->
        let e = e :?> DynamicExpression
        Combination(box e, upcast e.Arguments)

    | N.Goto ->
        let e = e :?> GotoExpression
        Combination(box e, objToSeq e.Value)

    | N.Index ->
        let e = e :?> IndexExpression
        Combination(box e, staticOrInstance e.Object e.Arguments)

    | N.Label ->
        let e = e :?> LabelExpression
        Combination(box e, objToSeq e.DefaultValue)

    | N.RuntimeVariables ->
        let e = e :?> RuntimeVariablesExpression
        Combination(box e, paramExprsToExprs e.Variables)

    | N.Loop ->
        let e = e :?> LoopExpression
        Combination(box e, upcast [|e.Body|])

    | N.Switch ->
        let e = e :?> SwitchExpression
        let xs = seq {
            yield e.SwitchValue 
            for c in e.Cases do
                yield! c.TestValues
                yield c.Body
            yield! objToSeq e.DefaultBody
        }
        Combination(box e, xs)

    | N.Try ->
        let e = e :?> TryExpression
        let xs = seq {
            yield e.Body
            yield! objToSeq e.Fault
            for c in e.Handlers do
                yield upcast c.Variable
                yield c.Filter
                yield c.Body
            yield! objToSeq e.Finally
        }
        Combination(box e, xs)

    | _ -> failwith ""

let rec tryPickL (|Pick|_|) = function
    | Pick x -> Some x
    | Combination(_, xs) -> Seq.tryPick (tryPickL (|Pick|_|)) xs
    | Lambda l -> Seq.tryPick (tryPickL (|Pick|_|)) l.Parameters
    | Parameter _ -> None


let getMethodL (e: Expression) =
    tryPickL (function
        | :? MethodCallExpression as e -> Some(e.Method :> System.Reflection.MethodBase)
        | :? NewExpression as e -> Some(e.Constructor :> _)
        | _ -> None
    ) e

getMethodL (E.Call(typeof<string>.GetMethod("Copy"), E.Constant("abc")))