namespace Alpa

[<Measure>] type c32
[<Measure>] type c32ix
[<Measure>] type c16ix

type internal int32<[<Measure>] 'u> = int<'u>

[<Struct; StructuredFormatDisplay "{StructuredFormatDisplay}">]
type ValueTuple2<'T1,'T2> =
    val Item1: 'T1
    val Item2: 'T2
    new (item1, item2) = {
        Item1 = item1
        Item2 = item2
    }
    member private x.StructuredFormatDisplay = sprintf "ValueTuple2(item1 = %A, item2 = %A)" x.Item1 x.Item2
    override x.ToString() = x.StructuredFormatDisplay

    
[<Struct; StructuredFormatDisplay "{StructuredFormatDisplay}">]
type ValueTuple3<'T1,'T2,'T3> =
    [<DefaultValue(false)>]
    val mutable Item1: 'T1
    [<DefaultValue(false)>]
    val mutable Item2: 'T2
    [<DefaultValue(false)>]
    val mutable Item3: 'T3

    member private x.StructuredFormatDisplay = sprintf "ValueTuple3(Item1 = %A, Item2 = %A, Item3 = %A)" x.Item1 x.Item2 x.Item3
    override x.ToString() = x.StructuredFormatDisplay

[<Struct; StructuredFormatDisplay "{StructuredFormatDisplay}">]
type ValueTuple4<'T1,'T2,'T3,'T4> =
    [<DefaultValue(false)>]
    val mutable Item1: 'T1
    [<DefaultValue(false)>]
    val mutable Item2: 'T2
    [<DefaultValue(false)>]
    val mutable Item3: 'T3
    [<DefaultValue(false)>]
    val mutable Item4: 'T4

    member private x.StructuredFormatDisplay = sprintf "ValueTuple4(Item1 = %A, Item2 = %A, Item3 = %A, Item4 = %A)" x.Item1 x.Item2 x.Item3 x.Item4
    override x.ToString() = x.StructuredFormatDisplay

[<Struct>]
type Slice<'T when 'T : unmanaged> =
    val Start: nativeptr<'T>
    val Length: int32
    new (start, length) = {
        Start = start
        Length = length
    }

[<Struct; StructuredFormatDisplay("{StructuredFormatDisplay}")>]
type Position =
    val Index: int32<c16ix>
    val Line: int32<c16ix>
    val Column: int32<c16ix>
    new (index, line, column) = {
        Index = index
        Line = line
        Column = column
    }
    member private x.StructuredFormatDisplay = sprintf "Position(index = %d, line = %d, column = %d)" x.Index x.Line x.Column
    override x.ToString() = x.StructuredFormatDisplay

type Symbol = string

type Special =
    | ``D,`` = ','
    | ``D;`` = ';'
    | ``D[`` = '['
    | ``D]`` = ']'
    | ``D{`` = '{'
    | ``D}`` = '}'
    | ``D(`` = '('
    | ``D)`` = ')'

    | ``O=`` = '='
    | ``O.`` = '.'
    | ``O:`` = ':'
    | ``O|`` = '|'

    | ``O->`` = 'a'
    | ``O<-`` = 'b'
    | ``O..`` = 'c'
    | ``O::`` = 'g'
    | ``O...`` = 'i'
    
    | I_ = '_'

    | Alias = 'A'
    | Case = 'B'
    | Class = 'C'
//    | In = 'D'
    | Type = 'E'
    | With = 'F'
    | Import = 'G'
    | Module = 'H'
    | For = 'I'
    | Where = 'J'
    | Let = 'K'

type TokenKind =
    /// delimiter;
    /// ex: "(" ")" ";";
    /// Value = int (char Special);
    /// Value2 = null;
    | D
    
    /// received identifier;
    /// ex: "type" "class" "module";
    /// Value = int (char Special);
    /// Value2 = null;
    | Rid
    
    /// received operator;
    /// ex: "=" "->" ":";
    /// Value = int (char Special);
    /// Value2 = null;
    | Rop
    
    /// identifier;
    /// ex: "a" "_123" "Test" "or";
    /// Value = 0;
    /// Value2 = box (Symbol ..);
    | Id
    
    /// quoted identifier;
    /// ex: "``++``" "`` id ! ``";
    /// Value = 0;
    /// Value2 = box (Symbol ..);
    | Qid
    
    /// operator;
    /// ex: "*" "!" "++";
    /// Value = 0;
    /// Value2 = box (Symbol ..);
    | Op
    
    /// quoted operator;
    /// ex: "`div`" "`mod`";
    /// Value = 0;
    /// Value2 = box (Symbol ..);
    | Qop
    
    /// integer literal;
    /// ex: "123" "0b11_00";
    /// Value = 0;
    /// Value2 = box(bigint ..);
    /// |
    /// Value = ..;
    /// Value2 = null;
    | I

    /// floating literal;
    /// ex: "0.1e-12_34" "123e12_34";
    /// Value = 0;
    /// Value2 = box(bigint .., bigint .., bigint ..);
    /// |
    /// Value = int ..;
    /// Value2 = null;
    | F
    
    /// character literal;
    /// ex: "'a'" "'\\u{20}'";
    /// Value = int '...';
    /// Value2 = null;
    | C

    /// string literal;
    /// ex: "\"a\"" "\"\\u{20}\"";
    /// Value = 0;
    /// Value2 = Symbol ..;
    | S

type TokenValue = obj
//    | CreatedInt32
//    | Bigint of bigint
//    | Float of bigint * bigint * bigint
//    | Symbol of Symbol

type Token =
    {
        TriviaStart: Position
        Start: Position
        Kind: TokenKind
        _value: int
        _value2: TokenValue
        End: Position
    }

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Token =
    let kind t = t.Kind
    let range t = t.Start.Index, t.End.Index

    let isR s t = 
        match t.Kind with
        | D 
        | Rop 
        | Rid -> LanguagePrimitives.EnumOfValue(char t._value) = (s: Special)
        | _ -> false

    let isI t = t.Kind = I
    let isF t = t.Kind = F
    let isC t = t.Kind = C
    let isS t = t.Kind = S

    let isId t =
        match t.Kind with
        | Id
        | Qid -> true
        | _ -> false

    let isOp t =
        match t.Kind with
        | Op
        | Qop -> true
        | _ -> false
    
namespace Alpa.IO

open System
open Alpa

type NativeBuffer<'T, [<Measure>] 'U when 'T : unmanaged> = {
    mutable items: nativeptr<'T>
    mutable capacity: int32<'U>
    mutable size: int32<'U>
    mutable freeItems: unit -> unit
}
    with
    override x.Finalize() = x.freeItems()
    interface IDisposable with
        member x.Dispose() =
            x.freeItems()
            System.GC.SuppressFinalize x

// using nativeptr
#nowarn "9"

module NativeBuffer =
    open System.Runtime.InteropServices
    module P = NativeInterop.NativePtr

    let alloc n = P.ofNativeInt<'a> <| Marshal.AllocHGlobal(sizeof<'a> * n)
    let free p = Marshal.FreeHGlobal(P.toNativeInt p)
    let nullptr<'a when 'a : unmanaged> = P.ofNativeInt<'a> 0n
    let copy xs ys size =
        let rec aux i =
            if i = size then ()
            else
                P.set ys i (P.get xs i)
                aux(i + 1)
        aux 0

    let freeOnce p =
        let isFree = ref false
        fun _ ->
            if !isFree then ()
            else
                free p
                isFree := true

    let newNativeBuffer capacity =
        let p = alloc(int capacity)
        {
            items = p
            capacity = capacity
            size = 0<_>
            freeItems = freeOnce p
        }

    let toSeq xs = seq { for i in 0..xs.size-1 -> P.get xs.items i }
    let add xs x =
        let extend xs =
            let newCapacity = xs.capacity + xs.capacity
            
            printfn "extend %A -> %A" xs.capacity newCapacity
            let ys = alloc (min 2146435071 (int newCapacity))
            
            copy xs.items ys (int xs.size)
            xs.freeItems()

            xs.items <- ys
            xs.capacity <- newCapacity
            xs.freeItems <- freeOnce ys

        let size = xs.size
        if xs.capacity = size then extend xs
            
        P.set xs.items (int size) x
        xs.size <- size + 1

    let get xs i = if 0 <= i && i < xs.size then Some(P.get xs.items i) else None
    let clear xs = xs.size <- 0<_>

type Buffer<'T> = {
    mutable items: array<'T>
    mutable size: int32
}
module Buffer =
    let newBuffer() = { items = Array.zeroCreate 4; size = 0 }

    let toSeq xs = seq { for i in 0..xs.size-1 -> xs.items.[i] }
    let add xs x =            
        let extend xs =
            let ys = Array.zeroCreate(min 2146435071 (xs.items.Length * 2))
            Array.Copy(xs.items, 0, ys, 0, xs.size)
            xs.items <- ys

        let size = xs.size
        if xs.items.Length = size then extend xs
            
        xs.items.[size] <- x
        xs.size <- size+1

    let get xs i = if 0 <= i && i < xs.size then Some xs.items.[i] else None

type CharStream = {
    buffer: nativeptr<char>
    length: int32<c16ix>
    mutable index: int32<c16ix>
    mutable line: int32<c16ix>
    mutable column: int32<c16ix>
    dispose: unit -> unit
}
    with
    override x.Finalize() = x.dispose()
    interface IDisposable with
        member x.Dispose() =
            x.dispose()
            System.GC.SuppressFinalize x
    