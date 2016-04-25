namespace Alpa

[<Measure>] type c32
[<Measure>] type c32ix
[<Measure>] type c16ix

type internal int32<[<Measure>] 'u> = int<'u>

[<Struct>]
type ValueTuple2<'T1,'T2> =
    val Item1: 'T1
    val Item2: 'T2
    new (item1, item2) = {
        Item1 = item1
        Item2 = item2
    }
    
[<Struct>]
type ValueTuple3<'T1,'T2,'T3> =
    [<DefaultValue(false)>]
    val mutable Item1: 'T1
    [<DefaultValue(false)>]
    val mutable Item2: 'T2
    [<DefaultValue(false)>]
    val mutable Item3: 'T3

[<Struct>]
type ValueTuple4<'T1,'T2,'T3,'T4> =
    [<DefaultValue(false)>]
    val mutable Item1: 'T1
    [<DefaultValue(false)>]
    val mutable Item2: 'T2
    [<DefaultValue(false)>]
    val mutable Item3: 'T3
    [<DefaultValue(false)>]
    val mutable Item4: 'T4

[<Struct>]
type Slice<'T when 'T : unmanaged> =
    val Start: nativeptr<'T>
    val Length: int32
    new (start, length) = {
        Start = start
        Length = length
    }

[<Struct>]
type Position =
    val Index: int32<c16ix>
    val Line: int32<c16ix>
    val Column: int32<c16ix>
    new (index, line, column) = {
        Index = index
        Line = line
        Column = column
    }

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
    /// Value = int (char Special);
    /// Value2 = CreatedInt32;
    | D
    
    /// received identifier;
    /// Value = int (char Special);
    /// Value2 = CreatedInt32;
    | Rid
    
    /// received operator;
    /// Value = int (char Special);
    /// Value2 = CreatedInt32;
    | Rop
    
    /// identifier;
    /// Value = 0;
    /// Value2 = Uncreated -> Name ..;
    | Id
    
    /// quoted identifier;
    /// Value = 0;
    /// Value2 = Uncreated -> Name ..;
    | Qid
    
    /// operator;
    /// Value = 0;
    /// Value2 = Uncreated -> Name ..;
    | Op
    
    /// quoted operator;
    /// Value = 0;
    /// Value2 = Uncreated -> Name ..;
    | Qop
    
    /// integer literal;
    /// Value = 0;
    /// Value2 = Uncreated  -> Bigint ..;
    /// |
    /// Value = 0           -> ..;
    /// Value2 = Uncreated  -> CreatedInt32;
    | I

    /// floating literal;
    /// Value = 0;
    /// Value2 = Uncreated -> Float(.., .., ..);
    /// |
    /// Value = 0           -> int ..;
    /// Value2 = Uncreated  -> CreatedInt32;
    | F
    
    /// character literal;
    /// Value = 0           -> '...';
    /// Value2 = Uncreated  -> CreatedInt32;
    | C

    /// string literal;
    /// Value = 0;
    /// Value2 = Uncreated -> String ..;
    | S

type TokenValue = 
    | Uncreated
    | CreatedInt32
    | Name of Symbol
    | Bigint of bigint
    | Float of bigint * bigint * bigint
    | String of Symbol

type Token =
    {
        TriviaStart: Position
        Start: Position
        Kind: TokenKind
        mutable _value: int
        mutable _value2: TokenValue
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
    
type Identifier = Token
type LongIdentifier = LongIdentifier of Identifier list * Identifier

type Pattern =
    | WildcardPattern // of ``_``: Keyword
    | LongIdentifierPattern of LongIdentifier

type LetHeader = LetHeader of Identifier * Pattern list
type Const = Token
type Expression =
    | ConstExpression of Const
    | LookupExpression of LongIdentifier
    | DotLookupExpression of Expression * LongIdentifier
    | ApplicationsExpression of Expression * Expression * Expression list
    | BlockExpression of Expression
    | SequentialExpression of Expression * Expression
    | LetExpression of LetHeader * Expression * Expression

namespace Alpa.IO

open System
open Alpa

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
        member x.Dispose() = x.dispose()
    