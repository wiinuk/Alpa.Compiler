[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Alpa.IO.CharStream

// using nativeptr
#nowarn "9"

open Alpa
open Alpa.IO
open System
open System.Runtime.InteropServices

module P = NativeInterop.NativePtr


let get xs i = P.get xs.buffer (int (xs.index + i))
let inline private (@) xs i = P.get xs.buffer (int (xs.index + i))

let char16ToChar32 (c: char) = int c * 1<c32>
let int32ToChar32 (c: int32) = c * 1<c32>
let stringLength (s: string) = s.Length * 1<c16ix>
let needSurrogatePair c = 0x10000<c32> <= c && c <= 0x10FFFF<c32>
let surrogatePairToChar32 (high: char) low = Char.ConvertToUtf32(high, low) * 1<c32>

let tabWidth = 4<c16ix>
let nextTabColumn column = (column - 1<_> + tabWidth - 1<_>) / tabWidth * tabWidth + 1<_>

let private advanceOf c xs =
    match c with
    | '\t' ->
        xs.column <- nextTabColumn xs.column
        xs.index <- xs.index + 1<_>

    | '\n' ->
        xs.line <- xs.line + 1<_>
        xs.column <- 1<_> 
        xs.index <- xs.index + 1<_>

    | _ ->
        xs.column <- xs.column + 1<_>
        xs.index <- xs.index + 1<_>

let private advanceN n xs =
    let rec aux i = if i < n then advanceOf (xs@(0<_>)) xs; aux(i + 1<_>) else ()
    aux 0<_>
    
let private advanceOfU c xs =
    if c = char16ToChar32 '\t' then
        xs.column <- nextTabColumn xs.column
        xs.index <- xs.index + 1<_>

    elif c = char16ToChar32 '\n' then
        xs.line <- xs.line + 1<_>
        xs.column <- 1<_>
        xs.index <- xs.index + 1<_>

    elif needSurrogatePair c then
        xs.column <- xs.column + 2<_>
        xs.index <- xs.index + 2<_>

    else
        xs.column <- xs.column + 1<_>
        xs.index <- xs.index + 1<_>

let ofString (s: string) =
    let once d =
        let isDisposed = ref false
        fun _ -> if not !isDisposed then (d(); isDisposed := true)

    let h = GCHandle.Alloc(s, GCHandleType.Pinned)
    let p = h.AddrOfPinnedObject() |> P.ofNativeInt<char>
    {
        buffer = p
        length = stringLength s
        index = 0<_>
        line = 1<_>
        column = 1<_>
        dispose = once <| fun _ -> h.Free()
    }
        
let position xs = Position(xs.index, xs.line, xs.column)

let canReadN n xs = xs.index + n <= xs.length
let canRead xs = canReadN 1<_> xs
    
let skipN n xs = canReadN n xs && (advanceN n xs; true)
let skip2 xs = skipN 2<_> xs
let skip xs = skipN 1<_> xs

let skipChar c xs = canRead xs && xs@(0<_>) = c && (advanceOf c xs; true)
let skipChar2 c1 c2 xs = canReadN 2<_> xs && xs@(0<_>) = c1 && xs@(1<_>) = c2 && (advanceOf c1 xs; advanceOf c2 xs; true)
        
let peek xs = if canRead xs then Nullable(xs@(0<_>)) else Nullable()
let peek2 xs =
    if canReadN 2<_> xs then ValueTuple3(Item1 = 2uy, Item2 = xs@(0<_>), Item3 = xs@(1<_>))
    elif canRead xs then ValueTuple3(Item1 = 1uy, Item2 = xs@(0<_>))
    else ValueTuple3()

let peekJust4 (r: byref<ValueTuple4<_,_,_,_>>) xs =
    if canReadN 4<_> xs then
        r.Item1 <- xs@(0<_>)
        r.Item2 <- xs@(1<_>)
        r.Item3 <- xs@(2<_>)
        r.Item4 <- xs@(3<_>)
        4<_>
    else
        0<c16ix>

let readNoneOf c xs =
    if not (canRead xs) then Nullable()
    else
        let c' = xs@(0<_>)
        if c <> c' then
            advanceOf c' xs
            Nullable c'
        else
            
            Nullable()

let peekU xs =
    let c1 = xs@(0<_>)
    let c2 = xs@(1<_>)
    if canReadN 2<_> xs && Char.IsHighSurrogate c1 && Char.IsLowSurrogate c2
    then Nullable(surrogatePairToChar32 c1 c2)
    elif canRead xs then Nullable(char16ToChar32 c1)
    else Nullable()

let satisfy p xs =
    if not (canRead xs) then Nullable()
    else
        let c = xs@(0<_>)
        if not (p c) then Nullable()
        else
            advanceOf c xs
            Nullable c

let satisfyU p xs =
    let r = peekU xs
    if not r.HasValue then Nullable()
    else
        let c = r.GetValueOrDefault()
        if not (p c) then Nullable()
        else
            ignore(advanceOfU c xs) 
            Nullable c

let skipManySatisfy p xs =
    let rec aux _ =
        let r = satisfy p xs
        if r.HasValue then aux()
        else ()
    aux()

let skipManySatisfyU p xs =
    let rec aux _ =
        let r = satisfyU p xs
        if r.HasValue then aux()
        else ()
    aux()
        
let skipMany1Satisfy p xs =
    let r = satisfy p xs
    if r.HasValue then
        skipManySatisfy p xs
        true
    else false

let manySatisfyChars p xs =
    let start = xs.index
    skipManySatisfy p xs
    Slice(P.add xs.buffer (int start), int (xs.index - start))

let skipManyChar c xs =
    let rec aux n = if skipChar c xs then aux(n+1) else n
    aux 0

let skipped p xs =
    let start = xs.index
    if p xs then Some(String(xs.buffer, int start, int (xs.index - start)))
    else None
        
let run p s =
    use xs = ofString s
    p xs

let (<--) (result: byref<ValueTuple3<_,_,_>>) xs =
    result.Item1 <- xs.index
    result.Item2 <- xs.line
    result.Item3 <- xs.column

let backtrack xs (state: byref<ValueTuple3<_,_,_>>) =
    xs.index <- state.Item1
    xs.line <- state.Item2
    xs.column <- state.Item3

let isEos xs = not (canRead xs)