module Alpa.RegexLexer

open System.Collections.Generic
open System.Text.RegularExpressions

type Result<'T,'E> = Ok of 'T | Error of 'E

type Position = int
let emptyPosition = 0
let isEmptyPosition p = p = 0
type Source<'a> = {
    startPos: Position
    value: 'a
    endPos: Position
}
module Source =
    let Source s v e = { startPos = s; value = v; endPos = e }
    let VirtualSource value = Source emptyPosition value emptyPosition

    let isVirtualSource { startPos = s } = isEmptyPosition s
    let value { value = value } = value
    let startPos { startPos = p } = p
    let endPos { endPos = p } = p
    let map m { startPos = s; value = v; endPos = e } = Source s (m v) e
    let (<<-) x1 x2 =
        if isEmptyPosition x1 then x2
        elif isEmptyPosition x2 then x1
        else x1

    let (->>) x1 x2 =
        if isEmptyPosition x1 then x2
        elif isEmptyPosition x2 then x1
        else x2

    let range { startPos = s1; endPos = e1 } value { startPos = s2; endPos = e2 } =
        if isEmptyPosition s1 then Source s2 value e2
        elif isEmptyPosition s2 then Source s1 value e1
        else Source s1 value e2

[<Struct>]
type ValueResult<'T,'E> =
    val IsOk: bool
    val OkItem1OrDefault: 'T
    val ErrorItem1OrDefault: 'E
    new (result) = {
        IsOk = true
        OkItem1OrDefault = result
        ErrorItem1OrDefault = Unchecked.defaultof<_>
    }
    new (error) = {
        IsOk = false
        OkItem1OrDefault = Unchecked.defaultof<_>
        ErrorItem1OrDefault = error
    }
let ValueOk (result: 'T) = ValueResult<'T,'E> result
let ValueError (error: 'E) = ValueResult<'T,'E> error

type TokenData<'t,'r,'e> = TokenData of name: string * regex: 'r * (string -> ValueResult<'t, 'e>)
type LexData<'t,'r,'e> = {
    trivia: 'r
    keyword: TokenData<'t,'r,'e>
    custom: TokenData<'t,'r,'e> array
}
let makeTokenOrError n r f = TokenData(n, r, f)
let makeToken n r make = TokenData(n, r, ValueOk << make)
let makeTokenOfTable name table =
    let concat pred sep table =
        Seq.filter (fst >> pred) table
        |> Seq.sortByDescending fst
        |> Seq.map (fun (p: string, _) -> Regex.Escape(p).Replace("]", "\\]"))
        |> String.concat sep

    let chars = concat (String.length >> (=) 1) "" table
    let strings = concat (String.length >> (<>) 1) "|" table

    let regex = if String.length chars = 0 then strings else strings + "|[" + chars + "]"
    let map = Dictionary()
    for k, v in table do map.Add(k, v)

    makeToken name regex <| fun t -> map.[t]
    
let compile { trivia = trivia; keyword = keyword; custom = custom } =
    let r p = Regex(p, RegexOptions.Compiled ||| RegexOptions.CultureInvariant ||| RegexOptions.ExplicitCapture )
    let customR (TokenData(n, p, f)) = TokenData(n, r p, f)
    {
        trivia = r trivia
        keyword = customR keyword
        custom = Array.map customR custom
    }

let lex { trivia = trivia; keyword = keyword; custom = custom } source =
    let scanR (r: Regex) source i =
        let m = r.Match(source, i)
        if m.Success && m.Index = i then i + m.Length
        else -1
            
    let rs = ResizeArray()
    let mutable errorPosition = -1
    let mutable error = None

    let scanC (TokenData(_, r: Regex, f)) source i =
        let m = r.Match(source, i)
        if m.Success && m.Index = i then
            let r: ValueResult<_,_> = f m.Value
            if r.IsOk then
                let startPos = i
                let endPos = i + m.Length
                rs.Add(Source.Source startPos r.OkItem1OrDefault endPos)
                endPos
            else
                error <- Some r.ErrorItem1OrDefault
                -1
        else -1

    let rec skipTrivias i = match scanR trivia source i with -1 -> i | i -> skipTrivias i
        
    let rec scanToken i customI customs =
        if customI = Array.length customs then
            errorPosition <- i
            -1
        else
            match scanC customs.[customI] source i with
            | -1 -> scanToken i (customI + 1) customs
            | i' ->
                match scanC keyword source i with
                | -1 -> i'
                | i'' when i' <= i'' -> rs.RemoveAt(rs.Count-2); i''
                | _ -> rs.RemoveAt(rs.Count-1); i'

    let rec scan i =
        let i = skipTrivias i
        if String.length source <= i then Ok <| rs.ToArray()
        else
            let i = scanToken i 0 custom
            if i = -1 then
                let lastT = if rs.Count = 0 then None else Some rs.[rs.Count-1]
                Error(errorPosition, error, lastT)
            else scan i
    scan 0

let lexer data = lex <| compile data

