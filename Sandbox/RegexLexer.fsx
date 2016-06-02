module RegexLexer

open System.Collections.Generic
open System.Text.RegularExpressions

type Result<'T,'E> = Ok of 'T | Error of 'E
type Custom<'t,'r> = Custom of name: string * regex: 'r * (string -> 't)
type LexData<'t,'r> = {
    trivia: 'r
    keyword: Custom<'t,'r>
    custom: Custom<'t,'r> array
}
let custom n r f = Custom(n, r, f)
let table name table =
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

    custom name regex <| fun t -> map.[t]
    
let compile { trivia = trivia; keyword = keyword; custom = custom } =
    let r p = Regex(p, RegexOptions.Compiled ||| RegexOptions.CultureInvariant ||| RegexOptions.ExplicitCapture )
    let customR (Custom(n, p, f)) = Custom(n, r p, f)
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
    let mutable errorIndex = -1

    let scanC (Custom(_, r: Regex, f)) source i =
        let m = r.Match(source, i)
        if m.Success && m.Index = i then
            rs.Add(f m.Value)
            i + m.Length
        else -1

    let rec skipTrivias i = match scanR trivia source i with -1 -> i | i -> skipTrivias i
        
    let rec scanToken i customI customs =
        if customI = Array.length customs then
            errorIndex <- i
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
            if i = -1 then Error errorIndex
            else scan i
    scan 0

let lexer data = lex <| compile data

