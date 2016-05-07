module Alpa.Lexer

open Alpa
open Alpa.Token
open Alpa.IO
open Alpa.IO.Buffer
open Alpa.IO.CharStream
open System

type internal U = System.Globalization.UnicodeCategory


let charRange l h c = l <= c && c <= h
let (|AsciiBinary|) = function '0' | '1' -> true | _ -> false
let (|AsciiOctal|) c = charRange '0' '7' c
let (|AsciiDecimal|) c = charRange '0' '9' c
let (|AsciiHex|) c = charRange '0' '9' c || charRange 'a' 'f' c || charRange 'A' 'F' c
let (|Whitespace|) = function
    | ' '
    | '\n'
    | '\r'
    | '\t'
    | '\v'
    | '\f'
    | '\u0085' // NEXT LINE (NEL)
    | '\u00A0' // NO-BREAK SPACE
    | '\u1680' // OGHAM SPACE MARK
    | '\u2000' // EN QUAD
    | '\u2001' // EM QUAD
    | '\u2002' // EN SPACE
    | '\u2003' // EM SPACE
    | '\u2004' // THREE-PER-EM SPACE
    | '\u2005' // FOUR-PER-EM SPACE
    | '\u2006' // SIX-PER-EM SPACE
    | '\u2007' // FIGURE SPACE
    | '\u2008' // PUNCTUATION SPACE
    | '\u2009' // THIN SPACE
    | '\u200A' // HAIR SPACE
    | '\u2028' // LINE SEPARATOR
    | '\u2029' // PARAGRAPH SEPARATOR
    | '\u202F' // NARROW NO-BREAK SPACE
    | '\u205F' // MEDIUM MATHEMATICAL SPACE
    | '\u3000' // IDEOGRAPHIC SPACE

    | '\uFFFF' // Noncharacter (Byte Order Mark)

        -> true
    | _ -> false
    
let (|FloatingPointE|) = function 'e' | 'E' -> true | _ -> false
let (|Delimiter|) = function
    | ',' | ';' | '[' | ']' | '{' | '}' | '(' | ')' -> true
    | _ -> false
    
/// '_' | Uppercase letter (Lu) | Lowercase letter (Ll) | Titlecase letter (Lt) | Modifier letter (Lm) | Other letter (Lo)
let (|IdStart|) = function '_' -> true | c -> Char.IsLetter c

let (|IdStartU|) x =
    if needSurrogatePair x then Char.IsLetter(Char.ConvertFromUtf32(int x), 0)
    else (|IdStart|) (char x)

/// `IdStart` | '\'' | '-' | '?' | '!' | Non-spacing mark (Mn) | Combining spacing mark (Mc) | Decimal number (Nd) | Connector punctuation (Pc)
let (|IdContinue|) = function
    | '_' | '\'' | '-' | '?' | '!' -> true
    | c ->
        Char.IsLetterOrDigit c ||
            match Char.GetUnicodeCategory c with
            | U.NonSpacingMark
            | U.SpacingCombiningMark
            | U.ConnectorPunctuation -> true
            | _ -> false
            
let (|IdContinueU|) x =
    if needSurrogatePair x then
        let s = Char.ConvertFromUtf32(int x)
        Char.IsLetterOrDigit(s, 0) ||
            match Char.GetUnicodeCategory(s, 0) with
            | U.NonSpacingMark
            | U.SpacingCombiningMark
            | U.ConnectorPunctuation -> true
            | _ -> false

    else (|IdContinue|) (char x)

let (|Op|) = function
    | '!' | '%' | '&' | '*' | '+' | '-' | '.' | '/' | ':' | '<' | '=' | '>' | '?' | '@' | '\\' | '^' | '|' | '~' -> true
    | c -> '\u007F' < c && (Char.IsSymbol c || Char.IsPunctuation c)

let (|OpU|) x =
    if needSurrogatePair x then 
        let s = Char.ConvertFromUtf32(int x)
        Char.IsSymbol(s, 0) ||
            Char.IsPunctuation(s, 0)

    else (|Op|) (char x)

let (|HighSurrogate|) c = Char.IsHighSurrogate c
let (|LowSurrogate|) c = Char.IsLowSurrogate c
    
[<AutoOpen>]
module Specials =
    
    /// '→', '\u2192', "RIGHTWARDS ARROW", UnicodeCategory.MathSymbol
    let rightwardsArrow = "\u2192"

    /// '←', '\u2190', "LEFTWARDS ARROW", UnicodeCategory.MathSymbol
    let leftwardsArrow = "\u2190"

    /// '‥', '\u2025', "TWO DOT LEADER", UnicodeCategory.OtherPunctuation
    let twoDotLeader = "\u2025"

    /// '∷', '\u2237', "PROPORTION", UnicodeCategory.MathSymbol
    let proportion = "\u2237"

    /// '…', '\u2026', "HORIZONTAL ELLIPSIS", UnicodeCategory.OtherPunctuation
    let horizontalEllipsis = "\u2026"

let receivedNames =
    let xs = System.Collections.Generic.Dictionary()

    xs.Add("_", Special.``I_``)
    xs.Add("alias", Special.Alias)
    xs.Add("case", Special.Case)
    xs.Add("class", Special.Class)
//    xs.Add("in", Special.In)
    xs.Add("type", Special.Type)
    xs.Add("with", Special.With)
    xs.Add("import", Special.Import)
    xs.Add("module", Special.Module)
    xs.Add("for", Special.For)
    xs.Add("where", Special.Where)
    xs.Add("let", Special.Let)

    xs.Add("=", Special.``O=``)
    xs.Add("->", Special.``O->``)
    xs.Add(rightwardsArrow, Special.``O->``)
    xs.Add("<-", Special.``O<-``)
    xs.Add(leftwardsArrow, Special.``O<-``)
    xs.Add(".", Special.``O.``)
    xs.Add(":", Special.``O:``)
    xs.Add("::", Special.``O::``)
    xs.Add(proportion, Special.``O::``) 
    xs.Add("|", Special.``O|``)
    xs.Add("..", Special.``O..``)
    xs.Add(twoDotLeader, Special.``O..``) 
    xs.Add("...", Special.``O...``)
    xs.Add(horizontalEllipsis, Special.``O...``) 
    xs

let digits1 isDigit charToInteger carry xs =
    let c = satisfy isDigit xs
    if not c.HasValue then Nullable()
    else
        let mutable n = charToInteger(c.GetValueOrDefault())
        let mutable d = Nullable()
        while
            (
                skipManyChar '_' xs |> ignore
                d <- satisfy isDigit xs
                d.HasValue
            )
            do n <- carry n (charToInteger(d.GetValueOrDefault()))

        Nullable n
    
let hexadecimalDigits1 xs =
    digits1 
        (|AsciiHex|) 
        (fun c -> bigint((int c &&& 15) + (int c >>> 6) * 9))
        (fun n d -> (n <<< 4) + d)
        xs

let decimalDigits1 xs =
    digits1
        (|AsciiDecimal|)
        (fun c -> bigint(int c - int '0'))
        (fun n d -> n * 10I + d)
        xs

let octalDigits1 xs =
    digits1
        (|AsciiOctal|)
        (fun c -> bigint(int c - int '0'))
        (fun n d -> (n <<< 3) + d)
        xs

let binaryDigits1 xs =
    digits1
        (|AsciiBinary|)
        (fun c -> bigint(int c - int '0'))
        (fun n d -> (n <<< 1) + d)
        xs
        
let int32Min = bigint Int32.MinValue
let int32Max = bigint Int32.MaxValue
let inInt32 n = int32Min <= n && n <= int32Max

let makeIntegerLiteral (result: byref<ValueTuple3<_,_,_>>) n =
    result.Item1 <- I
    if inInt32 n then
        result.Item2 <- int n
        result.Item3 <- null
    else
        result.Item2 <- 0
        result.Item3 <- box n
    true

let hexadecimalLiteral (result: byref<_>) xs =
    let r = peek2 xs
    match r.Item1, r.Item2, r.Item3 with
    | 2uy, '0', ('x' | 'X') ->
        skip2 xs |> ignore
        let n = hexadecimalDigits1 xs
        n.HasValue &&
        makeIntegerLiteral &result (n.GetValueOrDefault())

    | _ -> false
    
let octalLiteral (result: byref<_>) xs =
    let r = peek2 xs
    match r.Item1, r.Item2, r.Item3 with
    | 2uy, '0', ('o' | 'O') ->
        skip2 xs |> ignore
        let n = octalDigits1 xs
        n.HasValue &&
        makeIntegerLiteral &result (n.GetValueOrDefault())

    | _ -> false

let binaryLiteral (result: byref<_>) xs =
    let r = peek2 xs
    match r.Item1, r.Item2, r.Item3 with
    | 2uy, '0', ('b' | 'B') ->
        skip2 xs |> ignore
        let n = binaryDigits1 xs
        n.HasValue &&
        makeIntegerLiteral &result (n.GetValueOrDefault())

    | _ -> false

let makeFloatingPointLiteral (result: byref<ValueTuple3<_,_,_>>) n (f: bigint) (e: bigint) =
    result.Item1 <- F
    if f.IsZero && e.IsZero && inInt32 n then
        result.Item2 <- int n
        result.Item3 <- null
    else
        result.Item2 <- 0
        result.Item3 <- box (n, f, e)

let decimalExponent (result: byref<_>) n f xs =
    let e = satisfy (|FloatingPointE|) xs
    e.HasValue &&

    let s = satisfy (function '+' | '-' -> true | _ -> false) xs

    let r = decimalDigits1 xs
    r.HasValue &&
    
    let sign = if s.HasValue && s.GetValueOrDefault() = '-' then -1I else 1I
    let e = r.GetValueOrDefault() * sign
    makeFloatingPointLiteral &result n f e
    true

let decimalFractionSeqExponent (result: byref<_>) n xs =
    skipChar '.' xs &&

    let r = decimalDigits1 xs
    r.HasValue &&

    let f = r.GetValueOrDefault()
    let r = peek xs

    match r.HasValue, r.GetValueOrDefault() with
    | true, FloatingPointE true -> decimalExponent &result n f xs
    | _ -> makeFloatingPointLiteral &result n f 0I; true
                 
let decimalIntegerOrFloatingPointLiteral (result: byref<_>) xs =
    let r = decimalDigits1 xs
    r.HasValue &&

    let n = r.GetValueOrDefault()
    let r = peek xs
    match r.HasValue, r.GetValueOrDefault() with
    | true, '.' -> decimalFractionSeqExponent &result n xs
    | true, FloatingPointE true -> decimalExponent &result n 0I xs
    | _ -> makeIntegerLiteral &result n

let delimiter (result: byref<ValueTuple3<_,_,_>>) xs =
    let r = satisfy (|Delimiter|) xs
    r.HasValue && (
        let c = r.GetValueOrDefault()
        result.Item1 <- D
        result.Item2 <- int c
        result.Item3 <- null
        true
    )

let nameOrReceived (head, tail, nameTag, receivedTag) (result: byref<ValueTuple3<_,_,_>>) xs =
    let index = xs.index
    let r = satisfyU head xs
    r.HasValue && (
        skipManySatisfyU tail xs
        let s = String(xs.buffer, int index, int (xs.index - index))
        let mutable r = Unchecked.defaultof<_>
        if receivedNames.TryGetValue(s, &r) then
            result.Item1 <- receivedTag
            result.Item2 <- int (LanguagePrimitives.EnumToValue r : char)
            result.Item3 <- null
        else
            result.Item1 <- nameTag
            result.Item2 <- 0
            result.Item3 <- s :> obj
        true
    )

let idOrReceived (result: byref<_>) xs = nameOrReceived ((|IdStartU|), (|IdContinueU|), Id, Rid) &result xs
let opOrReceived (result: byref<_>) xs = nameOrReceived ((|OpU|), (|OpU|), Op, Rop) &result xs

let surrogateName (result: byref<ValueTuple3<_,_,_>>) xs =
    let r = peekU xs
    r.HasValue &&
        match r.GetValueOrDefault() with
        | IdStartU true -> idOrReceived &result xs
        | OpU true -> opOrReceived &result xs
        | _ -> false
        
let unicodeEscape (result: byref<_>) xs =
    skipChar2 'u' '{' xs &&

    let n = hexadecimalDigits1 xs
    n.HasValue &&

    let n = n.GetValueOrDefault()
    inInt32 n &&

    let n = int32ToChar32(int n)
    (0x000000<_> <= n && n <= 0x10FFFF<_>) &&
    skipChar '}' xs && (
        result <- n
        true
    )

/// Regex("""([rnt'"`\\]|u\{[0-9A-Fa-f](_*[0-9A-Fa-f]){0,5}\})""")
let escapedChar (result: byref<_>) xs =
    let (|Unescape|) = function
        | 'r' -> char16ToChar32 '\r'
        | 'n' -> char16ToChar32 '\n'
        | 't' -> char16ToChar32 '\t'
        | ('\'' | '"' | '`' | '\\') as c -> char16ToChar32 c
        | _ -> -1<_>

    let r = peek xs
    r.HasValue &&
        match r.GetValueOrDefault() with
        | 'u' -> unicodeEscape &result xs
        | Unescape -1<_> -> false
        | Unescape c -> skip xs && (result <- c; true)

let charLiteral (result: byref<ValueTuple3<_,_,_>>) xs =
    skipChar '\'' xs &&

    let c = readNoneOf '\'' xs
    c.HasValue &&

    let c = c.GetValueOrDefault()
    let mutable c32 = char16ToChar32 c

    (if c = '\\' then escapedChar &c32 xs else true) &&
    skipChar '\'' xs && (
        result.Item1 <- C
        result.Item2 <- int c32
        result.Item3 <- null
        true
    )

let buffer = System.Text.StringBuilder()
let quotedTextItems0 closeQuote (result: byref<_>) xs =
    let rs = buffer
    let rec aux _ =
        let r = peek xs
        r.HasValue &&
            match r.GetValueOrDefault() with
            | '\\' ->
                skip xs &&
                let mutable r = 0<_>
                escapedChar &r xs && (
                    if needSurrogatePair r 
                        then ignore(rs.Append(Char.ConvertFromUtf32(int r)))
                        else ignore(rs.Append(char r))
                    aux()
                )
            | c ->
                (c = closeQuote) ||
                (
                    ignore(rs.Append c);
                    skip xs && aux()
                )

    result <- rs.ToString()
    ignore(rs.Clear())
    aux()

let quotedTextItems1 closeQuote (result: byref<_>) xs =
    let r = peek xs
    r.HasValue &&

    let c = r.GetValueOrDefault()
    match c with
    | '\\' ->
        skip xs &&
        let mutable r = 0<_>
        escapedChar &r xs

    | _ -> (c <> closeQuote) && skip xs

    &&

    let mutable r = null
    quotedTextItems0 closeQuote &r xs &&
    (
        result <- string c + r
        true
    )

let stringLiteral (result: byref<ValueTuple3<_,_,_>>) xs =
    let mutable r = null
    skipChar '"' xs &&
    quotedTextItems0 '"' &r xs &&
    skipChar '"' xs &&
    (
        result.Item1 <- S
        result.Item2 <- 0
        result.Item3 <- r :> obj
        true
    )
    
let quotedIdentifier (result: byref<ValueTuple3<_,_,_>>) xs =
    let mutable r = null
    skipChar2 '`' '`' xs &&
    quotedTextItems1 '`' &r xs &&
    skipChar2 '`' '`' xs &&
    (
        result.Item1 <- Qid
        result.Item2 <- 0
        result.Item3 <- r :> obj
        true
    )
    
let quotedOperator (result: byref<ValueTuple3<_,_,_>>) xs =
    let mutable r = null
    skipChar '`' xs &&
    quotedTextItems1 '`' &r xs &&
    skipChar '`' xs &&
    (
        result.Item1 <- Qop
        result.Item2 <- 0
        result.Item3 <- r :> obj
        true
    )

let lineComment xs =
    skipChar2 '/' '/' xs &&
        (skipManySatisfy (function '\r' | '\n' -> false | _ -> true) xs; true)

let rec multiComment xs =
    skipChar2 '/' '*' xs &&
        let mutable r = ValueTuple3()
        let mutable success = false
        while
            (
            let c = peek2 xs
            match c.Item1, c.Item2, c.Item3 with
            | 2uy, '*', '/' ->
                success <- skip2 xs
                false

            | 2uy, '/', '*' -> multiComment xs
            | 2uy, '/', '/' -> lineComment xs
            | 2uy, '`', '`' -> quotedIdentifier &r xs
            | 2uy, '`', _ -> quotedOperator &r xs
            | 2uy, '"', _ -> stringLiteral &r xs

            | 2uy, _, ('*'|'/'|'`'|'"') -> skip xs
            | 2uy, _, _ -> skip2 xs
            | _ -> false
            )
            do ()
        success

let trivia xs =
    let rec aux _ =
        let c = peek2 xs
        match c.Item1, c.Item2, c.Item3 with
        | 1uy, Whitespace true, _ -> skip xs 
        | (0uy | 1uy), _, _ -> true
        | _, '/', '/' -> lineComment xs && aux()
        | _, '/', '*' -> multiComment xs && aux()
        | _, Whitespace false, _ -> true
        | _, _, Whitespace false ->
            ignore(skip xs)
            aux()

        | _ ->
            ignore(skip2 xs)
            aux()
    aux()

let tokenContinue (result: byref<_>) xs =
    let r = peek xs
    r.HasValue &&
    match r.GetValueOrDefault() with
    | AsciiDecimal true -> decimalIntegerOrFloatingPointLiteral &result xs
    | Delimiter true -> delimiter &result xs
    | IdStart true -> idOrReceived &result xs
    | Op true -> opOrReceived &result xs
    | _ -> false

let start xs =
    let rs = newBuffer()

    let mutable result = ValueTuple3()
    let mutable success = false
    let mutable triviaStart = Position()
    let mutable start = Position()
    while
        (
        triviaStart <- position xs
        trivia xs && (
            start <- position xs    

            let c = peek2 xs
            match c.Item1, c.Item2, c.Item3 with
            | 0uy, _, _ ->
                success <- true
                false

            | 1uy, _, _ -> tokenContinue &result xs

            | _, '"', _ -> stringLiteral &result xs
            | _, '\'', _ -> charLiteral &result xs
            | _, '`', '`' -> quotedIdentifier &result xs
            | _, '`', _ -> quotedOperator &result xs
            | _, '0', ('x' | 'X') -> hexadecimalLiteral &result xs
            | _, '0', ('o' | 'O') -> octalLiteral &result xs
            | _, '0', ('b' | 'B') -> binaryLiteral &result xs
            | _, AsciiDecimal true, _ -> decimalIntegerOrFloatingPointLiteral &result xs
            | _, Delimiter true, _ -> delimiter &result xs
            | _, IdStart true, _ -> idOrReceived &result xs
            | _, Op true, _ -> opOrReceived &result xs
            | _, HighSurrogate true, LowSurrogate true -> surrogateName &result xs
            | _ -> false
        )
        )
        do 
            add rs {
                TriviaStart = triviaStart
                Start = start
                Kind = result.Item1
                _value = result.Item2
                _value2 = result.Item3
                End = position xs
            }

    if success && trivia xs && isEos xs then Some rs
    else None