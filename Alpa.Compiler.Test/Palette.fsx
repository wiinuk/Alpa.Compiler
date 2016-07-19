open System
open System.IO
open System.Threading
open System.Windows.Forms

let day (t: DateTime) = t.Day
let span = TimeSpan.FromSeconds 1.

let startTimer onTick =
    let t = new Timer(Interval = int span.TotalMilliseconds)
    t.Tick.Add onTick
    t.Start()

let validate (t: DateTime) s =
    match t.DayOfWeek with
    | DayOfWeek.Sunday
    | DayOfWeek.Saturday -> TimeSpan.FromHours 2. < s
    | _ -> TimeSpan.FromMinutes 30. < s


type Stream = {
    Items: char array
    mutable Index: int
}
exception ReadException of string
let raiseReadExn f = Printf.kprintf (ReadException >> raise) f

let streamOfString xs = { Items = (xs + "").ToCharArray(); Index = 0 }
let runString r xs = r <| streamOfString xs

let canRead xs = xs.Index < xs.Items.Length

let skipSatisfy predicate xs =
    canRead xs &&
    predicate xs.Items.[xs.Index] &&
    (
        xs.Index <- xs.Index + 1
        true
    )

let satisfy predicate xs =
    if canRead xs then
        let c = xs.Items.[xs.Index]
        if predicate c then
            xs.Index <- xs.Index + 1
            int c
        else -1
    else -1

let readTrivia xs =
    let rec aux xs = if skipSatisfy Char.IsWhiteSpace xs then aux xs else ()
    aux xs

let readCharT c xs =
    readTrivia xs
    if skipSatisfy ((=) c) xs then () else raiseReadExn "readCharT %c" c
    readTrivia xs

let readChar c xs = satisfy ((=) c) xs
let readAny xs = satisfy (fun _ -> true) xs

let readStringT s xs =
    readTrivia xs
    let rec aux i =
        if String.length s = i then ()
        elif skipSatisfy ((=) s.[i]) xs then aux (i+1)
        else raiseReadExn "readStringT %A" s
    aux 0
    readTrivia xs

let readTuple3 r1 r2 r3 xs =
    readCharT '(' xs
    let x1 = r1 xs
    readCharT ',' xs
    let x2 = r2 xs
    readCharT ',' xs
    let x3 = r3 xs
    readCharT ')' xs
    x1, x2, x3

let readTable rs xs =
    let i = xs.Index
    let rec aux = function
        | [] -> raiseReadExn "readTable"
        | (r,v)::rs ->
            try
                ignore(r xs)
                v
            with 
            | ReadException _ ->
                xs.Index <- i
                aux rs
    aux rs

let readBool =
    readTable [
        readStringT "true", true
        readStringT "false", false
    ]

let readIntT xs =
    let readAsciiDigitOrM1 xs = satisfy (fun c -> '0' <= c && c <= '9') xs
    let toInt c = int c - int '0'

    readTrivia xs
    let sign =
        let c = satisfy (fun c -> c = '-' || c = '+') xs 
        if char c = '-' then -1 else 1

    match readAsciiDigitOrM1 xs with
    | -1 -> raiseReadExn "readIntT"
    | c ->
        let n = sign * toInt c
        let rec aux n xs =
            match readAsciiDigitOrM1 xs with
            | -1 -> n
            | c ->
                let n = Checked.(+) (Checked.(*) 10 n) (toInt c)
                aux n xs
        try
            let n = aux n xs
            readTrivia xs
            n
        with
        | :? OverflowException -> raiseReadExn "readIntT overflow"

let readStringLiteral xs =
    readTrivia xs
    if readChar '"' xs = -1 then raiseReadExn "readStringLiteral"
    else

    let buf = System.Text.StringBuilder()
    let rec aux () =
        match readAny xs with
        | -1 -> raiseReadExn "readStringLiteral"
        | c ->
            match char c with
            | '"' -> ()
            | '\\' ->
                match readAny xs with
                | -1 -> raiseReadExn "readStringLiteral"
                | c ->
                    match char c with
                    | 'r' -> '\r'
                    | 'n' -> '\n'
                    | c -> c
                    |> buf.Append
                    |> ignore
                    aux()
            | c ->
                buf.Append c
                |> ignore
                aux()
    aux()
    let s = buf.ToString()
    buf.Clear() |> ignore
    readTrivia xs
    s

let readDateTime xs =
    match DateTime.TryParse(readStringLiteral xs) with
    | true, x -> x
    | _ -> raiseReadExn "readDateTime"

let readTimeSpan xs =
    match TimeSpan.TryParse(readStringLiteral xs) with
    | true, x -> x
    | _ -> raiseReadExn "readTimeSpan"

let readEos xs = if xs.Index < xs.Items.Length then raiseReadExn "readEos"

let readAll r xs =
    let x = r xs
    readEos xs
    x

let serializer() =
    let r xs = runString (readAll (readTuple3 readDateTime readTimeSpan readBool)) xs
    let w (x: DateTime,y,z) = sprintf "(%A,%A,%A)" (x.ToUniversalTime().ToString("O")) (string y) z
    r, w

let r, w = serializer()
let test x =
    let d = w x
    let x' = r d 
    printfn "w: %A, r: %A" d x'
    x' = x

let d = let t = DateTime.Now in (t, t.AddMinutes 20. - t, true)

let (d1,d2,d3) = d
let (d1',d2',d3') =
    try w d |> r
    with
    | ReadException m ->
        printfn "%s" m
        reraise()


DateTime.Now.ToUniversalTime().ToString("O")
DateTime(calendar)

d1.Ticks = d1'.Ticks
d2 = d2'
d3 = d3'

test d

let useSetting using =
    let path = @"C:\Users\Public\Document\Pallete.log"
    use m = new Mutex(false, path)
    try
        m.WaitOne() |> ignore
        let r, w = serializer()
        if File.Exists path then r <| File.ReadAllText path
        else (DateTime.MinValue, TimeSpan.Zero, false)
        |> using
        |> w
        |> fun data -> File.WriteAllText(path, data)
    finally
        m.ReleaseMutex()

let onTick _ = useSetting <| fun (t,s,isSend) ->
    let now = DateTime.Now
    if day now <> day t then now, span, isSend
    else
        let s = s + span
        let isSend = if validate t s && not isSend then (sendMail(); true) else false
        t, s, isSend

let onStart _ = startTimer onTick