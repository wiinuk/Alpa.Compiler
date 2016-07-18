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

let satisfy predicate xs =
    xs.Index < xs.Items.Length &&
    predicate xs.Items.[xs.Index] &&
    (
        xs.Index <- xs.Index + 1
        true
    )

let readTrivia xs =
    let rec aux xs = if satisfy Char.IsWhiteSpace xs then aux xs else ()
    aux xs

let readCharT c xs =
    readTrivia xs
    if satisfy ((=) c) xs then () else raiseReadExn "readCharT %c" c
    readTrivia xs

let readStringT s xs =
    readTrivia xs
    let rec aux i =
        if String.length s = i then ()
        elif satisfy ((=) s.[i]) xs then aux (i+1)
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
    let rec aux = function
        | [] -> raiseReadExn "readTable"
        | (r,v)::rs -> try ignore(r xs); v with _ -> aux rs
    aux rs

let readBool =
    readTable [
        readStringT "true", true
        readStringT "false", false
    ]

let readIntT xs =
    

let readHms xs =
    let h = readIntT xs
    readCharT ':' xs
    let m = readIntT xs
    readCharT ':' xs
    let s = readIntT xs
    h, m, s

let readDateTime xs =
    let y = readIntT xs
    readCharT '/' xs
    let M = readIntT xs
    readCharT '/' xs
    let d = readIntT xs
    let h, m, s = readHms xs
    try DateTime(y, M, d, h, m, s)
    with
    | :? ArgumentOutOfRangeException -> raiseReadExn "readDateTime"

let readTimeSpan xs =
    try readHms xs |> TimeSpan
    with
    | :? ArgumentOutOfRangeException -> raiseReadExn "readTimeSpan"

let readEos xs = if xs.Index < xs.Items.Length then raiseReadExn "readEos"

let readAll r xs =
    let x = r xs
    readEos xs
    x

let serializer() =
    let r xs = runString (readAll (readTuple3 readDateTime readTimeSpan readBool)) xs
    let w x = sprintf "%A" x
    r, w

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