module internal FSharpSignatureData.Parser

[<Struct>]
type View<'a,'data>(xs: array<'a>, i: int, data: 'data) =
    member internal __.Chars = xs
    member internal __.Index = i
    member __.Data = data
    member __.IsEmpty = xs.Length <= i
    member internal __.Increment n = View(xs, i + n, data)

type Reply<'a,'c,'data> = Succ of 'a * View<'c,'data> | Fail of string list
    
type Parser<'c,'a,'data> = View<'c,'data> -> Reply<'a,'c,'data>
type ByteParser<'a,'data> = Parser<byte,'a,'data>

let succ x = fun xs -> Succ(x, xs)
let fail message = fun _ -> Fail [message]
let failf format = Printf.ksprintf fail format


let (>>.) l r = fun xs ->
    match l xs with
    | Fail e -> Fail e
    | Succ(_, xs) -> r xs

let (.>>.) l r = fun xs ->
    match l xs with
    | Fail e -> Fail e
    | Succ(l, xs) ->
        match r xs with
        | Fail e -> Fail e
        | Succ(r, xs) -> Succ((l, r), xs)

let (>>=) p f = fun xs ->
    match p xs with
    | Fail e -> Fail e
    | Succ(r, xs) ->
        let p = f r
        p xs
            
let (|>>) p f = fun xs ->
    match p xs with
    | Fail e -> Fail e
    | Succ(r, xs) -> Succ(f r, xs)

let (>>%) p x = p |>> fun _ -> x

let (<|>) l r = fun xs ->
    match l xs with
    | Fail e1 ->
        match r xs with
        | Fail e2 -> Fail(e1 @ e2)
        | r -> r
    | r -> r
        
let pipe2 l r f = fun xs ->
    match l xs with
    | Fail e -> Fail e
    | Succ(l, xs) ->
        match r xs with
        | Fail e -> Fail e
        | Succ(r, xs) -> Succ(f l r, xs)

let pipe3 p1 p2 p3 f = fun xs ->
    match p1 xs with
    | Fail e -> Fail e
    | Succ(r1, xs) -> pipe2 p2 p3 (fun r2 r3 -> f r1 r2 r3) xs

let pipe4 p1 p2 p3 p4 f = fun xs ->
    match p1 xs with
    | Fail e -> Fail e
    | Succ(r1, xs) -> pipe3 p2 p3 p4 (fun r2 r3 r4 -> f r1 r2 r3 r4) xs

let pipe5 p1 p2 p3 p4 p5 f = fun xs ->
    match p1 xs with
    | Fail e -> Fail e
    | Succ(r1, xs) -> pipe4 p2 p3 p4 p5 (fun r2 r3 r4 r5 -> f r1 r2 r3 r4 r5) xs

let tuple3 p1 p2 p3 = pipe3 p1 p2 p3 <| fun r1 r2 r3 -> r1, r2, r3
let tuple4 p1 p2 p3 p4 = pipe4 p1 p2 p3 p4 <| fun r1 r2 r3 r4 -> r1, r2, r3, r4
let tuple5 p1 p2 p3 p4 p5 = pipe5 p1 p2 p3 p4 p5 <| fun r1 r2 r3 r4 r5 -> r1, r2, r3, r4, r5
let tuple6 (p1, p2, p3, p4, p5, p6) =
    pipe5 p1 p2 p3 p4 (p5 .>>. p6) <| fun r1 r2 r3 r4 (r5, r6) ->
        r1, r2, r3, r4, r5, r6

let tuple7 (p1, p2, p3, p4, p5, p6, p7) =
    pipe5 p1 p2 p3 p4 (tuple3 p5 p6 p7) <| fun r1 r2 r3 r4 (r5, r6, r7) ->
        r1, r2, r3, r4, r5, r6, r7

let count n p xs =
    let rec aux rs xs = function
        | 0 -> Succ(List.rev rs, xs)
        | n ->
            match p xs with
            | Fail e -> Fail e
            | Succ(r, xs) -> aux (r::rs) xs (n - 1)

    if n < 0 then Fail [sprintf "count %d ... ..." n]
    else aux [] xs n

let skipCount n p xs =
    let rec aux xs = function
        | 0 -> Succ((), xs)
        | n ->
            match p xs with
            | Fail e -> Fail e
            | Succ(_, xs) -> aux xs (n - 1)

    if n < 0 then Fail [sprintf "skipCount %d ... ..." n]
    else aux xs n

//module Buffer =
//    let newArray() = Array.zeroCreate 4
//    let newSize() = 0
//
//    let asArray (items: array<_>) size =
//        if items.Length = size then items
//        else items.[0..size-1]
//
//    let add (items: array<_>) size v =            
//        let extend (items: array<_>) size =
//            let xs = Array.zeroCreate(min 2146435071 (items.Length * 2))
//            System.Array.Copy(items, 0, xs, 0, size)
//            xs
//
//        let items = if items.Length = size then extend items size else items
//            
//        items.[size] <- v
//        items
                
let countArray count p xs =
    if count < 0 then Fail [sprintf "countArray %d ... ..." count]
    else
        let items = Array.zeroCreate count
        let rec aux xs = function
            | 0 -> Succ(items, xs)
            | n ->
                match p xs with
                | Fail e -> Fail e
                | Succ(r, xs) ->
                    items.[count - n] <- r
                    aux xs (n - 1)
        aux xs count

let countRevIndexArray count p f xs =
    if count < 0 then Fail [sprintf "countRevArray %d ... ..." count]
    else
        let items = Array.zeroCreate count
        let rec aux xs i =
            if i = count then Succ(items, xs)
            else
                match p xs with
                | Fail e -> Fail e
                | Succ(r, xs) ->
                    items.[i] <- f r (count - 1 - i)
                    aux xs (i + 1)
        aux xs 0


let utf8String n (xs': View<_,_>) =
    let i = xs'.Index
    if i + n <= xs'.Chars.Length then
        let s = System.Text.Encoding.UTF8.GetString(xs'.Chars, i, n)
        Succ(s, xs'.Increment n)
    else Fail [sprintf "utf8String %d ..." n]

let many p = fun xs ->
    let rec aux rs xs =
        match p xs with
        | Fail _ -> Succ(List.rev rs, xs)
        | Succ(r, xs) -> aux (r::rs) xs
    aux [] xs



[<GeneralizableValue>]
let anyChar<'c,'s> : View<'c,'s> -> Reply<'c,'c,'s> = fun xs ->
    if xs.Index < xs.Chars.Length
    then Succ(xs.Chars.[xs.Index], xs.Increment 1)
    else Fail ["skip []"]

let pchar c (xs: View<_,_>) =
    if xs.Index < xs.Chars.Length then
        let x = xs.Chars.[xs.Index]
        if x = c then Succ(x, xs.Increment 1)
        else Fail [sprintf "pchar %A ..." c]
    else Fail [sprintf "pchar %A ..." c]
    
let anyOf cs (xs: View<_,_>) =
    if xs.Index < xs.Chars.Length then
        let x = xs.Chars.[xs.Index]
        if Seq.contains x cs then Succ(x, xs.Increment 1)
        else Fail [sprintf "anyOf %A ..." cs]
    else Fail [sprintf "anyOf %A ..." cs]

let parseData data p xs = p <| View(Seq.toArray xs, 0, data)
let parse p xs = parseData () p xs

let getState = fun (xs: View<_,_>) -> Succ(xs.Data, xs)
let mapWithState p f = fun (xs: View<_,_>) ->
    match p xs with
    | Fail e -> Fail e
    | Succ(r, xs) -> Succ(f r xs.Data, xs)

let hole() =
    let h = ref (fun _ -> failwith "hole: unfilled hole")
    h, (fun xs -> !h xs)
