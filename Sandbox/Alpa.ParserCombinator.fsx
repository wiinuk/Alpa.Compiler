[<AutoOpen>]
module Alpa.ParserCombinator.Primitives
#load "./Alpa.IO.Stream.fsx"

open Alpa.IO

type Parser<'c,'u,'e,'a> = Stream<'c, 'u> -> Reply<'a, 'e>
type Result<'c,'u,'e,'a> = Failure of error: 'e * index: int * last: option<'c> * state: 'u | Success of 'a

[<Literal>]
let Ok = ReplyStatus.Ok
[<Literal>]
let Error = ReplyStatus.Error

let (|Parser|) (p: Parser<_,_,_,_>) = p

let runWithState (Parser p) state xs =
    let xs = {
        Items = xs
        Index = 0
        UserState = state
    }
    let r = p xs
    if r.Status = Ok then Success r.Value
    else Failure(r.Error, xs.Index, Buffer.get xs.Items xs.Index, xs.UserState)

let (|>>) (Parser p) f = fun xs ->
    let r = p xs
    if r.Status <> Ok then Reply((), r.Error)
    else
        Reply(f r.Value)

let (>>%) p v = p |>> fun _ -> v
        
let (.>>) (Parser p1) (Parser p2) = fun xs ->
    let r1 = p1 xs
    if r1.Status <> Ok then r1
    else
        let r2 = p2 xs
        if r2.Status <> Ok then Reply((), r2.Error)
        else Reply r1.Value

let (>>.) (Parser p1) (Parser p2) = fun xs ->
    let r1 = p1 xs
    if r1.Status <> Ok then Reply((), r1.Error)
    else p2 xs

let (.>>.) (Parser p1) (Parser p2) = fun xs ->
    let r1 = p1 xs
    if r1.Status <> Ok then Reply((), r1.Error)
    else
        let r2 = p2 xs
        if r2.Status <> Ok then Reply((), r2.Error)
        else
            Reply((r1.Value, r2.Value))

let between pstart pend p = pstart >>. p .>> pend

let pipe2 (Parser p1) (Parser p2) f =
    let f = OptimizedClosures.FSharpFunc<_,_,_>.Adapt f
    fun xs ->
        let r1 = p1 xs
        if r1.Status <> Ok then Reply((), r1.Error)
        else
            let r2 = p2 xs
            if r2.Status <> Ok then Reply((), r2.Error)
            else
                Reply(f.Invoke(r1.Value, r2.Value))

let pipe3 (Parser p1) (Parser p2) (Parser p3) f =
    let f = OptimizedClosures.FSharpFunc<_,_,_,_>.Adapt f
    let p xs =
        let r1 = p1 xs
        if r1.Status <> Ok then Reply((), r1.Error)
        else
            let r2 = p2 xs
            if r2.Status <> Ok then Reply((), r2.Error)
            else
                let r3 = p3 xs
                if r3.Status <> Ok then Reply((), r3.Error)
                else
                    Reply(f.Invoke(r1.Value, r2.Value, r3.Value))
    p

let pipe4 (Parser p1) (Parser p2) (Parser p3) (Parser p4) f =
    let f = OptimizedClosures.FSharpFunc<_,_,_,_,_>.Adapt f
    let p xs =
        let r1 = p1 xs
        if r1.Status <> Ok then Reply((), r1.Error)
        else
            let r2 = p2 xs
            if r2.Status <> Ok then Reply((), r2.Error)
            else
                let r3 = p3 xs
                if r3.Status <> Ok then Reply((), r3.Error)
                else
                    let r4 = p4 xs
                    if r4.Status <> Ok then Reply((), r4.Error)
                    else
                        Reply(f.Invoke(r1.Value, r2.Value, r3.Value, r4.Value))
    p
            
let many (Parser p) =
    let p xs =
        let rec aux rs =
            let i = xs.Index
            let r = p xs
            if r.Status <> Ok then
                xs.Index <- i
                List.rev rs

            else aux(r.Value::rs)
        Reply(aux [])
    p

let sepBy1 (Parser p) (Parser sep) = pipe2 p (many (sep >>. p)) <| fun x xs -> x::xs

let (<|>) (Parser p1) (Parser p2) = fun xs ->
    let i = xs.Index
    let r = p1 xs
    if r.Status = Ok then r
    else
        xs.Index <- i
        p2 xs

let choice = function
    | [] -> fun _ -> Reply((), (), ReplyError.AnyError)
    | [p] -> p
    | p::ps ->
        let p xs =
            let startIndex = xs.Index
            let r = p xs
            let rec aux r' i' = function
                | [] ->
                    xs.Index <- i'
                    r'

                | (Parser p)::ps ->
                    xs.Index <- startIndex
                    let r = p xs
                    let i = xs.Index
                    if r.Status = Ok && i' < i then aux r i ps else aux r' i' ps
            aux r xs.Index ps
        p
    
let opt (Parser p) = fun xs ->
    let i = xs.Index
    let r = p xs
    if r.Status = Ok then Reply(Some r.Value)
    else
        xs.Index <- i
        Reply None

let createParserForwardedToRef() =
    let p = (fun _ -> failwith "not initialized")
    let r = ref p
    (fun xs -> !r xs), r

let satisfyE p e =
    let e = Reply((), e)
    fun xs ->
        if xs.Index < xs.Items.size then
            let t = xs.Items.items.[xs.Index]
            if p t then
                xs.Index <- xs.Index + 1
                Reply t
            else e
        else e

let eof xs =
    if xs.Items.size <= xs.Index then Reply(())
    else Reply((), (), ReplyError.RequireEof)