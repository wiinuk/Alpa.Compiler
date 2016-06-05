[<AutoOpen>]
module Alpa.ParserCombinator.Primitives
open Alpa
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

let optMap defaultValue map (Parser p) xs =
    let i = xs.Index
    let u = xs.UserState
    let r = p xs
    if r.Status = Ok then Reply(map r.Value)
    else
        xs.Index <- i
        xs.UserState <- u
        Reply defaultValue

let optDefault defaultValue p = optMap defaultValue id p
let optBool p = optMap false (fun _ -> true) p
let opt p = optMap None Some p

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

let pipe5(Parser p1, Parser p2, Parser p3, Parser p4, Parser p5, f) =
    let f = OptimizedClosures.FSharpFunc<_,_,_,_,_,_>.Adapt f
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
                        let r5 = p5 xs
                        if r5.Status <> Ok then Reply((), r5.Error)
                        else
                            Reply(f.Invoke(r1.Value, r2.Value, r3.Value, r4.Value, r5.Value))
    p
         
let manyRev (Parser p) =
    let p xs =
        let rec aux rs =
            let i = xs.Index
            let u = xs.UserState

            let r = p xs
            if r.Status = Ok && i < xs.Index then
                aux(r.Value::rs)
            else
                xs.Index <- i
                xs.UserState <- u
                rs

        Reply(aux [])
    p

let many p = manyRev p |>> List.rev
let many1 p = p .>>. many p

let separateBy1 p sep = p .>>. many (sep .>>. p)
let sepBy p sep = opt (p .>>. many (sep >>. p)) |>> function None -> [] | Some(x,xs) -> x::xs
let sepBy1 p sep = p .>>. many (sep >>. p)

let chainL1 (Parser p) (Parser op) f =
    let f = OptimizedClosures.FSharpFunc<_,_,_,_>.Adapt f
    let p xs =
        let rec aux a =
            let i = xs.Index
            let u = xs.UserState
            let rOp = op xs
            let mutable r = Unchecked.defaultof<_>
            if rOp.Status = Ok && (r <- p xs; r.Status = Ok && i < xs.Index) then
                aux(f.Invoke(a, rOp.Value, r.Value))
            else
                xs.Index <- i
                xs.UserState <- u
                a

        let r = p xs
        if r.Status = Ok then
            Reply(aux r.Value)
        else
            Reply((), r.Error)
    p

let choice = function
    | [] -> fun _ -> Reply((), (), ReplyError.AnyError)
    | [p] -> p
    | p::ps ->
        let p xs =
            let initIndex = xs.Index
            let initState = xs.UserState

            let rec aux (maxResult: Reply<_,_>) maxIndex maxUserState = function
                | [] ->
                    xs.Index <- maxIndex
                    xs.UserState <- maxUserState
                    maxResult

                | (Parser p)::ps ->
                    xs.Index <- initIndex
                    xs.UserState <- initState

                    let r = p xs
                    let i = xs.Index
                    let u = xs.UserState

                    if maxResult.Status <> Ok || (r.Status = Ok && maxIndex < i)
                    then aux r i u ps 
                    else aux maxResult maxIndex maxUserState ps

            aux (p xs) xs.Index xs.UserState ps
        p
    
let (<|>) l r = choice [l; r]

let createParserForwardedToRef() =
    let r = ref <| fun _ -> failwith "not initialized"
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

let satisfyMapE p f e =
    let e = Reply((), e)
    fun xs ->
        if xs.Index < xs.Items.size then
            let t = xs.Items.items.[xs.Index]
            if p t then
                xs.Index <- xs.Index + 1
                Reply(f t)
            else e
        else e

let specialE r e = satisfyE (Token.isR r) e
let operatorE e = satisfyE Token.isOp e
let identifierE e = satisfyE Token.isId e
let constantE e = satisfyE Token.isConstant e

let peekToken xs =
    if xs.Index < xs.Items.size then
        let t = xs.Items.items.[xs.Index]
        Reply t
    else
        Reply((), (), ReplyError.RequireAnyToken)

let getUserState xs = Reply xs.UserState
let updateState f xs = xs.UserState <- f xs.UserState; Reply(())

let eof xs =
    if xs.Items.size <= xs.Index then Reply(())
    else Reply((), (), ReplyError.RequireEof)