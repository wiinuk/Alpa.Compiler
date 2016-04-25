#load "./Alpa.Parser.fsx"

open Alpa
open Alpa.IO
open Alpa.Parser
open Alpa.ParserCombinator

let run p xs =
    match CharStream.run Lexer.start xs with
    | None -> Failure(ErrorNone, -1, None, initialState)
    | Some xs -> runWithState p initialState xs
    
let test p xs =
    for a, b in xs do
        match run p a with
        | Success x when x = b -> ()
        | e -> failwithf "%A" e
    printfn "ok"

run longIdentifier "a.b.c"

//let path0 = many (attempt (Parser.identifier .>> Delimiters.``.``))
//run path0 "a.b. "
//
//let longIdentifier = path0 .>>.? Parser.identifier 
//run longIdentifier "a.b. "
//
//let p = Parser.identifier >>. many longIdentifier
//run p "a a.b = -10"
//
//let path0 = many (Parser.identifier .>>? Delimiters.``.``)
//let longIdentifier = tuple2 path0 Parser.identifier
//run longIdentifier "a"
//
//run letHeader "a = 10"
//
//let letDefinition = letHeader .>>? Delimiters.``d=`` .>>. expression
//run letDefinition "a = 10"
//run start "a = 10"