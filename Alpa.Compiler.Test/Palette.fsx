open System.Reflection
open System.Reflection.Emit

type Stream = {
    mutable index : int
    items: byte array
}
let makeStream xs = {
    index = 0
    items = Seq.toArray xs
}
let canRead s = s.index < s.items.Length
let postIncr s =
    let x = s.index
    s.index <- s.index + 1
    x
let readU1 s = s.items.[postIncr s]

let makeMEnv (m: MethodBase) = m

let opMap =
    typeof<OpCodes>.GetFields()
    |> Seq.map (fun f -> f.GetValue null)
    |> Seq.choose (function :? OpCode as x -> Some x | _ -> None)
    |> Seq.map (fun x -> x.Value, x)
    |> Map.ofSeq

let readCode s =
    match readU1 s with
    | 0xFEuy ->
        readU1 s

    | v -> opMap.[int16 v]

let readInstr env s =
    let c = readCode s
    readU1 read s

let readIL env s = seq { while canRead s do yield readInstr env s }

let parseIL m =
    let env = makeMEnv m
    let b = m.GetMethodBody()
    let xs = b.GetILAsByteArray()
    readIL env (makeStream xs)