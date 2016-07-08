let rec gcd(x, y) =
    if y <> 0 then gcd(y, x % y)
    else x
    
gcd(10, 5)

// ---

let print x = printf "%A" x

print(stdin.ReadLine())

// ---

let foo = "5"
int(foo) + 3

// ---

let mutable counter = 0
while counter < 5 do
    print counter
    counter <- counter+1

for i in 0..4 do print(i)

// ---
module NumericLiteralG =
    let FromInt32(n) = System.Numerics.Complex(double<int> n, 0.0)
    let FromOne() = System.Numerics.Complex.One
    let FromZero() = System.Numerics.Complex.Zero

let ex1(i) =
    if i > 0. then sqrt(i)
    elif i = 0. then 0.
    else 1. * sqrt(-i)

// ---

print("Hello, world!")

// ---

open System.Collections.Generic

let d = dict ["spam", 1; "ham", 2] |> Dictionary

let def = 0
let k = "eggs"

let v =
    try d.[k]
    with :? KeyNotFoundException ->
        d.[k] <- def
        def

printfn "v: %d" v
printfn "d: %A" d

begin
    let d = Map ["spam", 1; "ham", 2]
    let def = 0
    let k = "eggs"
    let v, d =
        match Map.tryFind k d with
        | Some v -> v, d
        | None -> def, Map.add k def d
    
    printfn "v: %d" v
    printfn "d: %A" d
end

// ---

let ex2(a, b) =
    if not a && b then ()
    if b || not a then ()
    if (not a) && b then ()

// ---

let ex3(sequence) =
    for element in sequence do ()

// ---

let ex4(cond, expr1, expr2) =
    let a = if cond then expr1 else expr2
    ()

// ---
open System.IO

let ex5(_) =
    let openW(p) = new StreamWriter(File.OpenWrite(p))

    let f = openW("stay_open.txt")
    f.Write("every even number > 2 is the sum of two primes")
    assert false
    f.Close()

    using (openW("will_be_closed.txt")) (fun f ->
        f.Write("the sum of two primes > 2 is an even number")
        assert false
    )

    use f = openW("will_be_closed.txt")
    f.Write("the sum of two primes > 2 is an even number")
    assert false
    
    let f = openW("will_be_closed.txt")
    try
        f.Write("every even number > 2 is the sum of two primes")
        assert false
    finally
        f.Close()

    File.WriteAllText("will_be_closed.txt", "the sum of two primes > 2 is an even number")

// ---

module Ex = FSharp.Core.ExtraTopLevelOperators
type C = System.Console
Ex.double(10)
C.Write("a")

Seq.empty