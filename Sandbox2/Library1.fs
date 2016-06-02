namespace Sandbox2

type Class1() = 
    member this.X = "F#"

module X = 
    let f1 x xs = List.find (fun x' -> x = x') xs
    let f2 x xs = List.find ((=) x) xs

    let x0 = 0I
    let x1 = 1I
    let x10 = 10I
    let x123456789012345678901 = 123456789012345678901I

    let f x = x + 0I, x + 1I, x + 10I, x + 123456789012345678901I