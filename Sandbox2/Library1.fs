namespace Sandbox2

type Class1() = 
    member this.X = "F#"

[<Struct>]
type StructBox<'T> =
    [<DefaultValue(false)>]
    val mutable A: int64
    [<DefaultValue(false)>]
    val mutable B: int64
    [<DefaultValue(false)>]
    val mutable C: int64
    [<DefaultValue(false)>]
    val mutable D: int64
    [<DefaultValue(false)>]
    val mutable Value: 'T

module X = 
    let f1 x xs = List.find (fun x' -> x = x') xs
    let f2 x xs = List.find ((=) x) xs

    let x0 = 0I
    let x1 = 1I
    let x10 = 10I
    let x123456789012345678901 = 123456789012345678901I

    let f x = x + 0I, x + 1I, x + 10I, x + 123456789012345678901I

    let readByref() =
        let mutable n = 10
        let nr = &n
        nr <- 20
        let n2 = nr
        ()

    let structField() =
        let mutable a = StructBox<StructBox<_>>()
        a.Value.Value <- 10
        a.Value.Value

    let setRef (r1: int byref) (r2: int nativeptr) (r3: nativeint) (r4: unativeint) =
        r1 <- 10
        NativeInterop.NativePtr.write r2 10
        NativeInterop.NativePtr.write<int> (NativeInterop.NativePtr.ofNativeInt r3) 10
        NativeInterop.NativePtr.write<int> (NativeInterop.NativePtr.ofNativeInt(nativeint r4)) 10
        ()

    let setRefGeneric (p: _ nativeptr) x = NativeInterop.NativePtr.write p x

    let get (xs: _ array) i =
        [|0|].[0] |> ignore
        xs.[i]