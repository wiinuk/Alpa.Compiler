module ILPrinter.Test
#load "./ILPrinter.fsx"
#r "./../packages/FsCheck.2.5.0/lib/net45/FsCheck.dll"
open ILPrinter
open System
open System.Reflection.Emit
open System.Runtime.InteropServices

type Buffer = System.Collections.Generic.Stack<byte>
let writeU1 n (s: Buffer) = s.Push n

/// require: 0 <= n && n <= 0x1FFFFFFF
let writeNumber n s =
    let n = n &&& 0x1FFFFFFF
    if n <= 0x7F then writeU1 (uint8 n) s
    elif n <= 0x3FFF then
        writeU1 (uint8 (n >>> 8) ||| 0b10000000uy) s
        writeU1 (uint8 n) s
    else
        writeU1 (uint8 (n >>> 24) ||| 0b11000000uy) s
        writeU1 (uint8 (n >>> 16)) s
        writeU1 (uint8 (n >>> 8)) s
        writeU1 (uint8 n) s

// 0x49 = 0x01000012
let test () =
    let test orig comp =
        let decomp = readNumber (makeStream comp)
        if decomp <> orig then failwithf "comp: %A, decomp: %A, orig: %A" comp decomp orig

    test 0x03 "\x03"B
    test 0x7F "\x7F"B
    test 0x80 "\x80\x80"B
    test 0x2E57 "\xAE\x57"B
    test 0x3FFF "\xBF\xFF"B
    test 0x4000 "\xC0\x00\x40\x00"B
    test 0x1FFFFFFF "\xDF\xFF\xFF\xFF"B

//    0b11
//    0b110

    //test 3 "\x06"B
    //test -3 "\x7B"B
    //test 64 "\x80\x80"B
    //test -64 "\x01"B
    //test 8192 "\xC0\x00\x40\x00"B
    //test -8192 "\x80\x01"B
    //test 268435455 "\xDF\xFF\xFF\xFE"B
    //test -268435456 "\xC0\x00\x00\x01"B

let tryf() = try 1 / 0 with :? DivideByZeroException -> 0
let x() = [|20n; 30n|]
let app f x = f x
let f() =
    let y() = [|1s;2s|]
    print <@ y @>

    try print <@ tryf @>
    with e -> printfn "%A" e


type CC = System.Reflection.CallingConventions
type UC = System.Runtime.InteropServices.CallingConvention
let s = SignatureHelper.GetMethodSigHelper(CC.Standard, typeof<Void>)
let bs = s.GetSignature()


let env = {
    Modules = []
    TypeArgs = Type.EmptyTypes
    MethodTypeArgs = Type.EmptyTypes
    Handlers = [||]
}

let writeMethodSig
    {
        thisKind = thisKind
        callKind = callKind
        retType = retType
        genParams = genParams
        methodParams = methodParams
        varargParams = varargParams
    } =
    let addParams pars (s: SignatureHelper) =
        for Param(isByref, mods, t) in pars do
            let t = if isByref then t.MakeByRefType() else t
            let opts, reqs = List.partition (function Mod(isOpt=isOpt) -> isOpt) mods
            let getTypes xs = Seq.map (function Mod(_,t) -> t) xs |> Seq.toArray
            s.AddArgument(t, getTypes reqs, getTypes opts)

    let (Param(isByref, mods, retType)) = retType
    let tk =
        match thisKind with
        | ExplicitThis -> CC.ExplicitThis
        | HasThis -> CC.HasThis
        | ThisNone -> CC.Standard

    let ck =
        match callKind with
        | DefaultCall -> Choice1Of2 tk
        | Vararg -> Choice1Of2(tk ||| CC.VarArgs)
        | C -> Choice2Of2 UC.Cdecl
        | Stdcall -> Choice2Of2 UC.StdCall
        | Thiscall -> Choice2Of2 UC.ThisCall
        | Fastcall -> Choice2Of2 UC.FastCall

    let s = 
        match ck with
        | Choice1Of2 k -> SignatureHelper.GetMethodSigHelper(k, retType)
        | Choice2Of2 k -> SignatureHelper.GetMethodSigHelper(k, retType)

    addParams methodParams s

    match callKind, varargParams with
    | Vararg, _
    | _, _::_ -> s.AddSentinel()
    | _ -> ()

    addParams varargParams s

parseMethodSig env bs

let s() =
    let d = System.AppDomain.CurrentDomain
    let a = d.DefineDynamicAssembly(AssemblyName "test", AssemblyBuilderAccess.ReflectionOnly)
    let f = a.DefineDynamicModule "test.dll"

    let fsig = SignatureHelper.GetFieldSigHelper f
    fsig.AddSentinel()
    fsig.AddArgument(typeof<int>, true)

    let env = {
        Modules = [f]
        TypeArgs = Type.EmptyTypes
        MethodTypeArgs = Type.EmptyTypes
        Handlers = [||]
    }
    parseMethodSig env <| fsig.GetSignature()