module internal TastPickle.Types

[<Struct; StructuredFormatDisplay("{StructuredFormatDisplay}")>]
type Quote(value: string) =
    member __.StructuredFormatDisplay = value

type Ignore = Quote

let utf8 = System.Text.Encoding.UTF8
type ByteStream =
    {
        Items: array<byte>
        mutable Index: int
    }
    member x.ReadByte() =
        let r = x.Items.[x.Index]
        x.Index <- x.Index + 1
        r

    member x.ReadBytes n =
        let rs = x.Items.[x.Index..x.Index+n-1]
        x.Index <- x.Index + n
        rs

    member x.ReadUtf8String n =
        let r = utf8.GetString(x.Items, x.Index, n)
        x.Index <- x.Index + n
        r

    static member FromBytes(items, index) =
        if Array.length items <= index then failwith "FromBytes"
        else
            {
                Items = items
                Index = index
            }

type EntityData = Ignore
type Slot<'T> = ref<option<'T>>
let putSlot r v = r := Some v
let newSlot() = ref None
let isFill r = Option.isSome(!r)

type Entity = { Data: Slot<EntityData> }
type Tycon = Entity
type ILScopeRef = Ignore
type CcuThunk = Ignore
type TType = Ignore
type TyparData = Ignore
type Typar =
    { Data: Slot<TyparData>
      /// A cached TAST type used when this type variable is used as type.
      AsType: Slot<TType> }
type ValData = Ignore
type Val = { Data: Slot<ValData> }
type PublicPath = Ignore
type NonLocalEntityRef = Ignore
type ILModuleDef = Ignore

let q format = Printf.kprintf Quote format


let mkNonLocalEntityRef ccu mp = q"NonLocalEntityRef(%A, %A)" ccu mp


[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Tycon =
    let NewUnlinked() = { Tycon.Data = newSlot() }
    let Link { Tycon.Data = data } tg = putSlot data tg
    let IsLinked { Tycon.Data = data } = isFill data

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Typar =
    let NewUnlinked() = 
        let res = { Typar.Data = newSlot(); AsType = newSlot() }
        putSlot res.AsType <| q"TType_var(%A)" res
        res

    let Link { Typar.Data = data } tg = putSlot data tg
    let IsLinked { Typar.Data = data } = isFill data

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Val =
    let NewUnlinked() = { Val.Data = newSlot() }
    let Link { Val.Data = data } tg = putSlot data tg
    let IsLinked { Val.Data = data } = isFill data

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module CcuThunk =
    let CreateDelayed nm =
        q"{
            target = Unchecked.defaultof<_> 
            orphanfixup = false
            name = %A
        }" nm

module ILTypeRef =
    let Create(scope, enclosing, name) = 
        let hashCode = hash scope * 17 ^^^ (hash enclosing * 101 <<< 1) ^^^ (hash name * 47 <<< 2)
        q"{ trefScope = %A; trefEnclosing = %A; trefName = %A; hashCode = %A; asBoxedType = %A }"
            scope enclosing name hashCode Unchecked.defaultof<_>

let mkILBoxedType (tspec: ILTypeSpec) = tspec.TypeRef.AsBoxedType tspec