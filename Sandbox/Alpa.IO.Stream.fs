namespace Alpa.IO

open Alpa.IO
open Alpa.Token

type Stream<'t,'u> = {
    Items: Buffer<'t>
    mutable Index: int32
    mutable UserState: 'u
}

module Stream =
    let canRead xs = xs.Index < xs.Items.size
    let get xs i = xs.Items.items.[xs.Index + i]
    let peek xs = get xs 0
    let seek xs i = xs.Index <- xs.Index + i

type ReplyError = AnyError = 0 | RequireEof = -2 | RequireAnyToken = -3
type ReplyStatus = Ok = 1 | Error = 0

[<Struct>]
type Reply<'a,'e> =
    val Status: ReplyStatus
    val Value: 'a
    val Error: 'e

    new (value) = {
        Status = ReplyStatus.Ok
        Value = value
        Error = Unchecked.defaultof<_>
    }
    new ((), error) = {
        Status = ReplyStatus.Error
        Value = Unchecked.defaultof<_>
        Error = error
    }
    new ((), (), error) = {
        Status = enum(int<ReplyError> error)
        Value = Unchecked.defaultof<_>
        Error = Unchecked.defaultof<_>
    }