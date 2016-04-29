namespace Alpa.IO

open Alpa.IO
open Alpa.Token

type Stream<'t,'u> = {
    Items: Buffer<'t>
    mutable Index: int32
    mutable UserState: 'u
}
type ReplyError = AnyError = 0 | RequireEof = -2
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