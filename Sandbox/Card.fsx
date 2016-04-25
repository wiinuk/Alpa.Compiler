namespace global

type Suit =
    /// ♠
    | Spade
    /// ♥
    | Heart
    /// ♦
    | Diamond
    /// ♣
    | Club

type Rank = A | T2 | T3 | T4 | T5 | T6 | T7 | T8 | T9 | T10 | J | Q | K
type Card = Card of Suit * Rank | Joker


module Internal =
    [<RequiresExplicitTypeArguments>]
    let unsafeUnionValues<'union> =
        Reflection.FSharpType.GetUnionCases(typeof<'union>)
        |> Seq.map(fun u -> Reflection.FSharpValue.MakeUnion(u, [||]) :?> 'union)
open Internal

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Suit =
    let allSuit = Set unsafeUnionValues<Suit>

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Rank =
    let allRank = Set unsafeUnionValues<Rank>

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Card =
    open Suit
    open Rank

    let allCard = Set <| seq { for s in allSuit do for r in allRank -> Card(s, r) }