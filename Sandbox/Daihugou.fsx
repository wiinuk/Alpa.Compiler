#load ".\Card.fsx"
open System

type Player = Player of Card list
type state = {
    Random: Random
}

/// プレイヤーに、カードをできるだけ同じ数になるようにランダムに配る
let dealCards s cards players =
    ()