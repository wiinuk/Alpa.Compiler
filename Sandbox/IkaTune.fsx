type ability =
    | AbilityNone

    | DamageUp
    | DefenseUp
    /// Ink Saver (Main)
    | MainSaver
    /// Ink Saver (Sub)
    | SubSaver
    /// Ink Recovery Up
    | InkUp
    /// Run Speed Up
    | RunSpeed
    /// Swim Speed Up
    | SwimSpeed
    /// Special Charge Up
    | SpecialUp
    | SpecialDurationUp
    | QuickRespawn
    | SpecialSaver
    /// Quick Super Jump
    | QuickJump
    | BombRangeUp 

    | OpeningGambit
    | LastDitchEffort
    | Tenacity
    | Comeback
    | ColdBlooded
    /// Ninja Squid
    | Ninja
    | Haunt
    | Recon
    | BombSniffer
    /// Ink Resistance Up
    | InkResistance
    | StealthJump

type brand =
    | CustomBrand of string

    /// Squidforce
    | Bat
    /// Inkline
    | Sig
    /// Krak-On
    | Cur
    /// Rockenberg
    | Roc
    /// Splash Mob
    | Gim

    /// Tentatek
    | Aro
    /// Firefin
    | Hoc
    /// Forge
    | For
    /// Takoroka
    | Yac
    /// Zekko
    | Ezo
    /// Skalop
    | Htx
    /// Zink
    | Iro

/// Cuttlegear
let atar = CustomBrand "atar"
/// KOG
let kogg = CustomBrand "kogg"
/// amiibo
let amii = CustomBrand "amii" 
/// SQUID GIRL
let ikam = CustomBrand "ikam" 
/// Famitsu
let fami = CustomBrand "fami"

type gear_id = string 
type reality = R1 | R2 | R3 
type parts = Head | Body | Foot 
type gear = { 
    id: gear_id 
    parts: parts
    brand: brand 
    reality: reality 
    main: ability 
    sub1: ability
    sub2: ability
    sub3: ability
}

module JpNames =
    let ability = function    
        | AbilityNone -> "なし"

        | DamageUp -> "攻撃力アップ"
        | DefenseUp -> "防御力アップ"
        | MainSaver -> "インク効率アップ（メイン）"
        | SubSaver -> "インク効率アップ（サブ）"
        | InkUp -> "インク回復力アップ"
        | RunSpeed -> "ヒト移動速度アップ"
        | SwimSpeed -> "イカダッシュ速度アップ"
        | SpecialUp -> "スペシャル増加量アップ"
        | SpecialDurationUp -> "スペシャル時間延長"
        | QuickRespawn -> "復活時間短縮"
        | SpecialSaver -> "スペシャル減少量ダウン"
        | QuickJump -> "スーパージャンプ時間短縮"
        | BombRangeUp -> "ボム飛距離アップ"

        | OpeningGambit -> "スタートダッシュ"
        | LastDitchEffort -> "ラストスパート"
        | Tenacity -> "逆境強化"
        | Comeback -> "カムバック"
        | ColdBlooded -> "マーキングガード"
        | Ninja -> "イカニンジャ"
        | Haunt -> "うらみ"
        | Recon -> "スタートレーダー"
        | BombSniffer -> "ボムサーチ"
        | InkResistance -> "安全シューズ"
        | StealthJump -> "ステルスジャンプ"

    let abilityShort = function    
        | AbilityNone -> "なし"

        | DamageUp -> "攻撃増"
        | DefenseUp -> "防御増"
        | MainSaver -> "メイン"
        | SubSaver -> "サブ効"
        | InkUp -> "インク"
        | RunSpeed -> "ヒト速"
        | SwimSpeed -> "イカ速"
        | SpecialUp -> "スペ増"
        | SpecialDurationUp -> "スペ延"
        | QuickRespawn -> "復活短"
        | SpecialSaver -> "スペ減"
        | QuickJump -> "跳短縮"
        | BombRangeUp -> "ボム飛"

        | OpeningGambit -> "スタダ"
        | LastDitchEffort -> "ラスパ"
        | Tenacity -> "逆境化"
        | Comeback -> "カムバ"
        | ColdBlooded -> "マキガ"
        | Ninja -> "イカ忍"
        | Haunt -> "うらみ"
        | Recon -> "スタレ"
        | BombSniffer -> "ボムサ"
        | InkResistance -> "安全靴"
        | StealthJump -> "ステ跳"

    let brand = function
        | Bat -> "バトロイカ"
        | Sig -> "シグレニ"
        | Cur -> "クラーゲス"
        | Roc -> "ロッケンベルグ"
        | Gim -> "ジモン"

        | Aro -> "アロメ"
        | Hoc -> "ホッコリー"
        | For -> "フォーリマ"
        | Yac -> "ヤコ"
        | Ezo -> "エゾッコ"
        | Htx -> "ホタックス"
        | Iro -> "アイロニック"

        | CustomBrand n as b ->
            if b = atar then "アタリメイド"
            elif b = kogg then "KOG"
            elif b = amii then "Amiibo"
            elif b = ikam then "侵略！イカ娘"
            elif b = fami then "ファミ通"
            else n


let gear (n, b, r, m, p, s1, s2, s3) = { 
    id = n 
    brand = b 
    reality = r 
    main = m 
    parts = p 
    sub1 = s1
    sub2 = s2
    sub3 = s3
} 

let strength = function
    | CustomBrand _ -> AbilityNone
    | Bat -> DamageUp 
    | Sig -> DefenseUp 
    | Cur -> SwimSpeed 
    | Roc -> RunSpeed 
    | Gim -> MainSaver
    | Aro -> InkUp 
    | Hoc -> SubSaver 
    | For -> SpecialDurationUp 
    | Yac -> SpecialUp 
    | Ezo -> SpecialSaver 
    | Htx -> QuickRespawn 
    | Iro -> QuickJump

let weakness = function 
    | CustomBrand _ -> AbilityNone
    | Bat -> MainSaver 
    | Sig -> DamageUp 
    | Cur -> DefenseUp 
    | Roc -> SwimSpeed 
    | Gim -> RunSpeed 
     
    | Aro -> QuickJump 
    | Hoc -> InkUp 
    | For -> SubSaver 
    | Yac -> SpecialDurationUp 
    | Ezo -> SpecialUp 
    | Htx -> SpecialSaver 
    | Iro -> QuickRespawn 
    
let stackable = function 
    | AbilityNone
    | DamageUp
    | DefenseUp
    | MainSaver
    | SubSaver
    | InkUp
    | RunSpeed
    | SwimSpeed
    | SpecialUp
    | SpecialDurationUp
    | QuickRespawn
    | SpecialSaver
    | QuickJump
    | BombRangeUp -> true
    | OpeningGambit
    | LastDitchEffort
    | Tenacity
    | Comeback
    | ColdBlooded
    | Ninja
    | Haunt
    | Recon
    | BombSniffer
    | InkResistance
    | StealthJump -> false

let product = Seq.fold (*) 1.

let reality { brand = b; sub1 = s1; sub2 = s2; sub3 = s3 } = 
    let reality b a =
        if a = AbilityNone then 1.
        elif strength b = a then 10. / 33. 
        elif weakness b = a then 1. / 33.
        else 2. / 33.

    reality b s1 * reality b s2 * reality b s3
    
let abilityValue ability { main = m; sub1 = s1; sub2 = s2; sub3 = s3 } = 
    let ab target score x = if x = target then score else 0.
    ab ability 10. m +
    ab ability 3. s1 +
    ab ability 3. s2 +
    ab ability 3. s3
 
let set3 a g = { g with sub1 = a; sub2 = a; sub3 = a }

module Evaluators =
    type custom_info = {
        a: ability
        weight: float
        min: float
    }
    let defaultCustomInfo = {
        a = AbilityNone
        weight = 1.
        min = 0.
    }

    let modify reality requireAbilities =
        let rs = requireAbilities
        let evalGear { main = m } = if Seq.exists (fun (a,_) -> m = a) rs then 1. else 0.
        let gearVariation g =
            rs
            |> Seq.map (fun (a,_) -> a)
            |> Seq.filter stackable
            |> Seq.map (fun a -> set3 a g)

        let evalGears h b f =
            let score =
                rs
                |> Seq.map (fun (a,f') -> f' (abilityValue a h + abilityValue a b + abilityValue a f))
                |> product

            score * (reality h * reality b * reality f)

        evalGear, gearVariation, evalGears
        
    let average requireAbilities = requireAbilities |> Seq.map (fun a -> a, id) |> modify reality
    let custom reality requireAbilities =
        requireAbilities
        |> Seq.map (fun { a = a; weight = w; min = m } ->    
            a, (fun v -> if v < m then 0. else v * w)
        )
        |> modify reality

let topGears evaluator gears = 
    let evalGear, gearVariation, evalGears = evaluator

    let evalGears = OptimizedClosures.FSharpFunc<_,_,_,_>.Adapt evalGears
    let filterParts p = Seq.filter (fun { parts = p' } -> p' = p) 
    let variations = Seq.collect gearVariation

    let gs = Seq.filter (fun g -> 0. < evalGear g) gears 
    let hs = filterParts Head gs 
    let bs = filterParts Body gs 
    let fs = filterParts Foot gs 
    
    variations hs
    |> Seq.collect (fun h -> 
        variations bs 
        |> Seq.collect (fun b -> 
            variations fs 
            |> Seq.map (fun f ->
                (h,b,f), evalGears.Invoke(h, b, f)
            ) 
        ) 
    ) 
    |> Seq.sortByDescending snd 
 
// /.+\.png\t(.+)\t(.+)\t.+(?:\r\n.+\.png)?\t.+(?:\r\n.+\.png)?\t(\d)/f AnyAbility R$3 $2 "$1"
let heads = 
    let h a r b n = gear(n, b, r, a, Head, AbilityNone, AbilityNone, AbilityNone)
    let h' = h
    [|

    h DamageUp R1 Iro "スカッシュバンド" 
    h' DamageUp R2 amii "サムライヘルメット" 
    h DamageUp R2 For "ダイバーゴーグル" 
    h' DamageUp R3 atar "でんせつのぼうし" 
         
    h DefenseUp R1 Yac "ヤコメッシュ" 
    h DefenseUp R2 For "スプラッシュゴーグル" 
    h DefenseUp R2 Aro "チャリキング帽" 
    h' DefenseUp R2 amii "パワードマスク" 
         
    h MainSaver R1 Sig "ショートビーニー" 
    h MainSaver R2 Sig "スゲ" 
    h MainSaver R2 For "スタジオヘッドホン" 
    h MainSaver R3 Hoc "サファリハット" 
         
    h SubSaver R1 Cur "エイズリーバンダナ" 
    h SubSaver R1 Htx "ビバレッジキャップ" 
    h SubSaver R1 Ezo "ランニングバンド" 
    h SubSaver R2 For "オーロラヘッドホン" 
         
    h InkUp R1 Hoc "フグベルハット" 
    h InkUp R1 Bat "ヘッドバンド ホワイト" 
    h InkUp R2 For "トレジャーメット" 
    h InkUp R3 Htx "サイクルメット" 
         
    h RunSpeed R1 Iro "キャディ サンバイザー" 
    h' RunSpeed R2 atar "ヒーローヘッズ レプリカ" 
    h RunSpeed R3 For "テンタクルズメット" 
         
    h SwimSpeed R1 Sig "キャンプキャップ" 
    h' SwimSpeed R2 amii "イカパッチン" 
    h SwimSpeed R2 Hoc "カモメッシュ" 
    h SwimSpeed R3 For "ナイトビジョン" 
         
    h SpecialUp R1 Hoc "ヤキフグ サンバイザー" 
    h SpecialUp R2 Htx "イカベーダーキャップ" 
    h SpecialUp R2 Aro "ダテコンタクト" 
         
    h SpecialDurationUp R1 Sig "キャンプハット" 
    h SpecialDurationUp R2 Htx "イカンカン クラシック" 
    h SpecialDurationUp R3 Ezo "アローバンド ホワイト" 
         
    h QuickRespawn R1 Gim "クロブチ レトロ" 
    h QuickRespawn R1 Ezo "バックワードキャップ" 
    h QuickRespawn R2 For "イヤーマフ" 
         
    h SpecialSaver R1 Cur "2ラインメッシュ" 
    h SpecialSaver R1 Hoc "ジェットキャップ" 
    h SpecialSaver R2 For "イカスカルマスク" 
    h SpecialSaver R2 Htx "スケボーメット" 
    h QuickJump R1 Htx "イカンカン" 
    h QuickJump R1 Ezo "エゾッコメッシュ" 
    h QuickJump R1 Cur "マルベッコー" 
    h QuickJump R2 Gim "ボンボンニット" 
         
    h BombRangeUp R1 Htx "ウーニーズBBキャップ" 
    h BombRangeUp R1 Iro "テッカサイクルキャップ" 
    h BombRangeUp R2 Aro "サンサンサンバイザー" 
    h' BombRangeUp R2 atar "タコゾネススコープ" 
    h BombRangeUp R3 For "パイロットゴーグル" 
    h OpeningGambit R1 Iro "バスケバンド" 
    h' OpeningGambit R2 ikam "イカ娘ずきん" 
    h OpeningGambit R2 Gim "ボーダービーニー" 
    h OpeningGambit R3 Htx "チドリキャップ" 
    h OpeningGambit R3 For "モンゴウベレー" 
         
    h LastDitchEffort R1 Ezo "イロメガネ" 
    h LastDitchEffort R2 For "ロブスターブーニー" 
    h LastDitchEffort R3 Hoc "オクタグラス" 
    h LastDitchEffort R3 Roc "タレサン18K" 
    h LastDitchEffort R3 Htx "バイザーメット" 
         
    h Tenacity R1 Htx "ウインターボンボン" 
    h Tenacity R2 Ezo "アローバンド" 
    h' Tenacity R3 atar "アーマーメット レプリカ" 
    h Tenacity R3 Aro "サッカーバンド" 
    h Tenacity R3 For "タコマスク" 
         
    h Comeback R1 Aro "テニスバンド" 
    h Comeback R2 Ezo "5パネルキャップ" 
    h' Comeback R2 fami "タイショウのはちまき" 
    h Comeback R3 Htx "イカノルディック" 
    h Comeback R3 For "フェイスゴーグル"

    |] 
 
let bodies = 
    let b a r b n = gear(n, b, r, a, Body, AbilityNone, AbilityNone, AbilityNone)
    let b' = b
    [|

    b DamageUp R1 Iro "アイロニックレイヤード" 
    b DamageUp R1 Yac "アオサドーレ" 
    b DamageUp R1 Aro "かくれパイレーツ" 
    b DamageUp R1 Gim "カレッジスウェット ネイビー" 
    b DamageUp R1 Roc "ロッケンベルグT" 
    b' DamageUp R2 ikam "イカ娘ノースリーブ" 
    b DamageUp R2 Gim "ボーダーネイビー" 
    b DamageUp R3 Ezo "スタジャンロゴマシ" 
         
    b DefenseUp R1 Ezo "エゾッコラグラン" 
    b DefenseUp R1 Hoc "ニクショクT" 
    b DefenseUp R1 Htx "ミントT" 
    b DefenseUp R1 Hoc "ヤキフグ8bit" 
    b DefenseUp R2 Yac "FCカラスミ" 
    b DefenseUp R2 Gim "ベイビークラゲシャツ" 
    b DefenseUp R3 Aro "チャリキングジャージ" 
    b DefenseUp R3 Bat "レトロジャッジ" 
         
    b MainSaver R1 Roc "オータムネル" 
    b MainSaver R1 Yac "ベクトルパターン" 
    b MainSaver R1 Cur "レイニーブルーT" 
    b MainSaver R1 Bat "レイヤード ブラック" 
    b MainSaver R2 For "イカセーラー ホワイト" 
    b MainSaver R2 Ezo "ギンガムチェック アカ" 
         
    b SubSaver R1 Bat "イカホワイト" 
    b SubSaver R1 Htx "パールドットT" 
    b SubSaver R1 Iro "バスケジャージ" 
    b SubSaver R1 Roc "マルエリシャツ" 
    b SubSaver R1 Sig "ヤマビコT ブルー" 
    b' SubSaver R2 atar "タコゾネスプロテクター" 
    b SubSaver R2 Yac "チョコガサネ" 
         
    b InkUp R1 For "おどるイカアロハ" 
    b InkUp R1 Htx "グレープT" 
    b InkUp R1 Bat "バトロングホワイト" 
    b InkUp R2 Gim "シロシャツ" 
    b' InkUp R2 amii "スクールブレザー" 
    b InkUp R2 Ezo "ロゴマシマシアロハ" 
    b InkUp R2 Roc "ロッケンベルグT ホワイト" 
    b InkUp R3 Sig "フォレストダウン" 
         
    b RunSpeed R1 Aro "イカノメT ブラック" 
    b RunSpeed R1 Iro "ウーニーズBBシャツ" 
    b RunSpeed R1 Cur "クラーゲス528" 
    b RunSpeed R1 Gim "マリンボーダー" 
    b RunSpeed R2 For "F-190" 
    b RunSpeed R2 Yac "オレンジボーダーラガー" 
    b RunSpeed R3 Bat "ガチガサネ" 
         
    b SwimSpeed R1 Gim "カレッジスウェット グレー" 
    b SwimSpeed R1 Htx "チドリメロンＴ" 
    b SwimSpeed R1 Roc "ハラグロラグラン" 
    b SwimSpeed R1 Hoc "マルフグT" 
    b' SwimSpeed R1 kogg "ラインT ホワイト" 
    b' SwimSpeed R2 atar "ヒーロージャケット レプリカ" 
    b SwimSpeed R3 Sig "マウンテンダウン" 
         
    b SpecialUp R1 Bat "カモガサネ" 
    b SpecialUp R1 Cur "サニーオレンジT" 
    b SpecialUp R1 Gim "レタード オレンジ" 
    b SpecialUp R2 Ezo "ウラスカジャン" 
    b' SpecialUp R2 amii "サムライジャケット" 
    b' SpecialUp R3 atar "アーマージャケット レプリカ" 
    b SpecialUp R3 Hoc "ミスターベースボール" 
         
    b SpecialDurationUp R1 Iro "アイロニックロング" 
    b SpecialDurationUp R1 Cur "イカゴッチンベスト" 
    b SpecialDurationUp R1 Bat "イカブラック" 
    b SpecialDurationUp R1 Gim "パイレーツボーダー" 
    b SpecialDurationUp R1 Ezo "リールロールスウェット" 
    b SpecialDurationUp R2 Hoc "ジップアップ グリーン" 
    b SpecialDurationUp R2 Sig "マウンテンベリー" 
    b SpecialDurationUp R3 Roc "イカライダーWHITE" 
         
    b QuickRespawn R1 Yac "トリコロールラガー" 
    b QuickRespawn R1 Bat "わかばイカT" 
    b' QuickRespawn R2 fami "タイショウのまえかけ" 
    b' QuickRespawn R2 amii "パワードスーツ" 
    b QuickRespawn R2 Gim "ボーダーホワイト" 
    b QuickRespawn R3 Iro "FCジャージー" 
    b QuickRespawn R3 Ezo "イカスカジャン" 
    b QuickRespawn R3 Hoc "ジップアップ カモ" 
    b' SpecialSaver R1 kogg "ドカンT ブラック" 
    b SpecialSaver R1 Bat "レイヤード ホワイト" 
    b SpecialSaver R2 For "グリーンＴ" 
    b SpecialSaver R2 Iro "バスケジャージ ホーム" 
    b SpecialSaver R2 Yac "ベクトルラインガサネ" 
    b SpecialSaver R3 Htx "イカジャマイカ" 
    b SpecialSaver R3 Gim "タイシャツ" 
    b SpecialSaver R3 Bat "フェスＴ" 
         
    b QuickJump R1 Cur "イカスタンシャツ" 
    b QuickJump R1 Roc "ハラシロラグラン" 
    b QuickJump R1 Yac "ベクトルパターン グレー" 
    b QuickJump R1 Bat "マスタードガサネ" 
    b QuickJump R1 Sig "ヤマビコボーダー" 
    b QuickJump R2 Ezo "バニーポップ ブラック" 
    b QuickJump R2 Gim "ブロックストライプシャツ" 
    b QuickJump R2 Ezo "ミックスシャツグレー" 
    b BombRangeUp R1 Bat "イカバッテン マスタード" 
    b BombRangeUp R1 Yac "カモフラパープル" 
    b BombRangeUp R1 Gim "シャンブレーシャツ" 
    b BombRangeUp R2 Ezo "ギンガムチェック ミドリ" 
    b BombRangeUp R2 Hoc "ホッコリー ネイビー" 
    b BombRangeUp R3 For "イカセーラー ブルー" 
    b BombRangeUp R3 Roc "イカライダーBLACK" 
         
    b ColdBlooded R1 Cur "イカノボリベスト" 
    b ColdBlooded R1 Aro "イカノメT ライトブルー" 
    b ColdBlooded R1 Gim "よもぎポロ" 
    b ColdBlooded R2 Bat "イカリスウェット" 
    b ColdBlooded R2 Iro "テッカサイクルシャツ" 
    b ColdBlooded R3 Hoc "アーバンベスト ナイト" 
    b Ninja R1 Gim "さくらエビポロ" 
    b Ninja R1 Hoc "ソウショクT" 
    b Ninja R1 Sig "ボーダーモスグリーン" 
    b Ninja R2 Ezo "エゾッコパーカー アズキ" 
    b Ninja R2 Iro "スクールジャージー" 
    b Ninja R3 Bat "ガチホワイト" 
         
    b Haunt R1 Bat "イカバッテンロング" 
    b Haunt R1 Sig "ヤマビコT アイボリー" 
    b Haunt R2 For "F-010" 
    b Haunt R2 Hoc "アーバンベスト イエロー" 
    b Haunt R3 Roc "ヴィンテージチェック" 
    b' Haunt R3 atar "タコT" 
         
    b Recon R1 Gim "カレッジラグラン" 
    b Recon R1 Ezo "ピンポンポロ" 
    b Recon R1 Hoc "ヤキフグ8bit ホワイト" 
    b Recon R2 Bat "ガチブラック" 
    b Recon R2 Gim "レタード グリーン" 
    b Recon R3 Sig "マウンテンオリーブ"

    |] 
 
let foots = 
    let f a r b n = gear(n, b, r, a, Foot, AbilityNone, AbilityNone, AbilityNone)
    let f' = f
    [| 

    f DamageUp R1 Aro "シアンビーンズ"
    f DamageUp R1 Sig "レイニーシャボン"
    f DamageUp R2 Cur "アケビコンフォート"

    f DefenseUp R1 Roc "イカヤキチップ"
    f DefenseUp R1 Ezo "グリッチョ ブルー"
    f DefenseUp R2 Cur "スリッポン チドリ"

    f MainSaver R1 Yac "オレンジアローズ"
    f MainSaver R1 Iro "シーホースHi レッド"
    f' MainSaver R2 amii "パワードレッグス"
    f' MainSaver R2 atar "アーマーブーツ レプリカ"

    f SubSaver R1 Cur "ブルーベリーコンフォート"
    f' SubSaver R2 amii "スクールローファー"
    f SubSaver R3 Ezo "グリッチョ グリーン 限定版"
    f SubSaver R3 Gim "ベリベリホワイト"

    f InkUp R1 Cur "キャンバスHi モロヘイヤ"
    f InkUp R1 Iro "シーホース ホワイト"
    f InkUp R1 Gim "ジョーズモカシン"
    f InkUp R2 Sig "トレッキングライト"

    f RunSpeed R1 Aro "ウミウシパープル"
    f RunSpeed R1 Cur "オイスタークロッグ"
    f RunSpeed R1 Sig "レイニーアセロラ"
    f RunSpeed R2 Iro "シーホースHi ゴールド"
    f' RunSpeed R2 fami "タイショウのげた"

    f SwimSpeed R1 Ezo "グリッチョ オレンジ"
    f SwimSpeed R1 Roc "ラバーソール ホワイト"
    f' SwimSpeed R2 ikam "イカ娘シューズ"
    f SwimSpeed R2 Iro "シーホース ブラックレザー"

    f SpecialUp R1 Aro "ウミウシブルー"
    f SpecialUp R1 Cur "キャンバス クマノミ"
    f SpecialUp R1 Iro "シーホースHi ゾンビ"
    f SpecialUp R2 Roc "ラバーソール ターコイズ"
    f SpecialUp R2 Roc "ロッキンホワイト"

    f SpecialDurationUp R1 Iro "シーホースHi パープル"
    f' SpecialDurationUp R2 amii "サムライシューズ"
    f SpecialDurationUp R2 Sig "トレッキングカスタム"
    f SpecialDurationUp R2 Yac "ホワイトアローズ"

    f QuickRespawn R1 Roc "イカスミチップ"
    f QuickRespawn R1 Aro "ブラックビーンズ"
    f QuickRespawn R2 Cur "チョコクロッグ"
    f QuickRespawn R2 Roc "モトクロスブーツ"

    f SpecialSaver R1 Cur "キャンバス ホワイト"
    f SpecialSaver R2 atar "タコゾネスブーツ"
    f SpecialSaver R2 Roc "ロッキンイエロー"
    f SpecialSaver R3 Aro "ウミウシレッド"

    f QuickJump R1 Cur "スリッポン レッド"
    f QuickJump R2 atar "ヒーローキックス レプリカ"
    f QuickJump R3 Roc "ヌバックブーツ レッド"
    f QuickJump R3 Aro "ミルキーダウンブーツ"

    f BombRangeUp R1 Gim "シャークモカシン"
    f BombRangeUp R1 Cur "スリッポン ブルー"
    f BombRangeUp R1 Aro "ピンクビーンズ"
    f BombRangeUp R2 Roc "ヌバックブーツ イエロー"

    f BombSniffer R1 Cur "キャンバス バナナ"
    f BombSniffer R2 Iro "シーホース イエロー"
    f BombSniffer R3 Sig "トレッキングプロ"
    f BombSniffer R3 Yac "ユデスパイカ"
    f BombSniffer R3 Roc "ロッキンチェリー"
    
    f InkResistance R1 Aro "ウミウシイエロー"
    f InkResistance R1 Gim "ベリベリレッド"
    f InkResistance R2 Cur "キャンバスHi トマト"
    f InkResistance R2 Yac "レアスパイカ"
    f InkResistance R3 Roc "モトクロス ソリッドブルー"
    
    f StealthJump R1 Cur "キャンバスHi マッシュルーム"
    f StealthJump R2 Roc "ラバーソール チェリー"
    f StealthJump R2 Sig "レイニーモスグリーン"
    f StealthJump R3 Aro "アイスダウンブーツ"
    f StealthJump R3 Yac "クレイジーアローズ"
    |]

let gears = Seq.concat [heads; bodies; foots]
let (~+) n = Seq.find (function { id = n' } -> n = n') gears

// score [DamageUp; InkUp] +"スカッシュバンド" +""

let printGearJp ((h,b,f),score) =
    let showSub = function
        | [] -> ""
        | [s] -> JpNames.ability s
        | (s::_) as ss ->
            if Set.ofSeq ss |> Set.count = 1 then
                sprintf "%sx%d" (JpNames.abilityShort s) (Seq.length ss)
            else
                Seq.map JpNames.abilityShort ss
                |> String.concat ", "
                |> sprintf "(%s)"

    let showGear { id = n; main = m; brand = b; sub1 = s1; sub2 = s2; sub3 = s3 } =
        let ss = [s1;s2;s3]
        let etc =
            if Seq.forall ((=) (strength b)) ss then " (純)"
            elif Seq.forall ((=) (weakness b)) ss then " (偽)"
            else ""

        sprintf "\"%s\" %s&%s%s" n (JpNames.abilityShort m) (showSub ss) etc

    printfn "{ 頭 = %s; 体 = %s; 足 = %s; スコア = %0.04f }" (showGear h) (showGear b) (showGear f) score

fun _ ->
    let e = Evaluators.average [DamageUp; SwimSpeed; SubSaver; InkResistance]
    let e =
        let a = Evaluators.defaultCustomInfo
        Evaluators.custom (reality >> (*) 1.) [
            { a with a = DamageUp; min = 13. }
            { a with a = SwimSpeed }
            { a with a = SubSaver; min = 10. }
            { a with a = InkResistance }
        ]

    topGears e gears
    |> Seq.truncate 50
    |> Seq.iter printGearJp