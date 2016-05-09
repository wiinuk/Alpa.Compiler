module Alpa.Lexer.Test

open Alpa
open Alpa.Token
open Alpa.Lexer
open Alpa.IO
open Alpa.IO.CharStream
open Xunit
open Xunit.Sdk
open FsCheck.Xunit

let tokenInfo (source: string) t =
    let i1, i2 = range t
    kind t, source.[int<int<_>> i1 .. int<int<_>>i2 - 1]

let tokenInfoWithPosition (source: string) t =
    let i1, i2 = t.Start, t.End
    kind t, source.[int<int<_>> i1.Index .. int<int<_>>i2.Index - 1], (int<int<_>> i1.Line, int<int<_>> i1.Column), (int<int<_>> i2.Line, int<int<_>> i2.Column)

let lexP s = CharStream.run Lexer.start s |> Option.map (Buffer.toSeq >> Seq.map (tokenInfoWithPosition s))
let lex s = CharStream.run Lexer.start s |> Option.map (Buffer.toSeq >> Seq.map (tokenInfo s))

//let test xs =
//    for a, b in xs do
//        match lex a with
//        | None -> printfn "parse error %A" a
//        | Some rs ->
//            if Seq.compareWith compare rs b <> 0
//            then
//                printfn "failure %A => %A <> %A" a rs b
//
//let testPosition xs =
//    for a, b in xs do
//        match lexP a with
//        | None -> printfn "parse error %A" a
//        | Some rs ->
//            if Seq.compareWith compare rs b <> 0
//            then
//                printfn "failure %A => %A <> %A" a rs b
//
//
//let errorTest xs =
//    for x in xs do
//        match lex x with
//        | Some xs -> printfn "failure %A => %A" x xs
//        | _ -> ()

open System
let allChars = seq {for c in 0x000000..0x10ffff do if not (0x00d800 <= c && c <= 0x00dfff) then yield Char.ConvertFromUtf32 c}
//for c in allChars do
//    if Char.IsControl(c, 0) then
//        let i = Char.ConvertToUtf32(c, 0)
//        printfn "'%s' '\\u%04X'" c i

[<AutoOpen>]
module TokenInfos =
    
    /// punctuator
    let p x = Rop, x

    /// keyword
    let k x = Rid, x

    let d x = D, x
    let i x = I, x

    /// variable
    let v x = Id, x
    let c x = C, x

    /// operator
    let o x = Op, x

let assertSeq (exp: 'a seq) (act: 'a seq) =
    if Seq.compareWith compare exp act = 0 then ()
    else
        Assert.Equal<'a>(
            Seq.toArray exp, 
            Seq.toArray act, 
            LanguagePrimitives.FastGenericEqualityComparer
        )

let assertPositionEq src exp =
    match lexP src with
    | None -> Assert.True(false, src)
    | Some act -> assertSeq exp act

let assertLexError src =
    match lex src with
    | None -> ()
    | Some act -> Assert.True(false, src)

let assertLexErrors = List.iter assertLexError

let assertLexEq src exp =
    match lex src with
    | None -> Assert.True(false, src)
    | Some act -> assertSeq exp act 

[<Fact>]
let triviaPosition() =
    let (==) = assertPositionEq

    // trivia
    "aa ss" == [Id,"aa",(1,1),(1,3); Id,"ss",(1,4),(1,6)]
    "aa\ttt" == [Id,"aa",(1,1),(1,3); Id,"tt",(1,5),(1,7)]
    "aa\rrr" == [Id,"aa",(1,1),(1,3); Id,"rr",(1,4),(1,6)]
    "aa\nnn" == [Id,"aa",(1,1),(1,3); Id,"nn",(2,1),(2,3)]
    "aa \nsn" == [Id,"aa",(1,1),(1,3); Id,"sn",(2,1),(2,3)]
    "aa \n bn" == [Id,"aa",(1,1),(1,3); Id,"bn",(2,2),(2,4)]
    "aa\n ns" == [Id,"aa",(1,1),(1,3); Id,"ns",(2,2),(2,4)]
    "aa\r\nrn" == [Id,"aa",(1,1),(1,3); Id,"rn",(2,1),(2,3)]

    // utf32 id
    "\U0000AB01" == [Id,"\U0000AB01",(1,1),(1,2)] // "ꬁ", "ETHIOPIC SYLLABLE TTHU", UnicodeCategory.OtherLetter

[<Fact>]
let unusedCharError() =
    assertLexErrors [

        // unused delimiters
        "$"
        "#"
    
        // control char
        "\u0000" // NULL
        "\u0001" // START OF HEADING

        // Private Use Area
        "\uE000"
        "\U00100000"
    ]

    
[<Fact>]
let triviaError() =
    assertLexErrors [
        "/* *"
        "/* /* */"
        "/* \" */"
        "/* ` */"
        "/* `` */"
        "/* ``` */"
        "/* ```` */"
    ]

[<Fact>]
let numericLiteralError() =
    assertLexErrors ["0x_123"; "123.a123"]
    
[<Fact>]
let quotedIdAndOpError() =
    assertLexErrors [
        "````"
        "```"
        "``a`"
    
        "``"
        "`"
        "`a"
    ]
    
[<Fact>]
let charLiteralError() =
    assertLexErrors [
        "'"
        "'a"
        "'aa'"
        "'\\"
        "''"
        "'\\n"
        "'\\u"
        "'\\u{20}"
        "'\\'"
        "'\\u'"
        "'\\u{}'"
        "'\\u{20'"

        "'\\A'"
        "'\\u{110000}'"
    ]
    
[<Fact>]
let stringLiteralError() =
    assertLexErrors [
        "\""
        "\"a"
        "\"aa"
        "\"\\"
        "\"\\n"
        "\"\\u"
        "\"\\u{20}"
        "\"\\\""
        "\"\\u\""
        "\"\\u{}\""
        "\"\\u{20\""

        "\"\\A\""
    ]
    
[<Fact>]
let triviaFact() =
    let (==) = assertLexEq
    
    " //\n;" == [d";"]
    "\uFFFF\t\n\v\f\u0085\u00A0\u1680\u2000\u2001\u2002\u2003\u2004\u2005\u2006\u2007\u2008\u2009\u200A\u2028\u2029\u202F\u205F;" == [d";"]
    "// c\r\n;" == [d";"]
    ", //\r\n;" == [d","; d";"]
    "/**/;" == [d";"]
    "/* * /* * */**/;" == [d";"]
    ",/* `*/` /* ``*/`` */ \"*/\" // */\r\n */;" == [d","; d";"]

    ",/* \' */;" == [d","; d";"]

[<Fact>]
let numericLiteralFact() =
    let (==) = assertLexEq

    "0" == [i"0"]
    
    // System.Int64.MaxValue < n
    "012_345_678_912_345_678_912_" == [i"012_345_678_912_345_678_912_"]

    "0x0_123_456_789_ABC_DEF_abc_def" == [i"0x0_123_456_789_ABC_DEF_abc_def"]
    "0X123" == [i"0X123"]
    "0b0_111_" == [i"0b0_111_"]
    "0B1" == [i"0B1"]
    "0o1_234_567_" == [i"0o1_234_567_"]
    "0O123" == [i"0O123"]
    
    "0a123" == [i"0"; v"a123"]
    "a.1" == [v"a"; p"."; i"1"]
    
[<Fact>]
let charLiteralFact() =
    let (==) = assertLexEq

    "'a'" == [c"'a'"]
    "'\\''" == [c"'\\''"]
    "'\\r' '\\n' '\\t' '\\\"' '\\`' '\\\\'" == [c"'\\r'"; c"'\\n'"; c"'\\t'"; c"'\\\"'"; c"'\\`'"; c"'\\\\'"]
    "'\u{0}'" == [c"'\u{0}'"]
    "'\u{001}'" == [c"'\u{001}'"]

    // surrogate char
    "'\u{d800}'" == [c"'\u{d800}'"]

    "'\u{10FFFF}'" == [c"'\u{10FFFF}'"]
    "'\u{00000010FFFF}'" == [c"'\u{00000010FFFF}'"]
    "'\u{0000_0010_FFFF}'" == [c"'\u{0000_0010_FFFF}'"]
    
[<Fact>]
let delimiterFact() =
    assertLexEq ",;[]{}()" [d","; d";"; d"["; d"]"; d"{"; d"}"; d"("; d")"]
    
[<Fact>]
let receivedIdAndReceivedOpFact() =
    let (==) = assertLexEq

    "alias case class type with import module for where let" == [k"alias"; k"case"; k"class"; k"type"; k"with"; k"import"; k"module"; k"for"; k"where"; k"let"]

    "= . : | -> " + rightwardsArrow + " <- " + leftwardsArrow + " .. "
    + twoDotLeader + " :: " + proportion + " ... " + horizontalEllipsis ==
    [
        p"="; p"."; p":"; p"|"; p"->"; p rightwardsArrow; p "<-"; p leftwardsArrow;
        p".."; p twoDotLeader; p"::"; p proportion; p"..."; p horizontalEllipsis
    ]

    "; = ;; ==" == [d";"; p"="; d";"; d";"; o"=="]
    
[<Fact>]
let idFact() =
    let (==) = assertLexEq

    "a012" == [v"a012"]
    "_ __" == [k"_"; v"__"]
    "let let's-go!?" == [k"let"; v"let's-go!?"]
    
    "\u16CA" == [v"\u16CA"] // "ᛊ", "RUNIC LETTER SOWILO S", UnicodeCategory.OtherLetter
    "\u0272" == [v"\u0272"] // "ɲ", "LATIN SMALL LETTER N WITH LEFT HOOK", UnicodeCategory.LowercaseLetter
    "\u02E0" == [v"\u02E0"] // "ˠ", "MODIFIER LETTER SMALL GAMMA", UnicodeCategory.ModifierLetter
    "\u210F" == [v"\u210F"] // "ℏ", "PLANCK CONSTANT OVER TWO PI, UnicodeCategory.LowercaseLetter
    

    // utf32

    "\U0000AB01" == [v"\U0000AB01"] // "ꬁ", "ETHIOPIC SYLLABLE TTHU", UnicodeCategory.OtherLetter
    "\U00029E3D" == [v"\U00029E3D"] // "𩸽", "Unicode Han Character 'U+29E3D'", UnicodeCategory.OtherLetter

    "_\U0001D7E2" == [v"_\U0001D7E2"] // "𝟢", "MATHEMATICAL SANS-SERIF DIGIT ZERO", UnicodeCategory.DecimalDigitNumber
    "_\U0001D7EB" == [v"_\U0001D7EB"] // "𝟫", "MATHEMATICAL SANS-SERIF DIGIT NINE", UnicodeCategory.DecimalDigitNumber

    "\u16CA\U0001D7E2\U0000AB01" == [v"\u16CA\U0001D7E2\U0000AB01"]
    
[<Fact>]
let opFact() =
    let (==) = assertLexEq

    "x-+y, x -+y" == [v"x-"; o"+"; v"y"; d","; v"x"; o"-+"; v"y"]
    "a = b;" == [v"a"; p"="; v"b"; d";"]

    
    // utf32

    "\U0001F49A" == [o"\U0001F49A"] // "💚", "GREEN HEART", UnicodeCategory.OtherSymbol
    "\U0001F49B" == [o"\U0001F49B"] // "💛", "YELLOW HEART", UnicodeCategory.OtherSymbol
    "\U0001F49C" == [o"\U0001F49C"] // "💜", "PURPLE HEART", UnicodeCategory.OtherSymbol

    "\U0001F49A\U0001F49B" == [o"\U0001F49A\U0001F49B"]
    "+\U0001F49A\U0001F49B" == [o"+\U0001F49A\U0001F49B"]