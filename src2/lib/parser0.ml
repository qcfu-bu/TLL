open Fmt
open Names
open MParser
open Syntax0

let reserved =
  SSet.of_list
    [ "U"
    ; "L"
    ; "definition"
    ; "theorem"
    ; "inductive"
    ; "match"
    ; "fn"
    ; "ln"
    ; "fix"
    ; "let"
    ; "in"
    ; "match"
    ; "as"
    ; "with"
    ; "refl"
    ; "rew"
    ; "IO"
    ; "return"
    ; "proto"
    ; "end"
    ; "open"
    ; "fork"
    ; "recv"
    ; "send"
    ; "close"
    ; "stdin"
    ; "stdout"
    ; "stderr"
    ]
