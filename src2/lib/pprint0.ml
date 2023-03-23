open Fmt
open Names
open Syntax0

let pp_sort fmt = function U -> pf fmt "U" | L -> pf fmt "L"
let pp_role fmt = function Pos -> pf fmt "!" | Neg -> pf fmt "?"

let pp_prim fmt = function
  | Stdin -> pf fmt "stdin"
  | Stdout -> pf fmt "stdout"
  | Stderr -> pf fmt "stderr"

let rec pp_tm fmt = function
  (* inference *)
  | Ann (m, a) -> pf fmt "(%a : %a)" pp_tm m pp_t a
(* core *)
