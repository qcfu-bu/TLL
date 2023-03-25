open Fmt
open Bindlib
open TLL
open Names
open Syntax0
open Sedlexing
open Parsing

let test0 = parse (Utf8.from_string "((fn (x : A) ⇒ b) : vec)")
(* let test1 = unbox (Trans01.trans_tm [] test0) *)
(* let _ = pr "%a@." Pprint1.pp_tm test1 *)
