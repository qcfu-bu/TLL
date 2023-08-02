open Fmt
open TLL
open Sedlexing
open Lang0
open Syntax
open Parser

let _ =
  try
    if Array.length Sys.argv < 1 then
      epr "input file expected@."
    else
      let src_name = Sys.argv.(1) in
      let src_ch = open_in src_name in
      let m = parse (Utf8.from_channel src_ch) in
      pr "%a" pp_tm m
  with
  | Failure s ->
    let _ = pr "error -----------------------------------@.@." in
    pr "%s@." s
