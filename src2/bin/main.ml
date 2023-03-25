open Fmt
open Bindlib
open TLL
open Names
open Syntax0
open Sedlexing
open Parsing

let _ =
  if Array.length Sys.argv < 1 then
    epr "input file expected@."
  else
    let fname = Sys.argv.(1) in
    let ch = open_in fname in
    let dcls0 = parse (Utf8.from_channel ch) in
    let _, dcls1 = Trans01.trans_dcls [] dcls0 in
    let dcls1 = unbox dcls1 in
    pr "%a@." Pprint1.pp_dcls dcls1
