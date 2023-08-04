open Fmt
open TLL
open Sedlexing
open Parser
open Syntax0

let _ =
  try
    if Array.length Sys.argv < 1 then
      epr "input file expected@."
    else
      let src_name = Sys.argv.(1) in
      let src_ch = open_in src_name in
      let dcls0 = parse (Utf8.from_channel src_ch) in
      let _, dcls1 = Trans01.trans_dcls [] dcls0 in
      pr "%a" pp_dcls dcls0;
      pr "@.@.-----------------------------------------@.@.";
      pr "%a" Pprint1.pp_dcls dcls1
  with
  | Failure s ->
    let _ = pr "error -----------------------------------@.@." in
    pr "%s@." s
