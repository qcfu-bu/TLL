open Fmt
open Bindlib
open TLL
open Names
open Syntax0
open Prelude1
open Sedlexing
open Parsing

let _ =
  try
    if Array.length Sys.argv < 1 then
      epr "input file expected@."
    else
      let fname = Sys.argv.(1) in
      let ch = open_in fname in
      (* parsing *)
      let dcls0 = parse (Utf8.from_channel ch) in
      let _ = pr "parsing success--------------------------@.@." in
      (* trans01 *)
      let _, dcls1 = Trans01.trans_dcls prelude_nspc dcls0 in
      let dcls1 = Prelude1.prelude_dcls @ dcls1 in
      let _ = pr "%a@.@." Pprint1.pp_dcls dcls1 in
      let _ = pr "trans01 success--------------------------@.@." in
      (* trans1e *)
      let dcls1e = Trans1e.trans_dcls dcls1 in
      let _ = pr "%a@.@." Pprint1.pp_dcls dcls1e in
      let _ = pr "trans1e success--------------------------@.@." in
      ()
  with
  | Failure s ->
    let _ = pr "error -----------------------------------@.@." in
    pr "%s@." s
