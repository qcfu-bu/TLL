open Fmt
open Tll
open Parser0

let run s_in s_out =
  let ch_in = open_in s_in in
  let ch_out = open_out s_out in
  try
    match parse_channel ch_in with
    | Success dcls ->
      let s = str "%a@." Syntax0.pp_dcls dcls in
      let _ = Printf.fprintf ch_out "%s" s in
      let _ =
        Printf.fprintf ch_out
          "parse success---------------------------------------\n\n"
      in
      let _, dcls = Trans01.trans_dcls [] dcls in
      let s = str "%a@." Pprint1.pp_dcls dcls in
      let _ = Printf.fprintf ch_out "%s" s in
      let _ =
        Printf.fprintf ch_out
          "trans01 success---------------------------------------\n\n"
      in
      let dcls = Elab1.elab_dcls dcls in
      let s = str "%a@." Pprint1.pp_dcls dcls in
      let _ = Printf.fprintf ch_out "%s" s in
      let _ =
        Printf.fprintf ch_out
          "elab1 success---------------------------------------\n\n"
      in
      let dcls = Dyntype1.check_dcls dcls in
      let s = str "%a@." Pprint2.pp_dcls dcls in
      let _ = Printf.fprintf ch_out "%s" s in
      let _ =
        Printf.fprintf ch_out
          "dyntype1 success---------------------------------------\n\n"
      in
      ()
    | Failed (s, _) -> epr "%s\n" s
  with
  | Failure s -> epr "Failure: %s" s

let _ =
  if Array.length Sys.argv < 1 then
    epr "input file expected@."
  else
    let s = Sys.argv.(1) in
    run s (s ^ ".out")
