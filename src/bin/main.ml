open Fmt
open TLL
open Bindlib
open Sedlexing
open Parser
open Debug

let pp_prbms fmt groups =
  let open Constraint1e in
  let open Context1e in
  let rec aux i fmt = function
    | [] -> ()
    | [ (eqns, mctx) ] ->
      pf fmt "@[<v 0>group%d {|@;<1 2>@[<v 0>%a@;<1 0>%a@]@;<1 0>|}@]" i
        IPrbm.pp_eqns eqns MCtx.pp mctx
    | (eqns, mctx) :: prbms ->
      pf fmt "@[<v 0>group%d {|@;<1 2>@[<v 0>%a@;<1 0>%a@]@;<1 0>|}@]@.@.%a" i
        IPrbm.pp_eqns eqns MCtx.pp mctx
        (aux (i + 1))
        prbms
  in
  aux 0 fmt groups

let _ =
  try
    if Array.length Sys.argv < 1 then
      epr "input file expected@."
    else
      let _ = Debug.enable () in
      let src_name = Sys.argv.(1) in
      let src_ch = open_in src_name in
      let dcls0 = parse (Utf8.from_channel src_ch) in
      pr "%a" Syntax0.pp_dcls dcls0;
      pr "@.@.-----------------------------------------@.@.";
      let _, dcls1 = Trans01.trans_dcls [] dcls0 in
      pr "%a" Pprint1.pp_dcls dcls1;
      pr "@.@.-----------------------------------------@.@.";
      let dcls1e = Trans1e.trans_dcls dcls1 in
      pr "%a" Pprint1.pp_dcls dcls1e;
      pr "@.@.-----------------------------------------@.@."
  with
  | Failure s ->
    let _ = pr "error -----------------------------------@.@." in
    pr "%s@." s
