open Fmt
open TLL
open Bindlib
open Sedlexing
open Parser

let rec normalize_dcls env dcls =
  let open Syntax1 in
  let open Equality1 in
  match dcls with
  | Definition { name = x; relv; scheme = sch } :: dcls ->
    let xs, (m, a) = unmbind sch in
    let m = whnf ~expand:true env m in
    let a = whnf ~expand:true env a in
    let sch = bind_mvar xs (box_pair (lift_tm m) (lift_tm a)) in
    let env = Env.add_const x (unbox sch) env in
    Definition { name = x; relv; scheme = unbox sch } :: normalize_dcls env dcls
  | Inductive m :: dcls -> Inductive m :: normalize_dcls env dcls
  | [] -> []

let _ =
  try
    if Array.length Sys.argv < 1 then
      epr "input file expected@."
    else
      let src_name = Sys.argv.(1) in
      let src_ch = open_in src_name in
      let dcls0 = parse (Utf8.from_channel src_ch) in
      let _, dcls1 = Trans01.trans_dcls [] dcls0 in
      let dcls1_norm = normalize_dcls Equality1.Env.empty dcls1 in
      pr "%a" Syntax0.pp_dcls dcls0;
      pr "@.@.-----------------------------------------@.@.";
      pr "%a" Pprint1.pp_dcls dcls1;
      pr "@.@.-----------------------------------------@.@.";
      pr "%a" Pprint1.pp_dcls dcls1_norm
  with
  | Failure s ->
    let _ = pr "error -----------------------------------@.@." in
    pr "%s@." s
