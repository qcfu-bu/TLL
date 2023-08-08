open Fmt
open TLL
open Bindlib
open Sedlexing
open Parser

let rec normalize_dcls ctx dcls =
  let open Syntax1 in
  let open Context1 in
  let open Equality1 in
  match dcls with
  | Definition { name = x; relv; scheme = sch } :: dcls ->
    let xs, (m, a) = unmbind sch in
    let m = whnf ~expand:true ctx m in
    let a = whnf ~expand:true ctx a in
    let sch = bind_mvar xs (box_pair (lift_tm m) (lift_tm a)) in
    let env = Ctx.add_const x (unbox sch) ctx in
    Definition { name = x; relv; scheme = unbox sch } :: normalize_dcls env dcls
  | Inductive m :: dcls -> Inductive m :: normalize_dcls ctx dcls
  | [] -> []

let pp_prbms fmt groups =
  let open Constraint1 in
  let open Context1 in
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
      let src_name = Sys.argv.(1) in
      let src_ch = open_in src_name in
      let dcls0 = parse (Utf8.from_channel src_ch) in
      let _, dcls1 = Trans01.trans_dcls [] dcls0 in
      let prbms =
        let open Context1 in
        let open Equality1 in
        Trans1e.check_dcls Ctx.empty dcls1
      in
      pr "%a" Syntax0.pp_dcls dcls0;
      pr "@.@.-----------------------------------------@.@.";
      pr "%a" Pprint1.pp_dcls dcls1;
      pr "@.@.-----------------------------------------@.@.";
      pr "%a" pp_prbms prbms;
      pr "@.@.-----------------------------------------@.@."
  with
  | Failure s ->
    let _ = pr "error -----------------------------------@.@." in
    pr "%s@." s
