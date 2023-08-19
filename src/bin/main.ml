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

let main =
  let specs = [ ("-g", Arg.Unit Debug.enable, "Debug Mode") ] in
  let usage = "[-g] <src>" in
  let src_opt = ref None in
  let anon str = src_opt := Some str in
  Printexc.record_backtrace true;
  Arg.parse specs anon usage;
  match !src_opt with
  | Some src_file -> (
    try
      let src_ch = open_in src_file in
      let dcls0 = parse (Utf8.from_channel src_ch) in
      pr "%a" Syntax0.pp_dcls dcls0;
      pr "@.@.-----------------------------------------@.@.";
      let _, dcls1 = Trans01.trans_dcls [] dcls0 in
      pr "%a" Pprint1.pp_dcls dcls1;
      pr "@.@.-----------------------------------------@.@.";
      let dcls1e = Trans1e.trans_dcls dcls1 in
      pr "%a" Pprint1.pp_dcls dcls1e;
      pr "@.@.-----------------------------------------@.@.";
      let dcls2 = Trans12.trans_dcls dcls1e in
      pr "%a" Pprint2.pp_dcls dcls2;
      pr "@.@.-----------------------------------------@.@.";
      let dcls2e = Trans2e.trans_dcls dcls2 in
      pr "%a" Pprint2.pp_dcls dcls2e;
      pr "@.@.-----------------------------------------@.@."
    with
    | e -> epr "%a" exn_backtrace (e, Printexc.get_raw_backtrace ()))
  | None -> epr "input file expected@."
