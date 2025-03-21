open Fmt
open TLL
open Bindlib
open Sedlexing
open Parser
open Debug

let debug_mode () =
  Debug.enable ();
  Printexc.record_backtrace true

let main =
  let specs = [ ("-g", Arg.Unit debug_mode, "Debug Mode") ] in
  let usage = "[-g] <src>" in
  let src_opt = ref None in
  let anon str = src_opt := Some str in
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
      pr "@.@.-----------------------------------------@.@.";
      let dcls3 = Trans23.trans_dcls dcls2e in
      pr "%a" Pprint3.pp_dcls dcls3;
      pr "@.@.-----------------------------------------@.@."
    with
    | Failure s -> epr "%s@." s
    | e -> epr "%a" exn_backtrace (e, Printexc.get_raw_backtrace ()))
  | None -> epr "input file expected@."
