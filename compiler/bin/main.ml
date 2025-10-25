open Fmt
open TLL
open Bindlib
open Sedlexing
open Debug
open Names

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
      let main_c = Format.formatter_of_out_channel (open_out "gen/main.c") in
      let main_h = Format.formatter_of_out_channel (open_out "gen/main.h") in
      let dcls = Parser.parse (Utf8.from_channel src_ch) in
      let dcls = Trans01.trans_dcls Prelude1.prelude_nspc dcls in
      let dcls = Prelude1.prelude_dcls @ dcls in
      let dcls = Trans1e.trans_dcls dcls in
      let dcls = Trans12.trans_dcls dcls in
      let dcls = Trans2e.trans_dcls dcls in
      let dcls = Trans23.trans_dcls dcls in
      let dcls = Trans3e.trans_dcls dcls in
      let dcls = Trans34.trans_dcls dcls in
      let dcls = Trans4e.trans_dcls dcls in
      let dcls = Trans45.trans_dcls dcls in
      Emitter.emit dcls main_h main_c;
      pr "@.-----------------------------------------@.@.";
      pr "compilation successful@.";
      pr "mvars(sort)     : %d@." (SMeta.get_count ());
      pr "mvars(inference): %d@." (IMeta.get_count ());
      pr "equations checked: %d@.@." (Debug.eqn_count_get ())
    with
    | Failure s -> epr "%s@." s
    | e -> epr "%a" exn_backtrace (e, Printexc.get_raw_backtrace ()))
  | None -> epr "input file expected@."
