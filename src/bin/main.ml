open Fmt
open TLL
open Bindlib
open Sedlexing
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
  | Some src_file ->
    (try
       let src_ch = open_in src_file in
       let main_c = Format.formatter_of_out_channel (open_out "gen/main.c") in
       let main_h = Format.formatter_of_out_channel (open_out "gen/main.h") in

       let dcls0 = Parser.parse (Utf8.from_channel src_ch) in
       let dcls1 = Trans01.trans_dcls Prelude1.prelude_nspc dcls0 in
       let dcls1 = Prelude1.prelude_dcls @ dcls1 in
       let dcls1e = Trans1e.trans_dcls dcls1 in
       let dcls2 = Trans12.trans_dcls dcls1e in
       let dcls2e = Trans2e.trans_dcls dcls2 in
       let dcls3 = Trans23.trans_dcls dcls2e in
       let dcls3e = Trans3e.trans_dcls dcls3 in
       let dcls4 = Trans34.trans_dcls dcls3e in
       let dcls4e = Trans4e.trans_dcls dcls4 in
       let dcls5 = Trans45.trans_dcls dcls4e in
       Emitter.emit dcls5 main_h main_c;
     with
     | Failure s -> epr "%s@." s
     | e -> epr "%a" exn_backtrace (e, Printexc.get_raw_backtrace ()))
  | None -> epr "input file expected@."
