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
  | Some src_file ->
    (try
       let src_ch = open_in src_file in

       let dcls0 = parse (Utf8.from_channel src_ch) in
       pr "%a" Syntax0.pp_dcls dcls0;
       pr "@.@.parse success";
       pr "@.@.-----------------------------------------@.@.";

       let _, dcls1 = Trans01.trans_dcls Prelude1.prelude_nspc dcls0 in
       let dcls1 = Prelude1.prelude_dcls @ dcls1 in
       pr "%a" Pprint1.pp_dcls dcls1;
       pr "@.@.trans01 success";
       pr "@.@.-----------------------------------------@.@.";

       let dcls1e = Trans1e.trans_dcls dcls1 in
       pr "%a" Pprint1.pp_dcls dcls1e;
       pr "@.@.trans1e success";
       pr "@.@.-----------------------------------------@.@.";

       let dcls2 = Trans12.trans_dcls dcls1e in
       pr "%a" Pprint2.pp_dcls dcls2;
       pr "@.@.trans12 success";
       pr "@.@.-----------------------------------------@.@.";

       let dcls2e = Trans2e.trans_dcls dcls2 in
       pr "%a" Pprint2.pp_dcls dcls2e;
       pr "@.@.trans2e success";
       pr "@.@.-----------------------------------------@.@.";

       let dcls3 = Trans23.trans_dcls dcls2e in
       pr "%a" Pprint3.pp_dcls dcls3;
       pr "@.@.trans23 success";
       pr "@.@.-----------------------------------------@.@.";

       let dcls3e = Trans3e.trans_dcls dcls3 in
       pr "%a" Pprint3.pp_dcls dcls3e;
       pr "@.@.trans3e success";
       pr "@.@.-----------------------------------------@.@.";

       let dcls4 = Trans34.trans_dcls dcls3e in
       pr "%a" Pprint4.pp_dcls dcls4;
       pr "@.@.trans34 success";
       pr "@.@.-----------------------------------------@.@.";

       let dcls4e = Trans4e.trans_dcls dcls4 in
       pr "%a" Pprint4.pp_dcls dcls4e;
       pr "@.@.trans4e success";
       pr "@.@.-----------------------------------------@.@.";

       let dcls5 = Trans45.trans_dcls dcls4e in
       pr "%a" Pprint5.pp_prog dcls5;
       pr "@.@.trans45 success";
       pr "@.@.-----------------------------------------@.@.";

       let main_c = open_out "gen/main.c" in
       let main_h = open_out "gen/main.h" in
       Emitter.emit dcls5 main_h main_c;
       pr "compilation success";
       pr "@.@.-----------------------------------------@.@.";
     with
     | Failure s -> epr "%s@." s
     | e -> epr "%a" exn_backtrace (e, Printexc.get_raw_backtrace ()))
  | None -> epr "input file expected@."
