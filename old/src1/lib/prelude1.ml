open Fmt
open Bindlib
open Syntax0
open Trans01
open Sedlexing
open Parsing

let prelude_src = "prelude/prelude.tll"

let prelude_nspc, prelude_dcls =
  let ch = open_in prelude_src in
  let dcls0 = parse (Utf8.from_channel ch) in
  trans_dcls [] dcls0

let prelude_d id =
  try
    let d, _ = Option.get (find_data id prelude_nspc) in
    d
  with
  | _ -> failwith "prelude_d(%s)" id

let prelude_c id =
  try
    let c, _, _ = Option.get (find_cons id prelude_nspc) in
    c
  with
  | _ -> failwith "prelude_c(%s)" id

let prelude_i id =
  try Option.get (find_const id prelude_nspc) with
  | _ -> failwith "prelude_i(%s)" id

(* unit *)
let unit_d = prelude_d "unit"
let tt_c = prelude_c "tt"

(* boolean *)
let bool_d = prelude_d "bool"
let true_c = prelude_c "true"
let false_c = prelude_c "false"
let andb_i = prelude_i "andb"
let orb_i = prelude_i "orb"
let notb_i = prelude_i "notb"

(* natural numbers *)
let nat_d = prelude_d "nat"
let o_c = prelude_c "O"
let s_c = prelude_c "S"
let addn_i = prelude_i "addn"
let muln_i = prelude_i "muln"
let eqn_i = prelude_i "eqn"
let lten_i = prelude_i "lten"
let gten_i = prelude_i "gten"
let ltn_i = prelude_i "ltn"
let gtn_i = prelude_i "gtn"

(* ascii strings *)
let ascii_d = prelude_d "ascii"
let ascii_c = prelude_c "Ascii"
let string_d = prelude_d "string"
let emptyString_c = prelude_c "EmptyString"
let string_c = prelude_c "String"
let cats_i = prelude_i "cats"
let strlen_i = prelude_i "strlen"

(* lists *)
let list_d = prelude_d "list"
let nil_c = prelude_c "nil"
let cons_c = prelude_c "cons"
let len_i = prelude_i "len"
let append_i = prelude_i "append"

(* standard IO channels *)
let stdin_t_i = prelude_i "stdin_t"
let stdout_t_i = prelude_i "stdout_t"
let stderr_t_i = prelude_i "stderr_t"
let readline_i = prelude_i "readline"
let print_i = prelude_i "print"
let prerr_i = prelude_i "prerr"
