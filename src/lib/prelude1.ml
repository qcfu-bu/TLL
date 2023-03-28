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
  try Option.get (find_d id prelude_nspc) with
  | _ -> failwith id

let prelude_c id =
  try fst (Option.get (find_c id prelude_nspc)) with
  | _ -> failwith id

let prelude_v id =
  try Option.get (find_v id prelude_nspc) with
  | _ -> failwith id

(* unit *)
let unit_d = prelude_d "unit"
let tt_c = prelude_c "tt"

(* boolean *)
let bool_d = prelude_d "bool"
let true_c = prelude_c "true"
let false_c = prelude_c "false"
let andb_v = prelude_v "andb"
let orb_v = prelude_v "orb"
let notb_v = prelude_v "notb"

(* natural numbers *)
let nat_d = prelude_d "nat"
let o_c = prelude_c "O"
let s_c = prelude_c "S"
let addn_v = prelude_v "addn"
let muln_v = prelude_v "muln"
let eqn_v = prelude_v "eqn"
let lten_v = prelude_v "lten"
let gten_v = prelude_v "gten"
let ltn_v = prelude_v "ltn"
let gtn_v = prelude_v "gtn"

(* ascii strings *)
let ascii_d = prelude_d "ascii"
let ascii_c = prelude_c "Ascii"
let string_d = prelude_d "string"
let emptyString_c = prelude_c "EmptyString"
let string_c = prelude_c "String"
let cats_v = prelude_v "cats"
let strlen_v = prelude_v "strlen"

(* lists *)
let list_d = prelude_d "list"
let nil_c = prelude_c "nil"
let cons_c = prelude_c "cons"
let llist_d = prelude_d "llist"
let lnil_c = prelude_c "lnil"
let lcons_c = prelude_c "lcons"
let len_v = prelude_v "len"

(* let llen_v = prelude_v "llen" *)
let append_v = prelude_v "append"
let lappend_v = prelude_v "lappend"

(* linear box *)
let box_d = prelude_d "box"
let box_c = prelude_c "Box"
let map_box_v = prelude_v "map_box"
let unbox_v = prelude_v "unbox"

(* standard IO channels *)
let stdin_t_v = prelude_v "stdin_t"
let stdout_t_v = prelude_v "stdout_t"
let stderr_t_v = prelude_v "stderr_t"
let readline_v = prelude_v "readline"
let print_v = prelude_v "print"
let prerr_v = prelude_v "prerr"
