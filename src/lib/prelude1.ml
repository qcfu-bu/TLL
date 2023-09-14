open Fmt
open Bindlib
open Syntax0
open Trans01
open Spec
open Sedlexing
open Tokenize
open Parser

let prelude_src = "prelude/prelude.tll"

let prelude_nspc, prelude_dcls =
  let lexbuf = Utf8.from_channel (open_in prelude_src) in
  let lexer = with_tokenizer tokenize lexbuf in
  let dcls0 = loop lexer (Incremental.main (fst (lexing_positions lexbuf))) in
  trans_dcls0 [] dcls0

let prelude_ind id =
  try
    let ind, _, _, _ = Option.get (find_ind id prelude_nspc) in
    ind
  with _ -> failwith "prelude_ind(%s)" id

let prelude_constr id =
  try
    let constr, _, _, _ = Option.get (find_constr id prelude_nspc) in
    constr
  with _ -> failwith "prelude_c(%s)" id

let prelude_const id =
  try Option.get (find_const id prelude_nspc)
  with _ -> failwith "prelude_i(%s)" id

let unit_ind = prelude_ind "unit"
let tt_constr = prelude_constr "tt"

let exists0_ind = prelude_ind "exists0"
let exists1_ind = prelude_ind "exists1"

let ex0_constr = prelude_constr "ex0"
let ex1_constr = prelude_constr "ex1"

let bool_ind = prelude_ind "bool"

let true_constr = prelude_constr "true"
let false_constr = prelude_constr "false"
