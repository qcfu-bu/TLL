open Fmt
open Bindlib
open Syntax0
open Trans01
open Sedlexing
open Parser

let prelude_src = "prelude/prelude.tll"

let prelude_nspc, prelude_dcls =
  let ch = open_in prelude_src in
  let dcls0 = parse (Utf8.from_channel ch) in
  trans_dcls [] dcls0

let prelude_ind id =
  try
    let ind, _, _, _ = Option.get (find_ind id prelude_nspc) in
    ind
  with
  | _ -> failwith "prelude_ind(%s)" id

let prelude_constr id =
  try
    let constr, _, _, _ = Option.get (find_constr id prelude_nspc) in
    constr
  with
  | _ -> failwith "prelude_c(%s)" id

let prelude_const id =
  try Option.get (find_const id prelude_nspc) with
  | _ -> failwith "prelude_i(%s)" id

let exists0 = prelude_ind "exists0"
let exists1 = prelude_ind "exists1"
