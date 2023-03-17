open Fmt
open Bindlib
open TLL
open Names
open Syntax1

let f = mk "f"
let r = mk "r"
let x = mk "x"
let z = mk "z"

let test =
  unbox
    (bind_var f
       (_Fix f (bind_var r (_Lam R U (bind_var x (_App (_Var r) (_Var x)))))))
