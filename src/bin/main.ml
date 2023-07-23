open Bindlib
open TLL
open Lang2
open Syntax
open Util

let x = Var.mk [||] "x"
let y = Var.mk [||] "y"
let m = _Lam N _U (_Type _U) (bind_var x (_Var x (box [||])))
(* let () = print_endline "Hello, World!" *)
