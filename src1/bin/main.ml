open Fmt
open Tll
open Names
open Syntax1
open Equality1

let x = V.mk "x"
let y = V.mk "y"
let z = V.mk "z"

let m =
  lam R U x None
    (lam R U y None (App (Var x, Var y)))
let m = App (m, Var z)

let a = V.mk "a"
let b = V.mk "b"
let c = V.mk "c"

let n =
  lam R U a None
    (lam R U b None (App (Var a, Var b)))
let n = App (n, Var c)

(* let () = *)
(*   pr "equal(%a, %a) = %b\n"  *)
(*     V.pp z V.pp c (V.equal z c) *)

let () =
  let m' = whnf [Beta] VMap.empty m in
  let n' = whnf [Beta] VMap.empty n in
  pr "term{%a}, term{%a} = %b\n"
    pp_tm m' pp_tm n'
    (equal [Beta] VMap.empty m n)
