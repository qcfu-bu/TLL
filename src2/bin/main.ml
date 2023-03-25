open Fmt
open Bindlib
open TLL
open Names
open Syntax0

let test0 = Lam (R, U, Binder ("x", Id "x"))

let test1 =
  Lam (R, U, Binder ("x", Lam (N, L, Binder ("y", App [ Id "x"; Id "y" ]))))

let test2 =
  DTm
    ( R
    , "A"
    , ABind
        ( N
        , Type U
        , Binder ("A", ABind (R, Id "A", Binder ("A", ABase (Id "A", Id "A"))))
        ) )

let _, test3 = Trans01.trans_dcls [] [ test2; test2 ]
let test3 = unbox test3
let _ = pr "%a@." Pprint1.pp_dcls test3

open Sedlexing
open Tokenize

let test4 = parse (Utf8.from_string "\\- ok -\\ fn x {y} ⇒ x")

let test4 =
  parse (Utf8.from_string "let {f : ∀ (x : nat) ⊸ nat} = ln x y ⇒ x in f")

let test4 = parse (Utf8.from_string "bind (f x) fn (x y : nat) ⇒ x")
let test4 = parse (Utf8.from_string "ln (x : nat) ⇒ x")
let test5 = parse (Utf8.from_string "Vec x y z")
let test5 = parse (Utf8.from_string "∀ (x : nat) (v : vec x) → unit")
let test5 = parse (Utf8.from_string "∀ (x : nat) {v : vec x} → unit")
let test5 = parse (Utf8.from_string "∀ (x : nat) {v : vec x} ⊸ unit")
let test6 = parse (Utf8.from_string "f (x, y) (fn x ⇒ x)")
let test6 = parse (Utf8.from_string "∀ (f a b : U) → f a ≡ b → f b")
let _ = pr "%a@." Pprint0.pp_tm test6
let test6 = unbox (Trans01.trans_tm [] test6)
let test7 = parse (Utf8.from_string "fn x ⇒ rew [ x, _ ⇒ x ≡ a ] pf in H")
