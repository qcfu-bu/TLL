From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS tll_ast.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "m ~> n" (at level 30).
Inductive sta_step : term -> term -> Prop :=
| sta_pi0L A A' B s t :
  A ~> A' ->
  Pi0 A B s t ~> Pi0 A' B s t
| sta_pi1L A A' B s t :
  A ~> A' ->
  Pi1 A B s t ~> Pi1 A' B s t
| sta_pi0R A B B' s t :
  B ~> B' ->
  Pi0 A B s t ~> Pi0 A B' s t
| sta_pi1R A B B' s t :
  B ~> B' ->
  Pi1 A B s t ~> Pi1 A B' s t
| sta_lam0L A A' m s t :
  A ~> A' ->
  Lam0 A m s t ~> Lam0 A' m s t
| sta_lam1L A A' m s t :
  A ~> A' ->
  Lam1 A m s t ~> Lam1 A' m s t
| sta_lam0R A m m' s t :
  m ~> m' ->
  Lam0 A m s t ~> Lam0 A m' s t
| sta_lam1R A m m' s t :
  m ~> m' ->
  Lam1 A m s t ~> Lam1 A m' s t
| sta_appL m m' n :
  m ~> m' ->
  App m n ~> App m' n
| sta_appR m n n' :
  n ~> n' ->
  App m n ~> App m n'
| sta_beta0 A m n s t :
  (App (Lam0 A m s t) n) ~> m.[n/]
| sta_beta1 A m n s t :
  (App (Lam1 A m s t) n) ~> m.[n/]
where "m ~> n" := (sta_step m n).

Notation sta_red := (star sta_step).
Notation "m ~>* n" := (sta_red m n) (at level 30).
Notation "m === n" := (conv sta_step m n) (at level 50).
