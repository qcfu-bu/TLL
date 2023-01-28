From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS tll_ast sta_ctx.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive sta_val : term -> Prop :=
| sta_val_var x :
  sta_val (Var x)
| sta_val_sort s :
  sta_val (Sort s)
| sta_val_pi0 A B s :
  sta_val (Pi0 A B s)
| sta_val_pi1 A B s :
  sta_val (Pi1 A B s)
| sta_val_lam0 A m s :
  sta_val (Lam0 A m s)
| sta_val_lam1 A m s :
  sta_val (Lam1 A m s)
| sta_val_id A m n :
  sta_val (Id A m n)
| sta_val_refl m :
  sta_val (Refl m).

Reserved Notation "m ~> n" (at level 50).
Inductive sta_step : term -> term -> Prop :=
| sta_step_pi0L A A' B s :
  A ~> A' ->
  Pi0 A B s ~> Pi0 A' B s
| sta_step_pi1L A A' B s :
  A ~> A' ->
  Pi1 A B s ~> Pi1 A' B s
| sta_step_pi0R A B B' s :
  B ~> B' ->
  Pi0 A B s ~> Pi0 A B' s
| sta_step_pi1R A B B' s :
  B ~> B' ->
  Pi1 A B s ~> Pi1 A B' s
| sta_step_lam0L A A' m s :
  A ~> A' ->
  Lam0 A m s ~> Lam0 A' m s
| sta_step_lam1L A A' m s :
  A ~> A' ->
  Lam1 A m s ~> Lam1 A' m s
| sta_step_lam0R A m m' s :
  m ~> m' ->
  Lam0 A m s ~> Lam0 A m' s
| sta_step_lam1R A m m' s :
  m ~> m' ->
  Lam1 A m s ~> Lam1 A m' s
| sta_step_appL m m' n :
  m ~> m' ->
  App m n ~> App m' n
| sta_step_appR m n n' :
  n ~> n' ->
  App m n ~> App m n'
| sta_step_beta0 A m n s :
  App (Lam0 A m s) n ~> m.[n/]
| sta_step_beta1 A m n s :
  App (Lam1 A m s) n ~> m.[n/]
| sta_step_idA A A' m n :
  A ~> A' ->
  Id A m n ~> Id A' m n
| sta_step_idL A m m' n :
  m ~> m' ->
  Id A m n ~> Id A m' n
| sta_step_idR A m n n' :
  n ~> n' ->
  Id A m n ~> Id A m n'
| sta_step_refl m m' :
  m ~> m' ->
  Refl m ~> Refl m'
| sta_step_rwA A A' H P :
  A ~> A' ->
  Rw A H P ~> Rw A' H P
| sta_step_rwH A H H' P :
  H ~> H' ->
  Rw A H P ~> Rw A H' P
| sta_step_rwP A H P P' :
  P ~> P' ->
  Rw A H P ~> Rw A H P'
| sta_step_rwE A H m :
  Rw A H (Refl m) ~> H
where "m ~> n" := (sta_step m n).

Notation sta_red := (star sta_step).
Notation "m ~>* n" := (sta_red m n) (at level 50).
Notation "m === n" := (conv sta_step m n) (at level 50).
