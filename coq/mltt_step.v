From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS mltt_ast mltt_ctx.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "m ~> n" (at level 50).
Inductive mltt_step : term -> term -> Prop :=
| mltt_step_piL A A' B :
  A ~> A' ->
  Pi A B ~> Pi A' B
| mltt_step_piR A B B' :
  B ~> B' ->
  Pi A B ~> Pi A B'
| mltt_step_lamL A A' m :
  A ~> A' ->
  Lam A m ~> Lam A' m
| mltt_step_lamR A m m' :
  m ~> m' ->
  Lam A m ~> Lam A m'
| mltt_step_appL m m' n :
  m ~> m' ->
  App m n ~> App m' n
| mltt_step_appR m n n' :
  n ~> n' ->
  App m n ~> App m n'
| mltt_step_beta A m n :
  App (Lam A m) n ~> m.[n/]
| mltt_step_sigL A A' B :
  A ~> A' ->
  Sig A B ~> Sig A' B
| mltt_step_sigR A B B' :
  B ~> B' ->
  Sig A B ~> Sig A B'
| mltt_step_dpairL m m' n :
  m ~> m' ->
  DPair m n ~> DPair m' n
| mltt_step_dpairR m n n' :
  n ~> n' ->
  DPair m n ~> DPair m n'
| mltt_step_letinA A A' m n :
  A ~> A' ->
  LetIn A m n ~> LetIn A' m n
| mltt_step_letinL A m m' n :
  m ~> m' ->
  LetIn A m n ~> LetIn A m' n
| mltt_step_letinR A m n n' :
  n ~> n' ->
  LetIn A m n ~> LetIn A m n'
| mltt_step_iota A m1 m2 n :
  LetIn A (DPair m1 m2) n ~> n.[m2,m1/]
| mltt_step_ifteA A A' m n1 n2 :
  A ~> A' ->
  Ifte A m n1 n2 ~> Ifte A' m n1 n2
| mltt_step_ifteM A m m' n1 n2 :
  m ~> m' ->
  Ifte A m n1 n2 ~> Ifte A m' n1 n2
| mltt_step_ifteN1 A m n1 n1' n2 :
  n1 ~> n1' ->
  Ifte A m n1 n2 ~> Ifte A m n1' n2
| mltt_step_ifteN2 A m n1 n2 n2' :
  n2 ~> n2' ->
  Ifte A m n1 n2 ~> Ifte A m n1 n2'
| mltt_step_ifteT A n1 n2 :
  Ifte A TT n1 n2 ~> n1
| mltt_step_ifteF A n1 n2 :
  Ifte A FF n1 n2 ~> n2
| mltt_step_idA A A' m n :
  A ~> A' ->
  Id A m n ~> Id A' m n
| mltt_step_idL A m m' n :
  m ~> m' ->
  Id A m n ~> Id A m' n
| mltt_step_idR A m n n' :
  n ~> n' ->
  Id A m n ~> Id A m n'
| mltt_step_refl m m' :
  m ~> m' ->
  Refl m ~> Refl m'
| mltt_step_rwA A A' H P :
  A ~> A' ->
  Rw A H P ~> Rw A' H P
| mltt_step_rwH A H H' P :
  H ~> H' ->
  Rw A H P ~> Rw A H' P
| mltt_step_rwP A H P P' :
  P ~> P' ->
  Rw A H P ~> Rw A H P'
| mltt_step_rwE A H m :
  Rw A H (Refl m) ~> H
where "m ~> n" := (mltt_step m n).

Notation mltt_red := (star mltt_step).
Notation "m ~>* n" := (mltt_red m n) (at level 50).
Notation "m ≃ n" := (conv mltt_step m n) (at level 50).
