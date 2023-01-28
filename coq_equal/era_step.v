From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS tll_ast dyn_step.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "m ~>>> n" (at level 50).
Inductive era_step : term -> term -> Prop :=
| era_appL m m' n :
  m ~>>> m' ->
  App m n ~>>> App m' n
| era_appR m n n' :
  n ~>>> n' ->
  App m n ~>>> App m n'
| era_step_beta0 A m n s :
  App (Lam0 A m s) n ~>>> m.[n/]
| era_step_beta1 A m v s :
  dyn_val v ->
  App (Lam1 A m s) v ~>>> m.[v/]
| era_step_rwE A H P :
  Rw A H P ~>>> H
where "m ~>>> n" := (era_step m n).

Notation era_red := (star era_step).
Notation "m ~>>>* n" := (era_red m n) (at level 50).
