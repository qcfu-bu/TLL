From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS tll_ast.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive dyn_val : term -> Prop :=
| dyn_val_lam0 A B s t : dyn_val (Lam0 A B s t)
| dyn_val_lam1 A B s t : dyn_val (Lam1 A B s t).

Reserved Notation "m ~>> n" (at level 30).
Inductive dyn_step : term -> term -> Prop :=
| dyn_appL m m' n :
  m ~>> m' ->
  App m n ~>> App m' n
| dyn_appR m n n' :
  n ~>> n' ->
  App m n ~>> App m n'
| dyn_beta0 A m n s t :
  App (Lam0 A m s t) n ~>> m.[n/]
| dyn_beta1 A m v s t :
  dyn_val v ->
  App (Lam1 A m s t) v ~>> m.[v/]
where "m ~>> n" := (dyn_step m n).

Notation dyn_red := (star dyn_step).
Notation "m ~>>* n" := (dyn_red m n) (at level 30).
