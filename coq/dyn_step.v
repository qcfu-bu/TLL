From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS tll_ast.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive dyn_val : term -> Prop :=
| dyn_val_var x : dyn_val (Var x)
| dyn_val_lam0 A B s : dyn_val (Lam0 A B s)
| dyn_val_lam1 A B s : dyn_val (Lam1 A B s).

Reserved Notation "m ~>> n" (at level 30).
Inductive dyn_step : term -> term -> Prop :=
| dyn_appL m m' n :
  m ~>> m' ->
  App m n ~>> App m' n
| dyn_appR m n n' :
  n ~>> n' ->
  App m n ~>> App m n'
| dyn_beta0 A m n s :
  App (Lam0 A m s) n ~>> m.[n/]
| dyn_beta1 A m v s :
  dyn_val v ->
  App (Lam1 A m s) v ~>> m.[v/]
where "m ~>> n" := (dyn_step m n).

Notation dyn_red := (star dyn_step).
Notation "m ~>>* n" := (dyn_red m n) (at level 30).
