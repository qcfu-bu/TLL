From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS ptr_res.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "H1 ; m ~>> H2 ; n" (at level 50, m, H2, n at next level).
Inductive ptr_step : dyn_ctx -> term -> dyn_ctx -> term -> Prop :=
| ptr_step_lam0 H m s l :
  l = size H ->
  H ; (Lam0 Box m s) ~>> (Lam0 Box m s :{s} H) ; (Ptr l)
| ptr_step_lam1 H m s l :
  l = size H ->
  H ; (Lam1 Box m s) ~>> (Lam1 Box m s :{s} H) ; (Ptr l)
| ptr_step_appL H H' m m' n :
  H ; m ~>> H' ; m' ->
  H ; App m n ~>> H' ; App m' n
| ptr_step_appR H H' m n n' :
  H ; n ~>> H' ; n' ->
  H ; App m n ~>> H' ; App m n'
| ptr_step_beta0 H H' l m n s :
  free H l (Lam0 Box m s) H' ->
  H ; App (Ptr l) n ~>> H' ; m.[Box/]
| ptr_step_beta1 H H' lf la m s :
  free H lf (Lam1 Box m s) H' ->
  H ; App (Ptr lf) (Ptr la) ~>> H' ; m.[Ptr la/]
| ptr_step_rwE H m :
  H ; Rw Box m Box ~>> H ; m
where "H1 ; m ~>> H2 ; n" := (ptr_step H1 m H2 n).
