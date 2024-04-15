From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS ptr_res.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "H1 ; m ~>> H2 ; n" (at level 50, m, H2, n at next level).
Inductive ptr_step : heap -> term -> heap -> term -> Prop :=
| ptr_step_lam0 H m s l :
  l \notin domm H ->
  H ; Lam0 Box m s ~>> setm H l (Lam0 Box m s, s) ; Ptr l
| ptr_step_lam1 H m s l :
  l \notin domm H ->
  H ; Lam1 Box m s ~>> setm H l (Lam1 Box m s, s) ; (Ptr l)
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
| ptr_step_pair0L H H' m m' t :
  H ; m ~>> H' ; m' ->
  H ; Pair0 m Box t ~>> H' ; Pair0 m' Box t
| ptr_step_pair0 H l lm t :
  l \notin domm H ->
  H ; Pair0 (Ptr lm) Box t ~>> setm H l (Pair0 (Ptr lm) Box t, t) ; Ptr l
| ptr_step_pair1L H H' m m' n t :
  H ; m ~>> H' ; m' ->
  H ; Pair1 m n t ~>> H' ; Pair1 m' n t
| ptr_step_pair1R H H' m n n' t :
  H ; n ~>> H' ; n' ->
  H ; Pair1 m n t ~>> H' ; Pair1 m n' t
| ptr_step_pair1 H l lm ln t :
  l \notin domm H ->
  H ; Pair1 (Ptr lm) (Ptr ln) t ~>> setm H l (Pair1 (Ptr lm) (Ptr ln) t, t) ; Ptr l
| ptr_step_letinL H H' m m' n :
  H ; m ~>> H' ; m' ->
  H ; LetIn Box m n ~>> H' ; LetIn Box m' n
| ptr_step_iota0 H H' lm x l n t :
  free H l (Pair0 (Ptr lm) x t) H' ->
  H ; LetIn Box (Ptr l) n ~>> H' ; n.[Box,Ptr lm/]
| ptr_step_iota1 H H' lm ln l n t :
  free H l (Pair1 (Ptr lm) (Ptr ln) t) H' ->
  H ; LetIn Box (Ptr l) n ~>> H' ; n.[Ptr ln,Ptr lm/]
| ptr_step_tt H l :
  l \notin domm H ->
  H ; TT ~>> setm H l (TT, U) ; (Ptr l)
| ptr_step_ff H l :
  l \notin domm H ->
  H ; FF ~>> setm H l (FF, U) ; (Ptr l)
| ptr_step_ifteM H H' m m' n1 n2 :
  H ; m ~>> H' ; m' ->
  H ; Ifte Box m n1 n2 ~>> H' ; Ifte Box m' n1 n2
| ptr_step_ifteT H H' l n1 n2 :
  free H l TT H' ->
  H ; Ifte Box (Ptr l) n1 n2 ~>> H' ; n1
| ptr_step_ifteF H H' l n1 n2 :
  free H l FF H' ->
  H ; Ifte Box (Ptr l) n1 n2 ~>> H' ; n2
| ptr_step_rwE H m :
  H ; Rw Box m Box ~>> H ; m
where "H1 ; m ~>> H2 ; n" := (ptr_step H1 m H2 n).
