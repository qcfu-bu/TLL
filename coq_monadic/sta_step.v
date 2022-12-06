From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS tll_ast sta_ctx.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "m ~> n" (at level 30).
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
| sta_step_io A A' :
  A ~> A' ->
  IO A ~> IO A'
| sta_step_return m m' :
  m ~> m' ->
  Return m ~> Return m'
| sta_step_letinL m m' n :
  m ~> m' ->
  LetIn m n ~> LetIn m' n
| sta_step_letinR m n n' :
  n ~> n' ->
  LetIn m n ~> LetIn m n'
| sta_step_letret m n :
  LetIn (Return m) n ~> n.[m/]
where "m ~> n" := (sta_step m n).

Notation sta_red := (star sta_step).
Notation "m ~>* n" := (sta_red m n) (at level 30).
Notation "m === n" := (conv sta_step m n) (at level 50).
