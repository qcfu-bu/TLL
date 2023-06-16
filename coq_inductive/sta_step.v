From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS tll_ast.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Fixpoint mkApps (h : term) (ls : list (bool * term)%type) : term :=
  match ls with
  | nil => h
  | (false, m) :: ls => mkApps (App0 h m) ls
  | (true,  m) :: ls => mkApps (App1 h m) ls
  end.

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
where "m ~> n" := (sta_step m n).
