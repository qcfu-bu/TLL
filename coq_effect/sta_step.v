From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS etl_ast sta_ctx.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "m ~> n" (at level 50).
Inductive sta_step : term -> term -> Prop :=
| sta_step_forallL A A' B :
  A ~> A' ->
  Forall A B ~> Forall A' B
| sta_step_forallR A B B' :
  B ~> B' ->
  Forall A B ~> Forall A B'
| sta_step_arrowL A A' B :
  A ~> A' ->
  Arrow A B ~> Arrow A' B
| sta_step_arrowR A B B' :
  B ~> B' ->
  Arrow A B ~> Arrow A B'
| sta_step_lamL A A' m :
  A ~> A' ->
  Lam A m ~> Lam A' m
| sta_step_lamR A m m' :
  m ~> m' ->
  Lam A m ~> Lam A m'
| sta_step_funL A A' m :
  A ~> A' ->
  Fun A m ~> Fun A' m
| sta_step_funR A m m' :
  m ~> m' ->
  Fun A m ~> Fun A m'
| sta_step_instL m m' n : 
  m ~> m' ->
  Inst m n ~> Inst m' n
| sta_step_instR m n n' : 
  n ~> n' ->
  Inst m n ~> Inst m n'
| sta_step_callL m m' n : 
  m ~> m' ->
  Call m n ~> Call m' n
| sta_step_callR m n n' : 
  n ~> n' ->
  Call m n ~> Call m n'
| sta_step_betaI A m n :
  Inst (Lam A m) n ~> m.[n/]
| sta_step_betaC A m n :
  Call (Fun A m) n ~> m.[n/]
| sta_step_rand m m' :
  m ~> m' ->
  Rand m ~> Rand m'
where "m ~> n" := (sta_step m n).

Notation sta_red := (star sta_step).
Notation "m ~>* n" := (sta_red m n) (at level 50).
Notation "m === n" := (conv sta_step m n) (at level 50).
