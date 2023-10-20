From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS etl_ast sta_step.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive dyn_val : term -> Prop :=
| dyn_val_ty : 
  dyn_val Ty
| dyn_val_forall A B : 
  dyn_val (Forall A B)
| dyn_val_arrow A B : 
  dyn_val (Arrow A B)
| dyn_val_lam A m :
  dyn_val (Lam A m)
| dyn_val_fun A m :
  dyn_val (Fun A m)
| dyn_val_unitT :
  dyn_val UnitT
| dyn_val_unit :
  dyn_val Unit
| dyn_val_natT :
  dyn_val NatT
| dyn_val_nat n :
  dyn_val (Nat n).

Reserved Notation "m ~>> n" (at level 50).
Inductive dyn_step : term -> term -> Prop :=
| dyn_step_instL m m' n :
  m ~>> m' ->
  Inst m n ~>> Inst m' n
| dyn_step_instR A m n n' :
  n ~> n' ->
  Inst (Lam A m) n ~>> Inst (Lam A m) n'
| dyn_step_betaI A m n :
  Inst (Lam A m) n ~>> m.[n/]
| dyn_step_callL m m' n :
  m ~>> m' ->
  Call m n ~>> Call m' n
| dyn_step_callR A m n n' :
  n ~>> n' ->
  Call (Fun A m) n ~>> Call (Fun A m) n'
| dyn_step_betaC A m v :
  dyn_val v ->
  Call (Fun A m) v ~>> m.[v/]
| dyn_step_rand m m' :
  m ~>> m' ->
  Rand m ~>> Rand m'
| dyn_step_randE n :
  Rand Unit ~>> Nat n
where "m ~>> n" := (dyn_step m n).

Notation dyn_red := (star dyn_step).
Notation "m ~>>* n" := (dyn_red m n) (at level 50).
