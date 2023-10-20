From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_ctx sta_step.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "Γ ⊢ m : A" (at level 50, m, A at next level).
Inductive sta_type : sta_ctx -> term -> term -> Prop :=
| sta_axiom Γ :
  sta_wf Γ ->
  Γ ⊢ Ty : Ty
| sta_var Γ x A :
  sta_wf Γ ->
  sta_has Γ x A ->
  Γ ⊢ Var x : A
| sta_forall Γ A B :
  Γ ⊢ A : Ty ->
  (A :: Γ) ⊢ B : Ty ->
  Γ ⊢ Forall A B : Ty
| sta_arrow Γ A B :
  Γ ⊢ A : Ty ->
  (A :: Γ) ⊢ B.[ren (+1)] : Ty ->
  Γ ⊢ Arrow A B : Ty
| sta_lam Γ A B m :
  Γ ⊢ A : Ty ->
  (A :: Γ) ⊢ m : B ->
  Γ ⊢ Lam A m : Forall A B
| sta_fun Γ A B m :
  Γ ⊢ A : Ty ->
  (A :: Γ) ⊢ m : B.[ren (+1)] ->
  Γ ⊢ Fun A m : Arrow A B
| sta_inst Γ A B m n :
  Γ ⊢ m : Forall A B ->
  Γ ⊢ n : A ->
  Γ ⊢ Inst m n : B.[n/]
| sta_call Γ A B m n :
  Γ ⊢ m : Arrow A B ->
  Γ ⊢ n : A ->
  Γ ⊢ Call m n : B
| sta_unitT Γ :
  sta_wf Γ ->
  Γ ⊢ UnitT : Ty
| sta_unit Γ :
  sta_wf Γ ->
  Γ ⊢ Unit : UnitT
| sta_natT Γ :
  sta_wf Γ ->
  Γ ⊢ NatT : Ty
| sta_nat Γ n :
  sta_wf Γ ->
  Γ ⊢ Nat n : NatT
| sta_rand Γ m :
  Γ ⊢ m : UnitT ->
  Γ ⊢ Rand m : NatT
| sta_conv Γ A B m :
  A === B ->
  Γ ⊢ m : A ->
  Γ ⊢ B : Ty ->
  Γ ⊢ m : B
where "Γ ⊢ m : A" := (sta_type Γ m A)

with sta_wf : sta_ctx -> Prop :=
| sta_wf_nil : sta_wf nil
| sta_wf_cons Γ A :
  sta_wf Γ ->
  Γ ⊢ A : Ty ->
  sta_wf (A :: Γ).

Scheme sta_type_mut := Induction for sta_type Sort Prop
with sta_wf_mut := Induction for sta_wf Sort Prop.

Lemma sta_type_wf Γ m A : Γ ⊢ m : A -> sta_wf Γ.
Proof with eauto. elim=>{Γ m A}... Qed.
#[global] Hint Resolve sta_type_wf.

