From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS
  sta_ctx sta_step sta_type
  dyn_ctx dyn_step.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "Γ ; Δ ⊨ m : A" (at level 50, m, A at next level).
Inductive dyn_type : sta_ctx -> dyn_ctx -> term -> term -> Prop :=
| dyn_var Γ Δ x A :
  sta_has Γ x A ->
  dyn_has Δ x A ->
  Γ ; Δ ⊨ Var x : A
| dyn_lam0 Γ Δ A B m s t :
  Δ ▷ t ->
  Γ ⊢ Pi0 A B s t : @t ->
  (A :: Γ) ; (_: Δ) ⊨ m : B ->
  Γ ; Δ ⊨ Lam0 A m s t : Pi0 A B s t
| dyn_lam1 Γ Δ A B m s t :
  Δ ▷ t ->
  Γ ⊢ Pi1 A B s t : @t ->
  (A :: Γ) ; (A :{s} Δ) ⊨ m : B ->
  Γ ; Δ ⊨ Lam1 A m s t : Pi1 A B s t
| dyn_app0 Γ Δ A B m n s t :
  Γ ; Δ ⊨ m : Pi0 A B s t ->
  Γ ⊢ n : A ->
  Γ ; Δ ⊨ App m n : B.[n/]
| dyn_app1 Γ Δ1 Δ2 Δ A B m n s t :
  Δ1 ∘ Δ2 => Δ ->
  Γ ; Δ1 ⊨ m : Pi1 A B s t ->
  Γ ; Δ2 ⊨ n : A ->
  Γ ; Δ ⊨ App m n : B.[n/]
| dyn_conv Γ Δ A B m s :
  A === B ->
  Γ ; Δ ⊨ m : A ->
  Γ ⊢ B : @s ->
  Γ ; Δ ⊨ m : B
where "Γ ; Δ ⊨ m : A" := (dyn_type Γ Δ m A).

Inductive dyn_wf : sta_ctx -> dyn_ctx -> Prop :=
| dyn_wf_nil : dyn_wf nil nil
| dyn_wf_ty Γ Δ A s :
  dyn_wf Γ Δ ->
  Γ ⊢ A : @s ->
  dyn_wf (A :: Γ) (A :{s} Δ)
| dyn_wf_n Γ Δ A s :
  dyn_wf Γ Δ ->
  Γ ⊢ A : @s ->
  dyn_wf (A :: Γ) (_: Δ).
