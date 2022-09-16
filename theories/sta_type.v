From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_ctx sta_step.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "Γ ⊢ m : A" (at level 50, m, A at next level).

Inductive sta_type : sta_ctx term -> term -> term -> Prop :=
| sta_axiom Γ s :
  Γ ⊢ @s : @U
| sta_var Γ x A :
  sta_has Γ x A ->
  Γ ⊢ Var x : A
| sta_pi0 Γ A B s r t :
  Γ ⊢ A : @s ->
  (A :: Γ) ⊢ B : @r ->
  Γ ⊢ Pi0 A B s t : @t
| sta_pi1 Γ A B s r t :
  Γ ⊢ A : @s ->
  (A :: Γ) ⊢ B : @r ->
  Γ ⊢ Pi1 A B s t : @t
| sta_lam0 Γ A B m s t :
  Γ ⊢ Pi0 A B s t : @t ->
  (A :: Γ) ⊢ m : B ->
  Γ ⊢ Lam0 A m s t : Pi0 A B s t
| sta_lam1 Γ A B m s t :
  Γ ⊢ Pi1 A B s t : @t ->
  (A :: Γ) ⊢ m : B ->
  Γ ⊢ Lam1 A m s t : Pi1 A B s t
| sta_app0 Γ A B m n s t :
  Γ ⊢ m : Pi0 A B s t ->
  Γ ⊢ n : A ->
  Γ ⊢ App m n : B.[n/]
| sta_app1 Γ A B m n s t :
  Γ ⊢ m : Pi1 A B s t ->
  Γ ⊢ n : A ->
  Γ ⊢ App m n : B.[n/]
| sta_conv Γ A B m s :
  A === B ->
  Γ ⊢ m : A ->
  Γ ⊢ B : @s ->
  Γ ⊢ m : B
where "Γ ⊢ m : A" := (sta_type Γ m A).

Inductive sta_wf : sta_ctx term -> Prop :=
| sta_wf_nil : sta_wf nil
| sta_wf_cons Γ A s :
  sta_wf Γ ->
  Γ ⊢ A : @s ->
  sta_wf (A :: Γ).
