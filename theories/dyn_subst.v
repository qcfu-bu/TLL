From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_subst dyn_weak.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "Γ1 ; Δ1 ⊨ σ ⫤ Γ2 ; Δ2" (at level 50, σ, Γ2 at next level).

Inductive dyn_agree_subst :
  context term -> (var -> term) -> context term -> Prop :=
| agree_subst_nil σ :
  nil ⊢ σ ⊣ nil
| agree_subst_ty Δ σ Γ s A :
  Δ ⊢ σ ⊣ Γ ->
  A.[σ] :{s} Δ ⊢ up σ ⊣ A :{s} Γ
| agree_subst_n Δ σ Γ :
  Δ ⊢ σ ⊣ Γ ->
  _: Δ ⊢ up σ ⊣ _: Γ
| agree_subst_wkU Δ σ Γ n A :
  Δ ⊢ σ ⊣ Γ ->
  [Δ] ⊢ n : A.[σ] : U ->
  Δ ⊢ n .: σ ⊣ A :U Γ
| agree_subst_wkL Δ1 Δ2 Δ σ Γ n A :
  Δ1 ∘ Δ2 => Δ ->
  Δ1 ⊢ σ ⊣ Γ ->
  Δ2 ⊢ n : A.[σ] : L ->
  Δ ⊢ n .: σ ⊣ A :L Γ
| agree_subst_wkN Δ σ Γ n :
  Δ ⊢ σ ⊣ Γ ->
  Δ ⊢ n .: σ ⊣ _: Γ
| agree_subst_conv Δ σ Γ A B s l :
  A <: B ->
  [Δ] ⊢ B.[ren (+1)].[σ] : s @ l : U ->
  [Γ] ⊢ B : s @ l : U ->
  Δ ⊢ σ ⊣ A :{s} Γ ->
  Δ ⊢ σ ⊣ B :{s} Γ
where "Δ ⊢ σ ⊣ Γ" := (agree_subst Δ σ Γ).

