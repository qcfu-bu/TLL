From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_valid dyn_type.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma dyn_sta_type Θ Γ Δ m A : Θ ; Γ ; Δ ⊢ m : A -> Γ ⊢ m : A.
Proof with eauto using sta_type, sta_wf.
  move:Γ Δ m A.
  apply:(@dyn_type_mut _ (fun Γ Δ wf => sta_wf Γ))...
  Unshelve. all: eauto using bool.
Qed.
Hint Resolve dyn_sta_type.

Theorem dyn_valid Θ Γ Δ m A : Θ ; Γ ; Δ ⊢ m : A -> exists s, Γ ⊢ A : Sort s.
Proof.
  move=>ty.
  apply: sta_valid.
  apply: dyn_sta_type; eauto.
Qed.
