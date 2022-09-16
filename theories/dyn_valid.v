From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_valid dyn_type.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Lemma dyn_sta_type Γ Δ m A : Γ ; Δ ⊨ m : A -> Γ ⊢ m : A.
Proof with eauto using sta_type.
  move=>ty. elim: ty...
Qed.

Lemma dyn_sta_wf Γ Δ : dyn_wf Γ Δ -> sta_wf Γ.
Proof with eauto using sta_wf.
  move=>wf. elim: wf...
Qed.

Theorem dyn_valid Γ Δ m A :
  dyn_wf Γ Δ -> Γ ; Δ ⊨ m : A -> exists s, Γ ⊢ A : @s.
Proof.
  move=>wf ty.
  apply: sta_valid.
  apply: dyn_sta_wf; eauto.
  apply: dyn_sta_type; eauto.
Qed.

