From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Stdlib Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS logical_valid program_type.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma program_logical_type Γ Δ m A : Γ ; Δ ⊢ m : A -> Γ ⊢ m : A.
Proof with eauto using logical_type, logical_wf.
  move:Γ Δ m A.
  apply:(@program_type_mut _ (fun Γ Δ wf => logical_wf Γ))...
  Unshelve. all: eauto.
Qed.
#[global] Hint Resolve program_logical_type.

Theorem program_valid Γ Δ m A : Γ ; Δ ⊢ m : A -> exists s l, Γ ⊢ A : Sort s l.
Proof.
  move=>ty.
  apply: logical_valid.
  apply: program_logical_type; eauto.
Qed.
