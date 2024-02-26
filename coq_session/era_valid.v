From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS era_type.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma era_dyn_type Θ Γ Δ m m' A :
  Θ ; Γ ; Δ ⊢ m ~ m' : A -> Θ ; Γ ; Δ ⊢ m : A.
Proof with eauto using dyn_type. elim... Qed.
#[global] Hint Resolve era_dyn_type.

Lemma era_sta_type Θ Γ Δ m m' A :
  Θ ; Γ ; Δ ⊢ m ~ m' : A -> Γ ⊢ m : A.
Proof with eauto. eauto... Qed.
#[global] Hint Resolve era_sta_type.

Lemma era_type_wf Θ Γ Δ m m' A :
  Θ ; Γ ; Δ ⊢ m ~ m' : A -> dyn_wf Γ Δ. 
Proof with eauto. move=>erm. apply: dyn_type_wf... Qed.

Theorem era_valid Θ Γ Δ m m' A :
  Θ ; Γ ; Δ ⊢ m ~ m' : A -> exists s, Γ ⊢ A : Sort s.
Proof with eauto. move=>er. apply: dyn_valid... Qed.
