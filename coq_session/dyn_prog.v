From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS dyn_inv.

Lemma dyn_monad_canonical Θ v A T :
  Θ ; nil ; nil ⊢ v : T -> dyn_val v -> IO A ≃ T ->
  (exists u, dyn_val u ∧ v = Return u) ∨ (dyn_thunk v).
Proof.
  move e1:(nil)=>Γ.
  move e2:(nil)=>Δ ty.
  elim: ty A e1 e2=>//{Θ Γ Δ v T};
  try solve[intros; exfalso; solve_conv].
  { move=>Θ Γ Δ x s A emp wf hs1 hs2 A0 e1 e2 vl eq. subst. inv hs2. }
  { intros. subst. inv H2. eauto. }
  { intros. subst. inv H5. eauto. }
  { intros. subst. inv H6. eauto. }
  { intros. subst. inv H6. eauto. }
  { intros. subst. inv H8. eauto. }
  { intros. subst. inv H1.
    left. exists m. eauto. inv H3. }
  { intros. subst. inv H6. eauto. }
  { intros. subst. inv H1. eauto. }
  { intros. subst. inv H2. eauto. }
  { intros. subst. inv H2. eauto. }
  { intros. subst. inv H1. eauto. }
  { intros. subst. inv H1. eauto. }
  { intros. subst.
    apply: H1; eauto.
    apply: conv_trans.
    apply: H4.
    apply: conv_sym; eauto. }
Qed.
