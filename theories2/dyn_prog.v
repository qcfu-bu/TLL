From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_sr dyn_sr.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma dyn_pi0_canonical m A B C s t :
  nil ; nil ⊢ m : C -> C === Pi0 A B s t -> dyn_val m ->
  exists A n, m = Lam0 A n s t.
Proof with eauto.
  move e1:(nil)=>Γ.
  move e2:(nil)=>Δ ty.
  elim: ty A B s t e1 e2=>//{Γ Δ m C}.
  { move=>Γ Δ x A shs dhs A0 B s t e1 e2; subst. inv shs. }
  { move=>Γ Δ A B m s t k tyP ihm tym A0 B0 s0 t0
      e1 e2 /pi0_inj[eq1[eq2[e3 e4]]] vl; subst.
    exists A. exists m... }
  { move=>Γ Δ A B m n s t tym ihm tyn
      A0 B0 s0 t0 e1 e2 e3; subst.
    exfalso. solve_conv. }
  { move=>Γ Δ A B m n s t tym ihm tyn A0 B0
      s0 t0 e1 e2 eq vl. inv vl. }
  { move=>Γ Δ1 Δ2 Δ A B m n s t mrg tym ihm tyn ihn A0 B0
      s0 t0 e1 e2 eq vl. inv vl. }
  { move=>Γ Δ A B m s eq1 tym ihm tyB A0 B0 s0 t e1 e2 eq2 vl.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma dyn_pi1_canonical m A B C s t :
  nil ; nil ⊢ m : C -> C === Pi1 A B s t -> dyn_val m ->
  exists A n, m = Lam1 A n s t.
Proof with eauto.
  move e1:(nil)=>Γ.
  move e2:(nil)=>Δ ty.
  elim: ty A B s t e1 e2=>//{Γ Δ m C}.
  { move=>Γ Δ x A shs dhs A0 B s t e1 e2; subst. inv shs. }
  { move=>Γ Δ A B m n s t tym ihm tyn
      A0 B0 s0 t0 e1 e2 e3; subst.
    exfalso. solve_conv. }
  { move=>Γ Δ A B m s t k tyP ihm tym A0 B0 s0 t0
      e1 e2 /pi1_inj[eq1[eq2[e3 e4]]] vl; subst.
    exists A. exists m... }
  { move=>Γ Δ A B m n s t tym ihm tyn A0 B0
      s0 t0 e1 e2 eq vl. inv vl. }
  { move=>Γ Δ1 Δ2 Δ A B m n s t mrg tym ihm tyn ihn A0 B0
      s0 t0 e1 e2 eq vl. inv vl. }
  { move=>Γ Δ A B m s eq1 tym ihm tyB A0 B0 s0 t e1 e2 eq2 vl.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma dyn_prog m A : nil ; nil ⊢ m : A -> (exists n, m ~>> n) \/ dyn_val m.
Proof with eauto using dyn_step, dyn_val.
  move e1:(nil)=>Γ.
  move e2:(nil)=>Δ ty. elim: ty e1 e2=>{Γ Δ m A}.
  { move=>Γ Δ x A shs dhs e1 e2; subst. inv shs. }
  { move=>Γ Δ A B m s t k tyP tym ihm e1 e2; subst.
    right... }
  { move=>Γ Δ A B m s t k tyP tym ihm e1 e2; subst.
    right... }
  { move=>Γ Δ A B m n s t tym ihm tyn e1 e2; subst.
    have[[x st]|vl]:=ihm erefl erefl.
    { left. exists (App x n)... }
    { left.
      have[A0[n0 e]]:=dyn_pi0_canonical tym (convR _ _) vl.
      subst. exists (n0.[n/])... } }
  { move=>Γ Δ1 Δ2 Δ A B m n s t mrg tym ihm tyn ihn e1 e2; subst.
    inv mrg. have[[m' stm]|vlm]:=ihm erefl erefl.
    { left. exists (App m' n)... }
    { left. have[[n' stn]|vln]:=ihn erefl erefl.
      exists (App m n')...
      have[A0[n0 e]]:=dyn_pi1_canonical tym (convR _ _) vlm.
      subst. exists (n0.[n/])... } }
  { move=>Γ Δ A B m s eq tym ihm tyB e1 e2; subst... }
Qed.
