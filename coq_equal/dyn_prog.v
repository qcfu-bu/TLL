From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_prog dyn_sr.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma dyn_pi0_canonical m A B C s :
  nil ; nil ⊢ m : C -> C === Pi0 A B s -> dyn_val m ->
  exists A n, m = Lam0 A n s.
Proof with eauto.
  move e1:(nil)=>Γ.
  move e2:(nil)=>Δ ty.
  elim: ty A B s e1 e2=>//{Γ Δ m C}.
  { move=>Γ Δ x s A wf shs dhs A0 B s0 e1 e2; subst. inv shs. }
  { move=>Γ Δ A B m s k tym ihm A0 B0 s0
      e1 e2/pi0_inj[eq1[eq2 e3]] vl; subst.
    exists A. exists m... }
  { move=>Γ Δ A B m s t k tym _ A0 B0 s0 e1 e2 eq.
    exfalso. solve_conv. }
  { move=>Γ Δ A B m n s tym ihm tyn A0 B0 s0 e1 e2 eq vl. inv vl. }
  { move=>Γ Δ1 Δ2 Δ A B m n s mrg tym _ tyn _ A0 B0 s0 e1 e2 eq vl. inv vl. }
  { move=>Γ Δ A B H P m n s tyB tyH ihH tyP A0 B0 s0 e1 e2 eq vl. inv vl. }
  { move=>Γ Δ A B m s eq1 tym ihm tyB A0 B0 s0 e1 e2 eq2 vl.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma dyn_pi1_canonical m A B C s :
  nil ; nil ⊢ m : C -> C === Pi1 A B s -> dyn_val m ->
  exists A n, m = Lam1 A n s.
Proof with eauto.
  move e1:(nil)=>Γ.
  move e2:(nil)=>Δ ty.
  elim: ty A B s e1 e2=>//{Γ Δ m C}.
  { move=>Γ Δ x s A wf shs dhs A0 B s0 e1 e2; subst. inv shs. }
  { move=>Γ Δ A B m s k tym _ A0 B0 s0 e1 e2 eq.
    exfalso. solve_conv. }
  { move=>Γ Δ A B m s t k tym ihm A0 B0 s0
      e1 e2/pi1_inj[eq1[eq2 e3]] vl; subst.
    exists A. exists m... }
  { move=>Γ Δ A B m n s tym ihm tyn A0 B0 s0 e1 e2 eq vl. inv vl. }
  { move=>Γ Δ1 Δ2 Δ A B m n s mrg tym _ tyn _ A0 B0 s0 e1 e2 eq vl. inv vl. }
  { move=>Γ Δ A B H P m n s tyB tyH ihH tyP A0 B0 s0 e1 e2 eq vl. inv vl. }
  { move=>Γ Δ A B m s eq1 tym ihm tyB A0 B0 s0 e1 e2 eq2 vl.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma dyn_prog m A : nil ; nil ⊢ m : A -> (exists n, m ~>> n) \/ dyn_val m.
Proof with eauto using dyn_step, dyn_val.
  move e1:(nil)=>Γ.
  move e2:(nil)=>Δ ty. elim: ty e1 e2=>{Γ Δ m A}.
  { move=>Γ Δ x s A wf shs dhs e1 e2; subst. inv shs. }
  { move=>Γ Δ A B m s k tym ihm e1 e2. right... }
  { move=>Γ Δ A B m s t k tym ihm e1 e2. right... }
  { move=>Γ Δ A B m n s tym ihm tyn e1 e2; subst.
    have[[x st]|vl]:=ihm erefl erefl.
    { left. exists (App x n)... }
    { left.
      have[A0[n0 e]]:=dyn_pi0_canonical tym (convR _ _) vl.
      subst. exists (n0.[n/])... } }
  { move=>Γ Δ1 Δ2 Δ A B m n s mrg tym ihm tyn ihn e1 e2; subst.
    inv mrg. have[[m' stm]|vlm]:=ihm erefl erefl.
    { left. exists (App m' n)... }
    { left. have[[n' stn]|vln]:=ihn erefl erefl.
      exists (App m n')...
      have[A0[n0 e]]:=dyn_pi1_canonical tym (convR _ _) vlm.
      subst. exists (n0.[n/])... } }
  { move=>Γ Δ A B H P m n s tyB tyH ihH tyP e1 e2; subst.
    have[P0[rdP vlP]]:=sta_vn tyP.
    have tyP0:=sta_rd tyP rdP.
    have[n0 e]:=sta_id_canonical tyP0 (convR _ _) vlP. subst.
    left. exists H... }
  { move=>Γ Δ A B m s eq tym ihm tyB e1 e2; subst... }
Qed.
