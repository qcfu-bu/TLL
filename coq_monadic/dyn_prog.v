From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_sr dyn_sr.

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
  { move=>*. exfalso. solve_conv. }
  { move=>Γ Δ A B m n s tym ihm tyn A0 B0
      s0 e1 e2 _ vl. inv vl.
    have[eq _]:=dyn_rand_inv tym.
    exfalso. solve_conv. }
  { move=>Γ Δ1 Δ2 Δ A B m n s mrg tym _ tyn _ A0 B0
      s0 e1 e2 eq vl. inv vl.
    have[/pi1_inj[eq1[eq2 e k1]]]:=dyn_rand_inv tym.
    have[_ k2]:=dyn_it_inv tyn. subst. inv mrg.
    pose proof (sta_conv_subst (It .: ids) eq2) as H. asimpl in H.
    have eqx:=conv_trans _ (conv_sym eq) H.
    exfalso. solve_conv. }
  { move=>*. exfalso. solve_conv. }
  { move=>*. exfalso. solve_conv. }
  { move=>*. exfalso. solve_conv. }
  { move=>*. exfalso. solve_conv. }
  { move=>*. exfalso. solve_conv. }
  { move=>Γ Δ A B m s eq1 tym ihm tyB A0 B0 s0 e1 e2 eq2 vl.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma dyn_pi1_canonical m A B C s :
  nil ; nil ⊢ m : C -> C === Pi1 A B s -> dyn_val m ->
  m = Rand \/ exists A n, m = Lam1 A n s.
Proof with eauto.
  move e1:(nil)=>Γ.
  move e2:(nil)=>Δ ty.
  elim: ty A B s e1 e2=>//{Γ Δ m C}.
  { move=>Γ Δ x s A wf shs dhs A0 B s0 e1 e2; subst. inv shs. }
  { move=>*. exfalso. solve_conv. }
  { move=>Γ Δ A B m s t k tym ihm A0 B0 s0
      e1 e2/pi1_inj[eq1[eq2 e3]] vl; subst.
    right. exists A. exists m... }
  { move=>Γ Δ A B m n s tym ihm tyn A0 B0
      s0 e1 e2 _ vl. inv vl.
    have[eq _]:=dyn_rand_inv tym.
    exfalso. solve_conv. }
  { move=>Γ Δ1 Δ2 Δ A B m n s mrg tym _ tyn _ A0 B0
      s0 e1 e2 eq vl. inv vl.
    have[/pi1_inj[eq1[eq2 e k1]]]:=dyn_rand_inv tym.
    have[_ k2]:=dyn_it_inv tyn. subst. inv mrg.
    pose proof (sta_conv_subst (It .: ids) eq2) as H. asimpl in H.
    have eqx:=conv_trans _ (conv_sym eq) H.
    exfalso. solve_conv. }
  { move=>*. exfalso. solve_conv. }
  { move=>*. exfalso. solve_conv. }
  { move=>Γ Δ k wf A B s e1 e2/pi1_inj[eq1[eq2 e]] vl.
    by left. }
  { move=>*. exfalso. solve_conv. }
  { move=>*. exfalso. solve_conv. }
  { move=>Γ Δ A B m s eq1 tym ihm tyB A0 B0 s0 e1 e2 eq2 vl.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma dyn_unit_canonical m A :
  nil ; nil ⊢ m : A -> A === Unit -> dyn_val m -> m = It.
Proof with eauto.
  move e1:(nil)=>Γ.
  move e2:(nil)=>Δ ty.
  elim: ty e1 e2=>//{Γ Δ m A}.
  { move=>Γ Δ x s A wf shs dhs e1 e2; subst. inv shs. }
  { move=>*. exfalso. solve_conv. }
  { move=>*. exfalso. solve_conv. }
  { move=>Γ Δ A B m n s tym ihm tyn
      e1 e2 _ vl. inv vl.
    have[eq _]:=dyn_rand_inv tym.
    exfalso. solve_conv. }
  { move=>Γ Δ1 Δ2 Δ A B m n s mrg tym _ tyn _
      e1 e2 eq vl. inv vl.
    have[/pi1_inj[eq1[eq2 e k1]]]:=dyn_rand_inv tym.
    have[_ k2]:=dyn_it_inv tyn. subst. inv mrg.
    pose proof (sta_conv_subst (It .: ids) eq2) as H. asimpl in H.
    have eqx:=conv_trans _ (conv_sym eq) H.
    exfalso. solve_conv. }
  { move=>*. exfalso. solve_conv. }
  { move=>*. exfalso. solve_conv. }
  { move=>*. exfalso. solve_conv. }
  { move=>*. exfalso. solve_conv. }
  { move=>Γ Δ A B m s eq1 tym ihm tyB e1 e2 eq2 vl.
    apply: ihm... apply: conv_trans... }
Qed.

Lemma dyn_io_canonical m A B :
  nil ; nil ⊢ m : B -> B === IO A -> dyn_mval m ->
  exists n, m = Return n.
Proof with eauto.
  move e1:(nil)=>Γ.
  move e2:(nil)=>Δ ty.
  elim: ty A e1 e2=>//{Γ Δ m B}.
  { move=>Γ Δ x s A wf shs dhs A0 e1 e2. subst. inv shs. }
  { move=>*. exfalso. solve_conv. }
  { move=>*. exfalso. solve_conv. }
  { move=>Γ Δ A B m n s tym ihm tyn A0 e1 e2 eq vl. inv vl. }
  { move=>Γ Δ1 Δ2 Δ A B m n s mrg tym ihm tyn ihn A0 e1 e2 eq vl. inv vl. }
  { move=>*. exfalso. solve_conv. }
  { move=>*. exfalso. solve_conv. }
  { move=>*. exfalso. solve_conv. }
  { move=>Γ Δ m A tym ihm A0 eq1 eq2 eq3 vl. exists m... }
  { move=>Γ Δ1 Δ2 Δ m n A B s t mrg tyB tym ihm tyn ihn A0 e1 e2 eq vl. inv vl. }
  { move=>Γ Δ A B m s eq1 tym ihm tyB A0 e1 e2 eq2 vl. subst.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma dyn_prog m A : nil ; nil ⊢ m : A -> (exists n, m ~>> n) \/ dyn_val m.
Proof with eauto using dyn_step, dyn_val.
  move e1:(nil)=>Γ.
  move e2:(nil)=>Δ ty. elim: ty e1 e2=>{Γ Δ m A}.
  { move=>Γ Δ x s A wf shs dhs e1 e2; subst. inv shs. }
  { move=>Γ Δ A B m s k tym ihm e1 e2; subst.
    right... }
  { move=>Γ Δ A B m s t k tym ihm e1 e2; subst.
    right... }
  { move=>Γ Δ A B m n s tym ihm tyn e1 e2; subst.
    have[[x st]|vl]:=ihm erefl erefl.
    { left. exists (App x n)... }
    { left.
      have[A0[n0 e]]:=dyn_pi0_canonical tym (convR _ _) vl.
      subst. exists (n0.[n/])... } }
  { move=>Γ Δ1 Δ2 Δ A B m n s mrg tym ihm tyn ihn e1 e2; subst.
    inv mrg. have[[m' stm]|vlm]:=ihm erefl erefl.
    { left. exists (App m' n)... }
    { have[[n' stn]|vln]:=ihn erefl erefl.
      left. exists (App m n')...
      have[e|[A0[m0 e]]]:=dyn_pi1_canonical tym (convR _ _) vlm.
      subst.
      have[/pi1_inj[eq1[eq2 e k]]]:=dyn_rand_inv tym. subst.
      have{}tyn:=dyn_conv eq1 tyn (sta_unit sta_wf_nil).
      have e:=dyn_unit_canonical tyn (convR _ _) vln. subst.
      right...
      subst. left. exists m0.[n/]... } }
  { move=>Γ Δ k wf e1 e2. right... }
  { move=>Γ Δ n k wf e1 e2. right... }
  { move=>Γ Δ k wf e1 e2. right... }
  { move=>Γ Δ m A tym ihm e1 e2; subst.
    have[[e st]|vl]:=ihm erefl erefl.
    left. exists (Return e)...
    right... }
  { move=>Γ Δ1 Δ2 Δ m n A B s t mrg tyB tym ihm tyn _ e1 e2; subst. inv mrg.
    have[[n0 st]|vl]:=ihm erefl erefl.
    left. exists (LetIn n0 n)...
    right. constructor... }
  { move=>Γ Δ A B m s eq tym ihm tyB e1 e2; subst... }
Qed.

Lemma dyn_mprog m A R : nil ; nil ⊢ m : A -> (exists T n, R ; m ~>> T ; n) \/ dyn_mval m.
Proof with eauto using dyn_mstep, dyn_mval.
  move e1:(nil)=>Γ.
  move e2:(nil)=>Δ ty. elim: ty e1 e2 R=>{Γ Δ m A}.
  { move=>Γ Δ x s A wf shs dhs e1 e2. subst. inv shs. }
  { move=>Γ Δ A B m s k tym ihm e1 e2 R. subst. right... }
  { move=>Γ Δ A B m s t k tym ihm e1 e2 R. subst. right... }
  { move=>Γ Δ A B m n s tym ihm tyn e1 e2 R. subst. left.
    have[[x st]|vl]:=dyn_prog (dyn_app0 tym tyn).
    { exists R. exists x... }
    { inv vl. have[eq _]:=dyn_rand_inv tym. exfalso. solve_conv. } }
  { move=>Γ Δ1 Δ2 Δ A B m n s mrg tym ihm tyn ihn e1 e2 R. subst. left.
    have[[x st]|vl]:=dyn_prog (dyn_app1 mrg tym tyn).
    { exists R. exists x... }
    { inv vl. exists R.+1. exists (Return (Num R))... } }
  { move=>Γ Δ k wf e1 e2 R. subst. right... }
  { move=>Γ Δ n k wf e1 e2 R. subst. right... }
  { move=>Γ Δ k wf e1 e2 R. subst. right... }
  { move=>Γ Δ m A tym ihm e1 e2 R. subst.
    have[[x st]|vl]:=dyn_prog (dyn_return tym).
    { left. exists R. exists x... }
    { inv vl. right... } }
  { move=>Γ Δ1 Δ2 Δ m n A B s t mrg tyB tym ihm tyn ihn e1 e2 R. subst. inv mrg.
    left. have[[T[m0 st]]|vl]:=ihm erefl erefl R.
    { exists T. exists (LetIn m0 n)... }
    { have[m0 e]:=dyn_io_canonical tym (convR _ _) vl. subst. inv vl.
      exists R. exists n.[m0/].
      apply: dyn_mstep_letret... } }
  { move=>Γ Δ A B m s eq tym ihm tyB e1 e2 R. subst... }
Qed.
