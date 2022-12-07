From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS dyn_prog era_sr.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma era_lam0_canonical Γ Δ A B m n s :
  Γ ; Δ ⊢ Lam0 A m s ~ n : B -> exists m', n = Lam0 Box m' s.
Proof with eauto.
  move e:(Lam0 A m s)=>x ty. elim: ty A m s e=>//{Γ Δ x n B}.
  move=>Γ Δ A B m m' s k tym ihm A0 m0 s0[e1 e2 e3]; subst.
  exists m'...
Qed.

Lemma era_lam1_canonical Γ Δ A B m n s :
  Γ ; Δ ⊢ Lam1 A m s ~ n : B -> exists m', n = Lam1 Box m' s.
Proof with eauto.
  move e:(Lam1 A m s)=>x ty. elim: ty A m s e=>//{Γ Δ x n B}.
  move=>Γ Δ A B m m' s t k tym ihm A0 m0 s0[e1 e2 e3]; subst.
  exists m'...
Qed.

Lemma era_rand_canonical Γ Δ A m :
  Γ ; Δ ⊢ Rand ~ m : A -> m = Rand.
Proof. move e:(Rand)=>x ty. elim: ty e=>//{Γ Δ x m A}. Qed.

Lemma era_it_canonical Γ Δ A m :
  Γ ; Δ ⊢ It ~ m : A -> m = It.
Proof. move e:(It)=>x ty. elim: ty e=>//{Γ Δ x m A}. Qed.

Lemma era_return_canonical Γ Δ A m n :
  Γ ; Δ ⊢ Return m ~ n : A -> exists m, n = Return m.
Proof.
  move e:(Return m)=>x ty. elim: ty m e=>//{Γ Δ x n A}.
  move=>Γ Δ m m' A erm ihm m0[e]; subst. exists m'=>//.
Qed.

Lemma era_prog m m' A :
  nil ; nil ⊢ m ~ m' : A -> (exists n', m' ~>> n') \/ dyn_val m'.
Proof with eauto using dyn_step, dyn_val.
  move e1:(nil)=>Γ.
  move e2:(nil)=>Δ ty. elim: ty e1 e2=>{Γ Δ m m' A}.
  { move=>Γ Δ x s A wf shs dhs e1 e2; subst. inv shs. }
  { move=>Γ Δ A B m m' s k tym ihm e1 e2; subst.
    right... }
  { move=>Γ Δ A B m m' s t k tym ihm e1 e2; subst.
    right... }
  { move=>Γ Δ A B m m' n s erm ihm tyn e1 e2; subst.
    have[[x st]|vl]:=ihm erefl erefl.
    { left. exists (App x Box)... }
    { left. have{}vl:=era_dyn_val erm vl.
      have tym:=era_dyn_type erm.
      have[A0[n0 e]]:=dyn_pi0_canonical tym (convR _ _) vl. subst.
      have[m0 e]:=era_lam0_canonical erm. subst.
      exists (m0.[Box/])... } }
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' s mrg erm ihm ern ihn e1 e2; subst.
    inv mrg. have[[mx st1]|vlm]:=ihm erefl erefl.
    { left. exists (App mx n')... }
    { have[[nx st2]|vln']:=ihn erefl erefl.
      { left. exists (App m' nx)... }
      { have{}vlm:=era_dyn_val erm vlm.
        have tym:=era_dyn_type erm.
        have[e|[A0[n0 e]]]:=dyn_pi1_canonical tym (convR _ _) vlm. subst.
        { have e:=era_rand_canonical erm. subst.
          have[/pi1_inj[eq1[eq2 e]] _]:=dyn_rand_inv (era_dyn_type erm). subst.
          have{}ern:=era_conv eq1 ern (sta_unit sta_wf_nil).
          have vln:=era_dyn_val ern vln'.
          have e:=dyn_unit_canonical (era_dyn_type ern) (convR _ _) vln. subst.
          have e:=era_it_canonical ern. subst. right... }
        { subst. have[m1 e]:=era_lam1_canonical erm. subst.
          left. exists m1.[n'/]... } } } }
  { move=>Γ Δ k wf e1 e2; subst. right... }
  { move=>Γ Δ n k wf e1 e2; subst. right... }
  { move=>Γ Δ k wf e1 e2; subst. right... }
  { move=>Γ Δ m m' A erm ihm e1 e2; subst.
    have[[n' st]|vlm']:=ihm erefl erefl.
    { left. exists (Return n')... }
    { right... } }
  { move=>Γ Δ1 Δ2 Δ m m' n n' A B s t mrg tyB erm ihm ern ihn e1 e2; subst. inv mrg.
    have[[m'0 st]|vlm']:=ihm erefl erefl.
    { left. exists (LetIn m'0 n')... }
    { right... } }
  { move=>Γ Δ A B m m' s eq tym ihm tyB e1 e2; subst... }
Qed.

Lemma era_mprog m m' A R :
  nil ; nil ⊢ m ~ m' : A -> (exists T n', R ; m' ~>> T ; n') \/ dyn_mval m'.
Proof with eauto using dyn_mstep, dyn_step, dyn_mval.
  move e1:(nil)=>Γ.
  move e2:(nil)=>Δ ty. elim: ty e1 e2 R=>{Γ Δ m m' A}.
  { move=>Γ Δ x s A wf shs dhs e1 e2 R. subst. inv shs. }
  { move=>Γ Δ A B m m' s k erm ihm e1 e2 R. subst. right... }
  { move=>Γ Δ A B m m' s t k erm ihm e1 e2 R. subst. right... }
  { move=>Γ Δ A B m m' n s erm ihm tyn e1 e2 R. subst. left.
    have[[x st]|vl]:=era_prog (era_app0 erm tyn).
    { exists R. exists x... }
    { inv vl. } }
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' s mrg erm ihm ern ihn e1 e2 R. subst. left.
    have[[x st]|vl]:=era_prog (era_app1 mrg erm ern).
    { exists R. exists x... }
    { inv vl. exists R.+1. exists (Return (Num R))... } }
  { move=>Γ Δ k wf e1 e2 R. subst. right... }
  { move=>Γ Δ n k wf e1 e2 R. subst. right... }
  { move=>Γ Δ k wf e1 e2 R. subst. right... }
  { move=>Γ Δ m m' A erm ihm e1 e2 R. subst.
    have[[n' st]|vl]:=era_prog erm.
    { left. exists R. exists (Return n')... }
    { right... } }
  { move=>Γ Δ1 Δ2 Δ m m' n n' A B s t mrg tyB erm ihm ern ihn e1 e2 R. subst. inv mrg.
    left. have[[T[m0 st]]|vlm']:=ihm erefl erefl R.
    { exists T. exists (LetIn m0 n')... }
    { have vlm:=era_dyn_mval erm vlm'.
      have[n0 e]:=dyn_io_canonical (era_dyn_type erm) (convR _ _) vlm. subst.
      have[m e]:=era_return_canonical erm. subst. inv vlm'.
      exists R. exists n'.[m/]... } }
  { move=>Γ Δ A B m m' s eq1 erm ihm tyB e1 e2 R. subst... }
Qed.
