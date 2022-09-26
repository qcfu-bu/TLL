From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS dyn_prog era_sr.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma era_lam0_canonical Γ Δ A B m n s t :
  Γ ; Δ ⊢ Lam0 A m s t ~ n : B -> exists m', n = Lam0 Box m' s t.
Proof with eauto.
  move e:(Lam0 A m s t)=>x ty. elim: ty A m s t e=>//{Γ Δ x n B}.
  move=>Γ Δ A B m m' s t k tyP tym ihm A0 m0 s0 t0 [e1 e2 e3 e4]; subst.
  exists m'...
Qed.

Lemma era_lam1_canonical Γ Δ A B m n s t :
  Γ ; Δ ⊢ Lam1 A m s t ~ n : B -> exists m', n = Lam1 Box m' s t.
Proof with eauto.
  move e:(Lam1 A m s t)=>x ty. elim: ty A m s t e=>//{Γ Δ x n B}.
  move=>Γ Δ A B m m' s t k tyP tym ihm A0 m0 s0 t0 [e1 e2 e3 e4]; subst.
  exists m'...
Qed.

Lemma era_prog m m' A :
  nil ; nil ⊢ m ~ m' : A -> (exists n', m' ~>> n') \/ dyn_val m'.
Proof with eauto using dyn_step, dyn_val.
  move e1:(nil)=>Γ.
  move e2:(nil)=>Δ ty. elim: ty e1 e2=>{Γ Δ m m' A}.
  { move=>Γ Δ x A shs dhs e1 e2; subst. inv shs. }
  { move=>Γ Δ A B m m' s t k tyP tym ihm e1 e2; subst.
    right... }
  { move=>Γ Δ A B m m' s t k tyP tym ihm e1 e2; subst.
    right... }
  { move=>Γ Δ A B m m' n s t erm ihm tyn e1 e2; subst.
    have[[x st]|vl]:=ihm erefl erefl.
    { left. exists (App x Box)... }
    { left.
      have{}vl:=era_dyn_val vl erm.
      have tym:=era_dyn_type erm.
      have[A0[n0 e]]:=dyn_pi0_canonical tym (convR _ _) vl. subst.
      have[m0 e]:=era_lam0_canonical erm. subst.
      exists (m0.[Box/])... } }
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' s t mrg erm ihm ern ihn e1 e2; subst.
    inv mrg. have[[mx st1]|vlm]:=ihm erefl erefl.
    { left. exists (App mx n')... }
    { left. have[[nx st2]|vln]:=ihn erefl erefl.
      exists (App m' nx)...
      have{}vlm:=era_dyn_val vlm erm.
      have tym:=era_dyn_type erm.
      have[A0[n0 e]]:=dyn_pi1_canonical tym (convR _ _) vlm. subst.
      have[m0 e]:=era_lam1_canonical erm. subst.
      exists (m0.[n'/])... } }
  { move=>Γ Δ A B m m' s eq tym ihm tyB e1 e2; subst... }
Qed.
