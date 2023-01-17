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

Lemma era_pair0_canonical Γ Δ A m1 m2 n s :
  Γ ; Δ ⊢ Pair0 m1 m2 s ~ n : A -> exists m1', n = Pair0 m1' Box s.
Proof with eauto.
  move e:(Pair0 m1 m2 s)=>x ty. elim: ty m1 m2 s e=>//{Γ Δ x n A}.
  move=>Γ Δ A B m m' n t tyS erm ihm tyn m1 m2 s[e1 e2 e3]; subst.
  exists m'...
Qed.

Lemma era_pair1_canonical Γ Δ A m1 m2 n s :
  Γ ; Δ ⊢ Pair1 m1 m2 s ~ n : A -> exists m1' m2', n = Pair1 m1' m2' s.
Proof with eauto.
  move e:(Pair1 m1 m2 s)=>x ty. elim: ty m1 m2 s e=>//{Γ Δ x n A}.
  move=>Γ Δ1 Δ2 Δ A B m m' n n' t mrg tyS erm ihm tyn ihn m1 m2 s[e1 e2 e3]; subst.
  exists m'. exists n'...
Qed.

Lemma era_apair_canonical Γ Δ A m1 m2 n s :
  Γ ; Δ ⊢ APair m1 m2 s ~ n : A -> exists m1' m2', n = APair m1' m2' s.
Proof with eauto.
  move e:(APair m1 m2 s)=>x ty. elim: ty m1 m2 s e=>//{Γ Δ x n A}.
  move=>Γ Δ A B m m' n n' t tyS erm ihm tyn ihn m1 m2 s[e1 e2 e3]; subst.
  exists m'. exists n'...
Qed.

Theorem era_prog Γ Δ m m' A :
  Γ ; Δ ⊢ m ~ m' : A -> dyn_empty Δ -> (exists n', m' ~>> n') \/ dyn_val m'.
Proof with eauto using dyn_step, dyn_val.
  move=>ty. elim: ty=>{Γ Δ m m' A}.
  { move=>Γ Δ x s A wf shs dhs dN.
    exfalso. apply: dyn_has_empty... }
  { move=>Γ Δ A B m m' s k tym ihm. right... }
  { move=>Γ Δ A B m m' s t k tym ihm. right... }
  { move=>Γ Δ A B m m' n s erm ihm tyn dN.
    have[[x st]|vl]:=ihm dN.
    { left. exists (App x Box)... }
    { left.
      have{}vl:=era_dyn_val erm vl.
      have tym:=era_dyn_type erm.
      have[A0[n0 e]]:=dyn_pi0_canonical tym (convR _ _) dN vl. subst.
      have[m0 e]:=era_lam0_canonical erm. subst.
      exists (m0.[Box/])... } }
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' s mrg erm ihm ern ihn dN.
    have[dN1 dN2]:=dyn_empty_split mrg dN.
    have[[mx st1]|vlm]:=ihm dN1.
    { left. exists (App mx n')... }
    { left. have[[nx st2]|vln]:=ihn dN2.
      exists (App m' nx)...
      have{}vlm:=era_dyn_val erm vlm.
      have tym:=era_dyn_type erm.
      have[A0[n0 e]]:=dyn_pi1_canonical tym (convR _ _) dN1 vlm. subst.
      have[m0 e]:=era_lam1_canonical erm. subst.
      exists (m0.[n'/])... } }
  { move=>Γ Δ A B m m' n t tyS erm ihm tyn dN.
    have[[mx stm]|vlm]:=ihm dN.
    { left. exists (Pair0 mx Box t)... }
    { right... } }
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' t mrg tyS erm ihm ern ihn dN.
    have[dN1 dN2]:=dyn_empty_split mrg dN.
    have[[mx stm]|vlm]:=ihm dN1.
    { left. exists (Pair1 mx n' t)... }
    { have[[nx stn]|vln]:=ihn dN2.
      { left. exists (Pair1 m' nx t)... }
      { right... } } }
  { move=>Γ Δ1 Δ2 Δ A B C m m' n n' s r t mrg tyC erm ihm ern ihn dN.
    have[dN1 dN2]:=dyn_empty_split mrg dN.
    have[[mx stm]|vlm]:=ihm dN1.
    { left. exists (LetIn Box mx n')... }
    { have[m1[m2 e]]:=
        dyn_sig0_canonical
          (era_dyn_type erm)
          (convR _ _) dN1
          (era_dyn_val erm vlm). subst.
      have[mx e]:=era_pair0_canonical erm. subst.
      left. exists (n'.[Box,mx/])... } }
  { move=>Γ Δ1 Δ2 Δ A B C m m' n n' s r1 r2 t mrg tyC erm ihm ern ihn dN.
    have[dN1 dN2]:=dyn_empty_split mrg dN.
    have[[mx stm]|vlm]:=ihm dN1.
    { left. exists (LetIn Box mx n')... }
    { have[m1[m2 e]]:=
        dyn_sig1_canonical
          (era_dyn_type erm)
          (convR _ _) dN1
          (era_dyn_val erm vlm). subst.
      have[mx[my e]]:=era_pair1_canonical erm. subst.
      left. exists (n'.[my,mx/])... } }
  { move=>Γ Δ A B m m' n n' t k erm ihm ern ihn dN. right... }
  { move=>Γ Δ A B m m' t erm ihm dN.
    have[[mx stm]|vlm]:=ihm dN.
    { left. exists (Fst mx)... }
    { have[m1[m2 e]]:=
        dyn_with_canonical
          (era_dyn_type erm)
          (convR _ _) dN
          (era_dyn_val erm vlm). subst.
      have[mx[my e]]:=era_apair_canonical erm. subst.
      left. exists mx... } }
  { move=>Γ Δ A B m m' t erm ihm dN.
    have[[mx stm]|vlm]:=ihm dN.
    { left. exists (Snd mx)... }
    { have[m1[m2 e]]:=
        dyn_with_canonical
          (era_dyn_type erm)
          (convR _ _) dN
          (era_dyn_val erm vlm). subst.
      have[mx[my e]]:=era_apair_canonical erm. subst.
      left. exists my... } }
  { move=>Γ Δ A B m m' s eq tym ihm tyB dN... }
Qed.
