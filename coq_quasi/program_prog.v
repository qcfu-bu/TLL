(* This file presents the program level progress theorem and various
   canonical forms lemmas necessary to prove it. *)

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS logical_sr program_sr.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma program_pi0_canonical Γ Δ m A B C s :
  Γ ; Δ ⊢ m : C -> C === Pi0 A B s -> program_empty Δ -> program_val m ->
  exists A n, m = Lam0 A n s.
Proof with eauto.
  move=>ty. elim: ty A B s=>//{Γ Δ m C}.
  { move=>Γ Δ x s A wf shs dhs A0 B s0 eq dN vl.
    exfalso. apply: program_has_empty... }
  { move=>Γ Δ A B m s k tym ihm A0 B0 s0
      /pi0_inj[eq1[eq2 e3]] dN vl; subst.
    exists A. exists m... }
  { move=>*. exfalso. solve_conv. }
  { move=>Γ Δ A B m n s tym ihm tyn A0 B0
      s0 eq dN vl. inv vl. }
  { move=>Γ Δ1 Δ2 Δ A B m n s mrg tym _ tyn _ A0 B0
      s0 eq dN vl. inv vl. }
  { move=>*. exfalso. solve_conv. }
  { move=>*. exfalso. solve_conv. }
  { move=>Γ Δ1 Δ2 Δ A B C m n s r t mrg tyC tym ihm tyn ihn A0 B0
      s0 eq dN vl. inv vl. }
  { move=>Γ Δ1 Δ2 Δ A B C m n s r1 r2 t mrg tyC tym ihm tyn ihn A0 B0
      s0 eq dN vl. inv vl. }
  { move=>*. exfalso. solve_conv. }
  { move=>Γ Δ A B m t tym ihm A0 B0 s eq dN vl. inv vl. }
  { move=>Γ Δ A B m t tym ihm A0 B0 s eq dN vl. inv vl. }
  { move=>Γ Δ A B H P m n s h tyB tyH ihH tyP A0 B0 s0 e dN vl. inv vl. }
  { move=>Γ Δ A B m s eq1 tym ihm tyB A0 B0 s0 eq2 dN vl.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma program_pi1_canonical Γ Δ m A B C s :
  Γ ; Δ ⊢ m : C -> C === Pi1 A B s -> program_empty Δ -> program_val m ->
  exists A n, m = Lam1 A n s.
Proof with eauto.
  move=>ty. elim: ty A B s=>//{Γ Δ m C}.
  { move=>Γ Δ x s A wf shs dhs A0 B s0 eq dN vl.
    exfalso. apply: program_has_empty... }
  { move=>Γ Δ A B m s k tym _ A0 B0 s0 eq.
    exfalso. solve_conv. }
  { move=>Γ Δ A B m s t k tym ihm A0 B0 s0
      /pi1_inj[eq1[eq2 e3]] dN vl; subst.
    exists A. exists m... }
  { move=>Γ Δ A B m n s tym ihm tyn A0 B0
      s0 eq dN vl. inv vl. }
  { move=>Γ Δ1 Δ2 Δ A B m n s mrg tym _ tyn _ A0 B0
      s0 eq dN vl. inv vl. }
  { move=>*. exfalso. solve_conv. }
  { move=>*. exfalso. solve_conv. }
  { move=>Γ Δ1 Δ2 Δ A B C m n s r t mrg tyC tym ihm tyn ihn A0 B0
      s0 eq dN vl. inv vl. }
  { move=>Γ Δ1 Δ2 Δ A B C m n s r1 r2 t mrg tyC tym ihm tyn ihn A0 B0
      s0 eq dN vl. inv vl. }
  { move=>*. exfalso. solve_conv. }
  { move=>Γ Δ A B m t tym ihm A0 B0 s eq dN vl. inv vl. }
  { move=>Γ Δ A B m t tym ihm A0 B0 s eq dN vl. inv vl. }
  { move=>Γ Δ A B H P m n s h tyB tyH ihH tyP A0 B0 s0 e dN vl. inv vl. }
  { move=>Γ Δ A B m s eq1 tym ihm tyB A0 B0 s0 eq2 dN vl.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma program_sig0_canonical Γ Δ m A B C s :
  Γ ; Δ ⊢ m : C -> C === Sig0 A B s -> program_empty Δ -> program_val m ->
  exists m1 m2, m = Pair0 m1 m2 s.
Proof with eauto.
  move=>ty. elim: ty A B s=>//{Γ Δ m C}.
  { move=>Γ Δ x s A wf shs dhs A0 B s0 eq dN.
    exfalso. apply: program_has_empty... }
  { move=>*. exfalso. solve_conv. }
  { move=>*. exfalso. solve_conv. }
  { move=>Γ Δ A B m n s tym ihm tyn A0 B0 s0 eq dN vl. inv vl. }
  { move=>Γ Δ1 Δ2 Δ A B m n s mrg tym ihm tyn ihn A0 B0 s0 eq dN vl. inv vl. }
  { move=>Γ Δ A B m n t tyS tym ihm tyn A0 B0 s
      /sig0_inj[eq1[eq2 e3]] dN vl; subst.
    exists m. exists n... }
  { move=>*. exfalso. solve_conv. }
  { move=>Γ Δ1 Δ2 Δ A B C m n s r t mrg tyC tym ihm tyn ihn A0 B0
      s0 eq dN vl. inv vl. }
  { move=>Γ Δ1 Δ2 Δ A B C m n s r1 r2 t mrg tyC tym ihm tyn ihn A0 B0
      s0 eq dN vl. inv vl. }
  { move=>*. exfalso. solve_conv. }
  { move=>Γ Δ A B m t tym ihm A0 B0 s eq dN vl. inv vl. }
  { move=>Γ Δ A B m t tym ihm A0 B0 s eq dN vl. inv vl. }
  { move=>Γ Δ A B H P m n s h tyB tyH ihH tyP A0 B0 s0 e dN vl. inv vl. }
  { move=>Γ Δ A B m s eq1 tym ihm tyB A0 B0 s0 eq2 dN vl.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma program_sig1_canonical Γ Δ m A B C s :
  Γ ; Δ ⊢ m : C -> C === Sig1 A B s -> program_empty Δ -> program_val m ->
  exists m1 m2, m = Pair1 m1 m2 s.
Proof with eauto.
  move=>ty. elim: ty A B s=>//{Γ Δ m C}.
  { move=>Γ Δ x s A wf shs dhs A0 B s0 eq dN.
    exfalso. apply: program_has_empty... }
  { move=>*. exfalso. solve_conv. }
  { move=>*. exfalso. solve_conv. }
  { move=>Γ Δ A B m n s tym ihm tyn A0 B0 s0 eq dN vl. inv vl. }
  { move=>Γ Δ1 Δ2 Δ A B m n s mrg tym ihm tyn ihn A0 B0 s0 eq dN vl. inv vl. }
  { move=>*. exfalso. solve_conv. }
  { move=>Γ Δ1 Δ2 Δ A B m n t mrg tyS tym ihm tyn ihn A0 B0 s
      /sig1_inj[eq1[eq2 e3]]dN vl; subst.
    exists m. exists n... }
  { move=>Γ Δ1 Δ2 Δ A B C m n s r t mrg tyC tym ihm tyn ihn A0 B0
      s0 eq dN vl. inv vl. }
  { move=>Γ Δ1 Δ2 Δ A B C m n s r1 r2 t mrg tyC tym ihm tyn ihn A0 B0
      s0 eq dN vl. inv vl. }
  { move=>*. exfalso. solve_conv. }
  { move=>Γ Δ A B m t tym ihm A0 B0 s eq dN vl. inv vl. }
  { move=>Γ Δ A B m t tym ihm A0 B0 s eq dN vl. inv vl. }
  { move=>Γ Δ A B H P m n s h tyB tyH ihH tyP A0 B0 s0 e dN vl. inv vl. }
  { move=>Γ Δ A B m s eq1 tym ihm tyB A0 B0 s0 eq2 dN vl.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma program_with_canonical Γ Δ m A B C s :
  Γ ; Δ ⊢ m : C -> C === With A B s -> program_empty Δ -> program_val m ->
  exists m1 m2, m = APair m1 m2 s.
Proof with eauto.
  move=>ty. elim: ty A B s=>//{Γ Δ m C}.
  { move=>Γ Δ x s A wf shs dhs A0 B s0 eq dN.
    exfalso. apply: program_has_empty... }
  { move=>*. exfalso. solve_conv. }
  { move=>*. exfalso. solve_conv. }
  { move=>Γ Δ A B m n s tym ihm tyn A0 B0 s0 eq dN vl. inv vl. }
  { move=>Γ Δ1 Δ2 Δ A B m n s mrg tym ihm tyn ihn A0 B0 s0 eq dN vl. inv vl. }
  { move=>*. exfalso. solve_conv. }
  { move=>*. exfalso. solve_conv. }
  { move=>Γ Δ1 Δ2 Δ A B C m n s r t mrg tyC tym ihm tyn ihn A0 B0
      s0 eq dN vl. inv vl. }
  { move=>Γ Δ1 Δ2 Δ A B C m n s r1 r2 t mrg tyC tym ihm tyn ihn A0 B0
      s0 eq dN vl. inv vl. }
  { move=>Γ Δ A B m n t k tym ihm tyn ihn A0 B0 s
      /with_inj[eq1[eq2 e3]]dN vl; subst.
    exists m. exists n... }
  { move=>Γ Δ A B m t tym ihm A0 B0 s eq dN vl. inv vl. }
  { move=>Γ Δ A B m t tym ihm A0 B0 s eq dN vl. inv vl. }
  { move=>Γ Δ A B H P m n s h tyB tyH ihH tyP A0 B0 s0 e dN vl. inv vl. }
  { move=>Γ Δ A B m s eq1 tym ihm tyB A0 B0 s0 eq2 dN vl.
    apply: ihm...
    apply: conv_trans... }
Qed.

(* Theorem 9 (Program Progress) *)
Theorem program_prog Γ Δ m A :
  Γ ; Δ ⊢ m : A -> program_empty Δ -> (exists n, m ~>> n) \/ program_val m.
Proof with eauto using program_step, program_val.
  move=>ty. elim: ty=>{Γ Δ m A}.
  { move=>Γ Δ x s A wf shs dhs dN.
    exfalso. apply: program_has_empty... }
  { move=>Γ Δ A B m s k tym ihm dN. right... }
  { move=>Γ Δ A B m s t k tym ihm dN. right... }
  { move=>Γ Δ A B m n s tym ihm tyn dN.
    have[[x st]|vl]:=ihm dN.
    { left. exists (App x n)... }
    { left.
      have[A0[n0 e]]:=program_pi0_canonical tym (convR _ _) dN vl.
      subst. exists (n0.[n/])... } }
  { move=>Γ Δ1 Δ2 Δ A B m n s mrg tym ihm tyn ihn dN.
    have[dN1 dN2]:=program_empty_split mrg dN.
    have[[m' stm]|vlm]:=ihm dN1.
    { left. exists (App m' n)... }
    { left. have[A0[n0->]]:=program_pi1_canonical tym (convR _ _) dN1 vlm.
      have[[n' stn]|vln]:=ihn dN2.
      exists (App (Lam1 A0 n0 s) n')...
      exists (n0.[n/])... } }
  { move=>Γ Δ A B m n t tyS tym ihm tyn dN.
    have[[m' stm]|vlm]:=ihm dN.
    { left. exists (Pair0 m' n t)... }
    { right... } }
  { move=>Γ Δ1 Δ2 Δ A B m n t mrg tyS tym ihm tyn ihn dN.
    have[dN1 dN2]:=program_empty_split mrg dN.
    have[[m' stm]|vlm]:=ihm dN1.
    { left. exists (Pair1 m' n t)... }
    { have[[n' stn]|vln]:=ihn dN2.
      { left. exists (Pair1 m n' t)... }
      { right... } } }
  { move=>Γ Δ1 Δ2 Δ A B C m n s r t mrg tyC tym ihm tyn ihn dN.
    have[dN1 dN2]:=program_empty_split mrg dN.
    have[[m' stm]|vlm]:=ihm dN1.
    { left. exists (LetIn C m' n)... }
    { have[m1[m2 e]]:=program_sig0_canonical tym (convR _ _) dN1 vlm. subst.
      left. exists n.[m2,m1/]... } }
  { move=>Γ Δ1 Δ2 Δ A B C m n s r1 r2 t mrg tyC tym ihm tyn ihn dN.
    have[dN1 dN2]:=program_empty_split mrg dN.
    have[[m' stm]|vlm]:=ihm dN1.
    { left. exists (LetIn C m' n)... }
    { have[m1[m2 e]]:=program_sig1_canonical tym (convR _ _) dN1 vlm. subst.
      left. exists n.[m2,m1/]... } }
  { move=>Γ Δ A B m n t k tym ihm tyn ihn dN. right... }
  { move=>Γ Δ A B m t tym ihm dN.
    have[[m' stm]|vlm]:=ihm dN.
    { left. exists (Fst m')... }
    { have[m1[m2 e]]:=program_with_canonical tym (convR _ _) dN vlm. subst.
      left. exists m1... } }
  { move=>Γ Δ A B m t tym ihm dN.
    have[[m' stm]|vlm]:=ihm dN.
    { left. exists (Snd m')... }
    { have[m1[m2 e]]:=program_with_canonical tym (convR _ _) dN vlm. subst.
      left. exists m2... } }
  { move=>Γ Δ A B H P m n s h tyB tyH ihH tyP dN. left. exists H... }
  { move=>Γ Δ A B m s eq tym ihm tyB... }
Qed.
