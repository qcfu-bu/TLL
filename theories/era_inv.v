From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS era_subst.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma era_lam0_form Γ Δ m n X B s t :
  Γ ; Δ ⊨ m ~ Lam0 X n s t : B -> exists A n, m = Lam0 A n s t.
Proof.
  move e:(Lam0 X n s t)=>x er. elim: er X n s t e=>//{Γ Δ m x B}.
  move=>Γ Δ A B m m' s t k tyP er ih X n s0 t0 [e1 e2 e3 e4]; subst.
  exists A. by exists m.
Qed.

Lemma era_lam1_form Γ Δ m n X B s t :
  Γ ; Δ ⊨ m ~ Lam1 X n s t : B -> exists A n, m = Lam1 A n s t.
Proof.
  move e:(Lam1 X n s t)=>x er. elim: er X n s t e=>//{Γ Δ m x B}.
  move=>Γ Δ A B m m' s t k tyP er ih X n s0 t0 [e1 e2 e3 e4]; subst.
  exists A. by exists m.
Qed.

Lemma era_box_form Γ Δ m A : ~Γ ; Δ ⊨ m ~ Box : A.
Proof. move e:(Box)=>m' ty. elim: ty e=>//{Γ Δ m m' A}. Qed.

Lemma era_lam0_invX Γ Δ A1 A2 A3 B C m1 m2 s1 s2 t1 t2 r :
  dyn_wf (A3 :: Γ) (_: Δ) ->
  Γ ; Δ ⊨ Lam0 A1 m1 s1 t1 ~ Lam0 A2 m2 s1 t1 : C ->
  C === Pi0 A3 B s2 t2 ->
  (A3 :: Γ) ⊢ B : @r ->
  (A3 :: Γ) ; _: Δ ⊨ m1 ~ m2 : B /\ s1 = s2 /\ t1 = t2.
Proof with eauto.
  move e1:(Lam0 A1 m1 s1 t1)=>n1.
  move e2:(Lam0 A2 m2 s1 t1)=>n2 wf tyL.
  elim: tyL A1 A2 A3 B m1 m2 wf s1 s2 t1 t2 r e1 e2=>//{Γ Δ C n1 n2}.
  { move=>Γ Δ A B m m' s t k tyP tym ihm A1 A2 A3 B0 m1 m2 wf
      s1 s2 t1 t2 r0 [e1 e2 e3 e4][e5 e6 e7 e8]; subst.
    move=>/pi0_inj[eq1[eq2[e1 e2]]] tyB0; subst.
    have[r[tyA[tyB _]]]:=sta_pi0_inv tyP.
    split...
    apply: era_conv...
    apply: era_ctx_conv0.
    exact: wf.
    exact: (conv_sym eq1).
    exact: tyA.
    exact: tym. }
  { move=>Γ Δ A B m m' s eq1 tym ihm tyB A1 A2 A3 B0 m1 m2 wf
      s1 s2 t1 t2 r e1 e2 eq tyB0; subst.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma era_lam1_invX Γ Δ A1 A2 A3 B C m1 m2 s1 s2 t1 t2 r :
  dyn_wf (A3 :: Γ) (A3 :{s2} Δ) ->
  Γ ; Δ ⊨ Lam1 A1 m1 s1 t1 ~ Lam1 A2 m2 s1 t1 : C ->
  C === Pi1 A3 B s2 t2 ->
  (A3 :: Γ) ⊢ B : @r ->
  (A3 :: Γ) ; A3 :{s2} Δ ⊨ m1 ~ m2 : B /\ s1 = s2 /\ t1 = t2.
Proof with eauto.
  move e1:(Lam1 A1 m1 s1 t1)=>n1.
  move e2:(Lam1 A2 m2 s1 t1)=>n2 wf tyL.
  elim: tyL A1 A2 A3 B m1 m2 s1 s2 t1 t2 r wf e1 e2=>//{Γ Δ C n1 n2}.
  { move=>Γ Δ A B m m' s t k tyP tym ihm A1 A2 A3 B0 m1 m2
      s1 s2 t1 t2 r0 wf [e1 e2 e3 e4][e5 e6 e7 e8]; subst.
    move=>/pi1_inj[eq1[eq2[e1 e2]]] tyB0; subst.
    have[r[tyA[tyB _]]]:=sta_pi1_inv tyP.
    split...
    apply: era_conv...
    apply: era_ctx_conv1.
    exact: wf.
    exact: (conv_sym eq1).
    exact: tyA.
    exact: tym. }
  { move=>Γ Δ A B m m' s eq1 tym ihm tyB A1 A2 A3 B0 m1 m2
      s1 s2 t1 t2 r wf e1 e2 eq tyB0; subst.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma era_lam0_inv Γ Δ m m' A1 A2 A3 B s1 s2 t1 t2 x :
  dyn_wf Γ Δ ->
  Γ ⊢ Pi0 A1 B s1 t1 : @x ->
  Γ ; Δ ⊨ Lam0 A2 m s2 t2 ~ Lam0 A3 m' s2 t2 : Pi0 A1 B s1 t1 ->
  (A1 :: Γ) ; _: Δ ⊨ m ~ m' : B /\ s2 = s1 /\ t2 = t1.
Proof with eauto.
  move=>wf/sta_pi0_inv[r[tyA1[tyB _]]] tyL.
  apply: era_lam0_invX...
  apply: dyn_wf_n...
Qed.

Lemma era_lam1_inv Γ Δ m m' A1 A2 A3 B s1 s2 t1 t2 x :
  dyn_wf Γ Δ ->
  Γ ⊢ Pi1 A1 B s1 t1 : @x ->
  Γ ; Δ ⊨ Lam1 A2 m s2 t2 ~ Lam1 A3 m' s2 t2 : Pi1 A1 B s1 t1 ->
  (A1 :: Γ) ; A1 :{s1} Δ ⊨ m ~ m' : B /\ s2 = s1 /\ t2 = t1.
Proof with eauto.
  move=>wf/sta_pi1_inv[r[tyA1[tyB _]]] tyL.
  apply: era_lam1_invX...
  apply: dyn_wf_ty...
Qed.
