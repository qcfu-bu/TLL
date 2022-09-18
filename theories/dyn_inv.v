From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS dyn_subst.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma dyn_lam0_invX Γ Δ A1 A2 B C m s1 s2 t1 t2 r :
  dyn_wf (A2 :: Γ) (_: Δ) ->
  Γ ; Δ ⊢ Lam0 A1 m s1 t1 : C ->
  C === Pi0 A2 B s2 t2 ->
  (A2 :: Γ) ⊢ B : @r ->
  (A2 :: Γ) ; _: Δ ⊢ m : B /\ s1 = s2 /\ t1 = t2.
Proof with eauto.
  move e:(Lam0 A1 m s1 t1)=>n wf tyL.
  elim: tyL A1 A2 B m wf s1 s2 t1 t2 r e=>//{Γ Δ C n}.
  { move=>Γ Δ A B m s t k tyP tym ihm A1 A2 B0 m0 wf
      s1 s2 t1 t2 r0 [e1 e2 e3 e4]/pi0_inj[eq1[eq2[e5 e6]]] tyB0; subst.
    have[r[tyA[tyB _]]]:=sta_pi0_inv tyP.
    split...
    apply: dyn_conv...
    apply: dyn_ctx_conv0.
    exact: wf.
    exact: (conv_sym eq1).
    exact: tyA.
    exact: tym. }
  { move=>Γ Δ A B m s eq1 tym ihm tyB A1 A2 B0 m0 wf
      s1 s2 t1 t2 r e e2 tyB0; subst.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma dyn_lam1_invX Γ Δ A1 A2 B C m s1 s2 t1 t2 r :
  dyn_wf (A2 :: Γ) (A2 :{s2} Δ) ->
  Γ ; Δ ⊢ Lam1 A1 m s1 t1 : C ->
  C === Pi1 A2 B s2 t2 ->
  (A2 :: Γ) ⊢ B : @r ->
  (A2 :: Γ) ; A2 :{s2} Δ ⊢ m : B /\ s1 = s2 /\ t1 = t2.
Proof with eauto.
  move e:(Lam1 A1 m s1 t1)=>n wf tyL.
  elim: tyL A1 A2 B m s1 s2 t1 t2 r wf e=>//{Γ Δ C n}.
  { move=>Γ Δ A B m s t k tyP tym ihm A1 A2 B0 m0
      s1 s2 t1 t2 r0 wf [e1 e2 e3 e4]/pi1_inj[eq1[eq2[e5 e6]]] tyB0; subst.
    have[r[tyA[tyB _]]]:=sta_pi1_inv tyP.
    split...
    apply: dyn_conv...
    apply: dyn_ctx_conv1.
    exact: wf.
    exact: (conv_sym eq1).
    exact: tyA.
    exact: tym. }
  { move=>Γ Δ A B m s eq1 tym ihm tyB A1 A2 B0 m0
      s1 s2 t1 t2 r wf e e2 tyB0; subst.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma dyn_lam0_inv Γ Δ m A1 A2 B s1 s2 t1 t2 x :
  dyn_wf Γ Δ ->
  Γ ⊢ Pi0 A1 B s1 t1 : @x ->
  Γ ; Δ ⊢ Lam0 A2 m s2 t2 : Pi0 A1 B s1 t1 ->
  (A1 :: Γ) ; _: Δ ⊢ m : B /\ s2 = s1 /\ t2 = t1.
Proof with eauto.
  move=>wf/sta_pi0_inv[r[tyA1[tyB _]]] tyL.
  apply: dyn_lam0_invX...
  apply: dyn_wf_n...
Qed.

Lemma dyn_lam1_inv Γ Δ m A1 A2 B s1 s2 t1 t2 x :
  dyn_wf Γ Δ ->
  Γ ⊢ Pi1 A1 B s1 t1 : @x ->
  Γ ; Δ ⊢ Lam1 A2 m s2 t2 : Pi1 A1 B s1 t1 ->
  (A1 :: Γ) ; A1 :{s1} Δ ⊢ m : B /\ s2 = s1 /\ t2 = t1.
Proof with eauto.
  move=>wf/sta_pi1_inv[r[tyA1[tyB _]]] tyL.
  apply: dyn_lam1_invX...
  apply: dyn_wf_ty...
Qed.
