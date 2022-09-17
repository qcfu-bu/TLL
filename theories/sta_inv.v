From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_subst.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma sta_pi0_inv Γ A B C s t :
  Γ ⊢ Pi0 A B s t : C ->
  exists r, Γ ⊢ A : @s /\ (A :: Γ) ⊢ B : @r /\ C === @t.
Proof with eauto.
  move e:(Pi0 A B s t)=>m ty.
  elim: ty A B s t e=>//{Γ C m}.
  { move=>Γ A B s r t tyA ihA tyB ihB A0 B0 s0 t0
    [e1 e2 e3 e4]; subst.
    exists r... }
  { move=>Γ A B m s eq1 tym ihm tyB ihB A0 B0 s0 t0 e; subst.
    have[r[tyA0[tyB0 eq2]]]:=ihm _ _ _ _ erefl.
    exists r. repeat split...
    apply: conv_trans.
    apply: conv_sym...
    exact: eq2. }
Qed.

Lemma sta_pi1_inv Γ A B C s t :
  Γ ⊢ Pi1 A B s t : C ->
  exists r, Γ ⊢ A : @s /\ (A :: Γ) ⊢ B : @r /\ C === @t.
Proof with eauto.
  move e:(Pi1 A B s t)=>m ty.
  elim: ty A B s t e=>//{Γ C m}.
  { move=>Γ A B s r t tyA ihA tyB ihB A0 B0 s0 t0
    [e1 e2 e3 e4]; subst.
    exists r... }
  { move=>Γ A B m s eq1 tym ihm tyB ihB A0 B0 s0 t0 e; subst.
    have[r[tyA0[tyB0 eq2]]]:=ihm _ _ _ _ erefl.
    exists r. repeat split...
    apply: conv_trans.
    apply: conv_sym...
    exact: eq2. }
Qed.

Lemma sta_lam0_invX Γ A1 A2 B C m s1 s2 t1 t2 r :
  Γ ⊢ Lam0 A1 m s1 t1 : C ->
  C === Pi0 A2 B s2 t2 ->
  (A2 :: Γ) ⊢ B : @r ->
  (A2 :: Γ) ⊢ m : B.
Proof with eauto.
  move e:(Lam0 A1 m s1 t1)=>n tyL.
  elim: tyL A1 A2 B m s1 s2 t1 t2 r e=>//{Γ C n}.
  { move=>Γ A B m s t tyP ihP tym ihm A1 A2 B0 m0
      s1 s2 t1 t2 r0 [e1 e2 e3 e4]/pi0_inj[eq1[eq2[e5 e6]]] tyB0; subst.
    have[r[tyA[tyB _]]]:=sta_pi0_inv tyP.
    apply: sta_conv...
    apply: sta_ctx_conv.
    apply: (conv_sym eq1).
    exact: tyA.
    exact: tym. }
  { move=>Γ A B m s eq1 tym ihm tyB ihB A1 A2 B0 m0
      s1 s2 t1 t2 r e eq2 tyB0; subst.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma sta_lam1_invX Γ A1 A2 B C m s1 s2 t1 t2 r :
  Γ ⊢ Lam1 A1 m s1 t1 : C ->
  C === Pi1 A2 B s2 t2 ->
  (A2 :: Γ) ⊢ B : @r ->
  (A2 :: Γ) ⊢ m : B.
Proof with eauto.
  move e:(Lam1 A1 m s1 t1)=>n tyL.
  elim: tyL A1 A2 B m s1 s2 t1 t2 r e=>//{Γ C n}.
  { move=>Γ A B m s t tyP ihP tym ihm A1 A2 B0 m0
      s1 s2 t1 t2 r0 [e1 e2 e3 e4]/pi1_inj[eq1[eq2[e5 e6]]] tyB0; subst.
    have[r[tyA[tyB _]]]:=sta_pi1_inv tyP.
    apply: sta_conv...
    apply: sta_ctx_conv.
    apply: (conv_sym eq1).
    exact: tyA.
    exact: tym. }
  { move=>Γ A B m s eq1 tym ihm tyB ihB A1 A2 B0 m0
      s1 s2 t1 t2 r e eq2 tyB0; subst.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma sta_lam0_inv Γ m A1 A2 B s1 s2 t1 t2 x :
  Γ ⊢ Pi0 A1 B s1 t1 : @x ->
  Γ ⊢ Lam0 A2 m s2 t2 : Pi0 A1 B s1 t1 ->
  (A1 :: Γ) ⊢ m : B.
Proof with eauto.
  move=>/sta_pi0_inv[r[tyA1[tyB _]]] tyL.
  apply: sta_lam0_invX...
Qed.

Lemma sta_lam1_inv Γ m A1 A2 B s1 s2 t1 t2 x :
  Γ ⊢ Pi1 A1 B s1 t1 : @x ->
  Γ ⊢ Lam1 A2 m s2 t2 : Pi1 A1 B s1 t1 ->
  (A1 :: Γ) ⊢ m : B.
Proof with eauto.
  move=>/sta_pi1_inv[r[tyA1[tyB _]]] tyL.
  apply: sta_lam1_invX...
Qed.

Lemma sta_lam0_pi1_false Γ A1 A2 B C m s1 s2 t1 t2 :
  Γ ⊢ Lam0 A1 m s1 t1 : C -> C === Pi1 A2 B s2 t2 -> False.
Proof with eauto.
  move e:(Lam0 A1 m s1 t1)=>n tyL.
  elim: tyL A1 A2 B m s1 s2 t1 t2 e=>//{Γ C n}.
  { move=>Γ A B m s t tyP ihP tym ihm A1 A2 B0 m0
      s1 s2 t1 t2 [e1 e2 e3 e4] eq; subst.
    solve_conv. }
  { move=>Γ A B m s eq1 tym ihm tyB ihB A1 A2 B0 m0
      s1 s2 t1 t2 e eq2; subst.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma sta_lam1_pi0_false Γ A1 A2 B C m s1 s2 t1 t2 :
  Γ ⊢ Lam1 A1 m s1 t1 : C -> C === Pi0 A2 B s2 t2 -> False.
Proof with eauto.
  move e:(Lam1 A1 m s1 t1)=>n tyL.
  elim: tyL A1 A2 B m s1 s2 t1 t2 e=>//{Γ C n}.
  { move=>Γ A B m s t tyP ihP tym ihm A1 A2 B0 m0
      s1 s2 t1 t2 [e1 e2 e3 e4] eq; subst.
    solve_conv. }
  { move=>Γ A B m s eq1 tym ihm tyB ihB A1 A2 B0 m0
      s1 s2 t1 t2 e eq2; subst.
    apply: ihm...
    apply: conv_trans... }
Qed.
