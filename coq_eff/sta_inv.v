From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_subst.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma sta_pi0_inv Γ A B C s :
  Γ ⊢ Pi0 A B s : C ->
  exists t, (A :: Γ) ⊢ B : Sort t /\ C === Sort s.
Proof with eauto.
  move e:(Pi0 A B s)=>m ty.
  elim: ty A B s e=>//{Γ C m}.
  { move=>Γ A B s r t tyA ihA tyB ihB A0 B0 s0 [e1 e2 e3]; subst.
    exists t... }
  { move=>Γ A B m s eq1 tym ihm tyB ihB A0 B0 s0 e; subst.
    have[t[tyB0 eq2]]:=ihm _ _ _ erefl.
    exists t. split...
    apply: conv_trans.
    apply: conv_sym...
    exact: eq2. }
Qed.

Lemma sta_pi1_inv Γ A B C s :
  Γ ⊢ Pi1 A B s : C ->
  exists t, (A :: Γ) ⊢ B : Sort t /\ C === Sort s.
Proof with eauto.
  move e:(Pi1 A B s)=>m ty.
  elim: ty A B s e=>//{Γ C m}.
  { move=>Γ A B s r t tyA ihA tyB ihB A0 B0 s0 [e1 e2 e3]; subst.
    exists t... }
  { move=>Γ A B m s eq1 tym ihm tyB ihB A0 B0 s0 e; subst.
    have[t[tyB0 eq2]]:=ihm _ _ _ erefl.
    exists t. split...
    apply: conv_trans.
    apply: conv_sym...
    exact: eq2. }
Qed.

Lemma sta_io_inv Γ A B :
  Γ ⊢ IO A : B ->
  exists s, Γ ⊢ A : Sort s /\ B === Sort L.
Proof with eauto.
  move e:(IO A)=>m ty.
  elim: ty A e=>//{Γ B m}.
  { move=>Γ A s tyA ihA A0[e]; subst. exists s... }
  { move=>Γ A B m s eq1 tym ihm tyB ihB A0 e; subst.
    have[s0[tyA0 eq2]]:=ihm _ erefl.
    exists s0. split...
    apply: conv_trans.
    apply: conv_sym...
    exact: eq2. }
Qed.

Lemma sta_return_inv Γ m B :
  Γ ⊢ Return m : B ->
  exists A, Γ ⊢ m : A /\ B === IO A.
Proof with eauto.
  move e:(Return m)=>x ty.
  elim: ty m e=>//{Γ B x}.
  { move=>Γ m A tym ihm m0[e]; subst. exists A... }
  { move=>Γ A B m s eq1 tym ihm tyB ihB m0 e; subst.
    have[A0[tym0 eq2]]:=ihm _ erefl.
    exists A0. split...
    apply: conv_trans.
    apply: conv_sym...
    exact: eq2. }
Qed.

Lemma sta_lam0_pi1_false Γ A1 A2 B C m s1 s2 :
  Γ ⊢ Lam0 A1 m s1 : C -> C === Pi1 A2 B s2 -> False.
Proof with eauto.
  move e:(Lam0 A1 m s1)=>n tyL.
  elim: tyL A1 A2 B m s1 s2 e=>//{Γ C n}.
  { move=>Γ A B m s tym ihm A1 A2 B0 m0 s1 s2[e1 e2 e3] eq; subst.
    solve_conv. }
  { move=>Γ A B m s eq1 tym ihm tyB ihB A1 A2 B0 m0
      s1 s2 e eq2; subst.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma sta_lam1_pi0_false Γ A1 A2 B C m s1 s2 :
  Γ ⊢ Lam1 A1 m s1 : C -> C === Pi0 A2 B s2 -> False.
Proof with eauto.
  move e:(Lam1 A1 m s1)=>n tyL.
  elim: tyL A1 A2 B m s1 s2 e=>//{Γ C n}.
  { move=>Γ A B m s tym ihm A1 A2 B0 m0 s1 s2[e1 e2 e3] eq; subst.
    solve_conv. }
  { move=>Γ A B m s eq1 tym ihm tyB ihB A1 A2 B0 m0
      s1 s2 e eq2; subst.
    apply: ihm...
    apply: conv_trans... }
Qed.
