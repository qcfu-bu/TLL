From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_subst.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma sta_pi0_inv Γ A B C s :
  Γ ⊢ Pi0 A B s : C ->
  exists t, (A :: Γ) ⊢ B : Sort t /\ C ≃ Sort s.
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
  exists t, (A :: Γ) ⊢ B : Sort t /\ C ≃ Sort s.
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

Lemma sta_sig0_inv Γ A B C t :
  Γ ⊢ Sig0 A B t : C ->
  exists s r, r ⊑ t /\ Γ ⊢ A : Sort s /\ (A :: Γ) ⊢ B : Sort r /\ C ≃ Sort t.
Proof with eauto.
  move e:(Sig0 A B t)=>m ty.
  elim: ty A B t e=>//{Γ C m}.
  { move=>Γ A B s r t ord tyA ihA tyB ihB A0 B0 s0[e1 e2 e3]; subst.
    exists s. exists r... }
  { move=>Γ A B m s eq tym ihm tyB ihB A0 B0 t e; subst.
    have[s0[r[ord[tyA0[tyB0 eq']]]]]:=ihm _ _ _ erefl.
    exists s0. exists r. repeat split...
    apply: conv_trans.
    apply: conv_sym...
    exact: eq'. }
Qed.

Lemma sta_sig1_inv Γ A B C t :
  Γ ⊢ Sig1 A B t : C ->
  exists s r,
    s ⊑ t /\ r ⊑ t /\
    Γ ⊢ A : Sort s /\ (A :: Γ) ⊢ B : Sort r /\ C ≃ Sort t.
Proof with eauto.
  move e:(Sig1 A B t)=>m ty.
  elim: ty A B t e=>//{Γ C m}.
  { move=>Γ A B s r t ord1 ord2 tyA ihA tyB ihB A0 B0 s0[e1 e2 e3]; subst.
    exists s. exists r... }
  { move=>Γ A B m s eq tym ihm tyB ihB A0 B0 t e; subst.
    have[s0[r[ord1[ord2[tyA0[tyB0 eq']]]]]]:=ihm _ _ _ erefl.
    exists s0. exists r. repeat split...
    apply: conv_trans.
    apply: conv_sym...
    exact: eq'. }
Qed.

Lemma sta_ifte_inv Γ m n1 n2 A C :
  Γ ⊢ Ifte A m n1 n2 : C ->
  A.[m/] ≃ C /\
  Γ ⊢ m : Bool /\
  Γ ⊢ n1 : A.[TT/] /\
  Γ ⊢ n2 : A.[FF/].
Proof with eauto.
  move e:(Ifte A m n1 n2)=>x ty. elim: ty A m n1 n2 e=>//{Γ x C}.
  { move=>Γ A m n1 n2 s tym ihm tyA ihA tyn1 ihn1 tyn2 ihn2 A0 m0 n0 n3
      [e1 e2 e3 e4]; subst.
    repeat split... }
  { move=>Γ A B m s eq tym ihm tyB ihB A0 m0 n1 n2 e; subst.
    have[eqA[tym0[tyn1 tyn2]]]:=ihm _ _ _ _ erefl.
    repeat split...
    apply: conv_trans... }
Qed.

Lemma sta_io_inv Γ A B :
  Γ ⊢ IO A : B ->
  exists s, Γ ⊢ A : Sort s /\ B ≃ Sort L.
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
  exists A, Γ ⊢ m : A /\ B ≃ IO A.
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

Lemma sta_act0_inv Γ r A B C :
  Γ ⊢ Act0 r A B : C -> (A :: Γ) ⊢ B : Proto.
Proof with eauto.
  move e:(Act0 r A B)=>n tp. elim:tp r A B e=>//{Γ C n}.
  move=>Γ r A B tyB ihB r0 A0 B0[e1 e2 e3]; subst...
Qed.

Lemma sta_act1_inv Γ r A B C :
  Γ ⊢ Act1 r A B : C -> (A :: Γ) ⊢ B : Proto.
Proof with eauto.
  move e:(Act1 r A B)=>n tp. elim:tp r A B e=>//{Γ C n}.
  move=>Γ r A B tyB ihB r0 A0 B0[e1 e2 e3]; subst...
Qed.

Lemma sta_ch_inv Γ r A B :
  Γ ⊢ Ch r A : B -> Γ ⊢ A : Proto /\ B ≃ Sort L.
Proof with eauto.
  move e:(Ch r A)=>n tp. elim: tp r A e=>//{Γ B n}.
  { move=>Γ r A tyA ihA r0 A0[e1 e2]; subst=>//. }
  { move=>Γ A B m s eq1 tym ihm tyB ihB r A0 e; subst.
    have[tyA0 eq2]:=ihm _ _ erefl. split...
    apply: conv_trans.
    apply: conv_sym...
    exact: eq2. }
Qed.

Lemma sta_lam0_pi1_false Γ A1 A2 B C m s1 s2 :
  Γ ⊢ Lam0 A1 m s1 : C -> C ≃ Pi1 A2 B s2 -> False.
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
  Γ ⊢ Lam1 A1 m s1 : C -> C ≃ Pi0 A2 B s2 -> False.
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

Lemma sta_pair0_sig1_false Γ A B C m1 m2 s1 s2 :
  Γ ⊢ Pair0 m1 m2 s1 : C -> C ≃ Sig1 A B s2 -> False.
Proof with eauto.
  move e:(Pair0 m1 m2 s1)=>n tyP.
  elim: tyP A B m1 m2 s1 s2 e=>//{Γ C n}.
  { move=>*. solve_conv. }
  { move=>Γ A B m s eq1 tym ihm tyB ihB A0 B0 m1 m2 s1 s2 e eq2; subst.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma sta_pair1_sig0_false Γ A B C m1 m2 s1 s2 :
  Γ ⊢ Pair1 m1 m2 s1 : C -> C ≃ Sig0 A B s2 -> False.
Proof with eauto.
  move e:(Pair1 m1 m2 s1)=>n tyP.
  elim: tyP A B m1 m2 s1 s2 e=>//{Γ C n}.
  { move=>*. solve_conv. }
  { move=>Γ A B m s eq1 tym ihm tyB ihB A0 B0 m1 m2 s1 s2 e eq2; subst.
    apply: ihm...
    apply: conv_trans... }
Qed.
