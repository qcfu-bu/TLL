From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_subst.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma sta_pi0_inv Γ A B C s :
  Γ ⊢ Pi0 A B s : C ->
  exists t l1 l2, (A :: Γ) ⊢ B : Sort t l1 /\ C ≃ Sort s l2.
Proof with eauto.
  move e:(Pi0 A B s)=>m ty.
  elim: ty A B s e=>//{Γ C m}.
  { move=>Γ A B s r t l1 l2 tyA ihA tyB ihB A0 B0 s0 [e1 e2 e3]; subst.
    exists t. exists l2. exists (maxn l1 l2)... }
  { move=>Γ A B m s l eq1 tym ihm tyB ihB A0 B0 s0 e; subst.
    have[t[l1[l2[tyB0 eq2]]]]:=ihm _ _ _ erefl.
    exists t. exists l1. exists l2. split...
    apply: conv_trans.
    apply: conv_sym...
    exact: eq2. }
Qed.

Lemma sta_pi1_inv Γ A B C s :
  Γ ⊢ Pi1 A B s : C ->
  exists t l1 l2, (A :: Γ) ⊢ B : Sort t l1 /\ C ≃ Sort s l2.
Proof with eauto.
  move e:(Pi1 A B s)=>m ty.
  elim: ty A B s e=>//{Γ C m}.
  { move=>Γ A B s r t l1 l2 tyA ihA tyB ihB A0 B0 s0 [e1 e2 e3]; subst.
    exists t. exists l2. exists (maxn l1 l2)... }
  { move=>Γ A B m s l eq1 tym ihm tyB ihB A0 B0 s0 e; subst.
    have[t[l1[l2[tyB0 eq2]]]]:=ihm _ _ _ erefl.
    exists t. exists l1. exists l2. split...
    apply: conv_trans.
    apply: conv_sym...
    exact: eq2. }
Qed.

Lemma sta_sig0_inv Γ A B C t :
  Γ ⊢ Sig0 A B t : C ->
  exists s r l1 l2, s ⊑ t /\ Γ ⊢ A : Sort s l1 /\ (A :: Γ) ⊢ B : Sort r l2 /\ C ≃ Sort t (maxn l1 l2).
Proof with eauto.
  move e:(Sig0 A B t)=>m ty.
  elim: ty A B t e=>//{Γ C m}.
  { move=>Γ A B s r t l1 l2 ord tyA ihA tyB ihB A0 B0 s0[e1 e2 e3]; subst.
    exists s. exists r. exists l1. exists l2... }
  { move=>Γ A B m s l eq tym ihm tyB ihB A0 B0 t e; subst.
    have[s0[r[l1[l2[ord[tyA0[tyB0 eq']]]]]]]:=ihm _ _ _ erefl.
    exists s0. exists r. exists l1. exists l2. repeat split...
    apply: conv_trans.
    apply: conv_sym...
    exact: eq'. }
Qed.

Lemma sta_sig1_inv Γ A B C t :
  Γ ⊢ Sig1 A B t : C ->
  exists s r l1 l2,
    s ⊑ t /\ r ⊑ t /\
    Γ ⊢ A : Sort s l1 /\ (A :: Γ) ⊢ B : Sort r l2 /\ C ≃ Sort t (maxn l1 l2).
Proof with eauto.
  move e:(Sig1 A B t)=>m ty.
  elim: ty A B t e=>//{Γ C m}.
  { move=>Γ A B s r t l1 l2 ord1 ord2 tyA ihA tyB ihB A0 B0 s0[e1 e2 e3]; subst.
    exists s. exists r. exists l1. exists l2... }
  { move=>Γ A B m s l eq tym ihm tyB ihB A0 B0 t e; subst.
    have[s0[r[l1[l2[ord1[ord2[tyA0[tyB0 eq']]]]]]]]:=ihm _ _ _ erefl.
    exists s0. exists r. exists l1. exists l2. repeat split...
    apply: conv_trans.
    apply: conv_sym...
    exact: eq'. }
Qed.

Lemma sta_id_inv Γ A B m n :
  Γ ⊢ Id A m n : B ->
  exists l, Γ ⊢ m : A /\ Γ ⊢ n : A /\ B ≃ Sort U l.
Proof with eauto.
  move e:(Id A m n)=>x tyI.
  elim: tyI A m n e=>//{Γ x B}.
  { move=>Γ A m n l s tyA ihA tym ihm tyn ihn A0 m0 n0[e1 e2 e3]; subst... }
  { move=>Γ A B m l s eq tym ihm tyB ihB A0 m0 n e; subst.
    have[l0[tym0[tyn eq']]]:=ihm _ _ _ erefl.
    exists l0. repeat split...
    apply: conv_trans.
    apply: conv_sym...
    exact: eq'. }
Qed.

Lemma sta_lam0_pi1_false Γ A1 A2 B C m s1 s2 :
  Γ ⊢ Lam0 A1 m s1 : C -> C ≃ Pi1 A2 B s2 -> False.
Proof with eauto.
  move e:(Lam0 A1 m s1)=>n tyL.
  elim: tyL A1 A2 B m s1 s2 e=>//{Γ C n}.
  { move=>*. solve_conv. }
  { move=>Γ A B m s l eq1 tym ihm tyB ihB A1 A2 B0 m0 s1 s2 e eq2; subst.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma sta_lam1_pi0_false Γ A1 A2 B C m s1 s2 :
  Γ ⊢ Lam1 A1 m s1 : C -> C ≃ Pi0 A2 B s2 -> False.
Proof with eauto.
  move e:(Lam1 A1 m s1)=>n tyL.
  elim: tyL A1 A2 B m s1 s2 e=>//{Γ C n}.
  { move=>*. solve_conv. }
  { move=>Γ A B m s l eq1 tym ihm tyB ihB A1 A2 B0 m0 s1 s2 e eq2; subst.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma sta_pair0_sig1_false Γ A B C m1 m2 s1 s2 :
  Γ ⊢ Pair0 m1 m2 s1 : C -> C ≃ Sig1 A B s2 -> False.
Proof with eauto.
  move e:(Pair0 m1 m2 s1)=>n tyP.
  elim: tyP A B m1 m2 s1 s2 e=>//{Γ C n}.
  { move=>*. solve_conv. }
  { move=>Γ A B m s l eq1 tym ihm tyB ihB A0 B0 m1 m2 s1 s2 e eq2; subst.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma sta_pair1_sig0_false Γ A B C m1 m2 s1 s2 :
  Γ ⊢ Pair1 m1 m2 s1 : C -> C ≃ Sig0 A B s2 -> False.
Proof with eauto.
  move e:(Pair1 m1 m2 s1)=>n tyP.
  elim: tyP A B m1 m2 s1 s2 e=>//{Γ C n}.
  { move=>*. solve_conv. }
  { move=>Γ A B m s l eq1 tym ihm tyB ihB A0 B0 m1 m2 s1 s2 e eq2; subst.
    apply: ihm...
    apply: conv_trans... }
Qed.
