(** * Logical validity

    [logical_valid]: if [Γ ⊢ m : A] then [A] is itself well-typed at
    some sort and level. Also packages the inverted lambda lemmas
    [logical_lam0_invX] / [logical_lam1_invX] needed by subject
    reduction. *)

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Stdlib Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS logical_inv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem logical_valid Γ m A : Γ ⊢ m : A -> exists s l, Γ ⊢ A : Sort s l.
Proof with eauto using logical_type.
  move=>ty. elim: ty=>{Γ m A}...
  { move=>Γ x A wf hs.
    apply: logical_wf_ok... }
  { move=>Γ A B m s tym [t[l tyB]].
    have wf:=logical_type_wf tyB. inv wf.
    exists s. exists (maxn l0 l)... }
  { move=>Γ A B m s tym [t[l tyB]].
    have wf:=logical_type_wf tyB. inv wf.
    exists s. exists (maxn l0 l)... }
  { move=>Γ A B m n s tym[s0[l/logical_pi0_inv[t[l1[l2[tyB/sort_inj[e1 e2]]]]]]]tyn _; subst.
    exists t. exists l1. apply: logical_esubst...
    by autosubst. }
  { move=>Γ A B m n s tym[s0[l/logical_pi1_inv[t[l1[l2[tyB/sort_inj[e1 e2]]]]]]]tyn _; subst.
    exists t. exists l1. apply: logical_esubst...
    by autosubst. }
  { move=>Γ A B C m n s t l tyC _ tym _ _ _.
    have//={}tyC:=logical_subst tyC tym. exists s. exists l... }
  { move=>Γ A B C m n s t l tyC _ tym _ _ _.
    have//={}tyC:=logical_subst tyC tym. exists s. exists l... }
  { move=>Γ A m n1 n2 s l tyA ihA tym ihm tyn1 ihn1 tyn2 ihn2.
    exists s. exists l. apply: logical_esubst...
    by autosubst. }
  { move=>Γ A m tym[s[l tyA]]. exists U. exists l... }
  { move=>Γ A B H P m n s l tyB _ tyH _ tyP[r[l0 tyI]].
    have[_[tym[tyn _]]]:=logical_id_inv tyI. exists s. exists l.
    replace (Sort s l) with (Sort s l).[P,n/] by autosubst.
    apply: logical_substitution...
    repeat constructor; asimpl... }
Qed.

Lemma logical_lam0_invX Γ A1 A2 B C m s1 s2 t l :
  Γ ⊢ Lam0 A1 m s1 : C ->
  C ≃ Pi0 A2 B s2 ->
  (A2 :: Γ) ⊢ B : Sort t l ->
  (A2 :: Γ) ⊢ m : B.
Proof with eauto.
  move e:(Lam0 A1 m s1)=>n tyL.
  elim: tyL A1 A2 B m s1 s2 t l e=>//{Γ C n}.
  { move=>Γ A B m s tym _ A1 A2 B0 m0
      s1 s2 t l[e1 e2 e3]/pi0_inj[eq1[eq2 e4]]tyB0; subst.
    have wf:=logical_type_wf tym. inv wf.
    have wf:=logical_type_wf tyB0. inv wf.
    apply: logical_ctx_conv.
    apply: conv_sym...
    exact: H4.
    apply: logical_conv...
    apply: logical_ctx_conv... }
  { move=>Γ A B m s l eq1 tym ihm tyB ihB A1 A2 B0 m0
      s1 s2 t e eq2 tyB0; subst.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma logical_lam1_invX Γ A1 A2 B C m s1 s2 t l :
  Γ ⊢ Lam1 A1 m s1 : C ->
  C ≃ Pi1 A2 B s2 ->
  (A2 :: Γ) ⊢ B : Sort t l ->
  (A2 :: Γ) ⊢ m : B.
Proof with eauto.
  move e:(Lam1 A1 m s1)=>n tyL.
  elim: tyL A1 A2 B m s1 s2 t l e=>//{Γ C n}.
  { move=>Γ A B m s tym _ A1 A2 B0 m0
      s1 s2 t l[e1 e2 e3]/pi1_inj[eq1[eq2 e4]]tyB0; subst.
    have wf:=logical_type_wf tym. inv wf.
    have wf:=logical_type_wf tyB0. inv wf.
    apply: logical_ctx_conv.
    apply: conv_sym...
    exact: H4.
    apply: logical_conv...
    apply: logical_ctx_conv... }
  { move=>Γ A B m s l eq1 tym ihm tyB ihB A1 A2 B0 m0
      s1 s2 t e eq2 tyB0; subst.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma logical_lam0_inv Γ m A1 A2 B s1 s2 :
  Γ ⊢ Lam0 A2 m s2 : Pi0 A1 B s1 -> (A1 :: Γ) ⊢ m : B.
Proof with eauto.
  move=>ty.
  have[t[l/logical_pi0_inv[r[l1[l2[tyB _]]]]]]:=logical_valid ty.
  apply: logical_lam0_invX...
Qed.

Lemma logical_lam1_inv Γ m A1 A2 B s1 s2 :
  Γ ⊢ Lam1 A2 m s2 : Pi1 A1 B s1 -> (A1 :: Γ) ⊢ m : B.
Proof with eauto.
  move=>ty.
  have[t[l/logical_pi1_inv[r[l1[l2[tyB _]]]]]]:=logical_valid ty.
  apply: logical_lam1_invX...
Qed.

Lemma logical_pair0_invX Γ m n s C :
  Γ ⊢ Pair0 m n s : C ->
  forall A B r t l,
    C ≃ Sig0 A B r ->
    Γ ⊢ Sig0 A B r : Sort t l ->
    s = r /\ Γ ⊢ m : A /\ Γ ⊢ n : B.[m/].
Proof with eauto.
  move e:(Pair0 m n s)=>x ty.
  elim: ty m n s e=>//{Γ C x}.
  { move=>Γ A B m n t l ty1 _ tym _ tyn _ m0 n0 s[e1 e2 e3]A0 B0 r t0 l0
      /sig0_inj[e4[e5 e6]]ty2; subst.
    have[s[r0[l1[l2[ord[tyA0[tyB0/sort_inj[e1 e2]]]]]]]]:=logical_sig0_inv ty2; subst.
    have tym0:Γ ⊢ m : A0 by apply: logical_conv; eauto.
    repeat split...
    apply: logical_conv.
    apply: logical_conv_subst.
    all: eauto.
    apply: logical_esubst...
    by autosubst. }
  { move=>Γ A B m s l eq tym ihm _ _ m0 n s0 e A0 B0 r t eq' ty.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma logical_pair1_invX Γ m n s C :
  Γ ⊢ Pair1 m n s : C ->
  forall A B r t l,
    C ≃ Sig1 A B r ->
    Γ ⊢ Sig1 A B r : Sort t l ->
    s = r /\ Γ ⊢ m : A /\ Γ ⊢ n : B.[m/].
Proof with eauto.
  move e:(Pair1 m n s)=>x ty.
  elim: ty m n s e=>//{Γ C x}.
  { move=>Γ A B m n t l ty1 _ tym _ tyn _ m0 n0 s[e1 e2 e3]A0 B0 r t0 l0
      /sig1_inj[e4[e5 e6]]ty2; subst.
    have[s[r0[l1[l2[ord1[ord2[tyA0[tyB0/sort_inj[e1 e2]]]]]]]]]:=logical_sig1_inv ty2; subst.
    have tym0:Γ ⊢ m : A0 by apply: logical_conv; eauto.
    repeat split...
    apply: logical_conv.
    apply: logical_conv_subst.
    all: eauto.
    apply: logical_esubst...
    by autosubst. }
  { move=>Γ A B m s l eq tym ihm _ _ m0 n s0 e A0 B0 r t eq' ty.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma logical_pair0_inv Γ A B m n s r :
  Γ ⊢ Pair0 m n s : Sig0 A B r ->
  s = r /\ Γ ⊢ m : A /\ Γ ⊢ n : B.[m/].
Proof with eauto.
  move=>ty.
  have[t[l tyS]]:=logical_valid ty.
  apply: logical_pair0_invX...
Qed.

Lemma logical_pair1_inv Γ A B m n s r :
  Γ ⊢ Pair1 m n s : Sig1 A B r ->
  s = r /\ Γ ⊢ m : A /\ Γ ⊢ n : B.[m/].
Proof with eauto.
  move=>ty.
  have[t[l tyS]]:=logical_valid ty.
  apply: logical_pair1_invX...
Qed.

Lemma logical_refl_invX Γ n C :
  Γ ⊢ Refl n : C ->
  forall A m1 m2 s l,
    C ≃ Id A m1 m2 ->
    Γ ⊢ Id A m1 m2 : Sort s l ->
    Γ ⊢ n : A /\ n ≃ m1 /\ n ≃ m2.
Proof with eauto.
  move e:(Refl n)=>x ty.
  elim: ty n e=>//{Γ x C}.
  { move=>Γ A m tym ihm n[e1]A0 m1 m2 s l/id_inj[e2[e3 e4]]tyI; subst.
    have[l1[tym1 _]]:=logical_id_inv tyI.
    have[l2[r tyA0]]:=logical_valid tym1.
    repeat split...
    apply: logical_conv... }
  { move=>Γ A B m s l eqw tym ihm _ _ n e A0 m1 m2 s0 eq' tyI.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma logical_refl_inv Γ A m1 m2 n :
  Γ ⊢ Refl n : Id A m1 m2 -> Γ ⊢ n : A /\ n ≃ m1 /\ n ≃ m2.
Proof with eauto.
  move=>ty.
  have[s[l tyI]]:=logical_valid ty.
  apply: logical_refl_invX...
Qed.
