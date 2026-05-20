From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_inv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem sta_valid Γ m A : Γ ⊢ m : A -> exists s l, Γ ⊢ A : Sort s l.
Proof with eauto using sta_type.
  move=>ty. elim: ty=>{Γ m A}...
  { move=>Γ x A wf hs.
    apply: sta_wf_ok... }
  { move=>Γ A B m s tym [t[l tyB]].
    have wf:=sta_type_wf tyB. inv wf.
    exists s. exists (maxn l0 l)... }
  { move=>Γ A B m s tym [t[l tyB]].
    have wf:=sta_type_wf tyB. inv wf.
    exists s. exists (maxn l0 l)... }
  { move=>Γ A B m n s tym[s0[l/sta_pi0_inv[t[l1[l2[tyB/sort_inj[e1 e2]]]]]]]tyn _; subst.
    exists t. exists l1. apply: sta_esubst...
    by autosubst. }
  { move=>Γ A B m n s tym[s0[l/sta_pi1_inv[t[l1[l2[tyB/sort_inj[e1 e2]]]]]]]tyn _; subst.
    exists t. exists l1. apply: sta_esubst...
    by autosubst. }
  { move=>Γ A B C m n s t l tyC _ tym _ _ _.
    have//={}tyC:=sta_subst tyC tym. exists s. exists l... }
  { move=>Γ A B C m n s t l tyC _ tym _ _ _.
    have//={}tyC:=sta_subst tyC tym. exists s. exists l... }
  { move=>Γ A m n1 n2 s l tyA ihA tym ihm tyn1 ihn1 tyn2 ihn2.
    exists s. exists l. apply: sta_esubst...
    by autosubst. }
  { move=>Γ A m tym[s[l tyA]]. exists U. exists l... }
  { move=>Γ A B H P m n s l tyB _ tyH _ tyP[r[l0 tyI]].
    have[_[tym[tyn _]]]:=sta_id_inv tyI. exists s. exists l.
    replace (Sort s l) with (Sort s l).[P,n/] by autosubst.
    apply: sta_substitution...
    repeat constructor; asimpl... }
Qed.

Lemma sta_lam0_invX Γ A1 A2 B C m s1 s2 t l :
  Γ ⊢ Lam0 A1 m s1 : C ->
  C ≃ Pi0 A2 B s2 ->
  (A2 :: Γ) ⊢ B : Sort t l ->
  (A2 :: Γ) ⊢ m : B.
Proof with eauto.
  move e:(Lam0 A1 m s1)=>n tyL.
  elim: tyL A1 A2 B m s1 s2 t l e=>//{Γ C n}.
  { move=>Γ A B m s tym _ A1 A2 B0 m0
      s1 s2 t l[e1 e2 e3]/pi0_inj[eq1[eq2 e4]]tyB0; subst.
    have wf:=sta_type_wf tym. inv wf.
    have wf:=sta_type_wf tyB0. inv wf.
    apply: sta_ctx_conv.
    apply: conv_sym...
    exact: H4.
    apply: sta_conv...
    apply: sta_ctx_conv... }
  { move=>Γ A B m s l eq1 tym ihm tyB ihB A1 A2 B0 m0
      s1 s2 t e eq2 tyB0; subst.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma sta_lam1_invX Γ A1 A2 B C m s1 s2 t l :
  Γ ⊢ Lam1 A1 m s1 : C ->
  C ≃ Pi1 A2 B s2 ->
  (A2 :: Γ) ⊢ B : Sort t l ->
  (A2 :: Γ) ⊢ m : B.
Proof with eauto.
  move e:(Lam1 A1 m s1)=>n tyL.
  elim: tyL A1 A2 B m s1 s2 t l e=>//{Γ C n}.
  { move=>Γ A B m s tym _ A1 A2 B0 m0
      s1 s2 t l[e1 e2 e3]/pi1_inj[eq1[eq2 e4]]tyB0; subst.
    have wf:=sta_type_wf tym. inv wf.
    have wf:=sta_type_wf tyB0. inv wf.
    apply: sta_ctx_conv.
    apply: conv_sym...
    exact: H4.
    apply: sta_conv...
    apply: sta_ctx_conv... }
  { move=>Γ A B m s l eq1 tym ihm tyB ihB A1 A2 B0 m0
      s1 s2 t e eq2 tyB0; subst.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma sta_lam0_inv Γ m A1 A2 B s1 s2 :
  Γ ⊢ Lam0 A2 m s2 : Pi0 A1 B s1 -> (A1 :: Γ) ⊢ m : B.
Proof with eauto.
  move=>ty.
  have[t[l/sta_pi0_inv[r[l1[l2[tyB _]]]]]]:=sta_valid ty.
  apply: sta_lam0_invX...
Qed.

Lemma sta_lam1_inv Γ m A1 A2 B s1 s2 :
  Γ ⊢ Lam1 A2 m s2 : Pi1 A1 B s1 -> (A1 :: Γ) ⊢ m : B.
Proof with eauto.
  move=>ty.
  have[t[l/sta_pi1_inv[r[l1[l2[tyB _]]]]]]:=sta_valid ty.
  apply: sta_lam1_invX...
Qed.

Lemma sta_pair0_invX Γ m n s C :
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
    have[s[r0[l1[l2[ord[tyA0[tyB0/sort_inj[e1 e2]]]]]]]]:=sta_sig0_inv ty2; subst.
    have tym0:Γ ⊢ m : A0 by apply: sta_conv; eauto.
    repeat split...
    apply: sta_conv.
    apply: sta_conv_subst.
    all: eauto.
    apply: sta_esubst...
    by autosubst. }
  { move=>Γ A B m s l eq tym ihm _ _ m0 n s0 e A0 B0 r t eq' ty.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma sta_pair1_invX Γ m n s C :
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
    have[s[r0[l1[l2[ord1[ord2[tyA0[tyB0/sort_inj[e1 e2]]]]]]]]]:=sta_sig1_inv ty2; subst.
    have tym0:Γ ⊢ m : A0 by apply: sta_conv; eauto.
    repeat split...
    apply: sta_conv.
    apply: sta_conv_subst.
    all: eauto.
    apply: sta_esubst...
    by autosubst. }
  { move=>Γ A B m s l eq tym ihm _ _ m0 n s0 e A0 B0 r t eq' ty.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma sta_pair0_inv Γ A B m n s r :
  Γ ⊢ Pair0 m n s : Sig0 A B r ->
  s = r /\ Γ ⊢ m : A /\ Γ ⊢ n : B.[m/].
Proof with eauto.
  move=>ty.
  have[t[l tyS]]:=sta_valid ty.
  apply: sta_pair0_invX...
Qed.

Lemma sta_pair1_inv Γ A B m n s r :
  Γ ⊢ Pair1 m n s : Sig1 A B r ->
  s = r /\ Γ ⊢ m : A /\ Γ ⊢ n : B.[m/].
Proof with eauto.
  move=>ty.
  have[t[l tyS]]:=sta_valid ty.
  apply: sta_pair1_invX...
Qed.

Lemma sta_refl_invX Γ n C :
  Γ ⊢ Refl n : C ->
  forall A m1 m2 s l,
    C ≃ Id A m1 m2 ->
    Γ ⊢ Id A m1 m2 : Sort s l ->
    Γ ⊢ n : A /\ n ≃ m1 /\ n ≃ m2.
Proof with eauto.
  move e:(Refl n)=>x ty.
  elim: ty n e=>//{Γ x C}.
  { move=>Γ A m tym ihm n[e1]A0 m1 m2 s l/id_inj[e2[e3 e4]]tyI; subst.
    have[l1[tym1 _]]:=sta_id_inv tyI.
    have[l2[r tyA0]]:=sta_valid tym1.
    repeat split...
    apply: sta_conv... }
  { move=>Γ A B m s l eqw tym ihm _ _ n e A0 m1 m2 s0 eq' tyI.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma sta_refl_inv Γ A m1 m2 n :
  Γ ⊢ Refl n : Id A m1 m2 -> Γ ⊢ n : A /\ n ≃ m1 /\ n ≃ m2.
Proof with eauto.
  move=>ty.
  have[s[l tyI]]:=sta_valid ty.
  apply: sta_refl_invX...
Qed.
