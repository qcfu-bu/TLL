From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_inv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma sta_sort_uniq Γ s A :
  Γ ⊢ Sort s : A -> Sort U === A.
Proof with eauto.
  move e:(Sort s)=>n ty. elim: ty s e=>//{Γ n A}.
  move=>Γ A B m s eq tym ihm tyB ihB t e; subst.
  apply: conv_trans.
  apply: ihm...
  exact: eq.
Qed.

Lemma sta_has_uniq Γ x A B : sta_has Γ x A -> sta_has Γ x B -> A = B.
Proof with eauto.
  move=>hs. elim: hs B=>{Γ x A}.
  { move=>Γ A B hs. inv hs... }
  { move=>Γ A B x hs ih C hs'. inv hs'.
    rewrite (ih _ H3)... }
Qed.

Lemma sta_var_uniq Γ A B x :
  Γ ⊢ Var x : B -> sta_has Γ x A -> A === B.
Proof with eauto.
  move e:(Var x)=>n ty. elim: ty A x e=>//{Γ n B}.
  { move=>Γ x A wf hs1 A0 x0 [e] hs2; subst.
    by rewrite (sta_has_uniq hs1 hs2). }
  { move=>Γ A B m s eq tym ihm tyB ihB A0 x e hs; subst.
    apply: conv_trans.
    apply: ihm...
    exact: eq. }
Qed.

Lemma sta_lam0_uniq Γ A B C m s :
  Γ ⊢ Lam0 A m s : C -> (forall C, (A :: Γ) ⊢ m : C -> B === C) -> Pi0 A B s === C.
Proof with eauto.
  move e:(Lam0 A m s)=>n ty. elim: ty A B m s e=>//{Γ n C}.
  { move=>Γ A B m s tym ihm A0 B0 m0 s0 [e1 e2 e3] h; subst.
    have eq:=h _ tym.
    apply: sta_conv_pi0... }
  { move=>Γ A B m s eq tym ihm tyB ihB A0 B0 m0 s0 e h; subst.
    apply: conv_trans.
    apply: ihm...
    exact: eq. }
Qed.

Lemma sta_lam1_uniq Γ A B C m s :
  Γ ⊢ Lam1 A m s : C -> (forall C, (A :: Γ) ⊢ m : C -> B === C) -> Pi1 A B s === C.
Proof with eauto.
  move e:(Lam1 A m s)=>n ty. elim: ty A B m s e=>//{Γ n C}.
  { move=>Γ A B m s tym ihm A0 B0 m0 s0 [e1 e2 e3] h; subst.
    have eq:=h _ tym.
    apply: sta_conv_pi1... }
  { move=>Γ A B m s eq tym ihm tyB ihB A0 B0 m0 s0 e h; subst.
    apply: conv_trans.
    apply: ihm...
    exact: eq. }
Qed.

Lemma sta_app0_uniq Γ A B C m n s :
  Γ ⊢ App m n : C -> (forall C, Γ ⊢ m : C -> Pi0 A B s === C) -> B.[n/] === C.
Proof with eauto.
  move e:(App m n)=>x ty. elim: ty A B m n s e=>//{Γ x C}.
  { move=>Γ A B m n s tym ihm tyn ihn A0 B0 m0 n0 s0 [e1 e2] h; subst.
    have/pi0_inj[_[eq _]]:=h _ tym.
    apply: sta_conv_subst... }
  { move=>Γ A B m n s tym ihm tyn ihn A0 B0 m0 n0 s0 [e1 e2] h; subst.
    have eq:=h _ tym.
    exfalso. solve_conv. }
  { move=>Γ A B m s eq tym ihm tyB ihB A0 B0 m0 n s0 e h; subst.
    apply: conv_trans.
    apply: ihm...
    exact: eq. }
Qed.

Lemma sta_app1_uniq Γ A B C m n s :
  Γ ⊢ App m n : C -> (forall C, Γ ⊢ m : C -> Pi1 A B s === C) -> B.[n/] === C.
Proof with eauto.
  move e:(App m n)=>x ty. elim: ty A B m n s e=>//{Γ x C}.
  { move=>Γ A B m n s tym ihm tyn ihn A0 B0 m0 n0 s0 [e1 e2] h; subst.
    have eq:=h _ tym.
    exfalso. solve_conv. }
  { move=>Γ A B m n s tym ihm tyn ihn A0 B0 m0 n0 s0 [e1 e2] h; subst.
    have/pi1_inj[_[eq _]]:=h _ tym.
    apply: sta_conv_subst... }
  { move=>Γ A B m s eq tym ihm tyB ihB A0 B0 m0 n s0 e h; subst.
    apply: conv_trans.
    apply: ihm...
    exact: eq. }
Qed.

Lemma sta_uniq Γ m A B :
  Γ ⊢ m : A -> Γ ⊢ m : B -> A === B.
Proof with eauto.
  move=>ty. elim: ty B=>{Γ m A}.
  { move=>Γ s B tyB.
    apply: sta_sort_uniq... }
  { move=>Γ x A wf hs B ty.
    apply: sta_var_uniq... }
  { move=>Γ A B s r t tyA ihA tyB ihB B0 ty.
    have[_[_ eq]]:=sta_pi0_inv ty.
    apply: conv_sym... }
  { move=>Γ A B s r t tyA ihA tyB ihB B0 ty.
    have[_[_ eq]]:=sta_pi1_inv ty.
    apply: conv_sym... }
  { move=>Γ A B m s tym ihm B0 ty.
    apply: sta_lam0_uniq... }
  { move=>Γ A B m s tym ihm B0 ty.
    apply: sta_lam1_uniq... }
  { move=>Γ A B m n s tym ihm tyn ihn B0 ty.
    apply: sta_app0_uniq... }
  { move=>Γ A B m n s tym ihm tyn ihn B0 ty.
    apply: sta_app1_uniq... }
  { move=>Γ A B m s eq tym1 ihm tyB ihB B0 tym2.
    apply: conv_trans.
    apply: conv_sym...
    exact: ihm. }
Qed.
