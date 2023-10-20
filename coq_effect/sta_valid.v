From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_inv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem sta_valid Γ m A : Γ ⊢ m : A -> Γ ⊢ A : Ty.
Proof with eauto using sta_type.
  move=>ty. elim: ty=>{Γ m A}...
  { move=>Γ x A wf hs.
    apply: sta_wf_ok... }
  { move=>Γ A B m n tym ihm tyn ihn.
    have[tyB _]:=sta_forall_inv ihm.
    apply: sta_esubst...
    by autosubst. }
  { move=>Γ A B m n tym ihm tyn ihn.
    have[tyB _]:=sta_arrow_inv ihm.
    apply: sta_esubst...
    by autosubst.
    by autosubst. }
Qed.

Lemma sta_lam_invX Γ A1 A2 B C m :
  Γ ⊢ Lam A1 m : C ->
  C === Forall A2 B ->
  (A2 :: Γ) ⊢ B : Ty ->
  (A2 :: Γ) ⊢ m : B.
Proof with eauto.
  move e:(Lam A1 m)=>n tyL.
  elim: tyL A1 A2 B m e=>//{Γ C n}.
  { move=>Γ A B m tyA ihA tym _ A1 A2 B0 m0[e1 e2]/forall_inj[e3 e4]tyB0; subst.
    have wf:=sta_type_wf tym. inv wf.
    have wf:=sta_type_wf tyB0. inv wf.
    apply: sta_ctx_conv.
    apply: conv_sym...
    exact: H4.
    apply: sta_conv...
    apply: sta_ctx_conv... }
  { move=>Γ A B m eq1 tym ihm tyB ihB A1 A2 B0 m0 e eq2 tyB0; subst.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma sta_fun_invX Γ A1 A2 B C m :
  Γ ⊢ Fun A1 m : C ->
  C === Arrow A2 B ->
  (A2 :: Γ) ⊢ B.[ren (+1)] : Ty ->
  (A2 :: Γ) ⊢ m : B.[ren (+1)].
Proof with eauto.
  move e:(Fun A1 m)=>n tyL.
  elim: tyL A1 A2 B m e=>//{Γ C n}.
  { move=>Γ A B m tyA ihA tym _ A1 A2 B0 m0[e1 e2]/arrow_inj[e3 e4]tyB0; subst.
    have wf:=sta_type_wf tym. inv wf.
    have wf:=sta_type_wf tyB0. inv wf.
    apply: sta_ctx_conv.
    apply: conv_sym...
    exact: H4.
    apply: sta_conv.
    apply: sta_conv_subst.
    apply: e4.
    apply: tym.
    apply: sta_ctx_conv... }
  { move=>Γ A B m eq1 tym ihm tyB ihB A1 A2 B0 m0 e eq2 tyB0; subst.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma sta_lam_inv Γ m A1 A2 B :
  Γ ⊢ Lam A2 m : Forall A1 B -> (A1 :: Γ) ⊢ m : B.
Proof with eauto.
  move=>ty.
  have/sta_forall_inv[tyB _]:=sta_valid ty.
  apply: sta_lam_invX...
Qed.

Lemma sta_fun_inv Γ m A1 A2 B :
  Γ ⊢ Fun A2 m : Arrow A1 B -> (A1 :: Γ) ⊢ m : B.[ren (+1)].
Proof with eauto.
  move=>ty.
  have/sta_arrow_inv[tyB _]:=sta_valid ty.
  apply: sta_fun_invX...
Qed.
