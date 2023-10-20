From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_valid.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem sta_sr Γ m n A : Γ ⊢ m : A -> m ~> n -> Γ ⊢ n : A.
Proof with eauto using sta_type, sta_wf, sta_step.
  move=>ty. elim: ty n=>{Γ m A}...
  { move=>Γ wf n st. inv st. }
  { move=>Γ x A wf hs n st. inv st. }
  { move=>Γ A B tyA ihA tyB ihB n st. inv st.
    { have tyA':=ihA _ H2.
      apply: sta_forall...
      apply: sta_ctx_conv.
      apply: conv1i...
      exact: tyA'.
      exact: tyB. }
    { have tyB':=ihB _ H2.
      apply: sta_forall... } }
  { move=>Γ A B tyA ihA tyB ihB n st. inv st.
    { have tyA':=ihA _ H2.
      apply: sta_arrow...
      apply: sta_ctx_conv.
      apply: conv1i...
      exact: tyA'.
      exact: tyB. }
    { have tyB':=ihB _ (sta_step_subst _ H2).
      apply: sta_arrow... } }
  { move=>Γ A B m tyA ihA tym ihm n st. inv st.
    { have tyA':=ihA _ H2.
      have tyB:=sta_valid tym.
      apply: sta_conv.
      apply: conv1i...
      apply: sta_lam...
      apply: sta_ctx_conv.
      apply: conv1i...
      exact: tyA'.
      exact: tym.
      apply: sta_forall... }
    { have tym':=ihm _ H2.
      apply: sta_lam... } }
  { move=>Γ A B m tyA ihA tym ihm n st. inv st.
    { have tyA':=ihA _ H2.
      have tyB:=sta_valid tym.
      apply: sta_conv.
      apply: conv1i...
      apply: sta_fun...
      apply: sta_ctx_conv.
      apply: conv1i...
      exact: tyA'.
      exact: tym.
      apply: sta_arrow... }
    { have tym':=ihm _ H2.
      apply: sta_fun... } }
  { move=>Γ A B m n tym ihm tyn ihn x st. inv st.
    { have tym':=ihm _ H2... }
    { have tyn':=ihn _ H2.
      have/sta_forall_inv[tyB _]:=sta_valid tym.
      apply: sta_conv.
      apply: sta_conv_beta.
      apply: conv1i...
      apply: sta_inst...
      apply: sta_esubst...
      by autosubst. }
    { have tyP:=sta_valid tym.
      have/sta_lam_inv tym0:= tym.
      apply: sta_esubst... } }
  { move=>Γ A B m n tym ihm tyn ihn x st. inv st.
    { have tym':=ihm _ H2... }
    { have tyn':=ihn _ H2.
      apply: sta_call... }
    { have tyP:=sta_valid tym.
      have/sta_fun_inv tym0:= tym.
      apply: sta_esubst...
      by autosubst. } }
  { move=>Γ wf n st. inv st. }
  { move=>Γ wf n st. inv st. }
  { move=>Γ wf n st. inv st. }
  { move=>Γ n wf n0 st. inv st. }
  { move=>Γ m tym ihm n st. inv st... }
Qed.

Corollary sta_rd Γ m n A :
  Γ ⊢ m : A -> m ~>* n -> Γ ⊢ n : A.
Proof with eauto.
  move=>ty rd. elim: rd Γ A ty=>{n}...
  move=>n z rd ih st Γ A tym.
  have tyn:=ih _ _ tym.
  apply: sta_sr...
Qed.
