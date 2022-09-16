From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_valid.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem sta_sr Γ m n A :
  sta_wf Γ -> Γ ⊢ m : A -> m ~> n -> Γ ⊢ n : A.
Proof with eauto using sta_type, sta_step, sta_wf.
  move=>wf ty. elim: ty n wf=>{Γ m A}...
  { move=>Γ s n wf st. inv st. }
  { move=>Γ x A hs n wf st. inv st. }
  { move=>Γ A B s r t tyA ihA tyB ihB n wf st. inv st.
    { have tyA':=ihA _ wf H4.
      apply: sta_pi0...
      apply: sta_ctx_conv.
      apply: conv1i...
      exact: tyA.
      exact: tyB. }
    { have wf':sta_wf (A :: Γ) by eauto using sta_wf.
      have tyB':=ihB _ wf' H4.
      apply: sta_pi0... } }
  { move=>Γ A B s r t tyA ihA tyB ihB n wf st. inv st.
    { have tyA':=ihA _ wf H4.
      apply: sta_pi1...
      apply: sta_ctx_conv.
      apply: conv1i...
      exact: tyA.
      exact: tyB. }
    { have wf':sta_wf (A :: Γ) by eauto using sta_wf.
      have tyB':=ihB _ wf' H4.
      apply: sta_pi1... } }
  { move=>Γ A B m s t tyP ihP tym ihm n wf st. inv st.
    { have st:Pi0 A B s t ~> Pi0 A' B s t...
      have[r tyA tyB]:=sta_pi0_inv tyP.
      have tyP':=ihP  _ wf st.
      apply: sta_conv.
      apply: conv1i...
      apply: sta_lam0...
      apply: sta_ctx_conv.
      apply: conv1i...
      exact: tyA.
      exact: tym.
      exact: tyP. }
    { have[r tyA tyB]:=sta_pi0_inv tyP.
      have{}wf: sta_wf (A :: Γ) by eauto using sta_wf.
      have tym':=ihm _ wf H4.
      exact: sta_lam0. } }
  { move=>Γ A B m s t tyP ihP tym ihm n wf st. inv st.
    { have st:Pi1 A B s t ~> Pi1 A' B s t...
      have[r tyA tyB]:=sta_pi1_inv tyP.
      have tyP':=ihP  _ wf st.
      apply: sta_conv.
      apply: conv1i...
      apply: sta_lam1...
      apply: sta_ctx_conv.
      apply: conv1i...
      exact: tyA.
      exact: tym.
      exact: tyP. }
    { have[r tyA tyB]:=sta_pi1_inv tyP.
      have{}wf: sta_wf (A :: Γ) by eauto using sta_wf.
      have tym':=ihm _ wf H4.
      exact: sta_lam1. } }
  { move=>Γ A B m n s t tym ihm tyn ihn n0 wf st. inv st.
    { have tym':=ihm _ wf H2... }
    { have tyn':=ihn _ wf H2.
      have[_/sta_pi0_inv[r tyA tyB]]:=sta_valid wf tym.
      apply: sta_conv.
      apply: sta_conv_beta.
      apply: conv1i...
      apply: sta_app0...
      apply: sta_esubst...
      by autosubst. }
    { have[x tyP]:=sta_valid wf tym.
      have tym0:=sta_lam0_inv tyP tym.
      apply: sta_esubst... }
    { exfalso. apply: sta_lam1_pi0_false... } }
  { move=>Γ A B m n s t tym ihm tyn ihn n0 wf st. inv st.
    { have tym':=ihm _ wf H2... }
    { have tyn':=ihn _ wf H2.
      have[_/sta_pi1_inv[r tyA tyB]]:=sta_valid wf tym.
      apply: sta_conv.
      apply: sta_conv_beta.
      apply: conv1i...
      apply: sta_app1...
      apply: sta_esubst...
      by autosubst. }
    { exfalso. apply: sta_lam0_pi1_false... }
    { have[x tyP]:=sta_valid wf tym.
      have tym0:=sta_lam1_inv tyP tym.
      apply: sta_esubst... } }
Qed.
