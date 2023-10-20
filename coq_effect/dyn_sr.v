From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_sr dyn_step.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem dyn_sr Γ m n A : Γ ⊢ m : A -> m ~>> n -> Γ ⊢ n : A.
Proof with eauto using sta_type, sta_wf, sta_step, dyn_step, sta_sr.
  move=>ty. elim: ty n=>{Γ m A}.
  { move=>Γ wf n st. inv st. }
  { move=>Γ x A wf hs n st. inv st. }
  { move=>Γ A B tyA ihA tyB ihB n st. inv st. }
  { move=>Γ A B tyA ihA tyB ihB n st. inv st. }
  { move=>Γ A B m tyA ihA tym ihm n st. inv st. }
  { move=>Γ A B m tyA ihA tym ihm n st. inv st. }
  { move=>Γ A B m n tym ihm tyn ihn x st. inv st.
    { have tym':=ihm _ H2... }
    { have tyn':=sta_sr tyn H2.
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
  { move=>Γ A B m eq tym ihm tyB ihB n st.
    apply: sta_conv... }
Qed.

