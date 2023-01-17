From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_valid.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem sta_sr Γ m n A : Γ ⊢ m : A -> m ~> n -> Γ ⊢ n : A.
Proof with eauto using sta0_type, sta0_wf, sta_step.
  move=>/sta_sta0_type ty st. apply: sta0_sta_type.
  elim: ty n st=>{Γ m A}...
  { move=>Γ s wf n st. inv st. }
  { move=>Γ x A wf hs n st. inv st. }
  { move=>Γ A B s r t tyA ihA tyB ihB n st. inv st.
    { have tyA':=ihA _ H3.
      apply: sta0_pi0...
      apply: sta_sta0_type.
      move/sta0_sta_type in tyB.
      move/sta0_sta_type in tyA'.
      apply: sta_ctx_conv.
      apply: conv1i...
      exact: tyA'.
      exact: tyB. }
    { have tyB':=ihB _ H3.
      apply: sta0_pi0... } }
  { move=>Γ A B s r t tyA ihA tyB ihB n st. inv st.
    { have tyA':=ihA _ H3.
      apply: sta0_pi1...
      apply: sta_sta0_type.
      move/sta0_sta_type in tyB.
      move/sta0_sta_type in tyA'.
      apply: sta_ctx_conv.
      apply: conv1i...
      exact: tyA'.
      exact: tyB. }
    { have tyB':=ihB _ H3.
      apply: sta0_pi1... } }
  { move=>Γ A B m s r tyA ihA tym ihm n st. inv st.
    { have tyA':=ihA _ H3.
      move/sta0_sta_type in tym.
      move/sta0_sta_type in tyA'.
      have[t tyB]:=sta_valid tym.
      apply: sta0_conv.
      apply: conv1i...
      apply: sta0_lam0...
      apply: sta_sta0_type.
      apply: sta_ctx_conv.
      apply: conv1i...
      exact: tyA'.
      exact: tym.
      apply: sta0_pi0...
      apply: sta_sta0_type... }
    { have tym':=ihm _ H3.
      apply: sta0_lam0... } }
  { move=>Γ A B m s r tyA ihA tym ihm n st. inv st.
    { have tyA':=ihA _ H3.
      move/sta0_sta_type in tym.
      move/sta0_sta_type in tyA'.
      have[t tyB]:=sta_valid tym.
      apply: sta0_conv.
      apply: conv1i...
      apply: sta0_lam1...
      apply: sta_sta0_type.
      apply: sta_ctx_conv.
      apply: conv1i...
      exact: tyA'.
      exact: tym.
      apply: sta0_pi1...
      apply: sta_sta0_type... }
    { have tym':=ihm _ H3.
      apply: sta0_lam1... } }
  { move=>Γ A B m n s tym ihm tyn ihn x st. inv st.
    { have tym':=ihm _ H2... }
    { have tyn':=ihn _ H2.
      move/sta0_sta_type in tyn.
      have[_/sta_pi0_inv[r[tyB _]]]:=sta_valid (sta0_sta_type tym).
      apply: sta0_conv.
      apply: sta_conv_beta.
      apply: conv1i...
      apply: sta0_app0...
      apply: sta_sta0_type.
      apply: sta_esubst...
      by autosubst. }
    { have[x tyP]:=sta_valid (sta0_sta_type tym).
      have/sta_lam0_inv tym0:=sta0_sta_type tym.
      move/sta0_sta_type in tyn.
      apply: sta_sta0_type.
      apply: sta_esubst... }
    { exfalso. apply: sta_lam1_pi0_false.
      apply: sta0_sta_type... eauto. } }
  { move=>Γ A B m n s tym ihm tyn ihn x st. inv st.
    { have tym':=ihm _ H2... }
    { have tyn':=ihn _ H2.
      move/sta0_sta_type in tyn.
      have[_/sta_pi1_inv[r[tyB _]]]:=sta_valid (sta0_sta_type tym).
      apply: sta0_conv.
      apply: sta_conv_beta.
      apply: conv1i...
      apply: sta0_app1...
      apply: sta_sta0_type.
      apply: sta_esubst...
      by autosubst. }
    { exfalso. apply: sta_lam0_pi1_false.
      apply: sta0_sta_type... eauto. } 
    { have[x tyP]:=sta_valid (sta0_sta_type tym).
      have/sta_lam1_inv tym0:=sta0_sta_type tym.
      move/sta0_sta_type in tyn.
      apply: sta_sta0_type.
      apply: sta_esubst... } }
  { move=>Γ wf n st. inv st. }
  { move=>Γ wf n st. inv st. }
  { move=>Γ wf n st. inv st. }
  { move=>Γ i wf n st. inv st. }
  { move=>Γ wf n st. inv st. }
  { move=>Γ A s tyA iha n st. inv st... }
  { move=>Γ m A tym ihm n st. inv st... }
  { move=>Γ m n A B s tyB ihB tym ihm tyn ihn n0 st. inv st.
    { have{}ihm:=ihm _ H2. apply: sta0_letin... }
    { have{}ihn:=ihn _ H2. apply: sta0_letin... }
    { have wf:=sta_type_wf (sta0_sta_type tyn). inv wf.
      have[A0[tym0/io_inj eq]]:=sta_return_inv (sta0_sta_type tym).
      have{}tym0:=sta_conv (conv_sym eq) tym0 H2.
      have{}tyn:=sta0_sta_type tyn.
      have nm0:=sta_subst tyn tym0. asimpl in nm0.
      apply: sta_sta0_type... } }
Qed.

Corollary sta_rd Γ m n A :
  Γ ⊢ m : A -> m ~>* n -> Γ ⊢ n : A.
Proof with eauto.
  move=>ty rd. elim: rd Γ A ty=>{n}...
  move=>n z rd ih st Γ A tym.
  have tyn:=ih _ _ tym.
  apply: sta_sr...
Qed.
