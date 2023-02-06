From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_valid.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem sta_sr Γ m n A : Γ ⊢ m : A -> m ~> n -> Γ ⊢ n : A.
Proof with eauto using sta0_type, sta0_wf, sta_step, sta_type.
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
      apply: sta0_pi0... }
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
      apply: sta0_pi1... }
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
  { move=>Γ A B s r t ord tyA ihA tyB ihB n st. inv st.
    { have tyA':=ihA _ H3.
      move/sta0_sta_type in tyB.
      move/sta0_sta_type in tyA'.
      apply: sta0_sig0...
      apply: sta_sta0_type.
      apply: sta_ctx_conv.
      apply: conv1i...
      apply: tyA'.
      apply: tyB. }
    { have tyB':=ihB _ H3.
      apply: sta0_sig0... } }
  { move=>Γ A B s r t ord1 ord2 tyA ihA tyB ihB n st. inv st.
    { have tyA':=ihA _ H3.
      move/sta0_sta_type in tyB.
      move/sta0_sta_type in tyA'.
      apply: sta0_sig1.
      apply: ord1. apply: ord2.
      eauto.
      apply: sta_sta0_type.
      apply: sta_ctx_conv.
      apply: conv1i...
      apply: tyA'.
      apply: tyB. }
    { have tyB':=ihB _ H3.
      apply: sta0_sig1.
      apply: ord1. apply: ord2.
      all: eauto. } }
  { move=>Γ A B m n t tyS ihS tym ihm tyn ihn x st. inv st.
    { have/sta0_sta_type tym':=ihm _ H3.
      have tyS':=sta0_sta_type tyS.
      have[s[r[ord[tyA[tyB _]]]]]:=sta_sig0_inv tyS'.
      apply: sta0_pair0...
      apply: sta0_conv.
      apply: sta_conv_beta.
      apply: conv1...
      apply: tyn.
      apply: sta_sta0_type.
      apply: sta_esubst...
      by autosubst. }
    { have tyn':=ihn _ H3.
      apply: sta0_pair0... } }
  { move=>Γ A B m n t tyS ihS tym ihm tyn ihn x st. inv st.
    { have/sta0_sta_type tym':=ihm _ H3.
      have tyS':=sta0_sta_type tyS.
      have[s[r[ord1[ord2[tyA[tyB _]]]]]]:=sta_sig1_inv tyS'.
      apply: sta0_pair1...
      apply: sta0_conv.
      apply: sta_conv_beta.
      apply: conv1...
      apply: tyn.
      apply: sta_sta0_type.
      apply: sta_esubst...
      by autosubst. }
    { have tyn':=ihn _ H3.
      apply: sta0_pair1... } }
  { move=>Γ A B C m n s t tyC ihC tym ihm tyn ihn x st. inv st.
    { have/sta0_sta_type tyA':=ihC _ H3.
      move/sta0_sta_type in tyC.
      move/sta0_sta_type in tym.
      have//=tyCm:=sta_subst tyC tym.
      have wf:=sta_type_wf tyC. inv wf.
      have[s1[r[ord[tyA[tyB/sort_inj e]]]]]:=sta_sig0_inv H2; subst.
      have wkA':((Sig0 A B t).[ren (+2)] :: B :: A :: Γ) ⊢ A'.[ren (upren (+2))] : Sort s.
      { replace (Sort s) with (Sort s).[ren (upren (+2))] by eauto.
        apply: sta_rename...
        apply: sta_agree_ren_cons...
        replace (+2) with (id >>> (+1) >>> (+1)) by autosubst.
        apply: sta_agree_ren_wk...
        apply: sta_agree_ren_wk...
        apply: sta_agree_ren_refl... }
      have tyP:(B :: A :: Γ) ⊢ Pair0 (Var 1) (Var 0) t : (Sig0 A B t).[ren (+2)].
      { apply: sta_pair0.
        { replace (Sig0 A.[ren (+2)] B.[up (ren (+2))] t)
          with (Sig0 A B t).[ren (+1)].[ren (+1)] by autosubst.
          apply: sta_eweaken...
          instantiate (1 := Sort t)=>//.
          apply: sta_eweaken... eauto. }
        { replace A.[ren (+2)] with A.[ren (+1)].[ren (+1)] by autosubst.
          repeat constructor.
          econstructor... }
        { asimpl.
          repeat constructor.
          econstructor... } }
      have{}xA':=sta_subst wkA' tyP. asimpl in xA'.
      apply:sta0_conv.
      apply: sta_conv_subst.
      apply: conv1i...
      apply: sta0_letin0...
      apply: sta0_conv.
      apply: sta_conv_subst.
      apply: conv1...
      apply: tyn.
      apply: sta_sta0_type...
      eauto. }
    { have/sta0_sta_type tym':=ihm _ H3.
      move/sta0_sta_type in tyC.
      move/sta0_sta_type in tym.
      have//=tyCm:=sta_subst tyC tym.
      apply: sta0_conv.
      apply: sta_conv_beta.
      apply: conv1i...
      apply: sta0_letin0...
      eauto... }
    { have tyn':=ihn _ H3. apply: sta0_letin0... }
    { move/sta0_sta_type in tyn.
      move/sta0_sta_type in tym.
      have[e[tym1 tym2]]:=sta_pair0_inv tym; subst.
      apply: sta_sta0_type.
      replace C.[Pair0 m1 m2 t/]
        with C.[Pair0 (Var 1) (Var 0) t .: ren (+2)].[m2,m1/] by autosubst.
      apply: sta_substitution...
      repeat constructor...
      by asimpl. }
    { move/sta0_sta_type in tym.
      exfalso. apply: sta_pair1_sig0_false... } }
  { move=>Γ A B C m n s t tyC ihC tym ihm tyn ihn x st. inv st.
    { have/sta0_sta_type tyA':=ihC _ H3.
      move/sta0_sta_type in tyC.
      move/sta0_sta_type in tym.
      have//=tyCm:=sta_subst tyC tym.
      have wf:=sta_type_wf tyC. inv wf.
      have[s1[r[ord1[ord2[tyA[tyB/sort_inj e]]]]]]:=sta_sig1_inv H2; subst.
      have wkA':((Sig1 A B t).[ren (+2)] :: B :: A :: Γ) ⊢ A'.[ren (upren (+2))] : Sort s.
      { replace (Sort s) with (Sort s).[ren (upren (+2))] by eauto.
        apply: sta_rename...
        apply: sta_agree_ren_cons...
        replace (+2) with (id >>> (+1) >>> (+1)) by autosubst.
        apply: sta_agree_ren_wk...
        apply: sta_agree_ren_wk...
        apply: sta_agree_ren_refl... }
      have tyP:(B :: A :: Γ) ⊢ Pair1 (Var 1) (Var 0) t : (Sig1 A B t).[ren (+2)].
      { apply: sta_pair1.
        { replace (Sig1 A.[ren (+2)] B.[up (ren (+2))] t)
          with (Sig1 A B t).[ren (+1)].[ren (+1)] by autosubst.
          apply: sta_eweaken...
          instantiate (1 := Sort t)=>//.
          apply: sta_eweaken... eauto. }
        { replace A.[ren (+2)] with A.[ren (+1)].[ren (+1)] by autosubst.
          repeat constructor.
          econstructor... }
        { asimpl.
          repeat constructor.
          econstructor... } }
      have{}xA':=sta_subst wkA' tyP. asimpl in xA'.
      apply:sta0_conv.
      apply: sta_conv_subst.
      apply: conv1i...
      apply: sta0_letin1...
      apply: sta0_conv.
      apply: sta_conv_subst.
      apply: conv1...
      apply: tyn.
      apply: sta_sta0_type...
      eauto. }
    { have/sta0_sta_type tym':=ihm _ H3.
      move/sta0_sta_type in tyC.
      move/sta0_sta_type in tym.
      have//=tyCm:=sta_subst tyC tym.
      apply: sta0_conv.
      apply: sta_conv_beta.
      apply: conv1i...
      apply: sta0_letin1...
      eauto... }
    { have tyn':=ihn _ H3. apply: sta0_letin1... }
    { move/sta0_sta_type in tym.
      exfalso. apply: sta_pair0_sig1_false... }
    { move/sta0_sta_type in tyn.
      move/sta0_sta_type in tym.
      have[e[tym1 tym2]]:=sta_pair1_inv tym; subst.
      apply: sta_sta0_type.
      replace C.[Pair1 m1 m2 t/]
        with C.[Pair1 (Var 1) (Var 0) t .: ren (+2)].[m2,m1/] by autosubst.
      apply: sta_substitution...
      repeat constructor...
      by asimpl. } }
  { move=>Γ A m s tyA ihA tym ihm x st. inv st...
    { have tyA':=ihA _ H2.
      apply: sta0_conv.
      apply: conv1i...
      apply: sta0_fix...
      apply: sta0_conv.
      apply: sta_conv_subst.
      apply: conv1...
      apply: sta_sta0_type.
      apply: sta_ctx_conv.
      apply: conv1i...
      apply: sta0_sta_type...
      apply: sta0_sta_type...
      apply: sta_sta0_type.
      apply: sta_weaken (sta0_sta_type tyA') (sta0_sta_type tyA').
      eauto. }
    { have{}tyA:=sta0_sta_type tyA.
      have{}tym:=sta0_sta_type tym.
      have tyFix:=sta_fix tym.
      apply: sta_sta0_type.
      have:=sta_subst tym tyFix.
      by autosubst. } }
  { move=>Γ wf n st. inv st. }
  { move=>Γ wf n st. inv st. }
  { move=>Γ wf n st. inv st. }
  { move=>Γ wf n st. inv st. }
  { move=>Γ wf n st. inv st. }
  { move=>Γ A m n1 n2 s tyA ihA tym ihm tyn1 ihn1 tyn2 ihn2 n st. inv st...
    { have tyA':=ihA _ H4.
      have wf:=sta_type_wf (sta0_sta_type tym).
      have/=tyA'TT:=sta_subst (sta0_sta_type tyA') (sta_tt wf).
      have/=tyA'FF:=sta_subst (sta0_sta_type tyA') (sta_ff wf).
      apply: sta0_conv.
      apply: sta_conv_subst.
      apply: conv1i...
      apply: sta0_ifte...
      apply: sta0_conv.
      apply: sta_conv_subst.
      apply: conv1...
      all: eauto...
      apply: sta0_conv.
      apply: sta_conv_subst.
      apply: conv1...
      all: eauto...
      apply: sta_sta0_type.
      have:=sta_subst (sta0_sta_type tyA) (sta0_sta_type tym).
      asimpl... }
    { apply: sta0_conv.
      apply: sta_conv_beta.
      apply: conv1i...
      apply: sta0_ifte...
      have:=sta_subst (sta0_sta_type tyA) (sta0_sta_type tym).
      asimpl... } }
  { move=>Γ A s tyA ihA n st. inv st... }
  { move=>Γ m A tym ihm n st. inv st... }
  { move=>Γ m n A B s tyB ihB tym ihm tyn ihn n0 st. inv st.
    { have{}ihm:=ihm _ H2. apply: sta0_bind... }
    { have{}ihn:=ihn _ H2. apply: sta0_bind... }
    { have wf:=sta_type_wf (sta0_sta_type tyn). inv wf.
      have[A0[tym0/io_inj eq]]:=sta_return_inv (sta0_sta_type tym).
      have{}tym0:=sta_conv (conv_sym eq) tym0 H2.
      have{}tyn:=sta0_sta_type tyn.
      have nm0:=sta_subst tyn tym0. asimpl in nm0.
      apply: sta_sta0_type... } }
  { move=>Γ wf n st. inv st. }
  { move=>Γ r wf n st. inv st. }
  { move=>Γ r A B s tyA ihA tyB ihB n st. inv st...
    have tyA':=ihA _ H3.
    apply: sta0_act0...
    apply: sta_sta0_type.
    apply: sta_ctx_conv.
    apply: conv1i...
    apply: sta0_sta_type...
    apply: sta0_sta_type... }
  { move=>Γ r A B s tyA ihA tyB ihB n st. inv st...
    have tyA':=ihA _ H3.
    apply: sta0_act1...
    apply: sta_sta0_type.
    apply: sta_ctx_conv.
    apply: conv1i...
    apply: sta0_sta_type...
    apply: sta0_sta_type... }
  { move=>Γ r A tyA ihA n st. inv st... }
  { move=>Γ r x A clA tyA ihA n st. inv st. }
  { move=>Γ A m s tyCh ihCh tym ihm n st. inv st...
    have{}tyCh:=sta0_sta_type tyCh.
    have tyA:=sta_ch_inv tyCh.
    have/sta0_sta_type tyCh':=ihCh _ (sta_step_ch true H2).
    have tyA':=sta_ch_inv tyCh'.
    apply: sta0_conv.
    apply: sta_conv_io.
    apply: sta_conv_ch.
    apply: conv1i...
    apply: sta0_fork...
    apply: sta_sta0_type.
    apply: sta_ctx_conv.
    apply: sta_conv_ch.
    apply: conv1i...
    apply: tyCh'.
    apply: sta0_sta_type...
    apply: sta_sta0_type... }
  { move=>Γ r1 r2 A B m xor tym ihm n st. inv st... }
  { move=>Γ r1 r2 A B m xor tym ihm n st. inv st... }
  { move=>Γ r1 r2 A B m xor tym ihm n st. inv st... }
  { move=>Γ r1 r2 A B m xor tym ihm n st. inv st... }
  { move=>Γ r1 r2 m xor tym ihm n st. inv st... }
  { move=>Γ r1 r2 m xor tym ihm n st. inv st... }
Qed.

Corollary sta_rd Γ m n A :
  Γ ⊢ m : A -> m ~>* n -> Γ ⊢ n : A.
Proof with eauto.
  move=>ty rd. elim: rd Γ A ty=>{n}...
  move=>n z rd ih st Γ A tym.
  have tyn:=ih _ _ tym.
  apply: sta_sr...
Qed.
