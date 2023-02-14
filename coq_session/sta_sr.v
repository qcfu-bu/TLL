From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_valid.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem sta_psr Γ m n A : Γ ⊢ m : A -> m ≈> n -> Γ ⊢ n : A.
Proof with eauto using sta0_type, sta0_wf, sta_step, sta_type.
  move=>/sta_sta0_type ty st. apply: sta0_sta_type.
  elim: ty n st=>{Γ m A}...
  { move=>Γ s wf n st. inv st... }
  { move=>Γ x A wf hs n st. inv st... }
  { move=>Γ A B s r t tyA ihA tyB ihB n st. inv st.
    have tyA':=ihA _ H3.
    have tyB':=ihB _ H4.
    apply: sta0_pi0...
    apply: sta_sta0_type.
    move/sta0_sta_type in tyA'.
    move/sta0_sta_type in tyB'.
    apply: sta_ctx_conv.
    apply: conv1i...
    exact: tyA'.
    exact: tyB'. }
  { move=>Γ A B s r t tyA ihA tyB ihB n st. inv st.
    have tyA':=ihA _ H3.
    have tyB':=ihB _ H4.
    apply: sta0_pi1...
    apply: sta_sta0_type.
    move/sta0_sta_type in tyA'.
    move/sta0_sta_type in tyB'.
    apply: sta_ctx_conv.
    apply: conv1i...
    exact: tyA'.
    exact: tyB'. }
  { move=>Γ A B m s r tyA ihA tym ihm n st. inv st.
    have tyA':=ihA _ H3.
    have tym':=ihm _ H4.
    move/sta0_sta_type in tym'.
    move/sta0_sta_type in tyA'.
    have[t tyB]:=sta_valid tym'.
    apply: sta0_conv.
    apply: conv1i.
    constructor...
    apply: sta0_lam0...
    apply: sta_sta0_type.
    apply: sta_ctx_conv.
    apply: conv1i...
    exact: tyA'.
    exact: tym'.
    apply: sta0_pi0... }
  { move=>Γ A B m s r tyA ihA tym ihm n st. inv st.
    have tyA':=ihA _ H3.
    have tym':=ihm _ H4.
    move/sta0_sta_type in tym'.
    move/sta0_sta_type in tyA'.
    have[t tyB]:=sta_valid tym'.
    apply: sta0_conv.
    apply: conv1i.
    constructor...
    apply: sta0_lam1...
    apply: sta_sta0_type.
    apply: sta_ctx_conv.
    apply: conv1i...
    exact: tyA'.
    exact: tym'.
    apply: sta0_pi1... }
  { move=>Γ A B m n s tym ihm tyn ihn x st. inv st.
    { have tym':=ihm _ H1...
      have tyn':=ihn _ H3.
      move/sta0_sta_type in tyn.
      have[_/sta_pi0_inv[r[tyB _]]]:=sta_valid (sta0_sta_type tym).
      apply: sta0_conv.
      apply: sta_conv_beta.
      apply: conv1i...
      apply: sta0_app0...
      apply: sta_sta0_type.
      apply: sta_esubst...
      by autosubst. }
    { have/ihm tym':Lam0 A0 m0 s0 ≈> Lam0 A0 m' s0 by constructor...
      have tyn':=ihn _ H3.
      have[x tyP]:=sta_valid (sta0_sta_type tym').
      have[t[tyB/sort_inj e]]:=sta_pi0_inv tyP. subst.
      have/sta_lam0_inv tym0:=sta0_sta_type tym'.
      move/sta0_sta_type in tyn.
      move/sta0_sta_type in tyn'.
      have/= tyBn:=sta_subst tyB tyn.
      apply: sta_sta0_type.
      apply: sta_conv.
      apply: sta_conv_beta.
      apply: conv1i...
      apply: sta_esubst...
      apply: tyBn. } }
  { move=>Γ A B m n s tym ihm tyn ihn x st. inv st.
    { have tym':=ihm _ H1...
      have tyn':=ihn _ H3.
      move/sta0_sta_type in tyn.
      have[_/sta_pi1_inv[r[tyB _]]]:=sta_valid (sta0_sta_type tym).
      apply: sta0_conv.
      apply: sta_conv_beta.
      apply: conv1i...
      apply: sta0_app1...
      apply: sta_sta0_type.
      apply: sta_esubst...
      by autosubst. }
    { have/ihm tym':Lam1 A0 m0 s0 ≈> Lam1 A0 m' s0 by constructor...
      have tyn':=ihn _ H3.
      have[x tyP]:=sta_valid (sta0_sta_type tym').
      have[t[tyB/sort_inj e]]:=sta_pi1_inv tyP. subst.
      have/sta_lam1_inv tym0:=sta0_sta_type tym'.
      move/sta0_sta_type in tyn.
      move/sta0_sta_type in tyn'.
      have/= tyBn:=sta_subst tyB tyn.
      apply: sta_sta0_type.
      apply: sta_conv.
      apply: sta_conv_beta.
      apply: conv1i...
      apply: sta_esubst...
      apply: tyBn. } }
  { move=>Γ A B s r t ord tyA ihA tyB ihB n st. inv st.
    have tyA':=ihA _ H3.
    have tyB':=ihB _ H4.
    move/sta0_sta_type in tyA'.
    move/sta0_sta_type in tyB'.
    apply: sta0_sig0...
    apply: sta_sta0_type.
    apply: sta_ctx_conv.
    apply: conv1i...
    apply: tyA'.
    apply: tyB'. }
  { move=>Γ A B s r t ord1 ord2 tyA ihA tyB ihB n st. inv st.
    have tyA':=ihA _ H3.
    have tyB':=ihB _ H4.
    move/sta0_sta_type in tyA'.
    move/sta0_sta_type in tyB'.
    apply: sta0_sig1.
    apply: ord1. apply: ord2.
    eauto.
    apply: sta_sta0_type.
    apply: sta_ctx_conv.
    apply: conv1i...
    apply: tyA'.
    apply: tyB'. }
  { move=>Γ A B m n t tyS ihS tym ihm tyn ihn x st. inv st.
    have/sta0_sta_type tym':=ihm _ H3.
    have tyn':=ihn _ H4.
    have tyS':=sta0_sta_type tyS.
    have[s[r[ord[tyA[tyB _]]]]]:=sta_sig0_inv tyS'.
    apply: sta0_pair0...
    apply: sta0_conv.
    apply: sta_conv_beta.
    apply: conv1...
    apply: tyn'.
    apply: sta_sta0_type.
    apply: sta_esubst...
    by autosubst. }
  { move=>Γ A B m n t tyS ihS tym ihm tyn ihn x st. inv st.
    have/sta0_sta_type tym':=ihm _ H3.
    have tyn':=ihn _ H4.
    have tyS':=sta0_sta_type tyS.
    have[s[r[ord1[ord2[tyA[tyB _]]]]]]:=sta_sig1_inv tyS'.
    apply: sta0_pair1...
    apply: sta0_conv.
    apply: sta_conv_beta.
    apply: conv1...
    apply: tyn'.
    apply: sta_sta0_type.
    apply: sta_esubst...
    by autosubst. }
  { move=>Γ A B C m n s t tyC ihC tym ihm tyn ihn x st. inv st.
    { have/sta0_sta_type tyA':=ihC _ H2.
      have/sta0_sta_type tym':=ihm _ H4.
      have/sta0_sta_type tyn':=ihn _ H5.
      move/sta0_sta_type in tyC.
      move/sta0_sta_type in tym.
      have//=tyCm:=sta_subst tyC tym.
      have wf:=sta_type_wf tyC. inv wf.
      have[s1[r[ord[tyA[tyB/sort_inj e]]]]]:=sta_sig0_inv H3; subst.
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
      apply: conv_trans.
      apply: sta_conv_beta. apply: A'.
      apply: conv1i. apply: H4.
      apply: sta_conv_subst.
      apply: conv1i...
      apply: sta0_letin0...
      apply: sta0_conv.
      apply: sta_conv_subst.
      apply: conv1...
      apply: sta_sta0_type...
      apply: sta_sta0_type...
      apply: sta_sta0_type... }
    { have tym':=ihm _ (sta_pstep_pair0 s0 H2 H4).
      have tyn':=ihn _ H5.
      move/sta0_sta_type in tyC.
      move/sta0_sta_type in tyn'.
      move/sta0_sta_type in tym.
      move/sta0_sta_type in tym'.
      have[e[tym1 tym2]]:=sta_pair0_inv tym'; subst.
      have//=tyC':=sta_subst tyC tym.
      apply: sta_sta0_type.
      apply: sta_conv.
      apply: sta_conv_beta.
      apply: conv1i.
      constructor...
      replace C.[Pair0 m1' m2' t/]
        with C.[Pair0 (Var 1) (Var 0) t .: ren (+2)].[m2',m1'/] by autosubst.
      apply: sta_substitution...
      repeat constructor...
      by asimpl.
      apply: tyC'. }
    { move/sta0_sta_type in tym.
      exfalso. apply: sta_pair1_sig0_false... } }
  { move=>Γ A B C m n s t tyC ihC tym ihm tyn ihn x st. inv st.
    { have/sta0_sta_type tyA':=ihC _ H2.
      have/sta0_sta_type tym':=ihm _ H4.
      have/sta0_sta_type tyn':=ihn _ H5.
      move/sta0_sta_type in tyC.
      move/sta0_sta_type in tym.
      have//=tyCm:=sta_subst tyC tym.
      have wf:=sta_type_wf tyC. inv wf.
      have[s1[r[ord1[ord2[tyA[tyB/sort_inj e]]]]]]:=sta_sig1_inv H3; subst.
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
      apply: conv_trans.
      apply: sta_conv_beta. apply: A'.
      apply: conv1i. apply: H4.
      apply: sta_conv_subst.
      apply: conv1i...
      apply: sta0_letin1...
      apply: sta0_conv.
      apply: sta_conv_subst.
      apply: conv1...
      apply: sta_sta0_type...
      apply: sta_sta0_type...
      apply: sta_sta0_type... }
    { move/sta0_sta_type in tym.
      exfalso. apply: sta_pair0_sig1_false... }
    { have tym':=ihm _ (sta_pstep_pair1 s0 H2 H4).
      have tyn':=ihn _ H5.
      move/sta0_sta_type in tyC.
      move/sta0_sta_type in tyn'.
      move/sta0_sta_type in tym.
      move/sta0_sta_type in tym'.
      have[e[tym1 tym2]]:=sta_pair1_inv tym'; subst.
      have//=tyC':=sta_subst tyC tym.
      apply: sta_sta0_type.
      apply: sta_conv.
      apply: sta_conv_beta.
      apply: conv1i.
      constructor...
      replace C.[Pair1 m1' m2' t/]
        with C.[Pair1 (Var 1) (Var 0) t .: ren (+2)].[m2',m1'/] by autosubst.
      apply: sta_substitution...
      repeat constructor...
      by asimpl.
      apply: tyC'. } }
  { move=>Γ A m s tyA ihA tym ihm x st. inv st...
    { have tyA':=ihA _ H1.
      have tym':=ihm _ H3.
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
    { have tyA':=ihA _ H1.
      have tym':=ihm _ H3.
      have{}tyA:=sta0_sta_type tyA.
      have{}tyA':=sta0_sta_type tyA'.
      have{}tym':=sta0_sta_type tym'.
      have{}tym':(A' :: Γ) ⊢ m' : A'.[ren (+1)].
      { apply: sta_ctx_conv.
        apply: conv1i... apply: tyA'.
        apply: sta_conv.
        apply: sta_conv_subst.
        apply: conv1...
        apply: tym'.
        apply: sta_eweaken...
        simpl... }
      have tyFix:=sta_fix tym'.
      apply: sta_sta0_type.
      apply: sta_conv.
      apply: conv1i...
      have:=sta_subst tym' tyFix.
      autosubst.
      apply: tyA. } }
  { move=>Γ wf n st. inv st... }
  { move=>Γ wf n st. inv st... }
  { move=>Γ wf n st. inv st... }
  { move=>Γ wf n st. inv st... }
  { move=>Γ wf n st. inv st... }
  { move=>Γ A m n1 n2 s tyA ihA tym ihm tyn1 ihn1 tyn2 ihn2 n st. inv st...
    have tyA':=ihA _ H3.
    have tym':=ihm _ H5.
    have tyn1':=ihn1 _ H6.
    have tyn2':=ihn2 _ H7.
    have wf:=sta_type_wf (sta0_sta_type tym).
    have/=tyA'TT:=sta_subst (sta0_sta_type tyA') (sta_tt wf).
    have/=tyA'FF:=sta_subst (sta0_sta_type tyA') (sta_ff wf).
    apply: sta0_conv.
    apply: conv_trans.
    2:{ apply: sta_conv_subst.
        apply: conv1i... }
    apply: sta_conv_beta.
    apply: conv1i...
    apply: sta0_ifte...
    apply: sta0_conv.
    apply: sta_conv_subst.
    apply: conv1...
    apply: tyn1'.
    apply: sta_sta0_type...
    apply: sta0_conv.
    apply: sta_conv_subst.
    apply: conv1...
    apply: tyn2'.
    apply: sta_sta0_type...
    apply: sta_sta0_type.
    apply: sta_esubst...
    2:{ apply: sta0_sta_type... }
    2:{ apply: sta0_sta_type... }
    simpl... }
  { move=>Γ A s tyA ihA n st. inv st... }
  { move=>Γ m A tym ihm n st. inv st... }
  { move=>Γ m n A B s tyB ihB tym ihm tyn ihn n0 st. inv st.
    { have{}ihm:=ihm _ H1.
      have{}ihn:=ihn _ H3.
      apply: sta0_bind... }
    { have{}ihm:=ihm _ (sta_pstep_return H1).
      have{}ihn:=ihn _ H3.
      have[A0[tym'/io_inj eq]]:=sta_return_inv (sta0_sta_type ihm).
      have wf:=sta_type_wf (sta0_sta_type ihn). inv wf.
      have{}tym':=sta_conv (conv_sym eq) tym' H4.
      have{}ihn:=sta0_sta_type ihn.
      have tynm:=sta_subst ihn tym'. asimpl in tynm.
      apply: sta_sta0_type... } }
  { move=>Γ wf n st. inv st... }
  { move=>Γ r wf n st. inv st... }
  { move=>Γ r A B s tyA ihA tyB ihB n st. inv st...
    have tyA':=ihA _ H3.
    have tyB':=ihB _ H4.
    apply: sta0_act0...
    apply: sta_sta0_type.
    apply: sta_ctx_conv.
    apply: conv1i...
    apply: sta0_sta_type...
    apply: sta0_sta_type... }
  { move=>Γ r A B s tyA ihA tyB ihB n st. inv st...
    have tyA':=ihA _ H3.
    have tyB':=ihB _ H4.
    apply: sta0_act1...
    apply: sta_sta0_type.
    apply: sta_ctx_conv.
    apply: conv1i...
    apply: sta0_sta_type...
    apply: sta0_sta_type... }
  { move=>Γ r A tyA ihA n st. inv st... }
  { move=>Γ r x A clA tyA ihA n st. inv st... }
  { move=>Γ A m s tyCh ihCh tym ihm n st. inv st.
    have{}tyCh:=sta0_sta_type tyCh.
    have [tyA _]:=sta_ch_inv tyCh.
    have/sta0_sta_type tyCh':=ihCh _ (sta_pstep_ch true H1).
    have [tyA' _]:=sta_ch_inv tyCh'.
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

Theorem sta_prd Γ m n A :
  Γ ⊢ m : A -> m ≈>* n -> Γ ⊢ n : A.
Proof with eauto.
  move=>ty rd. elim: rd Γ A ty=>{n}...
  move=>n z rd ih st Γ A tym.
  have tyn:=ih _ _ tym.
  apply: sta_psr...
Qed.

Theorem sta_sr Γ m n A : Γ ⊢ m : A -> m ~> n -> Γ ⊢ n : A.
Proof with eauto using sta_step_pstep.
  move=>ty st. apply: sta_psr...
Qed.

Theorem sta_rd Γ m n A : Γ ⊢ m : A -> m ~>* n -> Γ ⊢ n : A.
Proof with eauto using sta_red_pred.
  move=>ty rd. apply: sta_prd...
Qed.
