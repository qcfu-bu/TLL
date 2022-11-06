From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS era_inv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma era_dyn_val Γ Δ m m' A :
  Γ ; Δ ⊢ m ~ m' : A -> dyn_val m' -> dyn_val m.
Proof with eauto using dyn_val.
  move=>ty. elim: ty=>{Γ Δ m m' A}...
  { move=>Γ Δ A B m m' n s tym ihm tyn vl. inv vl. }
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' s mrg tym ihm tyn ihn vl. inv vl. }
  { move=>Γ Δ A B m m' n t tyS tym ihm tyn vl. inv vl... }
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' t mrg tyS tym ihm tyn ihn vl. inv vl... }
  { move=>Γ Δ1 Δ2 Δ A B C m m' n n' s r t mrg tyC tym ihm tyn ihn vl. inv vl. }
  { move=>Γ Δ1 Δ2 Δ A B C m m' n n' s r1 r2 t mrg tyC tym ihm tyn ihn vl. inv vl. }
  { move=>Γ Δ A B m m' t tym ihm vl. inv vl. }
  { move=>Γ Δ A B m m' t tym ihm vl. inv vl. }
Qed.

Theorem era_sr Γ Δ m m' n' A :
  Γ ; Δ ⊢ m ~ m' : A -> m' ~>> n' ->
  exists2 n, m ~>> n & Γ ; Δ ⊢ n ~ n' : A.
Proof with eauto using dyn_step, era_type, dyn_val.
  move=>er. elim: er n'=>{Γ Δ m m' A}.
  { move=>Γ Δ x s A wf shs dhs n' st. inv st. }
  { move=>Γ Δ A B m m' s k erm ihm n' st. inv st. }
  { move=>Γ Δ A B m m' s t k erm ihm n' st. inv st. }
  { move=>Γ Δ A B m m' n s erm ihm tyn n' st. inv st.
    { have[x st tyx]:=ihm _ H2. exists (App x n)... }
    { inv H2. }
    { have[A'[m' e]]:=era_lam0_form erm.
      subst. exists (m'.[n/])...
      apply: era_subst0...
      apply: era_lam0_inv... }
    { have[A'[m' e]]:=era_lam1_form erm. subst.
      have/dyn_sta_type ty:=era_dyn_type erm.
      exfalso. apply: sta_lam1_pi0_false... } }
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' s mrg erm ihm ern ihn x st. inv st.
    { have[x st tyx]:=ihm _ H2. exists (App x n)... }
    { have[x st tyx]:=ihn _ H2. exists (App m x)...
      have tym:=era_dyn_type erm.
      have/dyn_sta_type tyn:=era_dyn_type ern.
      have[_/sta_pi1_inv[r[tyB _]]]:=dyn_valid tym.
      apply: era_conv.
      apply: sta_conv_beta.
      apply: conv1i.
      apply: dyn_sta_step...
      apply: era_app1...
      have:=sta_subst tyB tyn.
      asimpl... }
    { have[A'[m' e]]:=era_lam0_form erm. subst.
      have/dyn_sta_type ty:=era_dyn_type erm.
      exfalso. apply: sta_lam0_pi1_false... }
    { have[A'[m' e]]:=era_lam1_form erm.
      subst. exists (m'.[n/])...
      apply: dyn_step_beta1.
      apply: era_dyn_val...
      have{erm}[t erm]:=era_lam1_inv erm.
      have wf:=dyn_type_wf (era_dyn_type erm). inv wf.
      apply: era_subst1...
      apply: dyn_val_key.
      apply: era_dyn_type...
      exact: H5.
      apply: era_dyn_val... } }
  { move=>Γ Δ A B m m' n t tyS erm ihm tyn x st. inv st.
    have[s[r[ord[tyA[tyB _]]]]]:=sta_sig0_inv tyS.
    have[x st erx]:=ihm _ H3. exists (Pair0 x n t)...
    apply: era_pair0...
    apply: sta_conv.
    apply: sta_conv_beta.
    apply: conv1...
    apply: tyn.
    apply: sta_esubst...
    by autosubst. }
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' t mrg tyS tym ihm tyn ihn x st.
    have[s[r[ord1[ord2[tyA[tyB _]]]]]]:=sta_sig1_inv tyS. inv st.
    { have[x st erx]:=ihm _ H3. exists (Pair1 x n t)...
      apply: era_pair1...
      apply: era_conv.
      apply: sta_conv_beta.
      apply: conv1...
      apply: tyn.
      apply: sta_esubst...
      by autosubst. }
    { have[x st erx]:=ihn _ H3. exists (Pair1 m x t)... } }
  { move=>Γ Δ1 Δ2 Δ A B C m m' n n' s r t mrg tyC erm ihm ern ihn x st. inv st.
    { have[x st erx]:=ihm _ H3. exists (LetIn C x n)...
      apply: era_conv.
      apply: sta_conv_beta.
      apply: conv1i...
      apply: era_letin0...
      apply: sta_esubst...
      by autosubst. }
    { have[m3[m4 e]]:=era_pair0_form erm. subst.
      have wf:=dyn_type_wf (era_dyn_type ern). inv wf. inv H2.
      have[e1[e2[erm3 tym4]]]:=era_pair0_inv erm. subst.
      have vl:dyn_val (Pair0 m3 m4 t) by (apply: era_dyn_val; eauto).
      exists (n.[m4,m3/])...
      replace C.[Pair0 m3 m4 t/]
        with C.[Pair0 (Var 1) (Var 0) t .: ren (+2)].[m4,m3/] by autosubst.
      apply: era_substitution...
      apply: era_agree_subst_wk0...
      apply: era_agree_subst_wk1.
      apply: (dyn_val_key (era_dyn_type erm3) H7).
      inv vl...
      apply: merge_sym...
      eauto.
      by autosubst. }
    { have[m3[m4 e]]:=era_pair1_form erm. subst.
      have/dyn_sta_type ty:=era_dyn_type erm.
      exfalso. apply: sta_pair1_sig0_false... } }
  { move=>Γ Δ1 Δ2 Δ A B C m m' n n' s r1 r2 t mrg tyC erm ihm ern ihn x st. inv st.
    { have[x st erx]:=ihm _ H3. exists (LetIn C x n)...
      apply: era_conv.
      apply: sta_conv_beta.
      apply: conv1i...
      apply: era_letin1...
      apply: sta_esubst...
      by autosubst. }
    { have[m3[m4 e]]:=era_pair0_form erm. subst.
      have/dyn_sta_type ty:=era_dyn_type erm.
      exfalso. apply: sta_pair0_sig1_false... }
    { have[m3[m4 e]]:=era_pair1_form erm. subst.
      have wf:=dyn_type_wf (era_dyn_type ern). inv wf. inv H2.
      have[Δ1'[Δ2'[mrg'[e[erm3 erm4]]]]]:=era_pair1_inv erm. subst.
      have tym3:=era_dyn_type erm3.
      have tym4:=era_dyn_type erm4.
      have vl:dyn_val (Pair1 m3 m4 t) by (apply: era_dyn_val; eauto). inv vl.
      have k1:=dyn_val_key tym3 H7 H1.
      have k2:=dyn_val_key tym4 (sta_subst H5 (dyn_sta_type tym3)) H6.
      have[Δa[mrg1 mrg2]]:=merge_splitL mrg mrg'.
      exists (n.[m4,m3/])...
      replace C.[Pair1 m3 m4 t/]
        with C.[Pair1 (Var 1) (Var 0) t .: ren (+2)].[m4,m3/] by autosubst.
      apply: era_substitution...
      apply: era_agree_subst_wk1...
      apply: era_agree_subst_wk1...
      apply: merge_sym...
      by autosubst. } }
  { move=>Γ Δ A B m m' n n' t k erm ihm tyn ihn x st. inv st. }
  { move=>Γ Δ A B m m' t tym ihm x st. inv st.
    { have[x st erx]:=ihm _ H0. exists (Fst x)... }
    { have[m1[m2 e]]:=era_apair_form tym. subst.
      have[e[erm1 erm2]]:=era_apair_inv tym.
      subst. exists m1... } }
  { move=>Γ Δ A B m m' t tym ihm x st. inv st.
    { have[x st erx]:=ihm _ H0. exists (Snd x)... }
    { have[m1[m2 e]]:=era_apair_form tym. subst.
      have[e[erm1 erm2]]:=era_apair_inv tym.
      subst. exists m2... } }
  { move=>Γ Δ A B m m' s eq tym ihm tyB n' st.
    have[n st' tyn]:=ihm _ st.
    exists n... }
Qed.

Corollary era_rd Γ Δ m m' n' A :
  Γ ; Δ ⊢ m ~ m' : A -> m' ~>>* n' ->
  exists2 n, m ~>>* n & Γ ; Δ ⊢ n ~ n' : A.
Proof with eauto.
  move=>ty rd. elim: rd Γ Δ m A ty=>{n'}...
  move=>n n' rd ih st Γ Δ m A tym.
  have[x rdx tyx]:=ih _ _ _ _ tym.
  have[y sty tyy]:=era_sr tyx st.
  exists y...
  apply: star_trans...
  apply: star1...
Qed.
