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
  { move=>Γ Δ A B m m' n s erm ih tyn vl. inv vl. }
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' s mrg erm ihm ern ihn vl. inv vl.
    have->:=era_rand_form erm.
    have->:=era_it_form ern.
    constructor... }
  { move=>Γ Δ m m' A erm ihm vl. inv vl... }
  { move=>Γ Δ1 Δ2 Δ m m' n n' A B s t mrg tyB erm ihm ern ihn vl. inv vl... }
Qed.

Lemma era_dyn_mval Γ Δ m m' A :
  Γ ; Δ ⊢ m ~ m' : A -> dyn_mval m' -> dyn_mval m.
Proof with eauto using dyn_mval, dyn_mval_val.
  move=>ty. elim: ty=>{Γ Δ m m' A}...
  { move=>Γ Δ A B m m' n s erm ih tyn vl. inv vl. }
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' s mrg erm ihm ern ihn vl. inv vl. }
  { move=>Γ Δ m m' A erm ihm vl. inv vl.
    have vl:=era_dyn_val erm H0... }
  { move=>Γ Δ1 Δ2 Δ m m' n n' A B s t mrg tyB erm ihm ern ihn vl. inv vl... }
Qed.

Theorem era_sr Γ Δ m m' n' A :
  Γ ; Δ ⊢ m ~ m' : A -> m' ~>> n' ->
  exists2 n, m ~>> n & Γ ; Δ ⊢ n ~ n' : A.
Proof with eauto using dyn_step, era_type.
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
      apply: dyn_beta1.
      apply: era_dyn_val...
      have{erm}[t erm]:=era_lam1_inv erm.
      have wf:=dyn_type_wf (era_dyn_type erm). inv wf.
      apply: era_subst1...
      apply: dyn_val_key.
      apply: era_dyn_type...
      exact: H5.
      apply: era_dyn_val... } }
  { move=>Γ Δ k wf n' st. inv st. }
  { move=>Γ Δ n k wf n' st. inv st. }
  { move=>Γ Δ k wf n' st. inv st. }
  { move=>Γ Δ m m' A erm ihm n' st. inv st.
    have[m0 st0 tym0]:=ihm _ H0.
    exists (Return m0)... }
  { move=>Γ Δ1 Δ2 Δ m m' n n' A B s t mrg tyB erm ihm ern ihn n'0 st. inv st.
    have[m0 st0 tym0]:=ihm _ H2.
    exists (LetIn m0 n)... }
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

Theorem era_msr Γ Δ m m' n' A R T :
  Γ ; Δ ⊢ m ~ m' : A -> R ; m' ~>> T ; n' ->
  exists2 n, R ; m ~>> T ; n & Γ ; Δ ⊢ n ~ n' : A.
Proof with eauto using
  era_type, sta_step, dyn_step, dyn_mstep, dyn_wf, era_sr.
  move=>ty. elim: ty n' R T=>{Γ Δ m m' A}.
  { move=>Γ Δ x s A wf shs dhs n' R T st. inv st. inv H0. }
  { move=>Γ Δ A B m m' s k erm ihm n' R T st. inv st. inv H0. }
  { move=>Γ Δ A B m m' s t k erm ihm n' R T st. inv st. inv H0. }
  { move=>Γ Δ A B m m' n s erm ihm tyn n' R T st. inv st.
    have[x st ty]:=era_sr (era_app0 erm tyn) H0. exists x... }
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' s mrg erm ihm ern ihn n'0 R T st. inv st.
    { have[x st ty]:=era_sr (era_app1 mrg erm ern) H0. exists x... }
    { have wf1:=dyn_type_wf (era_dyn_type erm).
      have wf2:=dyn_type_wf (era_dyn_type ern).
      have e:=era_rand_form erm. subst.
      have e:=era_it_form ern. subst.
      have[t tyP]:=dyn_valid (era_dyn_type erm).
      have[r[tyB/sort_inj e]]:=sta_pi1_inv tyP. subst.
      have tyI:=dyn_sta_type (era_dyn_type ern).
      have/=tyBI:=sta_subst tyB tyI.
      have tyIO:=sta_io (sta_nat (dyn_sta_wf wf1)).
      have[/pi1_inj[eq1[eq2 e]]k1]:=dyn_rand_inv (era_dyn_type erm). subst.
      have[_ k2]:=dyn_it_inv (era_dyn_type ern).
      pose proof (sta_conv_subst (It .: ids) eq2) as H. asimpl in H.
      exists (Return (Num R))...
      apply: era_conv.
      apply: conv_sym...
      apply: era_return.
      apply: era_num...
      apply: key_merge...
      apply: dyn_wf_merge...
      apply: tyBI. } }
  { move=>Γ Δ k wf n' R T st. inv st. inv H0. }
  { move=>Γ Δ n k wf n' R T st. inv st. inv H0. }
  { move=>Γ Δ k wf n' R T st. inv st. inv H0. }
  { move=>Γ Δ m m' A erm ihm n' R T st. inv st.
    have[x st er]:=era_sr (era_return erm) H0. exists x... }
  { move=>Γ Δ1 Δ2 Δ m m' n n' A B s t mrg tyB erm ihm ern ihn n'0 R T st. inv st.
    { have[x st er]:=era_sr (era_letin mrg tyB erm ern) H0. exists x... }
    { have[m0 st er]:=ihm _ _ _ H0. exists (LetIn m0 n)... }
    { have wf:=dyn_type_wf (era_dyn_type ern). inv wf.
      have[n0 e]:=era_return_form erm. subst.
      have[A0[erv/io_inj eq]]:=era_return_inv erm.
      have{}erv:=era_conv (conv_sym eq) erv H5.
      have erv0:=era_dyn_val erv H0.
      have k:=dyn_val_key (era_dyn_type erv) H5 erv0.
      exists n.[n0/].
      apply: dyn_mstep_letret...
      have:=era_subst1 k (merge_sym mrg) ern erv.
      autosubst. } }
  { move=>Γ Δ A B m m' s eq erm ihm tyB n' R T st'.
    have[n st er]:=ihm _ _ _ st'. exists n... }
Qed.
