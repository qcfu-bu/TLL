From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS era_inv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma era_dyn_val Γ Δ m m' A :
  dyn_val m' -> Γ ; Δ ⊢ m ~ m' : A -> dyn_val m.
Proof with eauto using dyn_val.
  move=>vl. inv vl.
  { move=>/era_lam0_form[A'[m' e]]; subst... }
  { move=>/era_lam1_form[A'[m' e]]; subst... }
Qed.

Theorem era_sr Γ Δ m m' n' A :
  Γ ; Δ ⊢ m ~ m' : A -> m' ~>> n' ->
  exists2 n, m ~>> n & Γ ; Δ ⊢ n ~ n' : A.
Proof with eauto using dyn_step, era_type.
  move=>er. elim: er n'=>{Γ Δ m m' A}.
  { move=>Γ Δ x A wf shs dhs n' st. inv st. }
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
