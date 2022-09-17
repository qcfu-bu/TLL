From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS era_inv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma era_dyn_val Γ Δ m m' A :
  dyn_val m' -> Γ ; Δ ⊨ m ~ m' : A -> dyn_val m.
Proof with eauto using dyn_val.
  move=>vl. inv vl.
  { move=>/era_lam0_form[A'[m' e]]; subst... }
  { move=>/era_lam1_form[A'[m' e]]; subst... }
Qed.

Theorem era_sr Γ Δ m m' n' A :
  dyn_wf Γ Δ -> Γ ; Δ ⊨ m ~ m' : A -> m' ~>> n' ->
  exists2 n, m ~>> n & Γ ; Δ ⊨ n ~ n' : A.
Proof with eauto using dyn_step, era_type.
  move=>wf er. elim: er wf n'=>{Γ Δ m m' A}.
  { move=>Γ Δ x A shs dhs wf n' st. inv st. }
  { move=>Γ Δ A B m m' s t k tyP er ih wf n' st. inv st. }
  { move=>Γ Δ A B m m' s t k tyP er ih wf n' st. inv st. }
  { move=>Γ Δ A B m m' n s t er ih tyn wf n' st. inv st.
    { have[x st erx]:=ih wf _ H2. exists (App x n)... }
    { inv H2. }
    { have[A'[m' e]]:=era_lam0_form er.
      subst. exists (m'.[n/])...
      apply: era_subst0...
      have tyL:=era_dyn_type er.
      have[r tyP]:=dyn_valid wf tyL.
      have[ty _]//:=era_lam0_inv wf tyP er. }
    { have[A'[m' e]]:=era_lam1_form er. subst.
      have /dyn_sta_type ty:=era_dyn_type er.
      exfalso. apply: sta_lam1_pi0_false... } }
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' s t mrg erm ihm ern ihn wf x st. inv st.
    { have[wf1 wf2]:=dyn_wf_merge mrg wf.
      have[x st erx]:=ihm wf1 _ H2. exists (App x n)... }
    { have[wf1 wf2]:=dyn_wf_merge mrg wf.
      have[x st erx]:=ihn wf2 _ H2. exists (App m x)...
      have tym:=era_dyn_type erm.
      have/dyn_sta_type tyn:=era_dyn_type ern.
      have[_/sta_pi1_inv[r[_[tyB _]]]]:=dyn_valid wf1 tym.
      apply: era_conv.
      apply: sta_conv_beta.
      apply: conv1i.
      apply: dyn_sta_step...
      apply: era_app1...
      have:=sta_subst tyB tyn.
      asimpl... }
    { have[A'[m' e]]:=era_lam0_form erm. subst.
      have /dyn_sta_type ty:=era_dyn_type erm.
      exfalso. apply: sta_lam0_pi1_false... }
    { have[wf1 wf2]:=dyn_wf_merge mrg wf.
      have[A'[m' e]]:=era_lam1_form erm.
      subst. exists (m'.[n/])...
      apply: dyn_beta1.
      apply: era_dyn_val...
      have tym:=era_dyn_type erm.
      have[r tyP]:=dyn_valid wf1 tym.
      have[_[tyA _]]:=sta_pi1_inv tyP.
      have{erm}[erm _]:=era_lam1_inv wf1 tyP erm.
      apply: era_subst1...
      apply: dyn_val_key.
      exact: wf2.
      apply: era_dyn_type...
      exact: tyA.
      apply: era_dyn_val... } }
  { move=>Γ Δ A B m m' s eq tym ihm tyB wf n' st.
    have[n st' tyn]:=ihm wf _ st.
    exists n... }
Qed.

Corollary era_rd Γ Δ m m' n' A :
  dyn_wf Γ Δ -> Γ ; Δ ⊨ m ~ m' : A -> m' ~>>* n' ->
  exists2 n, m ~>>* n & Γ ; Δ ⊨ n ~ n' : A.
Proof with eauto.
  move=>wf ty rd. elim: rd Γ Δ m A wf ty=>{n'}...
  move=>n n' rd ih st Γ Δ m A wf tym.
  have[x rdx tyx]:=ih _ _ _ _ wf tym.
  have[y sty tyy]:=era_sr wf tyx st.
  exists y...
  apply: star_trans...
  apply: star1...
Qed.
