From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_prog dyn_sr era_inv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma era_dyn_val Γ Δ m m' A :
  dyn_val m' -> Γ ; Δ ⊢ m ~ m' : A -> dyn_val m.
Proof with eauto using dyn_val.
  move=>vl. inv vl.
  { move=>/era_var_form[x' e]; subst... }
  { move=>/era_lam0_form[A'[m' e]]; subst... }
  { move=>/era_lam1_form[A'[m' e]]; subst... }
Qed.

Theorem era_sr m m' n' A :
  nil ; nil ⊢ m ~ m' : A -> m' ~>> n' ->
  exists2 n, m ~>> n & nil ; nil ⊢ n ~ n' : A.
Proof with eauto using dyn_step, era_type, merge.
  move e1:(nil)=>Γ.
  move e2:(nil)=>Δ er. elim: er e1 e2 n'=>{Γ Δ m m' A}.
  { move=>Γ Δ x s A wf shs dhs e1 e2 n' st. inv st. }
  { move=>Γ Δ A B m m' s k erm ihm e1 e2 n' st. inv st. }
  { move=>Γ Δ A B m m' s t k erm ihm e1 e2 n' st. inv st. }
  { move=>Γ Δ A B m m' n s erm ihm tyn e1 e2 n' st. inv st.
    { have[x st tyx]:=ihm erefl erefl _ H2. exists (App x n)... }
    { inv H2. }
    { have[A'[m' e]]:=era_lam0_form erm.
      subst. exists (m'.[n/])...
      apply: era_subst0...
      apply: era_lam0_inv... }
    { have[A'[m' e]]:=era_lam1_form erm. subst.
      have/dyn_sta_type ty:=era_dyn_type erm.
      exfalso. apply: sta_lam1_pi0_false... } }
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' s mrg erm ihm ern ihn e1 e2 x st.
    subst. inv mrg. inv st.
    { have[x st tyx]:=ihm erefl erefl _ H2. exists (App x n)... }
    { have[x st tyx]:=ihn erefl erefl _ H2. exists (App m x)...
      have tym:=era_dyn_type erm.
      have/dyn_sta_type tyn:=era_dyn_type ern.
      have[_/sta_pi1_inv[r[tyB _]]]:=dyn_valid tym.
      apply: era_conv.
      apply: sta_conv_beta.
      apply: conv_sym.
      apply: star_conv.
      apply: dyn_sta_red...
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
  { move=>Γ Δ A B H H' P m n s tyB erH ihH tyP e1 e2 x st. inv st.
    have[P0[rdP vlP]]:=sta_vn tyP.
    have tyP0:=sta_rd tyP rdP.
    have[n0 e]:=sta_id_canonical tyP0 (convR _ _) vlP. subst.
    have tyr:=sta_rd tyP rdP.
    have[r tyI]:=sta_valid tyP.
    have[tym[tyn/sort_inj e]]:=sta_id_inv tyI. subst.
    have[tym0[eq1 eq2]]:=sta_refl_inv tyr.
    have sc:sconv (Refl m .: m .: ids) (P .: n .: ids).
    { move=>[|[|]]//=.
      apply: conv_trans. apply: sta_conv_refl. apply: conv_sym...
      apply: conv_sym. apply: star_conv...
      apply: conv_trans. apply: conv_sym... eauto. }
    have wkB:nil ⊢ B.[P,n/] : Sort s.
    { replace (Sort s) with (Sort s).[P,n/] by eauto.
      apply: sta_substitution...
      repeat constructor...
      all: asimpl... }
    exists H...
    apply: era_conv.
    apply: sta_conv_compat sc.
    all: eauto. }
  { move=>Γ Δ A B m m' s eq tym ihm tyB e1 e2 n' st. subst.
    have[n st' tyn]:=ihm erefl erefl _ st.
    exists n... }
Qed.

Corollary era_rd m m' n' A :
  nil ; nil ⊢ m ~ m' : A -> m' ~>>* n' ->
  exists2 n, m ~>>* n & nil ; nil ⊢ n ~ n' : A.
Proof with eauto.
  move=>ty rd. elim: rd m A ty=>{n'}...
  move=>n n' rd ih st m A tym.
  have[x rdx tyx]:=ih _ _ tym.
  have[y sty tyy]:=era_sr tyx st.
  exists y...
  apply: star_trans...
  apply: star1...
Qed.
