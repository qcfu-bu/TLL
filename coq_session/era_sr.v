From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS dyn_sr era_inv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma era_dyn_val Θ Γ Δ m m' A :
  Θ ; Γ ; Δ ⊢ m ~ m' : A -> dyn_val m -> dyn_val m'.
Proof with eauto using dyn_val.
  move=>ty. elim: ty=>{Θ Γ Δ m m' A}...
  { move=>Θ Γ Δ A B m m' n s erm ihm tyn vl. inv vl.
    have[m0 e]:=era_send0_form erm. subst.
    have vl:=ihm (dyn_val_send0 H0). inv vl.
    constructor... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m m' n n' s mrg1 mrg2 erm ihm tyn ihn vl. inv vl.
    have[m0 e]:=era_send1_form erm. subst.
    have vl:=ihm (dyn_val_send1 H1). inv vl.
    constructor... }
  { move=>Θ Γ Δ A B m n n' t tyS tym ern ihn vl. inv vl... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m m' n n' t mrg1 mrg2 tyS erm ihm ern ihn vl. inv vl... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m m' n n' s r t mrg1 mrg2 tyS erm _ ern _ vl. inv vl. }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m m' n n' s r1 r2 t mrg1 mrg2 tyS erm _ ern _ vl. inv vl. }
  { move=>Θ Γ Δ A m m' k1 k2 erm ihm vl. inv vl. }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m m' n1 n1' n2 n2' s mrg1 mrg2
           tyA erm _ ern1 _ ern2 _ vl. inv vl. }
  { move=>Θ Γ Δ m m' A erm ihm vl. inv vl... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m m' n n' A B s t mrg1 mrg2 tyB erm ihm ern ihn vl. inv vl... }
  { move=>Θ Γ Δ r1 r2 A B m m' xor erm ihm vl. inv vl... }
  { move=>Θ Γ Δ r1 r2 A B m m' xor erm ihm vl. inv vl... }
  { move=>Θ Γ Δ r1 r2 A B m m' xor erm ihm vl. inv vl... }
  { move=>Θ Γ Δ r1 r2 A B m m' xor erm ihm vl. inv vl... }
  { move=>Θ Γ Δ m m' erm ihm vl. inv vl... }
  { move=>Θ Γ Δ m m' erm ihm vl. inv vl... }
Qed.

Lemma era_val_stability Θ Γ Δ m m' A s :
  Θ ; Γ ; Δ ⊢ m ~ m' : A -> Γ ⊢ A : Sort s -> dyn_val m -> Θ ▷ s /\ Δ ▷ s.
Proof with eauto. move=>*. apply: dyn_val_stability... Qed.

Lemma era_pure_empty Θ Γ Δ m m' A :
  Θ ; Γ ; Δ ⊢ m ~ m' : A -> Θ ▷ U -> dyn_empty Θ.
Proof with eauto. move=>*. apply: dyn_pure_empty... Qed.

Theorem era_sr Θ m m' n A :
  Θ ; nil ; nil ⊢ m ~ m' : A ->
  m ~>> n ->
  exists2 n',
    Θ ; nil ; nil ⊢ n ~ n' : A &
    m' ~>> n'.
Proof with eauto using era_type, dyn_step, dyn_wf, dyn_val, merge.
  move e1:(nil)=>Γ.
  move e2:(nil)=>Δ er. elim: er e1 e2 n=>{Θ Γ Δ m m' A}...
  { move=>Θ Γ Δ x s A emp wf shs dhs e1 e2 n st. inv st. }
  { move=>Θ Γ Δ A B m m' s k1 k2 tym ihm e1 e2 n st. inv st. }
  { move=>Θ Γ Δ A B m m' s t k1 k2 tym ihm e1 e2 n st. inv st. }
  { move=>Θ Γ Δ A B m m' n s tym ihm tyn e1 e2 n0 st. inv st.
    { have[n' st tym']:=ihm erefl erefl _ H2.
      exists (App0 n' Box)... }
    { have[x tyP]:=era_valid tym.
      have[m1 e]:=era_lam0_form tym. subst.
      have tym0:=era_lam0_inv tym.
      exists m1.[Box/]...
      apply: era_subst0... } }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m m' n n' s mrg1 mrg2 tym ihm tyn ihn e1 e2 n0 st.
    subst. inv mrg2. inv st.
    { have[m0 tym0 st]:=ihm erefl erefl _ H2.
      exists (App1 m0 n')... }
    { have[n0 tyn0 st]:=ihn erefl erefl _ H2.
      exists (App1 m' n0)...
      have[x tyP]:=era_valid tym.
      have[r[tyB _]]:=sta_pi1_inv tyP.
      apply: era_conv.
      apply: sta_conv_beta.
      apply: conv_sym.
      apply: star_conv.
      apply: sta_red_pred.
      apply: dyn_sta_step...
      apply: era_app1...
      have:=sta_subst tyB (era_sta_type tyn).
      asimpl... }
    { have[x tyP]:=era_valid tym.
      have[r[tyB _]]:=sta_pi1_inv tyP.
      have[m0' tym0']:=era_lam1_form tym. subst.
      have[t tym0]:=era_lam1_inv tym.
      have wf:=era_type_wf tym0. inv wf.
      have[k1 k2]:=era_val_stability tyn H5 H2.
      have vl:=era_dyn_val tyn H2.
      exists (m0'.[n'/])...
      apply: era_subst1.
      apply: k1. apply: mrg1. apply: k2. apply: merge_nil.
      all: eauto. } }
  { move=>Θ Γ Δ A B m n n' t tyS tym tyn ihn e1 e2 n0 st. inv st.
    have[s[r[ord[tyA[tyB _]]]]]:=sta_sig0_inv tyS.
    have[n'1 ern' st]:=ihn erefl erefl _ H3.
    exists (Pair0 Box n'1 t)... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m m' n n' t mrg1 mrg2 tyS tym ihm tyn ihn e1 e2 n0 st.
    subst. inv mrg2. inv st.
    { have[s[r[ord1[ord2[tyA[tyB _]]]]]]:=sta_sig1_inv tyS.
      have[m'1 erm0 st]:=ihm erefl erefl _ H3.
      exists (Pair1 m'1 n' t)...
      apply: era_pair1...
      apply: era_conv.
      apply: sta_conv_beta.
      apply: star_conv.
      apply: sta_red_pred.
      apply: (dyn_sta_step (era_sta_type tym))...
      apply: tyn.
      apply: sta_esubst...
      by autosubst. }
    { have[n'1 ern st]:=ihn erefl erefl _ H3.
      exists (Pair1 m' n'1 t)... } }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m m' n n' s r t mrg1 mrg2 tyC tym ihm tyn ihn e1 e2 n0 st.
    subst. inv mrg2. inv st.
    { have[m'1 erm st]:=ihm erefl erefl _ H3.
      exists (LetIn Box m'1 n')...
      apply: era_conv.
      apply: sta_conv_beta.
      apply: conv_sym.
      apply: star_conv.
      apply: sta_red_pred.
      apply: (dyn_sta_step (era_sta_type tym))...
      apply: era_letin0...
      apply: sta_esubst...
      by autosubst. }
    { inv H3.
      have[m0 e]:=era_pair0_form tym. subst.
      have[e[_[tym1 tym2]]]:=era_pair0_inv tym. subst.
      have wf:=era_type_wf tyn. inv wf. inv H3.
      have[k1 k2]:=era_val_stability tym2 (sta_subst H5 tym1) H0.
      have[Θ0[emp mrg0]]:=era_type_empty tym2.
      have vl:=era_dyn_val tym2 H0.
      replace C.[Pair0 m1 m2 t/]
        with C.[Pair0 (Var 1) (Var 0) t .: ren (+2)].[m2,m1/] by autosubst.
      exists (n'.[m0,Box/])...
      apply: era_substitution...
      apply: (era_agree_subst_wk1 k1 k2)...
      apply: era_agree_subst_wk0...
      by autosubst. }
    { exfalso. apply: sta_pair1_sig0_false... } }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m m' n n' s r1 r2 t mrg1 mrg2 tyC tym ihm tyn ihn e1 e2 n0 st.
    subst. inv mrg2. inv st.
    { have[m'1 erm st]:=ihm erefl erefl _ H3.
      exists (LetIn Box m'1 n')...
      apply: era_conv.
      apply: sta_conv_beta.
      apply: conv_sym.
      apply: star_conv.
      apply: sta_red_pred.
      apply: (dyn_sta_step (era_sta_type tym))...
      apply: era_letin1...
      apply: sta_esubst...
      by autosubst. }
    { exfalso. apply: sta_pair0_sig1_false... }
    { inv H3.
      have[n1[n2 e]]:=era_pair1_form tym. subst.
      have[Θ1'[Θ2'[Δ1'[Δ2'[e[mrg1'[mrg2'[tym1 tym2]]]]]]]]:=era_pair1_inv tym.
      have wf:=era_type_wf tyn. inv wf. inv H3. inv mrg2'.
      have[Θ0[emp mrg0]]:=era_type_empty tym1.
      have [k1 k2]:=era_val_stability tym1 H8 H1.
      have [k3 k4]:=era_val_stability tym2 (sta_subst H6 (era_sta_type tym1)) H4.
      have vl1:=era_dyn_val tym1 H1.
      have vl2:=era_dyn_val tym2 H4.
      replace C.[Pair1 m1 m2 t/]
        with C.[Pair1 (Var 1) (Var 0) t .: ren (+2)].[m2,m1/] by autosubst.
      exists (n'.[n2,n1/])...
      apply: era_substitution...
      apply: (era_agree_subst_wk1 k3 k4)...
      apply: (era_agree_subst_wk1 k1 k2)...
      by autosubst. } }
  { move=>Θ Γ Δ A m m' k1 k2 tym ihm e1 e2 n st. subst. inv st.
    have tyF:=era_fix k1 k2 tym.
    have mrg:=pure_merge_self k1.
    exists (m'.[Fix Box m'/])...
    have:=era_subst1 k1 mrg k2 merge_nil tym tyF.
    by autosubst. }
  { move=>Θ Γ Δ emp wf k e1 e2 n st. inv st. }
  { move=>Θ Γ Δ emp wf k e1 e2 n st. inv st. }
  { move=>Θ Γ Δ emp wf k e1 e2 n st. inv st. }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m m' n1 n1' n2 n2' s mrg1 mrg2 tyA tym ihm tyn1 ihn1 tyn2 ihn2 e1 e2 n st.
    subst. inv mrg2. inv st.
    { have[m'1 tym' st]:=ihm erefl erefl _ H4.
      exists (Ifte Box m'1 n1' n2')...
      apply: era_conv.
      apply: sta_conv_beta.
      apply: conv_sym.
      apply: star_conv.
      apply: sta_red_pred.
      apply: dyn_sta_step...
      apply: era_ifte...
      apply: sta_subst tyA (era_sta_type tym). }
    { have e:=era_tt_form tym. subst.
      have emp:=era_tt_inv tym.
      have e:=merge_emptyL mrg1 emp. subst... }
    { have e:=era_ff_form tym. subst.
      have emp:=era_ff_inv tym.
      have e:=merge_emptyL mrg1 emp. subst... } }
  { move=>Θ Γ Δ m m' A tym ihm e1 e2 n st. inv st.
    have[m'1 erm st]:=ihm erefl erefl _ H0.
    exists (Return m'1)... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m m' n n' A B s t mrg1 mrg2 tyB tym ihm tyn ihn e1 e2 n0 st.
    subst. inv mrg2. inv st...
    { have[m'1 erm st]:=ihm erefl erefl _ H2.
      exists (Bind m'1 n')... }
    { have[v' e]:=era_return_form tym. subst.
      have tyv:=era_return_inv tym.
      have vl:=era_dyn_val tyv H2.
      have wf:=era_type_wf tyn. inv wf.
      have[k1 _]:=era_val_stability tyv H5 H2.
      exists n'.[v'/]...
      have:=era_subst1 k1 (merge_sym mrg1) (key_nil s) merge_nil tyn tyv.
      by asimpl. } }
  { move=>Θ Γ Δ r x A js wf k tyA e1 e2 n st. inv st. }
  { move=>Θ Γ Δ m m' A tym ihm e1 e2 n st. inv st. }
  { move=>Θ Γ Δ r1 r2 A B m m' xor tym ihm e1 e2 n st. inv st.
    have[m'1 erm st]:=ihm erefl erefl _ H0.
    exists (Recv0 m'1)... }
  { move=>Θ Γ Δ r1 r2 A B m m' xor tym ihm e1 e2 n st. inv st.
    have[m'1 erm st]:=ihm erefl erefl _ H0.
    exists (Recv1 m'1)... }
  { move=>Θ Γ Δ r1 r2 A B m m' xor tym ihm e1 e2 n st. inv st.
    have[m'1 erm st]:=ihm erefl erefl _ H0.
    exists (Send0 m'1)... }
  { move=>Θ Γ Δ r1 r2 A B m m' xor tym ihm e1 e2 n st. inv st.
    have[m'1 erm st]:=ihm erefl erefl _ H0.
    exists (Send1 m'1)... }
  { move=>Θ Γ Δ m m' tym ihm e1 e2 n st. inv st.
    have[m'1 erm st]:=ihm erefl erefl _ H0.
    exists (Wait m'1)... }
  { move=>Θ Γ Δ m m' tym ihm e1 e2 n st. inv st.
    have[m'1 erm st]:=ihm erefl erefl _ H0.
    exists (Close m'1)... }
  { move=>Θ Γ Δ A B m m' s eq erm ihm tyB e1 e2 n st. subst.
    have[n' ern st']:=ihm erefl erefl _ st. exists n'... }
Qed.

Corollary era_rd Θ m m' n A :
  Θ ; nil ; nil ⊢ m ~ m' : A ->
  m ~>>* n ->
  exists2 n',
    Θ ; nil ; nil ⊢ n ~ n' : A &
    m' ~>>* n'.
Proof with eauto.
  move=>ty rd. elim: rd Θ A ty=>{n}...
  move=>n z rd ih st Γ A tym.
  have[n' ern rd']:=ih _ _ tym.
  have[z' erz st']:=era_sr ern st.
  exists z'... exact: (starSE rd' st').
Qed.
