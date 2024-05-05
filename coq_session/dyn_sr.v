From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS dyn_inv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma dyn_sta_step Θ m n A :
  Θ ; nil ; nil ⊢ m : A -> m ~>> n -> m ~>* n.
Proof with eauto using sta_step, star1 with sta_red_congr.
  move e1:(nil)=>Γ.
  move e2:(nil)=>Δ ty. elim: ty e1 e2 n=>{Θ Γ Δ m A}.
  all: try solve[intros; subst;
                 try match goal with
                   | [ H : _ ∘ _ => [::] |- _ ] => inv H
                   end;
                 try match goal with
                   | [ H : _ ~>> _ |- _ ] => inv H
                   end;
                 eauto using sta_step, star1 with sta_red_congr].
  { intros. subst. eauto. }
Qed.

Lemma dyn_has_type Γ Δ x s A :
  dyn_has Δ x s A -> dyn_wf Γ Δ -> Γ ⊢ A : Sort s.
Proof with eauto.
  move=>hs. elim: hs Γ=>{Δ x s A}.
  { move=>Δ A s k Γ wf. inv wf.
    apply: sta_eweaken...
    by asimpl. }
  { move=>Δ A B x s hs ih Γ wf. inv wf.
    have tyA:=ih _ H2. 
    apply: sta_eweaken...
    by asimpl. }
  { move=>Δ A x s hs ih Γ wf. inv wf.
    have tyA:=ih _ H0. 
    apply: sta_eweaken...
    by asimpl. }
Qed.

Lemma dyn_has_key Δ x s A : dyn_has Δ x s A -> Δ ▷ s.
Proof with eauto using key, key_impure.
  elim=>{Δ x s A}.
  { move=>Δ A [|] k... }
  { move=>Δ A B x [|] hs k... }
  { move=>Δ A x [|] hs k... }
Qed.

Lemma dyn_val_stability Θ Γ Δ m A s :
  Θ ; Γ ; Δ ⊢ m : A -> Γ ⊢ A : Sort s -> dyn_val m -> Θ ▷ s /\ Δ ▷ s.
Proof with eauto using key_impure, key_empty, key_merge.
  destruct s...
  move=>ty. elim: ty=>{Θ Γ Δ m A}...
  { move=>Θ Γ Δ x s A emp wf shs dhs tyA vl.
    have tyAs:=dyn_has_type dhs wf.
    have e:=sta_unicity tyA tyAs. subst.
    split... apply: dyn_has_key... }
  { move=>Θ Γ Δ A B m s k1 k2 tym ihm tyP vl.
    have[_[_/sort_inj e]]:=sta_pi0_inv tyP. subst... }
  { move=>Θ Γ Δ A B m s t k1 k2 tym ihm tyP vl.
    have[_[_/sort_inj e]]:=sta_pi1_inv tyP. subst... }
  { move=>Θ Γ Δ A B m n s tym ihm tyn tyB vl. inv vl.
    have[r1[r2[A0[B0[xor[/pi0_inj[eqA[eqB e] tyv]]]]]]]:=dyn_send0_inv tym. subst.
    have[s tyCh]:=dyn_valid tyv.
    have[tyAct/sort_inj e]:=sta_ch_inv tyCh. subst.
    have tyB0:=sta_act0_inv tyAct.
    have[s tyA]:=sta_valid tyn.
    have{}tyB0:=sta_ctx_conv eqA tyA tyB0.
    have/={}tyIO:=sta_io (sta_ch r1 (sta_subst tyB0 tyn)).
    have/church_rosser[x rd1 rd2]:B.[n/] ≃ (IO (Ch r1 B0)).[n/].
    apply: sta_conv_subst...
    have tyx1:=sta_prd tyB rd1.
    have tyx2:=sta_prd tyIO rd2.
    have//:=sta_unicity tyx1 tyx2. }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n s mrg1 mrg2 tym ihm tyn ihn tyB vl. inv vl.
    have[r1[r2[A0[B0[xor[/pi1_inj[eqA[eqB e] tyv]]]]]]]:=dyn_send1_inv tym. subst.
    have[s tyCh]:=dyn_valid tyv.
    have[tyAct/sort_inj e]:=sta_ch_inv tyCh. subst.
    have tyB0:=sta_act1_inv tyAct.
    have[s tyA]:=dyn_valid tyn.
    have{}tyB0:=sta_ctx_conv eqA tyA tyB0.
    have/={}tyIO:=sta_io (sta_ch r1 (sta_subst tyB0 (dyn_sta_type tyn))).
    have/church_rosser[x rd1 rd2]:B.[n/] ≃ (IO (Ch r1 B0)).[n/].
    apply: sta_conv_subst...
    have tyx1:=sta_prd tyB rd1.
    have tyx2:=sta_prd tyIO rd2.
    have//:=sta_unicity tyx1 tyx2. }
  { move=>Θ Γ Δ A B m n t tyS1 tym tyn ihn tyS2 vl.
    have[s[r[ord[tyA[tyB/sort_inj e]]]]]:=sta_sig0_inv tyS2. subst.
    inv ord. inv vl.
    apply: ihn...
    apply: sta_esubst...
    by autosubst. }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n t mrg1 mrg2 tyS1 tym ihm tyn ihn tyS2 vl.
    have[s[r[ord1[ord2[tyA[tyB/sort_inj e]]]]]]:=sta_sig1_inv tyS2. subst.
    inv ord1. inv ord2. inv vl.
    have[k1 k2]:=ihm tyA H1.
    have[k3 k4]:=ihn (sta_subst tyB (dyn_sta_type tym)) H3.
    split... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r t mrg1 mrg2 tyC1 tym ihm tyn ihn tyC2 vl. inv vl. }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r1 r2 t mrg1 mrg2 tyC1 tym ihm tyn ihn tyC2 vl. inv vl. }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m n1 n2 s mrg1 mrg2 tyA tym ihm tyn1 ihn1 tyn2 ihn2 ty vl. inv vl. }
  { move=>Θ Γ Δ m A tym ihm ty vl.
    have[_[_/sort_inj e]]//:=sta_io_inv ty. }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m n A B s t mrg1 mrg2 tyB tym ihm tyn ihn ty vl.
    have[_[_/sort_inj e]]//:=sta_io_inv ty. }
  { move=>Θ Γ Δ r x A js wf k tyA ty vl.
    have[_/sort_inj e]//:=sta_ch_inv ty. }
  { move=>Θ Γ Δ m A tym ihm ty vl.
    have[_[_/sort_inj e]]//:=sta_io_inv ty. }
  { move=>Θ Γ Δ r1 r2 A B m xor tym ihm ty vl.
    have[_[_/sort_inj e]]//:=sta_io_inv ty. }
  { move=>Θ Γ Δ r1 r2 A B m xor tym ihm ty vl.
    have[_[_/sort_inj e]]//:=sta_io_inv ty. }
  { move=>Θ Γ Δ r1 r2 A B m xor tym ihm ty vl.
    have[_[_/sort_inj e]]//:=sta_pi0_inv ty. }
  { move=>Θ Γ Δ r1 r2 A B m xor tym ihm ty vl.
    have[_[_/sort_inj e]]//:=sta_pi1_inv ty. }
  { move=>Θ Γ Δ m tym ihm ty vl.
    have[_[_/sort_inj e]]//:=sta_io_inv ty. }
  { move=>Θ Γ Δ m tym ihm ty vl.
    have[_[_/sort_inj e]]//:=sta_io_inv ty. }
  { move=>Θ Γ Δ A B m s eq tym ihm tyB1 tyB2 vl.
    have[r tyA]:=dyn_valid tym.
    have[C rd1 rd2]:=church_rosser eq.
    apply: ihm...
    have tyCr:=sta_prd tyA rd1.
    have tyCU:=sta_prd tyB2 rd2.
    have<-:=sta_unicity tyCr tyCU... }
Qed.

Lemma dyn_pure_empty Θ Γ Δ m A :
  Θ ; Γ ; Δ ⊢ m : A -> Θ ▷ U -> dyn_empty Θ.
Proof with eauto using dyn_empty, merge_empty.
  elim=>{Θ Γ Δ m A}...
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n s mrg1 mrg2 tym ihm tyn ihn k.
    have[k1 k2]:=pure_split mrg1 k... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n s mrg1 mrg2 tyS tym ihm tyn ihn k.
    have[k1 k2]:=pure_split mrg1 k... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r t mrg1 mrg2 tyC tym ihm tyn ihn k.
    have[k1 k2]:=pure_split mrg1 k... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r1 r2 t mrg1 mrg2 tyC tym ihm tyn ihn k.
    have[k1 k2]:=pure_split mrg1 k... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m n1 n2 s mrg1 mrg2 tyA tym ihm tyn1 ihn1 tyn2 ihn2 k.
    have[k1 k2]:=pure_split mrg1 k... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m n A B s t mrg1 mrg2 tyB tym ihm tyn ihn k.
    have[k1 k2]:=pure_split mrg1 k... }
  { move=>Θ Γ Δ r x A js wf k1 tyA k2.
    exfalso. apply: pure_just... }
Qed.

Theorem dyn_sr Θ m n A :
  Θ ; nil ; nil ⊢ m : A -> m ~>> n -> Θ ; nil ; nil ⊢ n : A.
Proof with eauto using dyn_type, dyn_step, dyn_wf, merge.
  move e1:(nil)=>Γ.
  move e2:(nil)=>Δ ty. elim: ty e1 e2 n=>{Θ Γ Δ m A}...
  { move=>Θ Γ Δ x s A emp wf shs dhs e1 e2 n st. inv st. }
  { move=>Θ Γ Δ A B m s k1 k2 tym ihm e1 e2 n st. inv st. }
  { move=>Θ Γ Δ A B m s t k1 k2 tym ihm e1 e2 n st. inv st. }
  { move=>Θ Γ Δ A B m n s tym ihm tyn e1 e2 n0 st. inv st.
    { have tym':=ihm erefl erefl _ H2.
      apply: dyn_app0... }
    { have[x tyP]:=dyn_valid tym.
      have tym0:=dyn_lam0_inv tym.
      apply: dyn_subst0... } }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n s mrg1 mrg2 tym ihm tyn ihn e1 e2 n0 st.
    subst. inv mrg2. inv st.
    { have tym':=ihm erefl erefl _ H2.
      apply: dyn_app1... }
    { have tyn':=ihn erefl erefl _ H2.
      have[x tyP]:=dyn_valid tym.
      have[r[tyB _]]:=sta_pi1_inv tyP.
      apply: dyn_conv.
      apply: sta_conv_beta.
      apply: conv_sym.
      apply: star_conv.
      apply: sta_red_pred.
      apply: dyn_sta_step...
      apply: dyn_app1...
      have:=sta_subst tyB (dyn_sta_type tyn).
      asimpl... }
    { have[x tyP]:=dyn_valid tym.
      have[r[tyB _]]:=sta_pi1_inv tyP.
      have[t tym0]:=dyn_lam1_inv tym.
      have wf:=dyn_type_wf tym0. inv wf.
      have[k1 k2]:=dyn_val_stability tyn H5 H2.
      apply: dyn_subst1.
      apply: k1. apply: mrg1. apply: k2. apply: merge_nil.
      all: eauto. } }
  { move=>Θ Γ Δ A B m n t tyS tym ihm tyn e1 e2 n0 st. inv st.
    have[s[r[ord[tyA[tyB _]]]]]:=sta_sig0_inv tyS.
    apply: dyn_pair0... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n t mrg1 mrg2 tyS tym ihm tyn ihn e1 e2 n0 st.
    subst. inv mrg2. inv st.
    { have[s[r[ord1[ord2[tyA[tyB _]]]]]]:=sta_sig1_inv tyS.
      apply: dyn_pair1...
      apply: dyn_conv.
      apply: sta_conv_beta.
      apply: star_conv.
      apply: sta_red_pred.
      apply: (dyn_sta_step tym)...
      apply: tyn.
      apply: sta_esubst...
      by autosubst. }
    { apply: dyn_pair1... } }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r t mrg1 mrg2 tyC tym ihm tyn ihn e1 e2 n0 st.
    subst. inv mrg2. inv st.
    { apply: dyn_conv.
      apply: sta_conv_beta.
      apply: conv_sym.
      apply: star_conv.
      apply: sta_red_pred.
      apply: (dyn_sta_step tym)...
      apply: dyn_letin0...
      apply: sta_esubst...
      by autosubst. }
    { inv H3.
      have[e[tym1 tym2]]:=dyn_pair0_inv tym. subst.
      have wf:=dyn_type_wf tyn. inv wf. inv H3.
      have[k1 k2]:=dyn_val_stability tym2 (sta_subst H5 tym1) H0.
      have[Θ0[emp mrg0]]:=dyn_type_empty tym2.
      replace C.[Pair0 m1 m2 t/]
        with C.[Pair0 (Var 1) (Var 0) t .: ren (+2)].[m2,m1/] by autosubst.
      apply: dyn_substitution...
      apply: (dyn_agree_subst_wk1 k1 k2)...
      apply: dyn_agree_subst_wk0...
      by autosubst. }
    { exfalso. apply: sta_pair1_sig0_false... } }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r1 r2 t mrg1 mrg2 tyC tym ihm tyn ihn e1 e2 n0 st.
    subst. inv mrg2. inv st.
    { apply: dyn_conv.
      apply: sta_conv_beta.
      apply: conv_sym.
      apply: star_conv.
      apply: sta_red_pred.
      apply: (dyn_sta_step tym)...
      apply: dyn_letin1...
      apply: sta_esubst...
      by autosubst. }
    { exfalso. apply: sta_pair0_sig1_false... }
    { inv H3.
      have[Θ1'[Θ2'[Δ1'[Δ2'[e[mrg1'[mrg2'[tym1 tym2]]]]]]]]:=dyn_pair1_inv tym.
      have wf:=dyn_type_wf tyn. inv wf. inv H3. inv mrg2'.
      have[Θ0[emp mrg0]]:=dyn_type_empty tym1.
      have [k1 k2]:=dyn_val_stability tym1 H8 H1.
      have [k3 k4]:=dyn_val_stability tym2 (sta_subst H6 (dyn_sta_type tym1)) H4.
      replace C.[Pair1 m1 m2 t/]
        with C.[Pair1 (Var 1) (Var 0) t .: ren (+2)].[m2,m1/] by autosubst.
      apply: dyn_substitution...
      apply: (dyn_agree_subst_wk1 k3 k4)...
      apply: (dyn_agree_subst_wk1 k1 k2)...
      by autosubst. } }
  { move=>Θ Γ Δ emp wf k e1 e2 n st. inv st. }
  { move=>Θ Γ Δ emp wf k e1 e2 n st. inv st. }
  { move=>Θ Γ Δ emp wf k e1 e2 n st. inv st. }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m n1 n2 s mrg1 mrg2 tyA tym ihm tyn1 ihn1 tyn2 ihn2 e1 e2 n st.
    subst. inv mrg2. inv st.
    { have tym':=ihm erefl erefl _ H4.
      apply: dyn_conv.
      apply: sta_conv_beta.
      apply: conv_sym.
      apply: star_conv.
      apply: sta_red_pred.
      apply: dyn_sta_step...
      apply: dyn_ifte...
      apply: sta_subst tyA (dyn_sta_type tym). }
    { have emp:=dyn_tt_inv tym.
      have e:=merge_emptyL mrg1 emp. subst... }
    { have emp:=dyn_ff_inv tym.
      have e:=merge_emptyL mrg1 emp. subst... } }
  { move=>Θ Γ Δ m A tym ihm e1 e2 n st. inv st... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m n A B s t mrg1 mrg2 tyB tym ihm tyn ihn e1 e2 n0 st.
    subst. inv mrg2. inv st...
    have tyv:=dyn_return_inv tym.
    have wf:=dyn_type_wf tyn. inv wf.
    have[k1 _]:=dyn_val_stability tyv H5 H2.
    have:=dyn_subst1 k1 (merge_sym mrg1) (key_nil s) merge_nil tyn tyv.
    by asimpl. }
  { move=>Θ Γ Δ r x A js wf k tyA e1 e2 n st. inv st. }
  { move=>Θ Γ Δ m A tym ihm e1 e2 n st. inv st. }
  { move=>Θ Γ Δ r1 r2 A B m xor tym ihm e1 e2 n st. inv st... }
  { move=>Θ Γ Δ r1 r2 A B m xor tym ihm e1 e2 n st. inv st... }
  { move=>Θ Γ Δ r1 r2 A B m xor tym ihm e1 e2 n st. inv st... }
  { move=>Θ Γ Δ r1 r2 A B m xor tym ihm e1 e2 n st. inv st... }
  { move=>Θ Γ Δ m tym ihm e1 e2 n st. inv st... }
  { move=>Θ Γ Δ m tym ihm e1 e2 n st. inv st... }
Qed.

Theorem dyn_rd Θ m n A :
  Θ ; nil ; nil ⊢ m : A -> m ~>>* n -> Θ ; nil ; nil ⊢ n : A.
Proof with eauto.
  move=>ty rd. elim: rd Θ A ty=>{n}...
  move=>n z rd ih st Γ A tym.
  have tyn:=ih _ _ tym.
  apply: dyn_sr...
Qed.
