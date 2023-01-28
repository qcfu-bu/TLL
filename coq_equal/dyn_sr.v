From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_prog dyn_inv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma dyn_sta_red m n A :
  nil ⊢ m : A -> m ~>> n -> m ~>* n.
Proof with eauto using sta_step.
  move e:(nil)=>Γ ty. elim: ty e n=>{Γ m A}.
  { move=>Γ s wf e n st. inv st. }
  { move=>Γ x A wf shs e n st. inv st. }
  { move=>Γ A B s r t tyA ihA tyB ihB e n st. inv st. }
  { move=>Γ A B s r t tyA ihA tyB ihB e n st. inv st. }
  { move=>Γ A B m s tym ihm e n st. inv st. }
  { move=>Γ A B m s tym ihm e n st. inv st. }
  { move=>Γ A B m n s tym ihm tyn ihn e n0 st. inv st.
    { apply: sta_red_app... }
    { apply: sta_red_app... }
    { apply: star1... }
    { apply: star1... } }
  { move=>Γ A B m n s tym ihm tyn ihn e n0 st. inv st.
    { apply: sta_red_app... }
    { apply: sta_red_app... }
    { apply: star1... }
    { apply: star1... } }
  { move=>Γ A m n s tyA ihA tym ihm tyn ihn e n0 st. inv st. }
  { move=>Γ A m tym ihm e n st. inv st. }
  { move=>Γ A B H P m n s tyB ihB tyH ihH tyP ihP e n0 st. inv st.
    have[P0[rdP vlP]]:=sta_vn tyP.
    have tyP0:=sta_rd tyP rdP.
    have[n1 e]:=sta_id_canonical tyP0 (convR _ _) vlP. subst.
    apply: star_trans.
    apply: sta_red_rw...
    apply: star1... }
  { move=>Γ A B m s eq tym ihm tyB ihB e n st. subst.
    apply: ihm... }
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

Lemma dyn_val_key Γ Δ m A s :
  Γ ; Δ ⊢ m : A -> Γ ⊢ A : Sort s -> dyn_val m -> Δ ▷ s.
Proof with eauto using key_impure.
  destruct s...
  move=>ty. elim: ty=>{Γ Δ m A}.
  { move=>Γ Δ x s A shs dhs wf tyA vl.
    have tyAs:=dyn_has_type wf shs.
    have/sort_inj e:=sta_uniq tyA tyAs. subst.
    apply: dyn_has_key... }
  { move=>Γ Δ A B m s k tym ih tyP vl.
    have[_[_/sort_inj->//]]:=sta_pi0_inv tyP. }
  { move=>Γ Δ A B m s t k tym ih tyP vl.
    have[_[_/sort_inj->//]]:=sta_pi1_inv tyP. }
  { move=>Γ Δ A B m n s tym ih tyn tyB vl. inv vl. }
  { move=>Γ Δ1 Δ2 Δ A B m n s mrg tym ihm tyn ihn tyB vl. inv vl. }
  { move=>Γ Δ A B H P m n s tyB tyH ihH tyP ihP vl. inv vl. }
  { move=>Γ Δ A B m s eq tym ihm tyB1 tyB2 vl.
    have[r tyA]:=dyn_valid tym.
    have[C rd1 rd2]:=church_rosser eq.
    apply: ihm...
    have tyCr:=sta_rd tyA rd1.
    have tyCU:=sta_rd tyB2 rd2.
    have/sort_inj<-:=sta_uniq tyCr tyCU... }
Qed.


Theorem dyn_sr m n A :
  nil ; nil ⊢ m : A -> m ~>> n -> nil ; nil ⊢ n : A.
Proof with eauto using dyn_type, dyn_step, dyn_wf, merge.
  move e1:(nil)=>Γ.
  move e2:(nil)=>Δ ty. elim: ty e1 e2 n=>{Γ Δ m A}...
  { move=>Γ Δ x s A wf shs dhs e1 e2 n st. inv st. }
  { move=>Γ Δ A B m s k tym ihm e1 e2 n st. inv st. }
  { move=>Γ Δ A B m s t k tym ihm e1 e2 n st. inv st. }
  { move=>Γ Δ A B m n s tym ihm tyn e1 e2 n0 st. inv st.
    { have tym':=ihm erefl erefl _ H2.
      apply: dyn_app0... }
    { have tyn':=sta_rd tyn (dyn_sta_red tyn H2).
      have[t tyP]:=dyn_valid tym.
      have[r[tyB _]]:=sta_pi0_inv tyP.
      apply: dyn_conv.
      apply: sta_conv_beta.
      apply: conv_sym.
      apply: star_conv.
      apply: dyn_sta_red...
      apply: dyn_app0...
      have:=sta_subst tyB tyn.
      asimpl... }
    { have[x tyP]:=dyn_valid tym.
      have tym0:=dyn_lam0_inv tym.
      apply: dyn_subst0... }
    { exfalso.
      apply: sta_lam1_pi0_false...
      apply: dyn_sta_type... } }
  { move=>Γ Δ1 Δ2 Δ A B m n s mrg tym ihm tyn ihn e1 e2 n0 st.
    subst. inv mrg. inv st.
    { have tym':=ihm erefl erefl _ H2.
      apply: dyn_app1... }
    { have tyn':=ihn erefl erefl _ H2.
      have[x tyP]:=dyn_valid tym.
      have[r[tyB _]]:=sta_pi1_inv tyP.
      apply: dyn_conv.
      apply: sta_conv_beta.
      apply: conv_sym.
      apply: star_conv.
      apply: dyn_sta_red...
      apply: dyn_sta_type...
      apply: dyn_app1...
      have:=sta_subst tyB (dyn_sta_type tyn).
      asimpl... }
    { exfalso.
      apply: sta_lam0_pi1_false...
      apply: dyn_sta_type... }
    { have[x tyP]:=dyn_valid tym.
      have[r[tyB _]]:=sta_pi1_inv tyP.
      have[t tym0]:=dyn_lam1_inv tym.
      have wf:=dyn_type_wf tym0. inv wf.
      apply: dyn_subst1...
      apply: (dyn_val_key tyn)... } }
  { move=>Γ Δ A B H P m n s tyB tyH ihH tyP n0 e1 e2 st. inv st.
    have[P0[rdP vlP]]:=sta_vn tyP.
    have tyP0:=sta_rd tyP rdP.
    have[m0 e]:=sta_id_canonical tyP0 (convR _ _) vlP. subst.
    have[r tyI]:=sta_valid tyP.
    have[tym[tyn/sort_inj e]]:=sta_id_inv tyI. subst.
    have[tym0[eq1 eq2]]:=sta_refl_inv tyP0.
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
    apply: dyn_conv.
    apply: sta_conv_compat sc.
    all: eauto. }
Qed.

Corollary dyn_rd m n A :
  nil ; nil ⊢ m : A -> m ~>>* n -> nil ; nil ⊢ n : A.
Proof with eauto.
  move=>ty rd. elim: rd A ty=>{n}...
  move=>n z rd ih st A tym.
  have tyn:=ih _ tym.
  apply: dyn_sr...
Qed.
