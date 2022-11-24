From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS ptr_step ptr_subst era_sr.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma ptr_sr H1 H2 H H' x y z z' A :
  H1 ; x ~ y ~ z : A -> wr_heap H ->
  H1 ∘ H2 => H -> H ; z ~>> H' ; z' ->
  exists H1' H2' x' y',
    H1' ; x' ~ y' ~ z' : A /\ wr_heap H' /\
    pad H2 H2' /\ H1' ∘ H2' => H' /\ x ~>>* x' /\ y ~>>* y'.
Proof with eauto 7 using pad, era_type, resolve, merge, free, key, dyn_step.
  move=>{H1 x y z A}[H1 x y z A].
  move e1:(nil)=>Γ. move e2:(nil)=>Δ er.
  elim: er H1 H2 H H' z z' e1 e2=>{Γ Δ x y A}.
  { move=>Γ Δ x s A wf shs dhs H1 H2 H H' z z' e1 e2 rs wr mrg st; subst. inv shs. }
  { move=>Γ Δ A B m m' s k erm _ H1 H2 H H' z z' e1 e2 rs wr mrg st; subst.
    inv rs; inv st.
    have[<-_]:=merge_size mrg.
    have[wr1 wr2]:=wr_merge_inv mrg wr.
    destruct s.
    { exists (Lam0 Box m0 U :U H1).
      exists (Lam0 Box m0 U :U H2).
      exists (Lam0 A m U).
      exists (Lam0 Box m' U).
      repeat split...
      { econstructor...
        constructor...
        apply: resolve_wkU... }
      { constructor...
        have//=nfm':=nf_typing erm.
        have//:=resolve_wr_nfi H8 wr1 nfm'. } }
    { exists (Lam0 Box m0 L :L H1).
      exists (_: H2).
      exists (Lam0 A m L).
      exists (Lam0 Box m' L).
      repeat split...
      { econstructor...
        constructor...
        apply: resolve_wkN... }
      { constructor...
        have//=nfm':=nf_typing erm.
        have//:=resolve_wr_nfi H8 wr1 nfm'. } } }
  { move=>Γ Δ A B m m' s t k erm _ H1 H2 H H' z z' e1 e2 rs wr mrg st; subst.
    inv rs; inv st.
    have[<-_]:=merge_size mrg.
    have[wr1 wr2]:=wr_merge_inv mrg wr.
    destruct s.
    { exists (Lam1 Box m0 U :U H1).
      exists (Lam1 Box m0 U :U H2).
      exists (Lam1 A m U).
      exists (Lam1 Box m' U).
      repeat split...
      { econstructor...
        constructor...
        apply: resolve_wkU... }
      { constructor...
        have//=nfm':=nf_typing erm.
        have//:=resolve_wr_nfi H8 wr1 nfm'. } }
    { exists (Lam1 Box m0 L :L H1).
      exists (_: H2).
      exists (Lam1 A m L).
      exists (Lam1 Box m' L).
      repeat split...
      { econstructor...
        constructor...
        apply: resolve_wkN... }
      { constructor...
        have//=nfm':=nf_typing erm.
        have//:=resolve_wr_nfi H8 wr1 nfm'. } } }
  { move=>Γ Δ A B m m' n s erm ihm tyn H1 H2 H H' z z' e1 e2 rs wr mrg st; subst.
    inv rs; inv st.
    { have[H1'[H2'[x'[y'[wrx[wr'[pd[mrg'[rd1 rd2]]]]]]]]]:=ihm _ _ _ _ _ _ erefl erefl H6 wr mrg H9.
      inv wrx.
      exists H1'. exists H2'. exists (App x' n). exists (App y' Box).
      repeat split...
      apply: (star_hom (App^~ n)) rd1=>x y.
      apply: dyn_step_appL.
      apply: (star_hom (App^~ Box)) rd2=>x y.
      apply: dyn_step_appL. }
    { inv H9. }
    { have[H1'[mrg' rs]]:=resolve_free H9 H6 mrg. inv rs.
      have[A0[n0 e]]:=era_lam0_form erm. subst.
      exists H1'. exists H2. exists (n0.[n/]). exists (m'0.[Box/]).
      repeat split...
      { have ern0:=era_lam0_inv erm.
        apply: era_esubst0... }
      { have ern:=era_lam0_inv erm.
        have wr':=free_wr H9 wr.
        have[wr1 wr2]:=wr_merge_inv mrg' wr'.
        have[Hx[k mrgx]]:=split_self H1'.
        have[_ wrx]:=wr_merge_inv mrgx wr1.
        apply: resolve_subst...
        constructor.
        constructor... }
      { apply: free_wr... }
      { apply: star1... }
      { apply: star1... } }
    { have[wr1 wr2]:=wr_merge_inv mrg wr.
      have[wr3 wr4]:=wr_merge_inv H7 wr1.
      have//:=resolve_wr_box wr4 H11. }
    { have[wr1 wr2]:=wr_merge_inv mrg wr.
      have[wr3 wr4]:=wr_merge_inv H7 wr1.
      have//:=resolve_wr_box wr4 H11. }
    { have[wr1 wr2]:=wr_merge_inv mrg wr.
      have[wr3 wr4]:=wr_merge_inv H7 wr1.
      have//:=resolve_wr_box wr4 H11. }
    { have[wr1 wr2]:=wr_merge_inv mrg wr.
      have[wr3 wr4]:=wr_merge_inv H7 wr1.
      have//:=resolve_wr_box wr4 H11. } }
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' s mrg1 erm ihm ern ihn H1 H2 H H' z z' e1 e2 rs wr mrg2 st; subst.
    inv mrg1. inv rs; inv st.
    { have//:=era_box_form ern. }
    { have//:=era_box_form ern. }
    { have//:=era_box_form ern. }
    { have[wr1 wr2]:=wr_merge_inv mrg2 wr.
      have[H4[mrg3 mrg4]]:=merge_splitR mrg2 H7.
      have[H1'[H2'[x'[y'[wrx[wr'[pd[mrg5[rd1 rd2]]]]]]]]]:=
        ihm _ _ _ _ _ _ erefl erefl H10 wr (merge_sym mrg4) H13.
      have[H1p[H2p[pd1[pd2 mrp]]]]:=pad_merge pd mrg3.
      have[Hx[mrp1 mrp2]]:=merge_splitL (merge_sym mrg5) mrp.
      inv wrx.
      exists Hx. exists H2p. exists (App x' n). exists (App y' n').
      repeat split...
      { econstructor.
        apply: merge_sym...
        apply: H8.
        apply: resolve_pad... }
      { apply: (star_hom (App^~ n)) rd1=>x y.
        apply: dyn_step_appL. }
      { apply: (star_hom (App^~ n')) rd2=>x y.
        apply: dyn_step_appL. } }
    { have[H4[mrg3 mrg4]]:=merge_splitL mrg2 H7.
      have[H1'[H2'[x'[y'[wrx[wr'[pd[mrg5[rd1 rd2]]]]]]]]]:=
        ihn _ _ _ _ _ _ erefl erefl H11 wr (merge_sym mrg4) H13.
      have[H1p[H2p[pd1[pd2 mrp]]]]:=pad_merge pd mrg3.
      have[Hx[mrp1 mrp2]]:=merge_splitL (merge_sym mrg5) mrp.
      inv wrx.
      exists Hx. exists H2p. exists (App m x'). exists (App m' y').
      repeat split...
      { have[t tyP]:=dyn_valid (era_dyn_type erm).
        have[r[tyB/sort_inj e]]:=sta_pi1_inv tyP. subst.
        have tyn:=dyn_sta_type (era_dyn_type ern).
        have//=tyBn:=sta_subst tyB tyn.
        apply: era_conv.
        apply: sta_conv_beta.
        apply: conv_sym.
        apply: star_conv.
        apply: dyn_sta_red...
        econstructor...
        apply: tyBn. }
      { econstructor...
        apply: resolve_pad... }
      { apply: (star_hom (App m)) rd1=>x y.
        apply: dyn_step_appR. }
      { apply: (star_hom (App m')) rd2=>x y.
        apply: dyn_step_appR. } }
    { have[Hx[mrg3 mrg4]]:=merge_splitR mrg2 H7.
      have[Hy[mrg5 rs]]:=resolve_free H13 H10 (merge_sym mrg4). inv rs.
      have[A0[n1 e]]:=era_lam0_form erm. subst.
      exfalso. apply: sta_lam0_pi1_false... }
    { have[H4[mrg3 mrg4]]:=merge_splitR mrg2 H7.
      have[H5[mrg rs]]:=resolve_free H13 H10 (merge_sym mrg4). inv rs.
      have[Hx[mrg5 mrg6]]:=merge_splitL (merge_sym mrg) mrg3.
      have[A0[n0 e]]:=era_lam1_form erm. subst.
      have[r ern0]:=era_lam1_inv erm.
      have wr':=free_wr H13 wr.
      have[wr1 wr2]:=wr_merge_inv mrg wr'.
      have[wr3 wr4]:=wr_merge_inv mrg3 wr2.
      have[H3'[k mrg']]:=split_self H3.
      have[_ wr3']:=wr_merge_inv mrg' wr3.
      have vl':=wr_resolve_ptr wr3 H11.
      have vl:=era_dyn_val ern vl'.
      exists Hx. exists H2. exists n0.[n/]. exists m'0.[n'/].
      repeat split...
      { apply: era_subst1.
        apply: key_nil.
        apply: merge_nil.
        apply: ern0.
        apply: ern. }
      { have wf:=dyn_type_wf (era_dyn_type ern0). inv wf.
        have k1:=resolution (Ptr_well_resolved ern H11) H17 vl' wr3.
        destruct r.
        { apply: resolve_subst.
          apply: ern0.
          apply: merge_sym...
          apply: H16.
          apply: wr1.
          apply: agree_resolve_wkU.
          apply: merge_sym...
          all: eauto.
          constructor... }
        { apply: resolve_subst.
          apply: ern0.
          apply: merge_sym...
          all: eauto.
          apply: agree_resolve_wkL.
          apply: merge_sym...
          all: eauto.
          constructor... } }
      { apply: star1. apply: dyn_step_beta1... }
      { apply: star1. apply: dyn_step_beta1... } } }
