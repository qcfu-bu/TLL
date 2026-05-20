From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS era_sr ptr_step ptr_subst.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma ptr_srX H1 H2 H H' x y z z' A :
  H1 ; x ~ y ~ z : A -> wr_heap H ->
  H1 ∘ H2 => H -> H ; z ~>> H' ; z' ->
  exists H1' H2' x' y',
    H1' ; x' ~ y' ~ z' : A /\ wr_heap H' /\
    pad H2 H2' /\ H1' ∘ H2' => H' /\ x ~>>* x' /\ y ~>>* y'.
Proof with eauto 7 using era_type, resolve, dyn_step, key, merge, hmrg_setmU, hmrg_setmL, pad_refl.
  move=>{H1 x y z A}[H1 x y z A].
  move e1:(nil)=>Γ. move e2:(nil)=>Δ er.
  elim: er H1 H2 H H' z z' e1 e2=>{Γ Δ x y A}.
  { move=>Γ Δ x s A wf shs dhs H1 H2 H H' z z' e1 e2 rs wr mrg st; subst. inv shs. }
  { move=>Γ Δ A B m m' s k erm _ H1 H2 H H' z z' e1 e2 rs wr mrg st; subst.
    inv rs; inv st.
    have[wr1 wr2]:=wr_merge_inv mrg wr.
    destruct s.
    { exists (setm H1 l (Lam0 Box m0 U, U)).
      exists (setm H2 l (Lam0 Box m0 U, U)).
      exists (Lam0 A m U).
      exists (Lam0 Box m' U).
      rsplit...
      { econstructor.
        rewrite/free setmE eq_refl. rsplit.
        apply: resolve_wkU.
        constructor...
        by have[]:=hmrg_none mrg H10. }
      { have//=nfm':=nf_typing erm.
        have//=nfm0:=resolve_wr_nfi H8 wr1 nfm'.
        apply: wr_merge.
        apply: hmrg_setmU...
        move=>x. have:=wr1 x. rewrite setmE. by case: eqP.
        move=>x. have:=wr2 x. rewrite setmE. by case: eqP. }
      { apply: pad_setm.
        by have[]:=hmrg_none mrg H10. } }
    { exists (setm H1 l (Lam0 Box m0 L, L)).
      exists (H2).
      exists (Lam0 A m L).
      exists (Lam0 Box m' L).
      rsplit...
      { econstructor.
        rewrite/free setmE eq_refl. rsplit.
        rewrite remm_setm.
        constructor...
        by have[]:=hmrg_none mrg H10. }
      { have//=nfm':=nf_typing erm.
        have//=nfm0:=resolve_wr_nfi H8 wr1 nfm'.
        apply: wr_merge.
        apply: hmrg_setmL...
        move=>x. have:=wr1 x. rewrite setmE. by case: eqP.
        exact: wr2. } } }
  { move=>Γ Δ A B m m' s t k erm _ H1 H2 H H' z z' e1 e2 rs wr mrg st; subst.
    inv rs; inv st.
    have[wr1 wr2]:=wr_merge_inv mrg wr.
    destruct s.
    { exists (setm H1 l (Lam1 Box m0 U, U)).
      exists (setm H2 l (Lam1 Box m0 U, U)).
      exists (Lam1 A m U).
      exists (Lam1 Box m' U).
      rsplit...
      { econstructor.
        rewrite/free setmE eq_refl. rsplit.
        apply: resolve_wkU.
        constructor...
        by have[]:=hmrg_none mrg H10. }
      { have//=nfm':=nf_typing erm.
        have//=nfm0:=resolve_wr_nfi H8 wr1 nfm'.
        apply: wr_merge.
        apply: hmrg_setmU...
        move=>x. have:=wr1 x. rewrite setmE. by case: eqP.
        move=>x. have:=wr2 x. rewrite setmE. by case: eqP. }
      { apply: pad_setm.
        by have[]:=hmrg_none mrg H10. } }
    { exists (setm H1 l (Lam1 Box m0 L, L)).
      exists (H2).
      exists (Lam1 A m L).
      exists (Lam1 Box m' L).
      rsplit...
      { econstructor.
        rewrite/free setmE eq_refl. rsplit.
        rewrite remm_setm.
        constructor...
        by have[]:=hmrg_none mrg H10. }
      { have//=nfm':=nf_typing erm.
        have//=nfm0:=resolve_wr_nfi H8 wr1 nfm'.
        apply: wr_merge.
        apply: hmrg_setmL...
        move=>x. have:=wr1 x. rewrite setmE. by case: eqP.
        exact: wr2. } } }
  { move=>Γ Δ A B m m' n s erm ihm tyn H1 H2 H H' z z' e1 e2 rs wr mrg st; subst.
    inv rs; inv st.
    { have[H1'[H2'[x'[y'[wrx[wr'[pd[mrg'[rd1 rd2]]]]]]]]]:=ihm _ _ _ _ _ _ erefl erefl H6 wr mrg H9.
      inv wrx.
      exists H1'. exists H2'. exists (App x' n). exists (App y' Box).
      repeat split...
      { apply: (star_hom (App^~ n)) rd1=>x y.
        apply: dyn_step_appL. }
      { apply: (star_hom (App^~ Box)) rd2=>x y.
        apply: dyn_step_appL. } }
    { inv H9. }
    { have[H1'[mrg' rs]]:=resolve_free H9 H6 mrg. inv rs.
      have[A0[n0 e]]:=era_lam0_form erm. subst.
      exists H1'. exists H2. exists (n0.[n/]). exists (m'0.[Box/]).
      repeat split...
      { have[ern0 _]:=era_lam0_inv erm.
        apply: era_esubst0... }
      { have[ern _]:=era_lam0_inv erm.
        have wr':=free_wr H9 wr.
        have[wr1 wr2]:=wr_merge_inv mrg' wr'.
        have[Hx[k mrgx]]:=hsplit_self H1'.
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
      have[H4[mrg3 mrg4]]:=hmrg_splitR mrg2 H7.
      have[H1'[H2'[x'[y'[wrx[wr'[pd[mrg5[rd1 rd2]]]]]]]]]:=
        ihm _ _ _ _ _ _ erefl erefl H10 wr (hmrg_sym mrg4) H13.
      have[H1p[H2p[pd1[pd2 mrp]]]]:=pad_merge pd mrg3.
      have[Hx[mrp1 mrp2]]:=hmrg_splitL (hmrg_sym mrg5) mrp.
      inv wrx.
      exists Hx. exists H2p. exists (App x' n). exists (App y' n').
      repeat split...
      { econstructor.
        apply: hmrg_sym...
        apply: H8.
        apply: resolve_pad... }
      { apply: (star_hom (App^~ n)) rd1=>x y.
        apply: dyn_step_appL. }
      { apply: (star_hom (App^~ n')) rd2=>x y.
        apply: dyn_step_appL. } }
    { have[H4[mrg3 mrg4]]:=hmrg_splitL mrg2 H7.
      have[H1'[H2'[x'[y'[wrx[wr'[pd[mrg5[rd1 rd2]]]]]]]]]:=
        ihn _ _ _ _ _ _ erefl erefl H11 wr (hmrg_sym mrg4) H13.
      have[H1p[H2p[pd1[pd2 mrp]]]]:=pad_merge pd mrg3.
      have[Hx[mrp1 mrp2]]:=hmrg_splitL (hmrg_sym mrg5) mrp.
      inv wrx.
      exists Hx. exists H2p. exists (App m x'). exists (App m' y').
      repeat split...
      { have[t[lP tyP]]:=dyn_valid (era_dyn_type erm).
        have[r[l1[l2[tyB/sort_inj[e1 e2]]]]]:=sta_pi1_inv tyP. subst.
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
    { have[Hx[mrg3 mrg4]]:=hmrg_splitR mrg2 H7.
      have[Hy[mrg5 rs]]:=resolve_free H13 H10 (hmrg_sym mrg4). inv rs.
      have[A0[n1 e]]:=era_lam0_form erm. subst.
      exfalso. apply: sta_lam0_pi1_false... }
    { have[H4[mrg3 mrg4]]:=hmrg_splitR mrg2 H7.
      have[H5[mrg rs]]:=resolve_free H13 H10 (hmrg_sym mrg4). inv rs.
      have[Hx[mrg5 mrg6]]:=hmrg_splitL (hmrg_sym mrg) mrg3.
      have[A0[n0 e]]:=era_lam1_form erm. subst.
      have[r[ern0 _]]:=era_lam1_inv erm.
      have wr':=free_wr H13 wr.
      have[wr1 wr2]:=wr_merge_inv mrg wr'.
      have[wr3 wr4]:=wr_merge_inv mrg3 wr2.
      have[H3'[k mrg']]:=hsplit_self H3.
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
          apply: hmrg_sym...
          apply: H16.
          apply: wr1.
          apply: agree_resolve_wkU.
          apply: hmrg_sym...
          all: eauto.
          constructor... }
        { apply: resolve_subst.
          apply: ern0.
          apply: hmrg_sym...
          all: eauto.
          apply: agree_resolve_wkL.
          apply: hmrg_sym...
          all: eauto.
          constructor... } }
      { apply: star1. apply: dyn_step_beta1... }
      { apply: star1. apply: dyn_step_beta1... } } }
  { move=>Γ Δ A B m m' n t l tyS erm ihm tyn H1 H2 H H' z z' e1 e2 rs wr mrg st; subst.
    have[wr1 wr2]:=wr_merge_inv mrg wr.
    inv rs; inv st.
    { have[H1'[H2'[x'[y'[wrx[wr'[pd[mrg'[rd1 rd2]]]]]]]]]:=ihm _ _ _ _ _ _ erefl erefl H6 wr mrg H9.
      inv wrx.
      exists H1'. exists H2'. exists (Pair0 x' n t). exists (Pair0 y' Box t).
      rsplit...
      { have[s[r[l1[l2[ord[tyA[tyB _]]]]]]]:=sta_sig0_inv tyS.
        have tyx:=dyn_sta_type (dyn_rd (era_dyn_type erm) rd1).
        have//=tyBx:=sta_subst tyB tyx.
        econstructor...
        apply: sta_conv.
        apply: sta_conv_beta.
        apply: star_conv.
        apply: (dyn_sta_red (dyn_sta_type (era_dyn_type erm)))...
        apply: tyn.
        apply: tyBx. }
      { apply: (star_hom ((Pair0^~ n)^~ t)) rd1=>x y.
        apply: dyn_step_pair0L. }
      { apply: (star_hom ((Pair0^~ Box)^~ t)) rd2=>x y.
        apply: dyn_step_pair0L. } }
    { destruct t.
      { exists (setm H1 l0 (Pair0 (Ptr lm) Box U, U)).
        exists (setm H2 l0 (Pair0 (Ptr lm) Box U, U)).
        exists (Pair0 m n U).
        exists (Pair0 m' Box U).
        rsplit...
        { econstructor.
          rewrite/free setmE eq_refl. rsplit.
          apply: resolve_wkU.
          constructor...
          by have[]:=hmrg_none mrg H9. }
        { apply: wr_merge.
          apply: hmrg_setmU...
          move=>x. have:=wr1 x. rewrite setmE. by case: eqP.
          move=>x. have:=wr2 x. rewrite setmE. by case: eqP. }
        { apply: pad_setm.
          by have[]:=hmrg_none mrg H9. } }
      { exists (setm H1 l0 (Pair0 (Ptr lm) Box L, L)).
        exists (H2).
        exists (Pair0 m n L).
        exists (Pair0 m' Box L).
        rsplit...
        { econstructor.
          rewrite/free setmE eq_refl. rsplit.
          rewrite remm_setm.
          constructor...
          by have[]:=hmrg_none mrg H9. }
        { apply: wr_merge.
          apply: hmrg_setmL...
          move=>x. have:=wr1 x. rewrite setmE. by case: eqP.
          exact: wr2. } } } }
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' t l mrg1 tyS erm ihm ern ihn H1 H2 H H' z z' e1 e2 rs wr mrg2 st; subst.
    have[s[r[l1[l2[ord1[ord2[tyA[tyB _]]]]]]]]:=sta_sig1_inv tyS. inv mrg1.
    have[wr1 wr2]:=wr_merge_inv mrg2 wr.
    inv rs; inv st.
    { have[H4[mrg3 mrg4]]:=hmrg_splitR mrg2 H10.
      have[H1'[H2'[x'[y'[wrx[wr'[pd[mrg'[rd1 rd2]]]]]]]]]:=
        ihm _ _ _ _ _ _ erefl erefl H11 wr (hmrg_sym mrg4) H14. inv wrx.
      have[H1p[H2p[pd1[pd2 mrp]]]]:=pad_merge pd mrg3.
      have[Hx[mrp1 mrp2]]:=hmrg_splitL (hmrg_sym mrg') mrp.
      exists Hx. exists H2p. exists (Pair1 x' n t). exists (Pair1 y' n' t).
      repeat split...
      { have tyx:=dyn_sta_type (dyn_rd (era_dyn_type erm) rd1).
        have//=tyBx:=sta_subst tyB tyx.
        econstructor...
        apply: era_conv.
        apply: sta_conv_beta.
        apply: star_conv.
        apply: (dyn_sta_red (dyn_sta_type (era_dyn_type erm)))...
        apply: ern.
        apply: tyBx. }
      { econstructor.
        apply: hmrg_sym...
        apply: H7.
        apply: resolve_pad... }
      { apply: (star_hom ((Pair1^~ n)^~ t)) rd1=>x y.
        apply: dyn_step_pair1L. }
      { apply: (star_hom ((Pair1^~ n')^~ t)) rd2=>x y.
        apply: dyn_step_pair1L. } }
    { have[H4[mrg3 mrg4]]:=hmrg_splitL mrg2 H10.
      have[H1'[H2'[x'[y'[wrx[wr'[pd[mrg'[rd1 rd2]]]]]]]]]:=
        ihn _ _ _ _ _ _ erefl erefl H12 wr (hmrg_sym mrg4) H14. inv wrx.
      have[H1p[H2p[pd1[pd2 mrp]]]]:=pad_merge pd mrg3.
      have[Hx[mrp1 mrp2]]:=hmrg_splitL (hmrg_sym mrg') mrp.
      exists Hx. exists H2p. exists (Pair1 m x' t). exists (Pair1 m' y' t).
      repeat split...
      { econstructor...
        apply: resolve_pad... }
      { apply: (star_hom (Pair1 m^~ t)) rd1=>x y.
        apply: dyn_step_pair1R. }
      { apply: (star_hom (Pair1 m'^~ t)) rd2=>x y.
        apply: dyn_step_pair1R. } }
    { destruct t.
      { exists (setm H1 l0 (Pair1 (Ptr lm) (Ptr ln) U, U)).
        exists (setm H2 l0 (Pair1 (Ptr lm) (Ptr ln) U, U)).
        exists (Pair1 m n U).
        exists (Pair1 m' n' U).
        rsplit...
        { econstructor.
          rewrite/free setmE eq_refl. rsplit.
          apply: resolve_wkU.
          econstructor...
          by have[]:=hmrg_none mrg2 H14. }
        { apply: wr_merge.
          apply: hmrg_setmU...
          move=>x. have:=wr1 x. rewrite setmE. by case: eqP.
          move=>x. have:=wr2 x. rewrite setmE. by case: eqP. }
        { apply: pad_setm.
          by have[]:=hmrg_none mrg2 H14. } }
      { exists (setm H1 l0 (Pair1 (Ptr lm) (Ptr ln) L, L)).
        exists (H2).
        exists (Pair1 m n L).
        exists (Pair1 m' n' L).
        rsplit...
        { econstructor.
          rewrite/free setmE eq_refl. rsplit.
          rewrite remm_setm.
          econstructor...
          by have[]:=hmrg_none mrg2 H14. }
        { apply: wr_merge.
          apply: hmrg_setmL...
          move=>x. have:=wr1 x. rewrite setmE. by case: eqP.
          exact: wr2. } } } }
  { move=>Γ Δ1 Δ2 Δ A B C m m' n n' s r t l mrg1 tyC
      erm ihm ern _ H1 H2 H H' z z' e1 e2 rs wr mrg2 st; subst.
    inv mrg1. inv rs; inv st.
    { have[H4[mrg3 mrg4]]:=hmrg_splitR mrg2 H7.
      have[H1'[H2'[x'[y'[wrx[wr'[pd[mrg'[rd1 rd2]]]]]]]]]:=
        ihm _ _ _ _ _ _ erefl erefl H10 wr (hmrg_sym mrg4) H13. inv wrx.
      have[H1p[H2p[pd1[pd2 mrp]]]]:=pad_merge pd mrg3.
      have[Hx[mrp1 mrp2]]:=hmrg_splitL (hmrg_sym mrg') mrp.
      exists Hx. exists H2p. exists (LetIn C x' n). exists (LetIn Box y' n').
      repeat split...
      { apply: era_conv.
        apply: sta_conv_beta.
        apply: conv_sym.
        apply: star_conv.
        apply: dyn_sta_red...
        apply: era_letin0...
        apply: sta_esubst...
        autosubst. }
      { econstructor.
        apply: hmrg_sym...
        apply: H8.
        apply: resolve_pad... }
      { apply: (star_hom (LetIn C^~ n)) rd1=>x y.
        apply: dyn_step_letinL. }
      { apply: (star_hom (LetIn Box^~ n')) rd2=>x y.
        apply: dyn_step_letinL. } }
    { have[H4[mrg3 mrg4]]:=hmrg_splitR mrg2 H7.
      have[H1'[mrg' rs]]:=resolve_free H13 H10 (hmrg_sym mrg4). inv rs.
      have[Hx[mrg5 mrg6]]:=hmrg_splitL (hmrg_sym mrg') mrg3.
      have[m1[m2 e]]:=era_pair0_form erm. subst.
      have[e[_[erm1 tym2]]]:=era_pair0_inv erm. subst.
      have wr':=free_wr H13 wr.
      have[wr1 wr2]:=wr_merge_inv mrg2 wr.
      have[wr3 wr4]:=wr_merge_inv H7 wr1.
      have[wr5 wr6]:=wr_merge_inv mrg' wr'.
      have vl:=wr_resolve_ptr wr5 H15.
      have wf:=dyn_type_wf (era_dyn_type ern). inv wf.  inv H9.
      have k1:=resolution (Ptr_well_resolved erm1 H15) H17 vl wr5.
      have[H2'[k mrg2']]:=hsplit_self H1'.
      have[_ wr7]:=wr_merge_inv mrg2' wr5.
      exists Hx. exists H2. exists n.[m2,m1/]. exists (n'.[Box,m'0/]).
      repeat split...
      { replace C.[Pair0 m1 m2 t/] with
          C.[Pair0 (Var 1) (Var 0) t .: ren (+2)].[m2,m1/] by autosubst.
        apply: era_substitution.
        apply: ern.
        constructor.
        econstructor.
        apply: key_nil.
        all: eauto...
        asimpl... }
      { destruct r.
        { apply: resolve_subst...
          constructor.
          econstructor.
          apply: hmrg_sym mrg2'.
          all: eauto.
          constructor... }
        { apply: resolve_subst...
          constructor.
          econstructor.
          apply: hmrg_sym mrg2'.
          all: eauto.
          constructor... } }
      { apply: star1.
        constructor.
        constructor.
        apply: era_dyn_val... }
      { apply: star1.
        constructor.
        constructor... } }
    { have[H4[mrg3 mrg4]]:=hmrg_splitR mrg2 H7.
      have[H1'[mrg' rs]]:=resolve_free H13 H10 (hmrg_sym mrg4). inv rs.
      have[m1[m2 e]]:=era_pair1_form erm. subst.
      exfalso. apply: sta_pair1_sig0_false... } }
  { move=>Γ Δ1 Δ2 Δ A B C m m' n n' s r1 r2 t l mrg1 tyC
      erm ihm ern _ H1 H2 H H' z z' e1 e2 rs wr mrg2 st; subst.
    inv mrg1. inv rs; inv st.
    { have[H4[mrg3 mrg4]]:=hmrg_splitR mrg2 H7.
      have[H1'[H2'[x'[y'[wrx[wr'[pd[mrg'[rd1 rd2]]]]]]]]]:=
        ihm _ _ _ _ _ _ erefl erefl H10 wr (hmrg_sym mrg4) H13. inv wrx.
      have[H1p[H2p[pd1[pd2 mrp]]]]:=pad_merge pd mrg3.
      have[Hx[mrp1 mrp2]]:=hmrg_splitL (hmrg_sym mrg') mrp.
      exists Hx. exists H2p. exists (LetIn C x' n). exists (LetIn Box y' n').
      repeat split...
      { apply: era_conv.
        apply: sta_conv_beta.
        apply: conv_sym.
        apply: star_conv.
        apply: dyn_sta_red...
        apply: era_letin1...
        apply: sta_esubst...
        autosubst. }
      { econstructor.
        apply: hmrg_sym...
        apply: H8.
        apply: resolve_pad... }
      { apply: (star_hom (LetIn C^~ n)) rd1=>x y.
        apply: dyn_step_letinL. }
      { apply: (star_hom (LetIn Box^~ n')) rd2=>x y.
        apply: dyn_step_letinL. } }
    { have[H4[mrg3 mrg4]]:=hmrg_splitR mrg2 H7.
      have[H1'[mrg' rs]]:=resolve_free H13 H10 (hmrg_sym mrg4). inv rs.
      have[m1[m2 e]]:=era_pair0_form erm. subst.
      exfalso. apply: sta_pair0_sig1_false... }
    { have[H4[mrg3 mrg4]]:=hmrg_splitR mrg2 H7.
      have[H1'[mrg' rs]]:=resolve_free H13 H10 (hmrg_sym mrg4). inv rs.
      have[Hx[mrg5 mrg6]]:=hmrg_splitL (hmrg_sym mrg') mrg3.
      have[m1[m2 e]]:=era_pair1_form erm. subst.
      have[Δ1[Δ2[mrg[e[erm1 erm2]]]]]:=era_pair1_inv erm. inv mrg; subst.
      have wr':=free_wr H13 wr.
      have[wr1 wr2]:=wr_merge_inv mrg2 wr.
      have[wr3 wr4]:=wr_merge_inv H7 wr1.
      have[wr5 wr6]:=wr_merge_inv mrg' wr'.
      have[wr7 wr8]:=wr_merge_inv H16 wr5.
      have vm:=wr_resolve_ptr wr7 H18.
      have vn:=wr_resolve_ptr wr8 H19.
      have wf:=dyn_type_wf (era_dyn_type ern). inv wf.  inv H14.
      have k1:=resolution (Ptr_well_resolved erm1 H18) H21 vm wr7.
      have//=tyBm1:=sta_subst H17 (dyn_sta_type (era_dyn_type erm1)).
      have k2:=resolution (Ptr_well_resolved erm2 H19) tyBm1 vn wr8.
      have[H5'[k5 mrg5']]:=hsplit_self H5.
      have[H6'[k6 mrg6']]:=hsplit_self H6.
      have[_ wr5']:=wr_merge_inv mrg5' wr7.
      have[_ wr6']:=wr_merge_inv mrg6' wr8.
      exists Hx. exists H2. exists n.[m2,m1/]. exists (n'.[n'0,m'0/]).
      repeat split...
      { replace C.[Pair1 m1 m2 t/] with
          C.[Pair1 (Var 1) (Var 0) t .: ren (+2)].[m2,m1/] by autosubst.
        apply: era_substitution.
        apply: ern.
        econstructor. apply: key_nil.
        constructor.
        econstructor. apply: key_nil.
        all: eauto...
        asimpl... }
      { destruct r1; destruct r2.
        { apply: resolve_subst...
          econstructor...
          econstructor.
          apply: hmrg_sym mrg5'.
          all: eauto.
          constructor... }
        { apply: resolve_subst...
          econstructor...
          econstructor.
          apply: hmrg_sym mrg5'.
          all: eauto.
          constructor... }
        { apply: resolve_subst...
          econstructor...
          econstructor.
          apply: hmrg_sym mrg5'.
          all: eauto.
          constructor... }
        { apply: resolve_subst...
          econstructor...
          econstructor.
          apply: hmrg_sym mrg5'.
          all: eauto.
          constructor... } }
      { apply: star1.
        constructor.
        constructor.
        apply: era_dyn_val...
        apply: era_dyn_val... }
      { apply: star1.
        constructor.
        constructor... } } }
  { move=>Γ Δ wf k H1 H2 H H' z z' e1 e2 rs wr mrg st; subst.
    inv rs; inv st.
    exists (setm H1 l (TT, U)).
    exists (setm H2 l (TT, U)).
    exists TT. exists TT.
    rsplit...
    { econstructor.
      rewrite/free setmE eq_refl. rsplit.
      constructor...
      apply: hkey_setm... }
    { move=>x. have:=wr x. rewrite setmE. by case: eqP. }
    { apply: pad_setm.
      by have[]:=hmrg_none mrg H4. } }
  { move=>Γ Δ wf k H1 H2 H H' z z' e1 e2 rs wr mrg st; subst.
    inv rs; inv st.
    exists (setm H1 l (FF, U)).
    exists (setm H2 l (FF, U)).
    exists FF. exists FF.
    rsplit...
    { econstructor.
      rewrite/free setmE eq_refl. rsplit.
      constructor...
      apply: hkey_setm... }
    { move=>x. have:=wr x. rewrite setmE. by case: eqP. }
    { apply: pad_setm.
      by have[]:=hmrg_none mrg H4. } }
  { move=>Γ Δ1 Δ2 Δ A m m' n1 n1' n2 n2' s l mrg1 tyAQ erm ihm
           ern1 ihn1 ern2 ihn2 H1 H2 H H' z z' e1 e2 rs wr mrg2 st; subst.
    inv mrg1; inv rs; inv st.
    { have[H4[mrg3 mrg4]]:=hmrg_splitR mrg2 H8.
      have[H1'[H2'[x'[y'[wrx[wr'[pd[mrg'[rd1 rd2]]]]]]]]]:=
        ihm _ _ _ _ _ _ erefl erefl H11 wr (hmrg_sym mrg4) H15. inv wrx.
      have[H1p[H2p[pd1[pd2 mrp]]]]:=pad_merge pd mrg3.
      have[Hx[mrp1 mrp2]]:=hmrg_splitL (hmrg_sym mrg') mrp.
      exists Hx. exists H2p. exists (Ifte A x' n1 n2). exists (Ifte Box y' n1' n2').
      repeat split...
      { apply: era_conv.
        apply: sta_conv_beta.
        apply: conv_sym.
        apply: star_conv.
        apply: dyn_sta_red...
        apply: era_ifte...
        apply: sta_esubst...
        autosubst. }
      { econstructor.
        apply: hmrg_sym...
        apply: H7.
        apply: resolve_pad...
        apply: resolve_pad... }
      { apply: (star_hom ((Ifte A^~ n1)^~ n2)) rd1=>x y.
        apply: dyn_step_ifteM. }
      { apply: (star_hom ((Ifte Box^~ n1')^~ n2')) rd2=>x y.
        apply: dyn_step_ifteM. } }
    { have[H4[mrg3 mrg4]]:=hmrg_splitR mrg2 H8.
      have[H1'[mrg' rs]]:=resolve_free H15 H11 (hmrg_sym mrg4). inv rs.
      have[Hx[mrg5 mrg6]]:=hmrg_splitL (hmrg_sym mrg') mrg3.
      have e:=era_tt_form erm. subst.
      have e:=hmrg_pureR mrg5 H6. subst.
      have wr':=free_wr H15 wr.
      exists H3. exists H2. exists n1. exists n1'.
      repeat split...
      apply: star1. constructor.
      apply: star1. constructor. }
    { have[H4[mrg3 mrg4]]:=hmrg_splitR mrg2 H8.
      have[H1'[mrg' rs]]:=resolve_free H15 H11 (hmrg_sym mrg4). inv rs.
      have[Hx[mrg5 mrg6]]:=hmrg_splitL (hmrg_sym mrg') mrg3.
      have e:=era_ff_form erm. subst.
      have e:=hmrg_pureR mrg5 H6. subst.
      have wr':=free_wr H15 wr.
      exists H3. exists H2. exists n2. exists n2'.
      repeat split...
      apply: star1. constructor.
      apply: star1. constructor. } }
  { move=>Γ Δ A B x x' P m n s l tyB erx ihx tyP H1 H2 H H' z z' e1 e2 rs wr mrg st; subst.
    inv rs; inv st.
    exists H1. exists H2. exists x. exists x'.
    repeat split...
    { have[P0[rdP vlP]]:=sta_vn tyP.
      have tyP0:=sta_rd tyP rdP.
      have[n0 e]:=sta_id_canonical tyP0 (convR _ _) vlP. subst.
      have tyr:=sta_rd tyP rdP.
      have[r[lI tyI]]:=sta_valid tyP.
      have[l0[tym[tyn/sort_inj[e1 e2]]]]:=sta_id_inv tyI. subst.
      have[tym0[eq1 eq2]]:=sta_refl_inv tyr.
      have sc:sconv (Refl m .: m .: ids) (P .: n .: ids).
      { move=>[|[|]]//=.
        apply: conv_trans. apply: sta_conv_refl. apply: conv_sym...
        apply: conv_sym. apply: star_conv...
        apply: conv_trans. apply: conv_sym... eauto. }
      have wkB:nil ⊢ B.[P,n/] : Sort s l.
      { replace (Sort s l) with (Sort s l).[P,n/] by eauto.
        apply: sta_substitution...
        repeat constructor...
        all: asimpl... }
      apply: era_conv.
      apply: sta_conv_compat sc.
      all: eauto. }
    { apply: star1.
      apply: dyn_step_rwE. }
    { apply: star1.
      apply: dyn_step_rwE. } }
  { move=>Γ Δ A B m m' s l eq erm ihm tyB H1 H2 H H' z z' e1 e2 rs wr mrg st; subst.
    have[H1'[H2'[x'[y'[wrx[wr'[pd[mrg'[rd1 rd2]]]]]]]]]:=
      ihm _ _ _ _ _ _ erefl erefl rs wr mrg st. inv wrx.
    exists H1'. exists H2'. exists x'. exists y'.
    repeat split... }
Qed.

Theorem ptr_sr H H' x y z z' A :
  H ; x ~ y ~ z : A -> wr_heap H ->
  H ; z ~>> H' ; z' ->
  exists x' y', H' ; x' ~ y' ~ z' : A /\ wr_heap H' /\ x ~>>* x' /\ y ~>>* y'.
Proof with eauto.
  move=>wrx wr st.
  have[H0[k mrg]]:=hsplit_self H.
  have[H1'[H2'[x'[y'[wrx'[wr'[pd[mrg'[rd1 rd2]]]]]]]]]:=ptr_srX wrx wr mrg st.
  have k':=pad_key pd k.
  have e:=hmrg_pureR mrg' k'. subst.
  exists x'. exists y'...
Qed.
