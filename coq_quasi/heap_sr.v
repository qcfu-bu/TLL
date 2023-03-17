(* This file presents the heap subject reduction theorem. *)

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS
  program_prog erasure_sr erasure_prog
  heap_step heap_subst.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma program_wf_empty Γ Δ1 Δ2 :
  program_wf Γ Δ1 -> program_wf Γ Δ2 -> program_empty Δ1 -> program_empty Δ2 -> Δ1 = Δ2.
Proof with eauto.
  move=>wf1 wf2 dN1 dN2.
  apply: program_empty_uniq...
  have e1:=program_wf_size wf1.
  have e2:=program_wf_size wf2.
  by rewrite<-e1.
Qed.

Lemma program_logical_red Γ Δ m n A :
  Γ ; Δ ⊢ m : A -> m ~>>* n -> m ~>* n.
Proof with eauto.
  move=>ty rd. elim: rd A ty=>{n}...
  move=>m' n rd ih st A tym.
  have rdm:=ih _ tym.
  have tym':=program_rd tym rd.
  have rdm':=program_logical_step tym' st.
  apply: star_trans.
  apply: rdm.
  apply: rdm'.
Qed.

(* To prove the heap subject reduction theorem, a more general version
   of the theorem is proven first. heap_srX allows for parts of the heap
   to remain untouched by reduction. Intuitively, the sub-heaps that 
   participate in heap reductions are proven to obey subject reduction.
   Finally, the untouched sub-heaps are merged back together with the
   sub-heaps that come out of heap reduction. *)
Lemma heap_srX Γ H1 H2 H H' x y z z' A :
  Γ ; H1 ⊢ x ~ y ~ z : A -> wr_heap H ->
  H1 ∘ H2 => H -> H ; z ~>> H' ; z' ->
  exists H1' H2' x' y',
    Γ ; H1' ⊢ x' ~ y' ~ z' : A /\ wr_heap H' /\
    pad H2 H2' /\ H1' ∘ H2' => H' /\ x ~>>* x' /\ y ~>>* y'.
Proof with eauto 7 using
  pad, erasure_type, resolve, merge, lookup, key, program_step, program_iempty.
  move=>{Γ H1 x y z A}[Γ Δ H1 x y z A].
  move=>dN er.
  elim: er H1 H2 H H' z z' dN=>{Γ Δ x y A}.
  { move=>Γ Δ x s A wf shs dhs H1 H2 H H' z z' dN rs wr mrg st.
    exfalso. apply: program_has_empty... }
  { move=>Γ Δ A B m m' s k erm _ H1 H2 H H' z z' dN rs wr mrg st.
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
        econstructor...
        apply: resolve_wkU... }
      { constructor...
        have dNi:program_iempty (_: Δ) 1...
        have//=nfm':=nf_typing erm dNi.
        have//:=resolve_wr_nfi H8 wr1 nfm'. } }
    { exists (Lam0 Box m0 L :L H1).
      exists (_: H2).
      exists (Lam0 A m L).
      exists (Lam0 Box m' L).
      repeat split...
      { econstructor...
        econstructor...
        apply: resolve_wkN... }
      { constructor...
        have dNi:program_iempty (_: Δ) 1...
        have//=nfm':=nf_typing erm dNi.
        have//:=resolve_wr_nfi H8 wr1 nfm'. } } }
  { move=>Γ Δ A B m m' s t k erm _ H1 H2 H H' z z' dN rs wr mrg st.
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
        econstructor...
        apply: resolve_wkU... }
      { constructor...
        have dNi:program_iempty (A :{t} Δ) 1...
        have//=nfm':=nf_typing erm dNi.
        have//:=resolve_wr_nfi H8 wr1 nfm'. } }
    { exists (Lam1 Box m0 L :L H1).
      exists (_: H2).
      exists (Lam1 A m L).
      exists (Lam1 Box m' L).
      repeat split...
      { econstructor...
        econstructor...
        apply: resolve_wkN... }
      { constructor...
        have dNi:program_iempty (A :{t} Δ) 1...
        have//=nfm':=nf_typing erm dNi.
        have//:=resolve_wr_nfi H8 wr1 nfm'. } } }
  { move=>Γ Δ A B m m' n s erm ihm tyn H1 H2 H H' z z' dN rs wr mrg st.
    inv rs; inv st.
    { have[H1'[H2'[x'[y'[wrx[wr'[pd[mrg'[rd1 rd2]]]]]]]]]:=ihm _ _ _ _ _ _ dN H6 wr mrg H9.
      inv wrx.
      exists H1'. exists H2'. exists (App x' n). exists (App y' Box).
      repeat esplit...
      { apply: (star_hom (App^~ n)) rd1=>x y.
        apply: program_step_appL. }
      { apply: (star_hom (App^~ Box)) rd2=>x y.
        apply: program_step_appL. } }
    { inv H9. }
    { have[H1'[mrg' rs]]:=resolve_lookup H9 H6 mrg. inv rs.
      have[A0[n0 e]]:=erasure_lam0_form erm. subst.
      exists H1'. exists H2. exists (n0.[n/]). exists (m'0.[Box/]).
      repeat esplit...
      { have ern0:=erasure_lam0_inv erm.
        apply: erasure_esubst0... }
      { have ern:=erasure_lam0_inv erm.
        have wr':=lookup_wr H9 wr.
        have[wr1 wr2]:=wr_merge_inv mrg' wr'.
        have[Hx[k mrgx]]:=split_self H1'.
        have[_ wrx]:=wr_merge_inv mrgx wr1.
        apply: resolve_subst...
        constructor.
        constructor... }
      { apply: lookup_wr... }
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
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' s mrg1 erm ihm ern ihn H1 H2 H H' z z' dN rs wr mrg2 st.
    have[dN1 dN2]:=program_empty_split mrg1 dN. inv rs; inv st.
    { have//:=erasure_box_form ern. }
    { have//:=erasure_box_form ern. }
    { have//:=erasure_box_form ern. }
    { have[wr1 wr2]:=wr_merge_inv mrg2 wr.
      have[H4[mrg3 mrg4]]:=merge_splitR mrg2 H7.
      have[H1'[H2'[x'[y'[wrx[wr'[pd[mrg5[rd1 rd2]]]]]]]]]:=
        ihm _ _ _ _ _ _ dN1 H10 wr (merge_sym mrg4) H13.
      have[H1p[H2p[pd1[pd2 mrp]]]]:=pad_merge pd mrg3.
      have[Hx[mrp1 mrp2]]:=merge_splitL (merge_sym mrg5) mrp.
      inv wrx.
      exists Hx. exists H2p. exists (App x' n). exists (App y' n').
      repeat esplit...
      { have wf0:=program_type_wf (erasure_program_reflect H8).
        have wf2:=program_type_wf (erasure_program_reflect ern).
        have e:=program_wf_empty wf0 wf2 H6 dN2. subst.
        econstructor.
        apply: program_empty_self...
        apply: H8.
        apply: ern. }
      { econstructor.
        apply: merge_sym...
        apply: H9.
        apply: resolve_pad... }
      { apply: (star_hom (App^~ n)) rd1=>x y.
        apply: program_step_appL. }
      { apply: (star_hom (App^~ n')) rd2=>x y.
        apply: program_step_appL. } }
    { have[H4[mrg3 mrg4]]:=merge_splitL mrg2 H7.
      have[H1'[H2'[x'[y'[wrx[wr'[pd[mrg5[rd1 rd2]]]]]]]]]:=
        ihn _ _ _ _ _ _ dN2 H11 wr (merge_sym mrg4) H13.
      have[H1p[H2p[pd1[pd2 mrp]]]]:=pad_merge pd mrg3.
      have[Hx[mrp1 mrp2]]:=merge_splitL (merge_sym mrg5) mrp.
      inv wrx.
      exists Hx. exists H2p. exists (App m x'). exists (App m' y').
      repeat esplit...
      { have wf1:=program_type_wf (erasure_program_reflect erm).
        have wf0:=program_type_wf (erasure_program_reflect H8).
        have e:=program_wf_empty wf0 wf1 H6 dN1. subst.
        have[t tyP]:=program_valid (erasure_program_reflect erm).
        have[r[tyB/sort_inj e]]:=logical_pi1_inv tyP. subst.
        have tyn:=program_logical_reflect (erasure_program_reflect ern).
        have//=tyBn:=logical_subst tyB tyn.
        apply: erasure_conv.
        apply: logical_conv_beta.
        apply: conv_sym.
        apply: star_conv.
        apply: program_logical_red...
        econstructor...
        apply: program_empty_self...
        apply: tyBn. }
      { econstructor...
        apply: resolve_pad... }
      { have[wr1 wr2]:=wr_merge_inv mrg2 wr.
        have[wr0 wr3]:=wr_merge_inv H7 wr1.
        have vl':=wr_resolve_ptr wr0 H10.
        have vl:=erasure_program_val erm vl'.
        have[A0[n1 e]]:=
          program_pi1_canonical
            (erasure_program_reflect erm) (convR _ _) dN1 vl. subst.
        apply: (star_hom (App (Lam1 A0 n1 s))) rd1=>x y.
        apply: program_step_appR. }
      { have[wr1 wr2]:=wr_merge_inv mrg2 wr.
        have[wr0 wr3]:=wr_merge_inv H7 wr1.
        have vl':=wr_resolve_ptr wr0 H10.
        have vl:=erasure_program_val erm vl'.
        have[A0[n1 e]]:=
          program_pi1_canonical
            (erasure_program_reflect erm) (convR _ _) dN1 vl. subst.
        have[mx e]:=erasure_lam1_canonical erm. subst.
        apply: (star_hom (App (Lam1 Box mx s))) rd2=>x y.
        apply: program_step_appR. } }
    { have[Hx[mrg3 mrg4]]:=merge_splitR mrg2 H7.
      have[Hy[mrg5 rs]]:=resolve_lookup H13 H10 (merge_sym mrg4). inv rs.
      have[A0[n1 e]]:=erasure_lam0_form erm. subst.
      exfalso. apply: logical_lam0_pi1_false... }
    { have[H4[mrg3 mrg4]]:=merge_splitR mrg2 H7.
      have[H5[mrg rs]]:=resolve_lookup H13 H10 (merge_sym mrg4). inv rs.
      have[Hx[mrg5 mrg6]]:=merge_splitL (merge_sym mrg) mrg3.
      have[A0[n0 e]]:=erasure_lam1_form erm. subst.
      have[r ern0]:=erasure_lam1_inv erm.
      have wr':=lookup_wr H13 wr.
      have[wr1 wr2]:=wr_merge_inv mrg wr'.
      have[wr3 wr4]:=wr_merge_inv mrg3 wr2.
      have[H3'[k mrg']]:=split_self H3.
      have[_ wr3']:=wr_merge_inv mrg' wr3.
      have vl':=wr_resolve_ptr wr3 H11.
      have vl:=erasure_program_val ern vl'.
      exists Hx. exists H2. exists n0.[n/]. exists m'0.[n'/].
      repeat esplit...
      { have wf1:=program_type_wf (erasure_program_reflect erm).
        have wf2:=program_type_wf (erasure_program_reflect ern).
        have e:=program_wf_empty wf1 wf2 dN1 dN2. subst.
        apply: erasure_subst1.
        apply: program_empty_key.
        apply: dN2.
        apply: program_empty_self...
        apply: ern0.
        apply: ern. }
      { have wf:=program_type_wf (erasure_program_reflect ern0). inv wf.
        have k1:=resolution_stability (Well_resolved dN2 ern H11) H17 vl' wr3.
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
      { apply: star1. apply: program_step_beta1... }
      { apply: star1. apply: program_step_beta1... } } }
  { move=>Γ Δ A B m m' n t tyS erm ihm tyn H1 H2 H H' z z' dN rs wr mrg st.
    inv rs; inv st.
    { have[H1'[H2'[x'[y'[wrx[wr'[pd[mrg'[rd1 rd2]]]]]]]]]:=ihm _ _ _ _ _ _ dN H6 wr mrg H9.
      inv wrx.
      exists H1'. exists H2'. exists (Pair0 x' n t). exists (Pair0 y' Box t).
      repeat esplit...
      { have[s[r[ord[tyA[tyB _]]]]]:=logical_sig0_inv tyS.
        have tyx:=program_logical_reflect (program_rd (erasure_program_reflect erm) rd1).
        have//=tyBx:=logical_subst tyB tyx.
        constructor...
        apply: logical_conv.
        apply: logical_conv_beta.
        apply: star_conv.
        apply: (program_logical_red (erasure_program_reflect erm))...
        apply: tyn.
        apply: tyBx. }
      { apply: (star_hom ((Pair0^~ n)^~ t)) rd1=>x y.
        apply: program_step_pair0L. }
      { apply: (star_hom ((Pair0^~ Box)^~ t)) rd2=>x y.
        apply: program_step_pair0L. } }
    { have[e1 e2]:=merge_size mrg. destruct t.
      { exists (Pair0 (Ptr lm) Box U :U H1).
        exists (Pair0 (Ptr lm) Box U :U H2).
        exists (Pair0 m n U).
        exists (Pair0 m' Box U).
        repeat split...
        { econstructor...
          econstructor...
          apply: resolve_wkU... }
        { constructor... } }
      { exists (Pair0 (Ptr lm) Box L :L H1).
        exists (_: H2).
        exists (Pair0 m n L).
        exists (Pair0 m' Box L).
        repeat split...
        { econstructor...
          econstructor...
          constructor.
          apply: resolve_wkN... }
        { constructor... } } } }
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' t mrg1 tyS erm ihm ern ihn H1 H2 H H' z z' dN rs wr mrg2 st.
    have[s[r[ord1[ord2[tyA[tyB _]]]]]]:=logical_sig1_inv tyS.
    have[dN1 dN2]:=program_empty_split mrg1 dN. inv rs; inv st.
    { have[H4[mrg3 mrg4]]:=merge_splitR mrg2 H10.
      have[H1'[H2'[x'[y'[wrx[wr'[pd[mrg'[rd1 rd2]]]]]]]]]:=
        ihm _ _ _ _ _ _ dN1 H11 wr (merge_sym mrg4) H14. inv wrx.
      have[H1p[H2p[pd1[pd2 mrp]]]]:=pad_merge pd mrg3.
      have[Hx[mrp1 mrp2]]:=merge_splitL (merge_sym mrg') mrp.
      exists Hx. exists H2p. exists (Pair1 x' n t). exists (Pair1 y' n' t).
      repeat esplit...
      { have wf0:=program_type_wf (erasure_program_reflect H7).
        have wf2:=program_type_wf (erasure_program_reflect ern).
        have e:=program_wf_empty wf0 wf2 H6 dN2. subst.
        have tyx:=program_logical_reflect (program_rd (erasure_program_reflect erm) rd1).
        have//=tyBx:=logical_subst tyB tyx.
        econstructor...
        apply: program_empty_self...
        apply: erasure_conv.
        apply: logical_conv_beta.
        apply: star_conv.
        apply: (program_logical_red (erasure_program_reflect erm))...
        apply: ern.
        apply: tyBx. }
      { econstructor.
        apply: merge_sym...
        apply: H8.
        apply: resolve_pad... }
      { apply: (star_hom ((Pair1^~ n)^~ t)) rd1=>x y.
        apply: program_step_pair1L. }
      { apply: (star_hom ((Pair1^~ n')^~ t)) rd2=>x y.
        apply: program_step_pair1L. } }
    { have[H4[mrg3 mrg4]]:=merge_splitL mrg2 H10.
      have[H1'[H2'[x'[y'[wrx[wr'[pd[mrg'[rd1 rd2]]]]]]]]]:=
        ihn _ _ _ _ _ _ dN2 H12 wr (merge_sym mrg4) H14. inv wrx.
      have[H1p[H2p[pd1[pd2 mrp]]]]:=pad_merge pd mrg3.
      have[Hx[mrp1 mrp2]]:=merge_splitL (merge_sym mrg') mrp.
      exists Hx. exists H2p. exists (Pair1 m x' t). exists (Pair1 m' y' t).
      repeat esplit...
      { have wf0:=program_type_wf (erasure_program_reflect H7).
        have wf1:=program_type_wf (erasure_program_reflect erm).
        have e:=program_wf_empty wf0 wf1 H6 dN1. subst.
        econstructor...
        apply: program_empty_self... }
      { econstructor...
        apply: resolve_pad... }
      { apply: (star_hom (Pair1 m^~ t)) rd1=>x y.
        apply: program_step_pair1R. }
      { apply: (star_hom (Pair1 m'^~ t)) rd2=>x y.
        apply: program_step_pair1R. } }
    { have[e1 e2]:=merge_size mrg2. destruct t.
      { exists (Pair1 (Ptr lm) (Ptr ln) U :U H1).
        exists (Pair1 (Ptr lm) (Ptr ln) U :U H2).
        exists (Pair1 m n U).
        exists (Pair1 m' n' U).
        repeat split...
        { econstructor. apply: dN.
          econstructor...
          econstructor...
          apply: resolve_wkU... }
        { constructor... } }
      { exists (Pair1 (Ptr lm) (Ptr ln) L :L H1).
        exists (_: H2).
        exists (Pair1 m n L).
        exists (Pair1 m' n' L).
        repeat split...
        { econstructor. apply: dN.
          econstructor...
          econstructor...
          apply: resolve_wkN... }
        { constructor... } } } }
  { move=>Γ Δ1 Δ2 Δ A B C m m' n n' s r t mrg1 tyC
      erm ihm ern _ H1 H2 H H' z z' dN rs wr mrg2 st.
    have[dN1 dN2]:=program_empty_split mrg1 dN. inv rs; inv st.
    { have[H4[mrg3 mrg4]]:=merge_splitR mrg2 H7.
      have[H1'[H2'[x'[y'[wrx[wr'[pd[mrg'[rd1 rd2]]]]]]]]]:=
        ihm _ _ _ _ _ _ dN1 H10 wr (merge_sym mrg4) H13. inv wrx.
      have[H1p[H2p[pd1[pd2 mrp]]]]:=pad_merge pd mrg3.
      have[Hx[mrp1 mrp2]]:=merge_splitL (merge_sym mrg') mrp.
      exists Hx. exists H2p. exists (LetIn C x' n). exists (LetIn Box y' n').
      repeat esplit...
      { have wf2:=program_type_wf (erasure_program_reflect ern). inv wf2. inv H15.
        have wf0:=program_type_wf (erasure_program_reflect H8).
        have e:=program_wf_empty wf0 H17 H6 dN2. subst.
        apply: erasure_conv.
        apply: logical_conv_beta.
        apply: conv_sym.
        apply: star_conv.
        apply: program_logical_red...
        apply: erasure_letin0...
        apply: program_empty_self...
        apply: logical_esubst...
        autosubst. }
      { econstructor.
        apply: merge_sym...
        apply: H9.
        apply: resolve_pad... }
      { apply: (star_hom (LetIn C^~ n)) rd1=>x y.
        apply: program_step_letinL. }
      { apply: (star_hom (LetIn Box^~ n')) rd2=>x y.
        apply: program_step_letinL. } }
    { have[H4[mrg3 mrg4]]:=merge_splitR mrg2 H7.
      have[H1'[mrg' rs]]:=resolve_lookup H13 H10 (merge_sym mrg4). inv rs.
      have[Hx[mrg5 mrg6]]:=merge_splitL (merge_sym mrg') mrg3.
      have[m1[m2 e]]:=erasure_pair0_form erm. subst.
      have[e[_[erm1 tym2]]]:=erasure_pair0_inv erm. subst.
      have wr':=lookup_wr H13 wr.
      have[wr1 wr2]:=wr_merge_inv mrg2 wr.
      have[wr3 wr4]:=wr_merge_inv H7 wr1.
      have[wr5 wr6]:=wr_merge_inv mrg' wr'.
      have vl:=wr_resolve_ptr wr5 H15.
      have wf:=program_type_wf (erasure_program_reflect ern). inv wf.  inv H9.
      have k1:=resolution_stability (Well_resolved dN1 erm1 H15) H17 vl wr5.
      have[H2'[k mrg2']]:=split_self H1'.
      have[_ wr7]:=wr_merge_inv mrg2' wr5.
      exists Hx. exists H2. exists n.[m2,m1/]. exists (n'.[Box,m'0/]).
      repeat esplit...
      { have[<-eq]:=merge_size mrg1.
        have e:=program_empty_uniq dN2 dN1 eq. subst.
        replace C.[Pair0 m1 m2 t/] with
          C.[Pair0 (Var 1) (Var 0) t .: ren (+2)].[m2,m1/] by autosubst.
        apply: erasure_substitution.
        apply: ern.
        constructor.
        econstructor.
        apply: program_empty_key.
        all: eauto...
        apply: program_empty_self...
        asimpl... }
      { destruct r.
        { apply: resolve_subst...
          constructor.
          econstructor.
          apply: merge_sym mrg2'.
          all: eauto.
          constructor... }
        { apply: resolve_subst...
          constructor.
          econstructor.
          apply: merge_sym mrg2'.
          all: eauto.
          constructor... } }
      { apply: star1.
        constructor.
        constructor.
        apply: erasure_program_val... }
      { apply: star1.
        constructor.
        constructor... } }
    { have[H4[mrg3 mrg4]]:=merge_splitR mrg2 H7.
      have[H1'[mrg' rs]]:=resolve_lookup H13 H10 (merge_sym mrg4). inv rs.
      have[m1[m2 e]]:=erasure_pair1_form erm. subst.
      exfalso. apply: logical_pair1_sig0_false... } }
  { move=>Γ Δ1 Δ2 Δ A B C m m' n n' s r1 r2 t mrg1 tyC
      erm ihm ern _ H1 H2 H H' z z' dN rs wr mrg2 st.
    have[dN1 dN2]:=program_empty_split mrg1 dN. inv rs; inv st.
    { have[H4[mrg3 mrg4]]:=merge_splitR mrg2 H7.
      have[H1'[H2'[x'[y'[wrx[wr'[pd[mrg'[rd1 rd2]]]]]]]]]:=
        ihm _ _ _ _ _ _ dN1 H10 wr (merge_sym mrg4) H13. inv wrx.
      have[H1p[H2p[pd1[pd2 mrp]]]]:=pad_merge pd mrg3.
      have[Hx[mrp1 mrp2]]:=merge_splitL (merge_sym mrg') mrp.
      exists Hx. exists H2p. exists (LetIn C x' n). exists (LetIn Box y' n').
      repeat esplit...
      { have wf0:=program_type_wf (erasure_program_reflect H8).
        have wf2:=program_type_wf (erasure_program_reflect ern). inv wf2. inv H15.
        have e:=program_wf_empty wf0 H16 H6 dN2. subst.
        apply: erasure_conv.
        apply: logical_conv_beta.
        apply: conv_sym.
        apply: star_conv.
        apply: program_logical_red...
        apply: erasure_letin1...
        apply: program_empty_self...
        apply: logical_esubst...
        autosubst. }
      { econstructor.
        apply: merge_sym...
        apply: H9.
        apply: resolve_pad... }
      { apply: (star_hom (LetIn C^~ n)) rd1=>x y.
        apply: program_step_letinL. }
      { apply: (star_hom (LetIn Box^~ n')) rd2=>x y.
        apply: program_step_letinL. } }
    { have[H4[mrg3 mrg4]]:=merge_splitR mrg2 H7.
      have[H1'[mrg' rs]]:=resolve_lookup H13 H10 (merge_sym mrg4). inv rs.
      have[m1[m2 e]]:=erasure_pair0_form erm. subst.
      exfalso. apply: logical_pair0_sig1_false... }
    { have[H4[mrg3 mrg4]]:=merge_splitR mrg2 H7.
      have[H1'[mrg' rs]]:=resolve_lookup H13 H10 (merge_sym mrg4). inv rs.
      have[Hx[mrg5 mrg6]]:=merge_splitL (merge_sym mrg') mrg3.
      have[m1[m2 e]]:=erasure_pair1_form erm. subst.
      have[Δ1'[Δ2'[mrg[e[erm1 erm2]]]]]:=erasure_pair1_inv erm. subst.
      have[dN1' dN2']:=program_empty_split mrg dN1.
      have wr':=lookup_wr H13 wr.
      have[wr1 wr2]:=wr_merge_inv mrg2 wr.
      have[wr3 wr4]:=wr_merge_inv H7 wr1.
      have[wr5 wr6]:=wr_merge_inv mrg' wr'.
      have[wr7 wr8]:=wr_merge_inv H16 wr5.
      have vm:=wr_resolve_ptr wr7 H18.
      have vn:=wr_resolve_ptr wr8 H19.
      have wf:=program_type_wf (erasure_program_reflect ern). inv wf.  inv H14.
      have k1:=resolution_stability (Well_resolved dN1' erm1 H18) H21 vm wr7.
      have//=tyBm1:=logical_subst H17 (program_logical_reflect (erasure_program_reflect erm1)).
      have k2:=resolution_stability (Well_resolved dN2' erm2 H19) tyBm1 vn wr8.
      have[H5'[k5 mrg5']]:=split_self H5.
      have[H6'[k6 mrg6']]:=split_self H6.
      have[_ wr5']:=wr_merge_inv mrg5' wr7.
      have[_ wr6']:=wr_merge_inv mrg6' wr8.
      exists Hx. exists H2. exists n.[m2,m1/]. exists (n'.[n'0,m'0/]).
      repeat esplit...
      { have[<-sz0]:=merge_size mrg1.
        have[sz1 sz2]:=merge_size mrg.
        rewrite<-sz0 in sz2.
        have e:=program_empty_uniq dN2 dN1 sz0. subst.
        have e:=program_empty_uniq dN1' dN1 sz1. subst.
        have e:=program_empty_uniq dN2' dN2 sz2. subst.
        replace C.[Pair1 m1 m2 t/] with
          C.[Pair1 (Var 1) (Var 0) t .: ren (+2)].[m2,m1/] by autosubst.
        apply: erasure_substitution.
        apply: ern.
        econstructor.
        apply: program_empty_key.
        apply: dN2'.
        apply: program_empty_self...
        econstructor.
        apply: program_empty_key.
        apply: dN2'.
        apply: program_empty_self...
        all: eauto...
        asimpl... }
      { destruct r1; destruct r2.
        { apply: resolve_subst...
          econstructor...
          econstructor.
          apply: merge_sym mrg5'.
          all: eauto.
          constructor... }
        { apply: resolve_subst...
          econstructor...
          econstructor.
          apply: merge_sym mrg5'.
          all: eauto.
          constructor... }
        { apply: resolve_subst...
          econstructor...
          econstructor.
          apply: merge_sym mrg5'.
          all: eauto.
          constructor... }
        { apply: resolve_subst...
          econstructor...
          econstructor.
          apply: merge_sym mrg5'.
          all: eauto.
          constructor... } }
      { apply: star1.
        constructor.
        constructor.
        apply: erasure_program_val...
        apply: erasure_program_val... }
      { apply: star1.
        constructor.
        constructor... } } }
  { move=>Γ Δ A B m m' n n' t _ erm ihm ern ihn H1 H2 H H' z z' dN rs wr mrg st; subst.
    inv rs; inv st.
    have[<-_]:=merge_size mrg.
    have[wr1 wr2]:=wr_merge_inv mrg wr.
    destruct t.
    { exists (APair m0 n0 U :U H1).
      exists (APair m0 n0 U :U H2).
      exists (APair m n U).
      exists (APair m' n' U).
      repeat esplit...
      { econstructor...
        apply: program_empty_key... }
      { econstructor...
        constructor...
        apply: resolve_wkU...
        apply: resolve_wkU... }
      { have dNi:program_iempty Δ 0...
        have//=nfm':=nf_typing erm dNi.
        have//=nfn':=nf_typing ern dNi.
        constructor...
        have//:=resolve_wr_nfi H9 wr1 nfm'.
        have//:=resolve_wr_nfi H10 wr1 nfn'. } }
    { exists (APair m0 n0 L :L H1).
      exists (_: H2).
      exists (APair m n L).
      exists (APair m' n' L).
      repeat esplit...
      { econstructor...
        apply: program_empty_key... }
      { econstructor...
        constructor...
        apply: resolve_wkN...
        apply: resolve_wkN... }
      { have dNi:program_iempty Δ 0...
        have//=nfm':=nf_typing erm dNi.
        have//=nfn':=nf_typing ern dNi.
        constructor...
        have//:=resolve_wr_nfi H9 wr1 nfm'.
        have//:=resolve_wr_nfi H10 wr1 nfn'. } } }
  { move=>Γ Δ A B m m' t erm ihm H1 H2 H H' z z' dN rs wr mrg st; subst.
    inv rs; inv st.
    { have[H1'[H2'[x'[y'[wrx[wr'[pd[mrg'[rd1 rd2]]]]]]]]]:=
        ihm _ _ _ _ _ _ dN H6 wr mrg H5. inv wrx.
      exists H1'. exists H2'. exists (Fst x'). exists (Fst y').
      repeat esplit...
      { apply: (star_hom Fst) rd1=>x y.
        apply: program_step_fst. }
      { apply: (star_hom Fst) rd2=>x y.
        apply: program_step_fst. } }
    { have[H2'[mrg' rs]]:=resolve_lookup H5 H6 mrg. inv rs.
      have[m1[m2 e]]:=erasure_apair_form erm. subst.
      have[e[erm1 erm2]]:=erasure_apair_inv erm. subst.
      have wr':=lookup_wr H5 wr.
      exists H2'. exists H2. exists m1. exists m'0.
      repeat esplit...
      { apply: star1.
        apply: program_step_proj1. }
      { apply: star1.
        apply: program_step_proj1. } } }
  { move=>Γ Δ A B m m' t erm ihm H1 H2 H H' z z' dN rs wr mrg st; subst.
    inv rs; inv st.
    { have[H1'[H2'[x'[y'[wrx[wr'[pd[mrg'[rd1 rd2]]]]]]]]]:=
        ihm _ _ _ _ _ _ dN H6 wr mrg H5. inv wrx.
      exists H1'. exists H2'. exists (Snd x'). exists (Snd y').
      repeat esplit...
      { apply: (star_hom Snd) rd1=>x y.
        apply: program_step_snd. }
      { apply: (star_hom Snd) rd2=>x y.
        apply: program_step_snd. } }
    { have[H2'[mrg' rs]]:=resolve_lookup H5 H6 mrg. inv rs.
      have[n1[n2 e]]:=erasure_apair_form erm. subst.
      have[e[ern1 ern2]]:=erasure_apair_inv erm. subst.
      have wr':=lookup_wr H5 wr.
      exists H2'. exists H2. exists n2. exists n'.
      repeat esplit...
      { apply: star1.
        apply: program_step_proj2. }
      { apply: star1.
        apply: program_step_proj2. } } }
  { move=>Γ Δ A B x x' P m n s h tyB erx ihx tyP H1 H2 H H' z z' dN rs wr mrg st.
    inv rs; inv st.
    exists H1. exists H2. exists x. exists x'.
    repeat split...
    { econstructor...
      have[P0[rdP vlP]]:=logical_vn tyP h.
      have tyP0:=logical_rd tyP rdP.
      have[n0 e]:=logical_id_canonical tyP0 (convR _ _)
                    (logical_red_closed rdP h) vlP. subst.
      have tyr:=logical_rd tyP rdP.
      have[r tyI]:=logical_valid tyP.
      have[tym[tyn/sort_inj e]]:=logical_id_inv tyI. subst.
      have[tym0[eq1 eq2]]:=logical_refl_inv tyr.
      have sc:sconv (Refl m .: m .: ids) (P .: n .: ids).
      { move=>[|[|]]//=.
        apply: conv_trans. apply: logical_conv_refl. apply: conv_sym...
        apply: conv_sym. apply: star_conv...
        apply: conv_trans. apply: conv_sym... eauto. }
      have wkB:Γ ⊢ B.[P,n/] : Sort s.
      { replace (Sort s) with (Sort s).[P,n/] by eauto.
        apply: logical_substitution...
        repeat constructor...
        all: asimpl... }
      apply: erasure_conv.
      apply: logical_conv_compat sc.
      all: eauto. }
    { apply: star1.
      apply: program_step_rwE. }
    { apply: star1.
      apply: program_step_rwE. } }
  { move=>Γ Δ A B m m' s eq erm ihm tyB H1 H2 H H' z z' dN rs wr mrg st; subst.
    have[H1'[H2'[x'[y'[wrx[wr'[pd[mrg'[rd1 rd2]]]]]]]]]:=
      ihm _ _ _ _ _ _ dN rs wr mrg st. inv wrx.
    exists H1'. exists H2'. exists x'. exists y'.
    repeat esplit... }
Qed.

(* Theorem 14 (Heap Subject Reduction) *)
Theorem heap_sr Γ H H' x y z z' A :
  Γ ; H ⊢ x ~ y ~ z : A -> wr_heap H ->
  H ; z ~>> H' ; z' ->
  exists x' y', Γ ; H' ⊢ x' ~ y' ~ z' : A /\ wr_heap H' /\ x ~>>* x' /\ y ~>>* y'.
Proof with eauto.
  move=>wrx wr st.
  have[H0[k mrg]]:=split_self H.
  have[H1'[H2'[x'[y'[wrx'[wr'[pd[mrg'[rd1 rd2]]]]]]]]]:=heap_srX wrx wr mrg st.
  have k':=pad_key pd k.
  have e:=merge_pureR mrg' k'. subst.
  exists x'. exists y'...
Qed.
