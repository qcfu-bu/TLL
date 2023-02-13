From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq zify.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS
  dyn_sr proc_type proc_step proc_occurs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma proc_congr0_sym p q : proc_congr0 p q -> proc_congr0 q p.
Proof. elim; intros; eauto using proc_congr0. Qed.

Lemma proc_congr0_type Θ p q : Θ ⊢ p -> proc_congr0 p q -> Θ ⊢ q.
Proof with eauto using proc_type, proc_congr0.
  move=>ty. elim: ty q=>{Θ p}.
  { move=>Θ m tym q cgr. inv cgr.
    have[Θ0[emp mrg]]:=dyn_type_empty tym.
    econstructor.
    apply: merge_sym...
    all: repeat constructor... }
  { move=>Θ1 Θ2 Θ p q mrg typ ihp tyq ihq q0 cgr. inv cgr.
    { econstructor. apply: merge_sym. all: eauto. }
    { inv tyq.
      have[Θ4[mrg1 mrg2]]:=merge_splitL (merge_sym mrg) H1.
      econstructor. apply: mrg2.
      econstructor. apply: merge_sym mrg1.
      all: eauto. }
    { inv typ.
      have[Θ4[mrg1 mrg2]]:=merge_splitR mrg H1.
      econstructor. apply: (merge_sym mrg2). apply: H3.
      econstructor... }
    { inv typ.
      have wf:=proc_type_wf H2. inv wf. inv H1.
      have mrg': 
        Ch (~~r2) (term_cren A (+1)) :L Ch r2 A :L Θ1 ∘ _: _: Θ2 =>
        Ch (~~r2) (term_cren A (+1)) :L Ch r2 A :L Θ.
      repeat econstructor; eauto.
      econstructor...
      econstructor...
      replace (proc_cren q (+2)) with (proc_cren (proc_cren q (+1)) (+1)).
      apply: proc_cweaken.
      apply: proc_cweaken...
      rewrite<-proc_cren_comp.
      by asimpl. }
    { econstructor... }
    { econstructor.
      apply: mrg.
      apply: ihp. apply: proc_congr0_sym...
      apply: ihq. apply: proc_congr0_sym... }
    { inv tyq.
      have ty:=dyn_return_inv H1.
      have emp:=dyn_ii_inv ty.
      have e:=merge_emptyR mrg emp. subst... }
    { have wf1:=proc_type_wf typ.
      have wf2:=proc_type_wf tyq.
      have[Θ3[emp1 mrg1]]:=proc_wf_empty wf1.
      have[Θ4[emp2 mrg2]]:=proc_wf_empty wf2.
      have[Θ5[Θ6[mrg3[mrg4 mrg5]]]]:=merge_distr mrg mrg1 mrg2.
      have e:=merge_emptyL mrg4 emp1. subst.
      have e:=merge_emptyR mrg4 emp2. subst.
      econstructor.
      apply: merge_sym mrg3.
      econstructor...
      repeat constructor... } }
  { move=>Θ p r1 r2 A d typ ihp q cgr. inv cgr.
    { inv typ. inv H1; inv H5.
      { econstructor. apply: H2.
        econstructor...
        apply: proc_cstrengthen.
        apply: proc_cstrengthen.
        rewrite<-proc_cren_comp.
        by asimpl. }
      { have oc:=proc_occurs_iren H4 iren1.
        have pos:=proc_occurs_pos0 oc.
        inv pos. inv H6. }
      { have oc:=proc_occurs_iren H4 iren0.
        have pos:=proc_occurs_pos0 oc.
        inv pos. }
      { have oc:=proc_occurs_iren H4 iren0.
        have pos:=proc_occurs_pos0 oc.
        inv pos. } }
    { econstructor... }
    { have{}ihp:=ihp _ (proc_congr0_sym H0).
      econstructor... }
    { have wf:=proc_type_wf typ. inv wf. inv H1.
      have[Θ0[emp mrg]]:=proc_wf_empty H2.
      econstructor.
      apply: merge_sym mrg.
      eauto...
      repeat constructor... } }
Qed.

Lemma proc_congr_type Θ p q : Θ ⊢ p -> p ≡ q -> Θ ⊢ q.
Proof with eauto.
  move=>ty e. elim: e Θ ty=>//={q}.
  { move=>y z e ih cr Θ typ.
    apply: proc_congr0_type.
    apply: ih...
    apply: cr. }
  { move=>y z e ih cr Θ typ.
    apply: proc_congr0_type.
    apply: ih...
    apply: proc_congr0_sym... }
Qed.

Theorem proc_sr Θ p q : Θ ⊢ p -> p ≈>> q -> Θ ⊢ q.
Proof with eauto using merge, merge_sym, sta_type, dyn_type.
  move=>ty st. elim: st Θ ty=>{p q}.
  { move=>m m' st Θ ty. inv ty.
    constructor. apply: dyn_sr... }
  { move=>v n vl Θ ty. inv ty.
    have[Θ1[Θ2[Δ1[Δ2[A0[s[/merge_sym mrg1[mrg2[tyR/=tyn]]]]]]]]]:=
      dyn_bind_inv H1. inv mrg2.
    have wf:=dyn_type_wf tyn. inv wf.
    have tyv:=dyn_return_inv tyR.
    have[r tyA]:=dyn_valid tyv.
    have e:=sta_unicity H5 tyA. subst.
    have[k1 k2]:=dyn_val_stability tyv tyA vl.
    have tyIO:(A0 :: nil) ⊢ (IO Unit).[ren (+1)] : (Sort L).[ren (+1)].
    { apply: sta_weaken... }
    constructor.
    replace (IO Unit) with (IO Unit).[v/] by eauto.
    apply: dyn_subst1.
    apply: k1.
    apply: mrg1.
    apply: k2.
    constructor.
    replace (IO Unit) with (IO Unit.[ren (+1)]) by eauto.
    apply: dyn_conv.
    apply: sta_conv_io. apply: sta_conv_subst. apply: conv_sym...
    apply: tyn.
    apply: tyIO.
    apply: dyn_conv.
    apply: conv_sym...
    all: eauto. }
  { move=>A m m' n n' e1 e2 Θ ty. inv ty.
    have{H1}ty:=dyn_cweaken (dyn_cweaken H1).
    rewrite<-!term_cren_comp in ty.
    asimpl in ty.
    have[Θ1[Θ2[Δ1[Δ2[A0[s[mrg1[mrg2[tyF/=tyn]]]]]]]]]:=
      dyn_bind_inv ty. inv mrg2. inv mrg1. inv H2.
    have[tym/io_inj eq2]:=dyn_fork_inv tyF.
    have mrg0: Ch (~~ true) (term_cren A (+1)) :L _: Δ3 ∘ _: Ch true A :L Δ0 =>
               Ch (~~ true) (term_cren A (+1)) :L Ch true A :L Θ.
    { econstructor. econstructor. apply: merge_sym... }
    econstructor...
    econstructor...
    { have wf:=dyn_type_wf tyn. inv wf.
      have wf:=dyn_type_wf tym. inv wf.
      have wf:=dyn_type_proc_wf tyn. inv wf. inv H0.
      have[Θ0[emp mrg1]]:=proc_wf_empty H1.
      have{}mrg1: _: _: Δ3 ∘ Ch (~~ true) (term_cren A (+1)) :L _: Θ0 =>
                  Ch (~~ true) (term_cren A (+1)) :L _: Δ3...
      have[tyA _]:=sta_ch_inv H7.
      have[x eq3 eq4]:=church_rosser eq2.
      have tyx1:=sta_prd H5 eq3.
      have tyx2:=sta_prd (sta_ch false tyA) eq4.
      have e:=sta_unicity tyx1 tyx2. subst.
      have tyIO:(A0 :: nil) ⊢ (IO Unit).[ren (+1)] : (Sort L).[ren (+1)].
      { apply: sta_weaken... }
      have/=js: dyn_just
                  (Ch (~~ true) (term_cren A (+1)) :L _: Θ0) 0
                  (term_cren (Ch (~~ true) (term_cren A (+1))) (+1)).
      { constructor. constructor... }
      rewrite<-term_cren_comp in js. asimpl in js.
      econstructor.
      replace (IO Unit) with (IO Unit).[CVar 0/] by eauto.
      apply: dyn_esubst1...
      constructor.
      apply: key_impure.
      apply: key_impure.
      replace (IO Unit) with (IO Unit.[ren (+1)]) by eauto.
      apply: dyn_conv.
      apply: conv_sym...
      replace (Ch false (term_cren A (+2)))
        with (Ch false (term_cren A (+2)).[ren (+0)])
        by autosubst.
      repeat constructor...
      apply: H5. }
    { have wf:=dyn_type_wf tyn. inv wf.
      have wf:=dyn_type_wf tym. inv wf.
      have wf:=dyn_type_proc_wf tym. inv wf. inv H0.
      have[Θx[emp mrg1]]:=proc_wf_empty H1.
      have{}mrg1: _: _: Δ0 ∘ _: Ch true A :L Θx => _: Ch true A :L Δ0...
      have[tyA _]:=sta_ch_inv H7.
      have[x eq3 eq4]:=church_rosser eq2.
      have tyx1:=sta_prd H5 eq3.
      have tyx2:=sta_prd (sta_ch false tyA) eq4.
      have e:=sta_unicity tyx1 tyx2. subst.
      econstructor.
      replace (IO Unit) with (IO Unit).[CVar 1/] by eauto.
      apply: dyn_esubst1...
      apply: key_impure.
      apply: key_impure.
      replace (Ch true (term_cren A (+2)))
        with (Ch true (term_cren A (+2)).[ren (+0)])
        by autosubst.
      repeat constructor...
      replace (Ch true (term_cren A (+2)))
        with (term_cren (Ch true (term_cren A (+1))) (+1)).
      repeat constructor...
      simpl. rewrite<-term_cren_comp.
      by autosubst. } }
  { move=>m n1 n2 Θ ty. inv ty. inv H2. inv H1; inv H3.
    { inv H5.
      have[Θ1[Θ2[Δ1[Δ2[A0[s[mrg1[mrg2[tyR/=tyn]]]]]]]]]:=
        dyn_bind_inv H1. inv mrg2. inv mrg1; inv H5.
      have[r3[r4[A1[B0[_[_ tyv]]]]]]:=dyn_recv0_inv tyR.
      have[r[A2[js _]]]:=dyn_cvar_inv tyv. inv js. inv H5. }
    { inv H4. inv H5.
      have[Θ1[Θ2[Δ1[Δ2[A0[s[mrg1[mrg2[tyApp/=tyn1]]]]]]]]]:=
        dyn_bind_inv H1. inv mrg2. inv mrg1; inv H5.
      2:{ have[A1[B1[s1[[tyS _]|[Θ1[Θ2[Δ1[Δ2[mrg1[mrg2[tyS _]]]]]]]]]]]:=dyn_app_inv tyApp.
          have[r3[r4[A2[B2[_[_ ty]]]]]]:=dyn_send0_inv tyS.
          have[r[A3[js _]]]:=dyn_cvar_inv ty. inv js.
          inv mrg1. inv H5.
          have[r3[r4[A2[B2[_[_ ty]]]]]]:=dyn_send0_inv tyS.
          have[r[A3[js _]]]:=dyn_cvar_inv ty. inv js. }
      have[A1[B1[s1[[tyS[tym eq2]]|[Θ1[Θ2[Δ1[Δ2[mrg1[mrg2[tyS[tym eq2]]]]]]]]]]]]:=dyn_app_inv tyApp.
      2:{ have[r3[r4[A2[B2[_[eq _]]]]]]:=dyn_send0_inv tyS.
          exfalso. solve_conv. }
      have[r3[r4[A2[B2[xor1[/pi0_inj[eqA1[eqB1 e]]tyv0]]]]]]:=dyn_send0_inv tyS. subst.
      have[r[A3[js[tyA eq3]]]]:=dyn_cvar_inv tyv0. inv js. inv H5.
      have e:=merge_emptyL H6 H0. subst.
      rewrite<-term_cren_comp in eq3. asimpl in eq3.
      rewrite<-term_cren_comp in tyA. asimpl in tyA.
      have[e eq4]:=ch_inj eq3. subst.
      have[Θ3[Θ4[Δ1[Δ2[A3[s0[mrg1[mrg2[tyR/=tyn2]]]]]]]]]:=
        dyn_bind_inv H3. inv mrg2. inv mrg1. inv H7.
      2:{ have[r5[r6[A4[B4[_[_ tyv1]]]]]]:=dyn_recv0_inv tyR.
          have[r[A5[js _]]]:=dyn_cvar_inv tyv1. inv js. inv H7. }
      have[r5[r6[A4[B4[xor2[/io_inj eq6 tyv1]]]]]]:=dyn_recv0_inv tyR.
      have[r[A5[js[tyA5/ch_inj[e eq7]]]]]:=dyn_cvar_inv tyv1. subst.
      asimpl in eq7. inv js. inv H7.
      have e:=merge_emptyL H8 H4. subst.
      have[Δ6[Δ7[_[mrg0 _]]]]:=merge_distr H2 H6 H8.
      have e:=merge_emptyL mrg0 H0. subst.
      have e:=merge_emptyR mrg0 H4. subst. clear mrg0.
      rewrite<-term_cren_comp in H5. asimpl in H5. inv H5.
      have/act0_inj[eqA2[eqB2 e]]:=conv_trans _ eq4 (conv_sym eq7). subst.
      have/=/io_inj eqA0:=conv_trans _ eq2 (sta_conv_subst (m .: ids) eqB1).
      have wf:=dyn_type_proc_wf tyv1. inv wf. inv H5.
      have[s1 tyCh1]:=dyn_valid tyv0.
      have[s2 tyCh2]:=dyn_valid tyv1.
      have{tyCh1}[/sta_act0_inv tyB2/sort_inj e]:=sta_ch_inv tyCh1. subst.
      have{tyCh2}[/sta_act0_inv tyB4/sort_inj e]:=sta_ch_inv tyCh2.
      have wf:=dyn_type_wf tyn1. inv wf.
      have wf:=dyn_type_wf tyn2. inv wf.
      have wf:=sta_type_wf tyB2. inv wf.
      have wf:=sta_type_wf tyB4. inv wf.
      have/=tyB2m:=sta_subst tyB2 (sta_conv eqA1 tym H14).
      have tyChB2:=sta_ch (~~r) tyB2m.
      have/=tyB4m:=sta_subst tyB4 (sta_conv (conv_trans _ eqA1 eqA2) tym H17).
      have tyChB4:=sta_ch r tyB4m.
      econstructor...
      econstructor.
      2:{ constructor.
          econstructor.
          2:{ constructor. }
          2:{ constructor... }
          3:{ apply: tyn1. }
          2:{ constructor.
              apply: dyn_conv.
              apply: conv_trans.
              apply: sta_cren_conv0.
              apply: (+2).
              apply: convR _.
              apply: conv_sym...
              simpl.
              replace (term_cren B2.[m/] (+2))
                with (term_cren B2.[m/] (+2)).[ren (+0)] by autosubst.
              repeat constructor.
              replace (Ch (~~ r) (term_cren B2.[m/] (+2)))
                with (term_cren (Ch (~~ r) (term_cren B2.[m/] (+1))) (+1)).
              2:{ simpl. rewrite<-term_cren_comp. autosubst. }
              eapply dyn_just_O.
              apply: dyn_empty_n...
              apply: sta_crename0...
              apply: H13. }
          repeat constructor... }
      constructor.
      constructor.
      apply: merge_sym...
      constructor.
      econstructor.
      2:{ constructor. }
      4:{ apply: tyn2. }
      2:{ constructor... }
      repeat constructor...
      constructor.
      apply: dyn_conv.
      apply: conv_sym...
      constructor.
      econstructor...
      apply: sta_conv.
      apply: conv_trans.
      apply: eqA1.
      apply: eqA2.
      apply: tym.
      apply: H17.
      2:{ eauto. }
      apply: dyn_conv.
      apply: sta_conv_subst.
      apply: sta_conv_ch.
      apply: eqB2.
      2:{ eauto. }
      apply: dyn_conv.
      apply: sta_cren_conv0.
      apply: (+2).
      eauto.
      rewrite term_cren_beta1.
      simpl.
      replace (term_cren B2 (+2)).[term_cren m (+2)/]
        with (term_cren B2 (+2)).[term_cren m (+2)/].[ren (+0)] by autosubst.
      repeat constructor.
      rewrite<-term_cren_beta1.
      replace (Ch r (term_cren B2.[m/] (+2)))
        with (term_cren (Ch r (term_cren B2.[m/] (+1))) (+1)).
      repeat constructor...
      simpl. rewrite<-term_cren_comp. asimpl...
      rewrite<-term_cren_beta1.
      apply: sta_crename0...
      constructor... }
    { inv H4.
      have[Θ1[Θ2[Δ1[Δ2[A0[s[mrg1[mrg2[tyApp/=tyn]]]]]]]]]:=
        dyn_bind_inv H1. inv mrg2. inv mrg1.
      have[A1[B1[s0[[tyS _]|[Θ3[Θ4[Δ5[Δ6[mrg1[mrg2[tyS _]]]]]]]]]]]:=dyn_app_inv tyApp.
      have[r3[r4[A2[B2[_[_ tyv]]]]]]:=dyn_send0_inv tyS.
      have[r[A3[js _]]]:=dyn_cvar_inv tyv. inv js.
      inv mrg1.
      have[r3[r4[A2[B2[_[_ tyv]]]]]]:=dyn_send0_inv tyS.
      have[r[A3[js _]]]:=dyn_cvar_inv tyv. inv js. }
    { inv H4.
      have[Θ1[Θ2[Δ1[Δ2[A0[s[mrg1[mrg2[tyApp/=tyn]]]]]]]]]:=
        dyn_bind_inv H1. inv mrg2. inv mrg1.
      have[A1[B1[s0[[tyS _]|[Θ3[Θ4[Δ5[Δ6[mrg1[mrg2[tyS _]]]]]]]]]]]:=dyn_app_inv tyApp.
      have[r3[r4[A2[B2[_[_ tyv]]]]]]:=dyn_send0_inv tyS.
      have[r[A3[js _]]]:=dyn_cvar_inv tyv. inv js.
      inv mrg1.
      have[r3[r4[A2[B2[_[_ tyv]]]]]]:=dyn_send0_inv tyS.
      have[r[A3[js _]]]:=dyn_cvar_inv tyv. inv js. } }
  { move=>m n1 n2 Θ ty. inv ty. inv H2. inv H1; inv H3.
    { inv H5.
      have[Θ1[Θ2[Δ1[Δ2[A0[s[mrg1[mrg2[tyR/=tyn]]]]]]]]]:=
        dyn_bind_inv H1. inv mrg2. inv mrg1.
      have[r3[r4[A1[B1[_[_ tyv]]]]]]:=dyn_recv0_inv tyR.
      have[r[A2[js _]]]:=dyn_cvar_inv tyv. inv js. }
    { inv H5.
      have[Θ1[Θ2[Δ1[Δ2[A0[s[mrg1[mrg2[tyR/=tyn]]]]]]]]]:=
        dyn_bind_inv H1. inv mrg2. inv mrg1.
      have[r1[r3[A1[B1[_[_ tyv]]]]]]:=dyn_recv0_inv tyR.
      have[r[A2[js _]]]:=dyn_cvar_inv tyv. inv js. }
    { inv H4. inv H5.
      have{H3}[Θ1[Θ2[Δ1[Δ2[A0[s0[mrg1[mrg2[tyR/=tyn2]]]]]]]]]:=
        dyn_bind_inv H3. inv mrg2. inv mrg1; inv H4.
      2:{ have[r1[r3[A1[B1[_[_ tyv]]]]]]:=dyn_recv0_inv tyR.
          have[r[A2[js _]]]:=dyn_cvar_inv tyv. inv js. }
      have[r1[r3[A1[B1[xor1[/io_inj eq1 tyv0]]]]]]:=dyn_recv0_inv tyR.
      have[r4[A2[js[tyA2 eq2]]]]:=dyn_cvar_inv tyv0. asimpl in eq2.
      have{eq2}[e eq2]:=ch_inj eq2. subst.
      inv js. inv H4.
      rewrite<-term_cren_comp in eq2. asimpl in eq2.
      rewrite<-term_cren_comp in tyA2. asimpl in tyA2.
      have e:=merge_emptyL H5 H0. subst.
      have[Θ3[Θ4[Δ5[Δ6[A3[s1[mrg1[mrg2[tyApp/=tyn1]]]]]]]]]:=
        dyn_bind_inv H1. inv mrg2. inv mrg1. inv H6.
      2:{ have[A2[B2[s2[[tyS _]|[Θ1[Θ2[Δ1[Δ2[mrg1[mrg2[tyS _]]]]]]]]]]]:=
          dyn_app_inv tyApp.
          have[r1[r4[A4[B4[_[_ tyv1]]]]]]:=dyn_send0_inv tyS.
          have[r[A5[js _]]]:=dyn_cvar_inv tyv1. inv js. inv H6.
          inv mrg1. inv H6.
          have[r1[r4[A4[B4[_[_ tyv1]]]]]]:=dyn_send0_inv tyS.
          have[r[A5[js _]]]:=dyn_cvar_inv tyv1. inv js. inv H6. }
      have[A2[B2[s2[[tyS[tym eqA3]]|[Θ1[Θ2[Δ1[Δ2[mrg1[mrg2[tyS _]]]]]]]]]]]:=
        dyn_app_inv tyApp.
      2:{ have[r1[_[A4[B4[_[eq _]]]]]]:=dyn_send0_inv tyS.
          exfalso. solve_conv. }
      have[r1[r4[A4[B4[xor2[/pi0_inj[eqA2[eqB2 e]] tyv1]]]]]]:=
        dyn_send0_inv tyS. subst.
      have[r[A5[js[tyA5 eqCh]]]]:=dyn_cvar_inv tyv1. asimpl in eqCh.
      have{eqCh}[e eq3]:=ch_inj eqCh. subst.
      inv js. inv H6.
      have e:=merge_emptyL H7 H3. subst.
      rewrite<-term_cren_comp in H4. asimpl in H4. inv H4.
      have{eq2 eq3}/act0_inj[eqA1[eqB1 e]]:=
        conv_trans _ eq2 (conv_sym eq3). subst.
      have eqIO:IO A3 === (IO (Ch r B4)).[m/].
      { apply: conv_trans...
        apply: sta_conv_subst... }
      asimpl in eqIO.
      have{eqIO}eqA3:=io_inj eqIO.
      have[s2 tyCh0]:=dyn_valid tyv0.
      have[s3 tyCh1]:=dyn_valid tyv1.
      have{tyCh0}[tyAct0/sort_inj e]:=sta_ch_inv tyCh0. subst.
      have{tyCh1}[tyAct1/sort_inj e]:=sta_ch_inv tyCh1. subst.
      have{tyAct0}tyB1:=sta_act0_inv tyAct0.
      have{tyAct1}tyB4:=sta_act0_inv tyAct1.
      have wf:=sta_type_wf tyB1. inv wf. inv H6.
      have wf:=sta_type_wf tyB4. inv wf. inv H6.
      have wf:=dyn_type_wf tyn1. inv wf. inv H10.
      have wf:=dyn_type_wf tyn2. inv wf. inv H10.
      have[Δ1[Δ2[_[mrg _]]]]:=merge_distr H2 H7 H5.
      have e:=merge_emptyL mrg H3. subst.
      have e:=merge_emptyR mrg H0. subst.
      have tym4:=sta_conv eqA2 tym H9.
      have tym1:=sta_conv (conv_trans _ eqA2 (conv_sym eqA1)) tym H8.
      have/=tyBm1:=sta_subst tyB1 tym1.
      have/=tyBm2:=sta_subst tyB4 tym4.
      econstructor...
      econstructor.
      2:{ constructor.
          econstructor.
          2:{ constructor. }
          2:{ constructor... }
          3:{ apply: tyn1. }
          2:{ constructor.
              apply: dyn_conv.
              apply: sta_cren_conv0.
              apply: (+2).
              apply: conv_sym...
              2:{ eauto. }
              simpl.
              replace (Ch r (term_cren B4.[m/] (+2)))
                with (Ch r (term_cren B4.[m/] (+2))).[ren (+0)] by autosubst.
              econstructor...
              replace (Ch r (term_cren B4.[m/] (+2)))
                with (term_cren (term_cren (Ch r B4.[m/]) (+1)) (+1)).
              constructor.
              constructor...
              rewrite<-term_cren_comp. asimpl...
              constructor.
              apply: sta_crename0.
              apply: sta_esubst...
              eauto. }
          constructor.
          constructor.
          apply: H7. }
      constructor.
      constructor...
      constructor.
      econstructor.
      2:{ constructor. }
      2:{ constructor... }
      3:{ apply: tyn2. }
      2:{ constructor.
          apply: dyn_conv.
          apply: conv_sym...
          2:{ eauto. }
          constructor.
          econstructor.
          apply: sort_leqL.
          eauto.
          constructor...
          apply: sta_conv.
          apply: conv_sym.
          apply: conv_trans.
          apply: eqA1.
          apply: (conv_sym eqA2).
          eauto.
          eauto.
          asimpl.
          apply: dyn_conv.
          apply: sta_cren_conv0.
          apply: (+2).
          apply: sta_conv_ch.
          apply: sta_conv_subst.
          apply: conv_sym...
          asimpl.
          replace (Ch (~~r) (term_cren B4.[m/] (+2)))
            with (Ch (~~r) (term_cren B4.[m/] (+2))).[ren (+0)] by autosubst.
          econstructor...
          replace (Ch (~~r) (term_cren B4.[m/] (+2)))
            with (term_cren (term_cren (Ch (~~r) B4.[m/]) (+1)) (+1)).
          constructor.
          apply: dyn_empty_n...
          rewrite<-term_cren_comp...
          constructor.
          apply: sta_crename0...
          constructor... }
      constructor... }
    { inv H4.
      have[Θ1[Θ2[Δ1[Δ2[A0[s[mrg1[mrg2[tyApp/=tyn]]]]]]]]]:=
        dyn_bind_inv H1. inv mrg2. inv mrg1. inv H4.
      have[A1[B1[s0[[tyS _]|[Θ1[Θ2[Δ1[Δ2[mrg1[mrg2[tyS _]]]]]]]]]]]:=dyn_app_inv tyApp.
      { have[r1[r3[A2[B2[_[_ tyv]]]]]]:=dyn_send0_inv tyS.
        have[r[A3[js _]]]:=dyn_cvar_inv tyv. inv js. inv H4. }
      { inv mrg2. inv mrg1. inv H4.
        have[r1[r3[A2[B2[_[_ tyv]]]]]]:=dyn_send0_inv tyS.
        have[r[A3[js _]]]:=dyn_cvar_inv tyv. inv js. inv H4. } } }
  { move=>v n1 n2 vl Θ ty. inv ty. inv H2. inv H1; inv H3.
    { inv H5.
      have[Θ1[Θ2[Δ1[Δ2[A0[s[mrg1[mrg2[tyR/=tyn]]]]]]]]]:=
        dyn_bind_inv H1. inv mrg2. inv mrg1. inv H5.
      have[r3[r4[A1[B1[_[_ tyv]]]]]]:=dyn_recv1_inv tyR.
      have[r[A2[js _]]]:=dyn_cvar_inv tyv. inv js. inv H5. }
    { inv H4. inv H5.
      have{H3}[Θ1[Θ2[Δ1[Δ2[A0[s0[mrg1[mrg2[tyR/=tyn2]]]]]]]]]:=
        dyn_bind_inv H3. inv mrg2. inv mrg1. inv H4.
      2:{ have[r3[r4[A1[B1[_[_ tyv]]]]]]:=dyn_recv1_inv tyR.
          have[r[A2[js _]]]:=dyn_cvar_inv tyv. inv js. inv H4. }
      have{H1}[Θ3[Θ4[Δ6[Δ7[A1[s1[mrg3[mrg4[tyApp/=tyn1]]]]]]]]]:=
        dyn_bind_inv H1. inv mrg4. inv mrg3.
      2:{ have[A2[B2[r[[tyS _]|[Θ1[Θ2[Δ8[Δ9[mrg1[mrg2[tyS _]]]]]]]]]]]:= dyn_app_inv tyApp.
          have[r3[r4[A3[B3[_[_ tyv]]]]]]:=dyn_send1_inv tyS.
          have[r0[A4[js _]]]:=dyn_cvar_inv tyv. inv js.
          inv mrg1.
          have[r3[r4[A3[B3[_[_ tyv]]]]]]:=dyn_send1_inv tyS.
          have[r0[A4[js _]]]:=dyn_cvar_inv tyv. inv js. }
      inv H3.
      have[r3[r4[A2[B2[xor1[/io_inj eq0 tyv1]]]]]]:=dyn_recv1_inv tyR.
      have[r5[A3[js[tyA3/=eq1]]]]:=dyn_cvar_inv tyv1. asimpl in eq1. inv js. inv H3.
      rewrite<-term_cren_comp in H1. asimpl in H1.
      have{eq1}[e eq1]:=ch_inj eq1. subst. inv H1.
      have e:=merge_emptyL H5 H0. subst.
      have[A3[B3[s3[[tyS[tyvl eq2]]|[Θ5[Θ6[Δ8[Δ9[mrg1[mrg2[tyS[tyvl eq2]]]]]]]]]]]]:=
        dyn_app_inv tyApp.
      { have[r1[r2[A4[B4[_[eq _]]]]]]:=dyn_send1_inv tyS.
        exfalso. solve_conv. }
      inv mrg2. inv mrg1.
      2:{ have[r1[r2[A4[B4[_[_ ty]]]]]]:=dyn_send1_inv tyS.
          have[r[A5[js _]]]:=dyn_cvar_inv ty. inv js. }
      inv H6.
      have[r1[r2[A4[B4[xor2[/pi1_inj[eqA3[tyB3 e]] tyv0]]]]]]:=dyn_send1_inv tyS. subst.
      have[r[A5[js[tyA5/=eq3]]]]:=dyn_cvar_inv tyv0.
      have{eq3}[e eq3]:=ch_inj eq3. subst. inv js. inv H6.
      asimpl in eq3.
      rewrite<-term_cren_comp in eq3. asimpl in eq3.
      rewrite<-term_cren_comp in tyA5. asimpl in tyA5.
      have e:=merge_emptyL H7 H1. subst.
      have[Δ1[_[_[mrg _]]]]:=merge_distr H2 H4 H5.
      have e:=merge_emptyR mrg H0. subst.
      have{mrg H7}[Δx[mrg _]]:=merge_splitL mrg H7.
      have e:=merge_emptyL mrg H1. subst.
      have e:=merge_emptyR mrg H0. subst.
      have/=/io_inj eqA1:IO A1 === (IO (Ch (~~r5) B4)).[v/].
      { apply:conv_trans.
        apply: eq2.
        apply:sta_conv_subst... }
      have/act1_inj[eqA2[eqB2 e]]:=conv_trans _ eq1 (conv_sym eq3). subst.
      have wf:=dyn_type_wf tyn1. inv wf. inv H7.
      have wf:=dyn_type_wf tyn2. inv wf. inv H7.
      have[s2 tyCh0]:=dyn_valid tyv0.
      have[s3 tyCh1]:=dyn_valid tyv1.
      have{tyCh0}[tyAct0/sort_inj e]:=sta_ch_inv tyCh0. subst.
      have{tyCh1}[tyAct1/sort_inj e]:=sta_ch_inv tyCh1. subst.
      have tyB4:=sta_act1_inv tyAct0.
      have tyB2:=sta_act1_inv tyAct1.
      have wf:=sta_type_wf tyB4. inv wf. inv H6.
      have wf:=sta_type_wf tyB2. inv wf. inv H6.
      have tyvl3:=dyn_sta_type tyvl.
      have tyvl4:=sta_conv eqA3 tyvl3 H7.
      have/=tyB4v:=sta_subst tyB4 tyvl4.
      have tyvl2:=sta_conv (conv_sym eqA2) tyvl4 H8.
      have/=tyB2v:=sta_subst tyB2 tyvl2.
      have{mrg}[_[Δ4[_[_ mrg]]]]:=merge_distr H2 H4 (merge_sym H5).
      have e:=merge_emptyR mrg H1. subst.
      have[Δy[mrg1 mrg2]]:=merge_splitR (merge_sym H4) mrg.
      have[Δz[mrg3 mrg4]]:=merge_splitL H2 mrg2.
      econstructor...
      econstructor.
      2:{ constructor.
          econstructor.
          2:{ constructor. }
          2:{ constructor... }
          3:{ apply: tyn1. }
          2:{ constructor.
              apply: dyn_conv.
              apply: sta_cren_conv0.
              apply: (+2).
              apply: conv_sym...
              2:{ apply: H9. }
              simpl.
              replace (term_cren B4.[v/] (+2))
                with (term_cren B4.[v/] (+2)).[ren (+0)] by autosubst.
              constructor...
              2:{ constructor. }
              2:{ apply: sta_crename0... }
              replace (Ch (~~ r5) (term_cren B4.[v/] (+2)))
                with (term_cren (Ch (~~ r5) (term_cren B4.[v/] (+1))) (+1)).
              constructor.
              apply: dyn_empty_n...
              simpl. rewrite<-term_cren_comp. by asimpl. }
          constructor.
          constructor.
          apply: merge_sym... }
      2:{ constructor.
          econstructor.
          2:{ constructor. }
          2:{ constructor... }
          3:{ apply: tyn2. }
          2:{ constructor.
              apply: dyn_conv.
              apply: conv_sym...
              2:{ apply: H10. }
              econstructor.
              2:{ constructor. }
              3:{ apply: dyn_conv.
                  apply: conv_sym.
                  apply: conv_trans.
                  apply: eqA2.
                  apply: conv_sym eqA3.
                  apply: tyvl.
                  eauto. }
              2:{ econstructor... }
              2:{ asimpl.
                  have eq:term_cren (Ch r5 B4.[v/]) (+2) === Ch r5 B2.[v/].
                  { apply: conv_trans.
                    apply: sta_cren_conv0.
                    apply: sta_conv_ch.
                    apply: sta_conv_subst.
                    apply: conv_sym...
                    eauto. }
                  apply: dyn_conv.
                  apply: eq.
                  2:{ constructor... }
                  simpl.
                  replace (Ch r5 (term_cren B4.[v/] (+2)))
                    with (Ch r5 (term_cren B4.[v/] (+2))).[ren (+0)] by autosubst.
                  constructor...
                  replace (Ch r5 (term_cren B4.[v/] (+2)))
                    with (term_cren (term_cren (Ch r5 B4.[v/]) (+1)) (+1)).
                  constructor.
                  constructor.
                  eauto.
                  simpl. rewrite<-term_cren_comp. by asimpl.
                  constructor.
                  apply: sta_crename0... }
              constructor.
              constructor.
              apply: merge_sym... }
          repeat constructor... }
      constructor.
      constructor.
      apply: merge_sym... }
    { inv H4.
      have[Θ1[Θ2[Δ1[Δ2[A0[s[mrg1[mrg2[tyR/=tyn]]]]]]]]]:=
        dyn_bind_inv H1. inv mrg2. inv mrg1.
      have[A1[B1[r[[tyS _]|[Θ1[Θ2[Δ4[Δ5[mrg1[mrg2[tyS _]]]]]]]]]]]:=dyn_app_inv tyR.
      have[r3[r4[A2[B2[_[_ tyv]]]]]]:=dyn_send1_inv tyS.
      have[r5[A3[js _]]]:=dyn_cvar_inv tyv. inv js.
      inv mrg1.
      have[r3[r4[A2[B2[_[_ tyv]]]]]]:=dyn_send1_inv tyS.
      have[r5[A3[js _]]]:=dyn_cvar_inv tyv. inv js. }
    { inv H4.
      have[Θ1[Θ2[Δ1[Δ2[A0[s[mrg1[mrg2[tyR/=tyn]]]]]]]]]:=
        dyn_bind_inv H1. inv mrg2. inv mrg1.
      have[A1[B1[r[[tyS _]|[Θ1[Θ2[Δ4[Δ5[mrg1[mrg2[tyS _]]]]]]]]]]]:=dyn_app_inv tyR.
      have[r3[r4[A2[B2[_[_ tyv]]]]]]:=dyn_send1_inv tyS.
      have[r5[A3[js _]]]:=dyn_cvar_inv tyv. inv js.
      inv mrg1.
      have[r3[r4[A2[B2[_[_ tyv]]]]]]:=dyn_send1_inv tyS.
      have[r5[A3[js _]]]:=dyn_cvar_inv tyv. inv js. } }
  { move=>v n1 n2 vl Θ ty. inv ty. inv H2. inv H1; inv H3.
    { inv H5.
      have[Θ1[Θ2[Δ1[Δ2[A0[s[mrg1[mrg2[tyR/=tyn]]]]]]]]]:=
        dyn_bind_inv H1. inv mrg1.
      have[r1[r3[A1[B1[_[_ tyv]]]]]]:=dyn_recv1_inv tyR.
      have[r[A2[js _]]]:=dyn_cvar_inv tyv. inv js. }
    { inv H5.
      have[Θ1[Θ2[Δ1[Δ2[A0[s[mrg1[mrg2[tyR/=tyn]]]]]]]]]:=
        dyn_bind_inv H1. inv mrg1.
      have[r1[r3[A1[B1[_[_ tyv]]]]]]:=dyn_recv1_inv tyR.
      have[r[A2[js _]]]:=dyn_cvar_inv tyv. inv js. }
    { inv H4. inv H5.
      have{H3}[Θ1[Θ2[Δ1[Δ2[A1[s1[mrg1[mrg2[tyR/=tyn2]]]]]]]]]:=
        dyn_bind_inv H3. inv mrg2. inv mrg1.
      2:{ have[r1[r3[A0[B[_[_ tyv]]]]]]:=dyn_recv1_inv tyR.
          have[r[A2[js _]]]:=dyn_cvar_inv tyv. inv js. }
      inv H4.
      have{tyR}[r1[r3[A2[B2[xor1[/io_inj eqA1 tyv0]]]]]]:=dyn_recv1_inv tyR.
      have[r[A3[js[tyA3 eqCh1]]]]:=dyn_cvar_inv tyv0. asimpl in eqCh1.
      have{eqCh1}[e eqAct2]:=ch_inj eqCh1. subst. inv js. inv H4.
      have e:=merge_emptyL H5 H0. subst.
      rewrite<-term_cren_comp in tyA3. asimpl in tyA3.
      rewrite<-term_cren_comp in eqAct2. asimpl in eqAct2.
      have[s tyCh]:=dyn_valid tyv0.
      have{tyCh}[tyAct2/sort_inj e]:=sta_ch_inv tyCh. subst.
      have{tyAct2}tyB2:=sta_act1_inv tyAct2.
      have wf:=sta_type_wf tyB2. inv wf. inv H4.
      have wf:=dyn_type_wf tyn2. inv wf. inv H7.
      have{H1}[Θ1[Θ2[Δ1[Δ2[A3[s3[mrg1[mrg2[tyApp/=tyn1]]]]]]]]]:=
        dyn_bind_inv H1. inv mrg2. inv mrg1. inv H4.
      2:{ have[A0[B0[s0[[tyS _]|[Θ1[Θ2[Δ1[Δ2[mrg1[mrg2[tyS _]]]]]]]]]]]:=dyn_app_inv tyApp.
          have[r1[r4[A4[B4[_[_ tyv1]]]]]]:=dyn_send1_inv tyS.
          have[r[A5[js _]]]:=dyn_cvar_inv tyv1. inv js. inv H4.
          inv mrg1. inv H4.
          have[r1[r4[A4[B4[_[_ tyv1]]]]]]:=dyn_send1_inv tyS.
          have[r[A5[js _]]]:=dyn_cvar_inv tyv1. inv js. inv H4. }
      have{tyApp}[A4[B4[s4[[tyS _]|[Θ1[Θ2[Δ1[Δ2[mrg1[mrg2[tyS[tyvl4 eqIO]]]]]]]]]]]]:=dyn_app_inv tyApp.
      have[r1[r4[A0[B0[_[eq _]]]]]]:=dyn_send1_inv tyS. exfalso. solve_conv.
      inv mrg2. inv mrg1. inv H4.
      2:{ have[r1[r4[A0[B0[_[_ tyv1]]]]]]:=dyn_send1_inv tyS.
          have[r[A5[js _]]]:=dyn_cvar_inv tyv1. inv js. inv H4. }
      have[r1[r4[A5[B5[xor2[/pi1_inj[eqA4[eqB4 e]] tyv1]]]]]]:=dyn_send1_inv tyS. subst.
      have[r[A6[js[tyA6 eqCh2]]]]:=dyn_cvar_inv tyv1. asimpl in eqCh2.
      have{eqCh2}[e eqAct1]:=ch_inj eqCh2. subst. inv js. inv H4.
      have wf:=dyn_type_wf tyn1. inv wf. inv H11.
      have[s0 tyCh]:=dyn_valid tyv1.
      have{tyCh}[tyAct/sort_inj e]:=sta_ch_inv tyCh. subst.
      have{tyAct}tyB5:=sta_act1_inv tyAct.
      have wf:=sta_type_wf tyB5. inv wf. inv H10.
      rewrite<-term_cren_comp in H3. asimpl in H3. inv H3.
      have/=/io_inj eqA3:IO A3 === (IO (Ch r B5)).[v/].
      { apply: conv_trans...
        apply: sta_conv_subst.
        eauto. }
      have/act1_inj[eqA5[eqB5 e]]:=conv_trans _ eqAct1 (conv_sym eqAct2). subst.
      have tyvl5:=dyn_sta_type (dyn_conv eqA4 tyvl4 H11).
      have tyvl2:=dyn_conv (conv_trans _ eqA4 eqA5) tyvl4 H6.
      have/=tyB5v:=sta_subst tyB5 tyvl5.
      have/=tyB2v:=sta_subst tyB2 (dyn_sta_type tyvl2).

      have e:=merge_emptyL H8 H1. subst.
      have[Δx[mrg1 mrg2]]:=merge_splitL H7 (merge_sym H8).
      have[Δ1[Δ2[mrg3[mrg4 mrg5]]]]:=merge_distr H2 (merge_sym mrg2) H5.
      have e:=merge_emptyL mrg4 H1. subst.
      have e:=merge_emptyR mrg4 H0. subst.
      have e:=merge_emptyL mrg3 H1. subst.
      have e:=merge_emptyR mrg2 H1. subst.
      have[Δy[mrg6 mrg7]]:=merge_splitL mrg2 (merge_sym mrg1).
      have e:=merge_emptyR mrg6 H1. subst.
      have[Δz[mrg8 mrg9]]:=merge_splitR mrg2 (merge_sym mrg1).
      have e:=merge_emptyR mrg8 H1. subst.
      have[Δx[mrg10 mrg11]]:=merge_splitL mrg5 mrg9.

      econstructor...
      econstructor.

      2:{ constructor.
          econstructor.
          2:{ constructor. }
          2:{ constructor... }
          3:{ apply: tyn1. }
          2:{ constructor.
              apply: dyn_conv.
              apply: sta_cren_conv0.
              apply: (+2).
              apply: conv_sym...
              2:{ eauto. }
              simpl.
              replace (Ch r (term_cren B5.[v/] (+2)))
                with (Ch r (term_cren B5.[v/] (+2))).[ren (+0)] by autosubst.
              constructor.
              2:{ constructor. }
              2:{ constructor. }
              replace (Ch r (term_cren B5.[v/] (+2)))
                with (term_cren (term_cren (Ch r B5.[v/]) (+1)) (+1)).
              constructor.
              constructor.
              eauto.
              rewrite<-term_cren_comp. asimpl...
              apply: sta_crename0... }
          repeat constructor.
          apply: merge_sym... }

      2:{ constructor.
          econstructor.
          2:{ constructor. }
          2:{ constructor... }
          3:{ eauto. }
          2:{ constructor.
              apply: dyn_conv.
              apply: conv_sym...
              2:{ eauto. }
              econstructor.
              2:{ constructor. }
              2:{ econstructor.
                  apply: sort_leq_Lgt.
                  apply: sort_leq_Lgt.
                  eauto.
                  constructor... }
              2:{ eauto. }
              2:{ simpl.
                  apply: dyn_conv.
                  apply: sta_cren_conv0.
                  apply: (+2).
                  apply: sta_conv_ch.
                  apply: sta_conv_subst.
                  apply: eqB5.
                  2:{ constructor... }
                  simpl.
                  replace (Ch (~~r) (term_cren B5.[v/] (+2)))
                    with (Ch (~~r) (term_cren B5.[v/] (+2))).[ren (+0)] by autosubst.
                  constructor.
                  2:{ constructor. }
                  2:{ constructor. }
                  2:{ apply: sta_crename0... }
                  replace (Ch (~~r) (term_cren B5.[v/] (+2)))
                    with (term_cren (term_cren (Ch (~~r) B5.[v/]) (+1)) (+1)).
                  constructor.
                  apply: dyn_empty_n...
                  rewrite<-term_cren_comp. asimpl... }
              repeat constructor.
              eauto. }
          repeat constructor.
          eauto. }
      repeat constructor.
      apply: merge_sym... }
    { inv H4.
      have[Θ1[Θ2[Δ1[Δ2[A0[s[mrg1[mrg2[tyApp/=tyn]]]]]]]]]:=
        dyn_bind_inv H1. inv mrg1. inv H4.
      have[A1[B1[s0[[tyS _]|[Θ1[Θ2[Δ4[Δ5[mrg1[_[tyS _]]]]]]]]]]]:=dyn_app_inv tyApp.
      have[r1[r3[A2[B2[_[_ tyv]]]]]]:=dyn_send1_inv tyS.
      have[r[A3[js _]]]:=dyn_cvar_inv tyv. inv js. inv H4.
      inv mrg1. inv H4.
      have[r1[r3[A2[B2[_[_ tyv]]]]]]:=dyn_send1_inv tyS.
      have[r[A3[js _]]]:=dyn_cvar_inv tyv. inv js. inv H4. } }
  { move=>m m' n n' e1 e2 Θ ty. inv ty. inv H2. inv H1; inv H3.
    { inv H5.
      have[Θ1[Θ2[Δ1[Δ2[A0[s[mrg1[mrg2[tyW/=tyn]]]]]]]]]:=
        dyn_bind_inv H1. inv mrg2. inv mrg1. inv H5.
      have[r3[r4[xor[_ tyv]]]]:=dyn_wait_inv tyW.
      have[r[A1[js _]]]:=dyn_cvar_inv tyv.
      inv js. inv H5. }
    { inv H4. inv H5.
      have{H1}ty1:_: _: Δ0; [::]; [::] ⊢ Bind (Return II) m : IO Unit.
      { have[Θ1[Θ2[Δ1[Δ2[A0[s[mrg1[mrg2[tyC/=tyn]]]]]]]]]:=
          dyn_bind_inv H1. inv mrg2. inv mrg1; inv H5.
        { have wf:=dyn_type_wf tyn. inv wf.
          have[r3[r4[xor[/io_inj eq2 tyv]]]]:=dyn_close_inv tyC.
          have[r[A1[js _]]]:=dyn_cvar_inv tyv. inv js. inv H7.
          have e:=merge_emptyL H6 H0. subst.
          have[x rd1 rd2]:=church_rosser eq2.
          have tyx1:=sta_prd H8 rd1.
          have tyx2:=sta_prd (sta_unit sta_wf_nil) rd2.
          have e:=sta_unicity tyx1 tyx2. subst.
          econstructor...
          constructor.
          apply: dyn_conv.
          apply: conv_sym...
          repeat constructor...
          apply: H8. }
        { have[r3[r4[xor[_ tyv]]]]:=dyn_close_inv tyC.
          have[r[A1[js _]]]:=dyn_cvar_inv tyv. inv js. } }
      have{H3}ty2:_: _: Δ3; [::]; [::] ⊢ Bind (Return II) n : IO Unit.
      { have[Θ1[Θ2[Δ1[Δ2[A0[s[mrg1[mrg2[tyW/=tyn]]]]]]]]]:=
          dyn_bind_inv H3. inv mrg2. inv mrg1; inv H4.
        { have wf:=dyn_type_wf tyn. inv wf.
          have[r3[r4[xor[/io_inj eq2 tyv]]]]:=dyn_wait_inv tyW.
          have[r[A1[js _]]]:=dyn_cvar_inv tyv. inv js. inv H6.
          have e:=merge_emptyL H5 H0. subst.
          have[x rd1 rd2]:=church_rosser eq2.
          have tyx1:=sta_prd H7 rd1.
          have tyx2:=sta_prd (sta_unit sta_wf_nil) rd2.
          have e:=sta_unicity tyx1 tyx2. subst.
          econstructor...
          constructor.
          apply: dyn_conv.
          apply: conv_sym...
          repeat constructor...
          apply: H7. }
        { have[r3[r4[xor[_ tyv]]]]:=dyn_wait_inv tyW.
          have[r[A1[js _]]]:=dyn_cvar_inv tyv. inv js. inv H4. } }
      have e: ( - 2) = ((-1) >>> ((-1) >>> id)).
      { f_ext. move=>x. asimpl. lia. }
      econstructor...
      { constructor.
        replace (IO Unit) with (term_cren (IO Unit) (-2)) by eauto.
        replace (Bind (Return II) (term_cren m (-2)))
          with (term_cren (Bind (Return II) m) (-2)) by eauto.
        rewrite e.
        apply: dyn_crename...
        repeat constructor. }
      { constructor.
        replace (IO Unit) with (term_cren (IO Unit) (-2)) by eauto.
        replace (Bind (Return II) (term_cren n (-2)))
          with (term_cren (Bind (Return II) n) (-2)) by eauto.
        rewrite e.
        apply: dyn_crename...
        repeat constructor. } }
    { inv H4.
      have[Θ1[Θ2[Δ1[Δ2[A0[s[mrg1[mrg2[tyC/=tyn]]]]]]]]]:=
        dyn_bind_inv H1. inv mrg2. inv mrg1.
      have[r3[r4[_[_ tyv]]]]:=dyn_close_inv tyC.
      have[r[A1[js _]]]:=dyn_cvar_inv tyv. inv js. }
    { inv H4.
      have[Θ1[Θ2[Δ1[Δ2[A0[s[mrg1[mrg2[tyC/=tyn]]]]]]]]]:=
        dyn_bind_inv H1. inv mrg2. inv mrg1.
      have[r3[r4[_[_ tyv]]]]:=dyn_close_inv tyC.
      have[r[A1[js _]]]:=dyn_cvar_inv tyv. inv js. } }
  { move=>m m' n n' e1 e2 Θ ty. inv ty. inv H2. inv H1; inv H3.
    { inv H5.
      have[Θ1[Θ2[Δ1[Δ2[A0[s[mrg1[mrg2[tyW/=tyn]]]]]]]]]:=
        dyn_bind_inv H1. inv mrg2. inv mrg1.
      have[r3[r4[_[_ tyv]]]]:=dyn_wait_inv tyW.
      have[r[A1[js _]]]:=dyn_cvar_inv tyv. inv js. }
    { inv H5.
      have[Θ1[Θ2[Δ1[Δ2[A0[s[mrg1[mrg2[tyW/=tyn]]]]]]]]]:=
        dyn_bind_inv H1. inv mrg2. inv mrg1.
      have[r3[r4[_[_ tyv]]]]:=dyn_wait_inv tyW.
      have[r[A1[js _]]]:=dyn_cvar_inv tyv. inv js. }
    { inv H4. inv H5.
      have{H1}ty1:_: _: Δ0; [::]; [::] ⊢ Bind (Return II) m : IO Unit.
      { have[Θ1[Θ2[Δ1[Δ2[A0[s[mrg1[mrg2[tyC/=tym]]]]]]]]]:=
          dyn_bind_inv H1. inv mrg2. inv mrg1; inv H5.
        { have wf:=dyn_type_wf tym. inv wf.
          have[r3[r4[xor[/io_inj eq2 tyv]]]]:=dyn_close_inv tyC.
          have[r[A1[js _]]]:=dyn_cvar_inv tyv. inv js. inv H7.
          have e:=merge_emptyL H6 H0. subst.
          have[x rd1 rd2]:=church_rosser eq2.
          have tyx1:=sta_prd H8 rd1.
          have tyx2:=sta_prd (sta_unit sta_wf_nil) rd2.
          have e:=sta_unicity tyx1 tyx2. subst.
          econstructor...
          constructor.
          apply: dyn_conv.
          apply: conv_sym...
          repeat constructor...
          apply: H8. }
        { have[r3[r4[xor[_ tyv]]]]:=dyn_close_inv tyC.
          have[r[A1[js _]]]:=dyn_cvar_inv tyv. inv js. inv H5. } }
      have{H3}ty2:_: _: Δ3; [::]; [::] ⊢ Bind (Return II) n : IO Unit.
      { have[Θ1[Θ2[Δ1[Δ2[A0[s[mrg1[mrg2[tyW/=tyn]]]]]]]]]:=
          dyn_bind_inv H3. inv mrg2. inv mrg1; inv H4.
        { have wf:=dyn_type_wf tyn. inv wf.
          have[r3[r4[xor[/io_inj eq2 tyv]]]]:=dyn_wait_inv tyW.
          have[r[A1[js _]]]:=dyn_cvar_inv tyv. inv js. inv H6.
          have e:=merge_emptyL H5 H0. subst.
          have[x rd1 rd2]:=church_rosser eq2.
          have tyx1:=sta_prd H7 rd1.
          have tyx2:=sta_prd (sta_unit sta_wf_nil) rd2.
          have e:=sta_unicity tyx1 tyx2. subst.
          econstructor...
          constructor.
          apply: dyn_conv.
          apply: conv_sym...
          repeat constructor...
          apply: H7. }
        { have[r3[r4[xor[_ tyv]]]]:=dyn_wait_inv tyW.
          have[r[A1[js _]]]:=dyn_cvar_inv tyv. inv js. } }
      have e: ( - 2) = ((-1) >>> ((-1) >>> id)).
      { f_ext. move=>x. asimpl. lia. }
      econstructor...
      { constructor.
        replace (IO Unit) with (term_cren (IO Unit) (-2)) by eauto.
        replace (Bind (Return II) (term_cren m (-2)))
          with (term_cren (Bind (Return II) m) (-2)) by eauto.
        rewrite e.
        apply: dyn_crename...
        repeat constructor. }
      { constructor.
        replace (IO Unit) with (term_cren (IO Unit) (-2)) by eauto.
        replace (Bind (Return II) (term_cren n (-2)))
          with (term_cren (Bind (Return II) n) (-2)) by eauto.
        rewrite e.
        apply: dyn_crename...
        repeat constructor. } }
    { inv H4.
      have[Θ1[Θ2[Δ1[Δ2[A0[s[mrg1[mrg2[tyC/=tyn]]]]]]]]]:=
        dyn_bind_inv H1. inv mrg2. inv mrg1. inv H4.
      have[r3[r4[_[_ tyv]]]]:=dyn_close_inv tyC.
      have[r[A1[js _]]]:=dyn_cvar_inv tyv. inv js. inv H4. } }
  { move=>o p q st ih Θ ty... inv ty. econstructor... }
  { move=>p q st ih Θ ty. inv ty. econstructor... }
  { move=>p p' q q' eq1 st ih eq2 Θ ty.
    have{}ty:=proc_congr_type ty eq1.
    move/ih in ty.
    have{}ty//:=proc_congr_type ty eq2. }
Qed.
