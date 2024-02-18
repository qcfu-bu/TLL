From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq zify.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS era_cren era_sr proc_sr eproc_occurs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma eproc_congr0_type Θ p p' q :
  proc_congr0 p q -> Θ ⊢ p ~ p' -> exists2 q', proc_congr0 p' q' & Θ ⊢ q ~ q'.
Proof with eauto using era_type, eproc_type, proc_congr0.
  move=>cgr. elim: cgr Θ p'=>{p q}.
  { move=>p q Θ p' er. inv er.
    exists (q' ∣ p'0)...
    econstructor.
    apply: merge_sym...
    all: eauto. }
  { move=>o p q Θ p' er. inv er. inv H5.
    have[Θ4[mrg1 mrg2]]:=merge_splitL (merge_sym H1) H2.
    exists ((p'0 ∣ p') ∣ q'0)...
    econstructor. apply: mrg2.
    econstructor. apply: merge_sym.
    all: eauto. }
  { move=>p q Θ p' er. inv er. inv H3.
    exists (ν.(p' ∣ proc_cren q' (+2))).
    constructor.
    move: H4. move e:(~~r2)=>r1 erp.
    econstructor. apply: (esym e).
    econstructor.
    2:{ apply: erp. }
    2:{ replace (proc_cren q (+2)) with (proc_cren (proc_cren q (+1)) (+1)).
        replace (proc_cren q' (+2)) with (proc_cren (proc_cren q' (+1)) (+1)).
        apply: eproc_cweaken.
        apply: eproc_cweaken.
        apply: H5.
        rewrite<-proc_cren_comp. by asimpl.
        rewrite<-proc_cren_comp. by asimpl. }
    repeat constructor... }
  { move=>p p' q q' cgr1 ih1 cgr2 ih2 Θ p0 er. inv er.
    have[p1 cgr3 erp]:=ih1 _ _ H3.
    have[q1 cgr4 erq]:=ih2 _ _ H5.
    exists (p1 ∣ q1)... }
  { move=>p p' cgr ih Θ p0 er. inv er.
    have[p1 cgr1 erp]:=ih _ _ H2.
    exists (ν.p1)... }
  { move=>p Θ p' er. inv er. inv H5.
    have[n e]:=era_return_form H2. subst.
    have er:=era_return_inv H2.
    have e:=era_ii_form er. subst.
    have emp:=era_ii_inv er.
    have e:=merge_emptyR H1 emp. subst... }
Qed.

Lemma eproc_congr0_typei Θ p q q' :
  proc_congr0 p q -> Θ ⊢ q ~ q' -> exists2 p', proc_congr0 p' q' & Θ ⊢ p ~ p'.
Proof with eauto using era_type, eproc_type, proc_congr0.
  move=>cgr. elim: cgr Θ q'=>{p q}.
  { move=>p q Θ q' er. inv er.
    exists (q'0 ∣ p'). constructor.
    econstructor.
    apply: merge_sym...
    all: eauto. }
  { move=>o p q Θ q' er. inv er. inv H3.
    have[Θ4[mrg1 mrg2]]:=merge_splitR H1 H2.
    exists (p'0 ∣ (q' ∣ q'0)). apply: proc_congr0_assoc.
    econstructor.
    apply: merge_sym.
    apply: mrg2.
    eauto.
    econstructor... }
  { move=>p q Θ q' er. inv er. inv H2. inv H1; inv H3.
    { have[q0 e]:=eproc_cren_inv H6. subst.
      replace (proc_cren q (+2))
        with (proc_cren (proc_cren q (+1)) (+1)) in H6.
      replace (proc_cren q0 (+2))
        with (proc_cren (proc_cren q0 (+1)) (+1)) in H6.
      have erq:=eproc_cstrengthen (eproc_cstrengthen H6).
      exists (ν.p'0 ∣ q0).
      constructor.
      econstructor...
      rewrite<-proc_cren_comp. by asimpl.
      rewrite<-proc_cren_comp. by asimpl. }
    { have[q0 e]:=eproc_cren_inv H6. subst.
      have:=eproc_occurs_iren H6 iren1.
      have[->_]:proc_occurs 1 (proc_cren q (+2)) = 1 ∧
               proc_occurs 1 (proc_cren q0 (+2)) = 1.
      apply: eproc_type_occurs1...
      repeat constructor.
      by move=>[]. }
    { have[q0 e]:=eproc_cren_inv H6. subst.
      have:=eproc_occurs_iren H6 iren0.
      have[->_]:proc_occurs 0 (proc_cren q (+2)) = 1 ∧
               proc_occurs 0 (proc_cren q0 (+2)) = 1.
      apply: eproc_type_occurs1...
      repeat constructor.
      by move=>[]. }
    { have[q0 e]:=eproc_cren_inv H6. subst.
      have:=eproc_occurs_iren H6 iren0.
      have[->_]:proc_occurs 0 (proc_cren q (+2)) = 1 ∧
               proc_occurs 0 (proc_cren q0 (+2)) = 1.
      apply: eproc_type_occurs1...
      repeat constructor.
      by move=>[]. } }
  { move=>p p' q q' cgr1 ih1 crg2 ih2 Θ q0 er. inv er.
    have[p2 cgr3 erp]:=ih1 _ _ H3.
    have[q2 cgr4 erq]:=ih2 _ _ H5.
    exists (p2 ∣ q2)... }
  { move=>p p' cgr ih Θ q' er. inv er.
    have[p1 cgr1 erp]:=ih _ _ H2.
    exists (ν.p1)... }
  { move=>p Θ q' er.
    have wf:=eproc_type_wf er.
    have[Θ0[emp mrg]]:=proc_wf_empty wf.
    exists (q' ∣ ⟨ Return II ⟩)...
    econstructor.
    apply: merge_sym.
    all: eauto.
    repeat constructor... }
Qed.

Lemma eproc_congr_type Θ p p' q :
  p ≡ q -> Θ ⊢ p ~ p' -> exists2 q', p' ≡ q' & Θ ⊢ q ~ q'.
Proof with eauto.
  move=>eq. elim: eq Θ p'=>{q}...
  { move=>y z eq1 ih cr1 Θ p' erp.
    have[q' eq2 ery]:=ih _ _ erp.
    have[z' cr2 erz]:=eproc_congr0_type cr1 ery.
    exists z'... apply: conv_trans. apply: eq2. by apply: conv1. }
  { move=>y z eq1 ih cr1 Θ p' erp.
    have[q' eq2 ery]:=ih _ _ erp.
    have[z' cr2 erz]:=eproc_congr0_typei cr1 ery.
    exists z'... apply: conv_trans. apply: eq2. apply: conv_sym. by apply: conv1. }
Qed.

Theorem eproc_sr Θ p p' q :
  Θ ⊢ p ~ p' -> p ≈>> q -> exists2 q', Θ ⊢ q ~ q' & p' ≈>> q'.
Proof with eauto using merge, merge_sym, sta_type, era_type.
  move=>er st. elim: st Θ p' er=>{p q}.
  { move=>m m' st Θ p' ty. inv ty.
    have[m'1 er st']:=era_sr H1 st.
    exists ⟨ m'1 ⟩. by constructor. by constructor. }
  
  { move=>A m m' n n' e1 e2 Θ p' ty. inv ty.
    have[x[n' e]]:=era_bind_form H1. subst.
    have[Θ1[Θ2[Δ2[Δ3[A0[s[mrg1[mrg2[tyF/=tyn]]]]]]]]]:=era_bind_inv H1.
    have[m' e]:=era_fork_form tyF. subst.
    have[_[tym/io_inj eq2]]:=era_fork_inv tyF.
    move=>{eq2 tym tyn tyF mrg2 mrg1 s A0 Θ1 Θ2 Δ2 Δ3}.
    have{H1}ty:=era_cweaken (era_cweaken H1).
    rewrite<-!term_cren_comp in ty.
    asimpl in ty.
    have[Θ1[Θ2[Δ1[Δ2[A0[s[mrg1[mrg2[tyF/=tyn]]]]]]]]]:=
      era_bind_inv ty. inv mrg2. inv mrg1. inv H2.
    have[_[tym/io_inj eq2]]:=era_fork_inv tyF.
    have mrg0: Ch (~~ true) (term_cren A (+1)) :L _: Δ3 ∘ _: Ch true A :L Δ0 =>
           Ch (~~ true) (term_cren A (+1)) :L Ch true A :L Θ.
    { econstructor. econstructor. apply: merge_sym... }
    econstructor. 2:{ apply: proc_step_fork... }
    econstructor...
    econstructor...
    { have wf:=era_type_wf tyn. inv wf.
      have wf:=era_type_wf tym. inv wf.
      have wf:=era_type_proc_wf tyn. inv wf. inv H0.
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
      apply: era_esubst1...
      constructor.
      apply: key_impure.
      apply: key_impure.
      replace (IO Unit) with (IO Unit.[ren (+1)]) by eauto.
      apply: era_conv.
      apply: conv_sym...
      replace (Ch false (term_cren A (+2)))
        with (Ch false (term_cren A (+2)).[ren (+0)])
        by autosubst.
      repeat constructor...
      apply: H5. }
    { have wf:=era_type_wf tyn. inv wf.
      have wf:=era_type_wf tym. inv wf.
      have wf:=era_type_proc_wf tym. inv wf. inv H0.
      have[Θx[emp mrg1]]:=proc_wf_empty H1.
      have{}mrg1: _: _: Δ0 ∘ _: Ch true A :L Θx => _: Ch true A :L Δ0...
      have[tyA _]:=sta_ch_inv H7.
      have[x eq3 eq4]:=church_rosser eq2.
      have tyx1:=sta_prd H5 eq3.
      have tyx2:=sta_prd (sta_ch false tyA) eq4.
      have e:=sta_unicity tyx1 tyx2. subst.
      econstructor.
      replace (IO Unit) with (IO Unit).[CVar 1/] by eauto.
      apply: era_esubst1...
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

  { move=>m n1 n2 Θ p' ty. inv ty. inv H2. inv H1; inv H3.
    { inv H6.
      have[x[n2' e]]:=era_bind_form H1. subst.
      have[Θ1[Θ2[Δ1[Δ2[A0[s[mrg1[mrg2[tyR/=tyn]]]]]]]]]:=era_bind_inv H1.
      have[n' e]:=era_recv0_form tyR. subst.
      inv mrg2. inv mrg1; inv H5.
      have[r3[r4[A1[B0[_[_ tyv]]]]]]:=era_recv0_inv tyR.
      have e:=era_cvar_form tyv. subst.
      have[r[A2[_[js _]]]]:=era_cvar_inv tyv. inv js. inv H5. }
    { inv H4. inv H6.
      have[x[n1' e]]:=era_bind_form H1. subst.
      have[Θ1[Θ2[Δ1[Δ2[A0[s[mrg1[mrg2[tyApp/=tyn1]]]]]]]]]:=
        era_bind_inv H1. inv mrg2. inv mrg1; inv H5.
      2:{ have[y e]:=era_app0_form tyApp. subst.
          have[A1[B1[s1[_[tyS _]]]]]:=era_app0_inv tyApp.
          have[x e]:=era_send0_form tyS. subst.
          have[r3[r4[A2[B2[_[_ ty]]]]]]:=era_send0_inv tyS.
          have e:=era_cvar_form ty. subst.
          have[r[A3[_[js _]]]]:=era_cvar_inv ty. inv js. }
      have[y e]:=era_app0_form tyApp. subst.
      have[A1[B1[s1[_[tyS[tym eq2]]]]]]:=era_app0_inv tyApp.
      have[x e]:=era_send0_form tyS. subst.
      have[r3[r4[A2[B2[xor1[/pi0_inj[eqA1[eqB1 e]]tyv0]]]]]]:=era_send0_inv tyS. subst.
      have e:=era_cvar_form tyv0. subst.
      have[r[A3[_[js[tyA eq3]]]]]:=era_cvar_inv tyv0. inv js. inv H5.
      have e:=merge_emptyL H6 H0. subst.
      rewrite<-term_cren_comp in eq3. asimpl in eq3.
      rewrite<-term_cren_comp in tyA. asimpl in tyA.
      have[e eq4]:=ch_inj eq3. subst.
      have[x[n2' e]]:=era_bind_form H3. subst.
      have[Θ3[Θ4[Δ1[Δ2[A3[s0[mrg1[mrg2[tyR/=tyn2]]]]]]]]]:=
        era_bind_inv H3. inv mrg2. inv mrg1. inv H7.
      2:{ have[y e]:=era_recv0_form tyR. subst.
          have[r5[r6[A4[B4[_[_ tyv1]]]]]]:=era_recv0_inv tyR.
          have e:=era_cvar_form tyv1. subst.
          have[r[A5[_[js _]]]]:=era_cvar_inv tyv1. inv js. inv H7. }
      have[y e]:=era_recv0_form tyR. subst.
      have[r5[r6[A4[B4[xor2[/io_inj eq6 tyv1]]]]]]:=era_recv0_inv tyR.
      have e:=era_cvar_form tyv1. subst.
      have[r[A5[_[js[tyA5/ch_inj[e eq7]]]]]]:=era_cvar_inv tyv1. subst.
      asimpl in eq7. inv js. inv H7.
      have e:=merge_emptyL H8 H4. subst.
      have[Δ6[Δ7[_[mrg0 _]]]]:=merge_distr H2 H6 H8.
      have e:=merge_emptyL mrg0 H0. subst.
      have e:=merge_emptyR mrg0 H4. subst. clear mrg0.
      rewrite<-term_cren_comp in H5. asimpl in H5. inv H5.
      have/act0_inj[eqA2[eqB2 e]]:=conv_trans _ eq4 (conv_sym eq7). subst.
      have/=/io_inj eqA0:=conv_trans _ eq2 (sta_conv_subst (m .: ids) eqB1).
      have wf:=era_type_proc_wf tyv1. inv wf. inv H5.
      have[s1 tyCh1]:=era_valid tyv0.
      have[s2 tyCh2]:=era_valid tyv1.
      have{tyCh1}[/sta_act0_inv tyB2/sort_inj e]:=sta_ch_inv tyCh1. subst.
      have{tyCh2}[/sta_act0_inv tyB4/sort_inj e]:=sta_ch_inv tyCh2.
      have wf:=era_type_wf tyn1. inv wf.
      have wf:=era_type_wf tyn2. inv wf.
      have wf:=sta_type_wf tyB2. inv wf.
      have wf:=sta_type_wf tyB4. inv wf.
      have/=tyB2m:=sta_subst tyB2 (sta_conv eqA1 tym H14).
      have tyChB2:=sta_ch (~~r) tyB2m.
      have/=tyB4m:=sta_subst tyB4 (sta_conv (conv_trans _ eqA1 eqA2) tym H17).
      have tyChB4:=sta_ch r tyB4m.
      econstructor.
      2:{ apply: proc_step_com0. }
      econstructor...
      econstructor.
      2:{ constructor.
          econstructor.
          2:{ constructor. }
          2:{ constructor... }
          3:{ apply: tyn1. }
          2:{ constructor.
              apply: era_conv.
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
              apply: sta_crename...
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
      apply: era_conv.
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
      apply: era_conv.
      apply: sta_conv_subst.
      apply: sta_conv_ch.
      apply: eqB2.
      2:{ eauto. }
      apply: era_conv.
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
      apply: sta_crename...
      constructor... }
    { inv H4.
      have[x[n1' e]]:=era_bind_form H1. subst.
      have[Θ1[Θ2[Δ1[Δ2[A0[s[mrg1[mrg2[tyApp/=tyn]]]]]]]]]:=
        era_bind_inv H1. inv mrg2. inv mrg1.
      have[m' e]:=era_app0_form tyApp. subst.
      have[A1[B1[s0[_[tyS _]]]]]:=era_app0_inv tyApp.
      have[y e]:=era_send0_form tyS. subst.
      have[r3[r4[A2[B2[_[_ tyv]]]]]]:=era_send0_inv tyS.
      have e:=era_cvar_form tyv. subst.
      have[r[A3[_[js _]]]]:=era_cvar_inv tyv. inv js. }
    { inv H4.
      have[x[n1' e]]:=era_bind_form H1. subst.
      have[Θ1[Θ2[Δ1[Δ2[A0[s[mrg1[mrg2[tyApp/=tyn]]]]]]]]]:=
        era_bind_inv H1. inv mrg2. inv mrg1.
      have[m' e]:=era_app0_form tyApp. subst.
      have[A1[B1[s0[_[tyS _]]]]]:=era_app0_inv tyApp.
      have[y e]:=era_send0_form tyS. subst.
      have[r3[r4[A2[B2[_[_ tyv]]]]]]:=era_send0_inv tyS.
      have e:=era_cvar_form tyv. subst.
      have[r[A3[_[js _]]]]:=era_cvar_inv tyv. inv js. } }

  { move=>m n1 n2 Θ p' ty. inv ty. inv H2. inv H1; inv H3.
    { inv H6.
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
      2:{ have[A2[B2[s2[tyS _]]]]:= dyn_app0_inv tyApp.
          have[r1[r4[A4[B4[_[_ tyv1]]]]]]:=dyn_send0_inv tyS.
          have[r[A5[js _]]]:=dyn_cvar_inv tyv1. inv js. inv H6. }
      have[A2[B2[s2[tyS[tym eqA3]]]]]:= dyn_app0_inv tyApp.
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
              apply: sta_crename.
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
          apply: sta_crename...
          constructor... }
      constructor... }
    { inv H4.
      have[Θ1[Θ2[Δ1[Δ2[A0[s[mrg1[mrg2[tyApp/=tyn]]]]]]]]]:=
        dyn_bind_inv H1. inv mrg2. inv mrg1. inv H4.
      have[A1[B1[s0[tyS _]]]]:=dyn_app0_inv tyApp.
      { have[r1[r3[A2[B2[_[_ tyv]]]]]]:=dyn_send0_inv tyS.
        have[r[A3[js _]]]:=dyn_cvar_inv tyv. inv js. inv H4. } } }

  { admit. }
  { admit. }
  { admit. }
  { admit. }
  { admit. }
  { admit. }
  { move=>p x q y eq1 st ih eq2 Θ p' erp.
    have[x' eq3 erx]:=eproc_congr_type eq1 erp.
    have[y' eqy st']:=ih _ _ erx.
    have[z' eqz erz]:=eproc_congr_type eq2 eqy.
    exists z'...
    apply: proc_congr.
    apply: eq3.
    apply: st'.
    apply: eqz. }
Admitted.
