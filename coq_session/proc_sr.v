From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq zify.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS
  dyn_sr proc_type proc_step proc_occurs proc_act.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma proc_congr0_sym p q : proc_congr0 p q -> proc_congr0 q p.
Proof. elim; move=>*; eauto using proc_congr0. Qed.

Lemma proc_congr0_type Θ p q : Θ ⊢ p -> proc_congr0 p q -> Θ ⊢ q.
Proof with eauto using proc_type, proc_congr0.
  move=>ty. elim: ty q=>{Θ p}.
  { move=>Θ m tym q cgr. inv cgr. }
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
      apply: ihq. apply: proc_congr0_sym... } }
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
      econstructor... } }
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

Lemma proc_congr_exp_inj m p : ⟨ m ⟩ ≡ p -> p = ⟨ m ⟩.
Proof.
  elim=>//={p}.
  move=>y z e1 e2 cr; subst. inv cr.
  move=>y z e1 e2 cr; subst. inv cr.
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
      have tyx1:=sta_rd H5 eq3.
      have tyx2:=sta_rd (sta_ch false tyA) eq4.
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
        with (Ch false (term_cren A (+2)).[ren (+@size (elem term) nil)])
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
      have tyx1:=sta_rd H5 eq3.
      have tyx2:=sta_rd (sta_ch false tyA) eq4.
      have e:=sta_unicity tyx1 tyx2. subst.
      econstructor.
      replace (IO Unit) with (IO Unit).[CVar 1/] by eauto.
      apply: dyn_esubst1...
      apply: key_impure.
      apply: key_impure.
      replace (Ch true (term_cren A (+2)))
        with (Ch true (term_cren A (+2)).[ren (+@size (elem term) nil)])
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
    { inv H5.
    (*   have[Θ1[Θ2[Δ1[Δ2]]]] *)
    (*   have[Θ1[Θ2[Δ1[Δ2[A0[B[s[t[mrg1[mrg2[tyB[tyR[tyn/io_inj eq]]]]]]]]]]]]]:= *)
    (*     dyn_bind_inv H1. inv mrg2. inv mrg1. inv H5. *)
    (*   have[r3[r4[A1[B0[_[_ tyv]]]]]]:=dyn_recv0_inv tyR. *)
    (*   have[r[A2[js _]]]:=dyn_cvar_inv tyv. inv js. inv H5. } *)
    (* { inv H4. inv H5. *)
    (*   have[Θ1[Θ2[Δ1[Δ2[A0[B[s[t[mrg1[mrg2[tyB[tyApp[tyn1/io_inj eq1]]]]]]]]]]]]]:= *)
    (*     dyn_bind_inv H1. inv mrg2. inv mrg1; inv H5. *)
    (*   2:{ have[A1[B1[s1[[tyS _]|[Θ1[Θ2[Δ1[Δ2[mrg1[mrg2[tyS _]]]]]]]]]]]:=dyn_app_inv tyApp. *)
    (*       have[r3[r4[A2[B2[_[_ ty]]]]]]:=dyn_send0_inv tyS. *)
    (*       have[r[A3[js _]]]:=dyn_cvar_inv ty. inv js. *)
    (*       inv mrg1. inv H5. *)
    (*       have[r3[r4[A2[B2[_[_ ty]]]]]]:=dyn_send0_inv tyS. *)
    (*       have[r[A3[js _]]]:=dyn_cvar_inv ty. inv js. } *)
    (*   have[A1[B1[s1[[tyS[tym eq2]]|[Θ1[Θ2[Δ1[Δ2[mrg1[mrg2[tyS[tym eq2]]]]]]]]]]]]:=dyn_app_inv tyApp. *)
    (*   2:{ have[r3[r4[A2[B2[_[eq _]]]]]]:=dyn_send0_inv tyS. *)
    (*       exfalso. solve_conv. } *)
    (*   have[r3[r4[A2[B2[xor1[/pi0_inj[eqA1[eqB1 e]]tyv0]]]]]]:=dyn_send0_inv tyS. subst. *)
    (*   have[r[A3[js[tyA eq3]]]]:=dyn_cvar_inv tyv0. inv js. inv H5. *)
    (*   rewrite<-term_cren_comp in eq3. asimpl in eq3. *)
    (*   rewrite<-term_cren_comp in tyA. asimpl in tyA. *)
    (*   have[e eq4]:=ch_inj eq3. subst. *)
    (*   have e:=merge_emptyL H6 H0. subst. *)
    (*   have[Θ3[Θ4[Δ1[Δ2[A3[B3[s0[t0[mrg1[mrg2[tyB3[tyR[tyn2/io_inj eq5]]]]]]]]]]]]]:= *)
    (*     dyn_bind_inv H3. inv mrg2. inv mrg1. inv H7. *)
    (*   2:{ have[r5[r6[A4[B4[_[_ tyv1]]]]]]:=dyn_recv0_inv tyR. *)
    (*       have[r[A5[js _]]]:=dyn_cvar_inv tyv1. inv js. inv H7. } *)
    (*   have[r5[r6[A4[B4[xor2[/io_inj eq6 tyv1]]]]]]:=dyn_recv0_inv tyR. *)
    (*   have[r[A5[js[tyA5/ch_inj[e eq7]]]]]:=dyn_cvar_inv tyv1. subst. *)
    (*   asimpl in eq7. inv js. inv H7. *)
    (*   rewrite<-term_cren_comp in H5. asimpl in H5. inv H5. *)
    (*   have/act0_inj[eqA2[eqB2 e]]:=conv_trans _ eq4 (conv_sym eq7). subst. *)
    (*   have/=/io_inj eqA0:=conv_trans _ eq2 (sta_conv_subst (m .: ids) eqB1). *)
    (*   have wf:=dyn_type_proc_wf tyv1. inv wf. inv H5. *)
    (*   have[s1 tyCh1]:=dyn_valid tyv0. *)
    (*   have[s2 tyCh2]:=dyn_valid tyv1.  *)
    (*   have{tyCh1}[/sta_act0_inv tyB2/sort_inj e]:=sta_ch_inv tyCh1. subst. *)
    (*   (* have[/sta] *) *)
      



      
      (* have/=[A6[B6[tyAct1[eq8 eq9]]]]:=sta_conv_act0_inv (conv_sym eq4) H11 can_cancel2. *)
      (* have/=[A7[B7[tyAct2[eq10 eq11]]]]:=sta_conv_act0_inv (conv_sym eq7) H11 can_cancel2. *)
      (* have/act0_inj[eq12[eq13 _]]:=conv_trans _ eq8 (conv_sym eq10). *)
      (* have/act0_inj[eq14[eq15 _]]:=eq9. *)
      (* have/act0_inj[eq16[eq17 _]]:=eq11. *)
      admit. }
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
  { admit. }
  { admit. }
  { admit. }
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
          have tyx1:=sta_rd H8 rd1.
          have tyx2:=sta_rd (sta_unit sta_wf_nil) rd2.
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
          have tyx1:=sta_rd H7 rd1.
          have tyx2:=sta_rd (sta_unit sta_wf_nil) rd2.
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
          have tyx1:=sta_rd H8 rd1.
          have tyx2:=sta_rd (sta_unit sta_wf_nil) rd2.
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
          have tyx1:=sta_rd H7 rd1.
          have tyx2:=sta_rd (sta_unit sta_wf_nil) rd2.
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
