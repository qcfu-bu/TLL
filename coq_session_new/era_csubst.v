From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq zify.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS dyn_csubst era_cren.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma era_csubstitution Θ1 Θ2 Γ Δ m m' A σ :
  Θ2 ; Γ ; Δ ⊢ m ~ m' : A -> Θ1 ⊩ σ ⫣ Θ2 ->
  Θ1 ; Γ ; Δ ⊢ csubst σ m ~ csubst σ m' : A.
Proof with eauto using dyn_agree_csubst_key, dyn_sta_agree_csubst, dyn_agree_csubst_empty, key.
  move=>ty. elim: ty Θ1 σ=>{Θ2 Γ Δ m m' A}//=.
  { move=>Θ Γ Δ x s A emp wf shs dhs Θ1 σ agr. econstructor... }
  { move=>Θ Γ Δ A B m m' s k1 k2 tym ihm Θ1 σ agr.
    have wf:=era_type_wf tym. inv wf.
    have[t tyB]:=era_valid tym.
    have agr0:=dyn_sta_agree_csubst agr.
    apply: era_conv.
    2:{ constructor...
        apply: era_ctx_conv0.
        2:{ apply: sta_csubstitution... }
        2:{ apply: ihm... }
        rewrite<-sta_csubst_cren...
        by apply: sta_cren_conv0. }
    { apply: sta_conv_pi0...
      rewrite<-sta_csubst_cren...
      by apply: sta_cren_conv0. }
    { econstructor... } }
  { move=>Θ Γ Δ A B m m' s t k1 k2 tym ihm Θ1 σ agr.
    have wf:=era_type_wf tym. inv wf.
    have[r tyB]:=era_valid tym.
    have agr0:=dyn_sta_agree_csubst agr.
    apply: era_conv.
    2:{ econstructor...
        apply: era_ctx_conv1.
        2:{ apply: sta_csubstitution... }
        2:{ apply: ihm... }
        rewrite<-sta_csubst_cren...
        by apply: sta_cren_conv0. }
    { apply: sta_conv_pi1...
      rewrite<-sta_csubst_cren...
      by apply: sta_cren_conv0. }
    { econstructor... } }
  { move=>Θ Γ Δ A B m m' n s tym ihm tyn Θ1 σ agr.
    have[t tyP]:=era_valid tym.
    have[r[tyB/sort_inj e]]:=sta_pi0_inv tyP. subst.
    have agr0:=dyn_sta_agree_csubst agr.
    apply: era_conv.
    2:{ econstructor...
        exact: sta_csubstitution. }
    { apply: sta_conv_beta.
      rewrite<-sta_csubst_cren...
      by apply: sta_cren_conv0. }
    { apply: sta_esubst... by []. } }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m m' n n' s mrg1 mrg2 tym ihm tyn ihn Θx σ agr.
    have[Θa[Θb[mrg3[agr1 agr2]]]]:=dyn_agree_csubst_merge agr mrg1.
    have[t tyP]:=era_valid tym.
    have[r[tyB/sort_inj e]]:=sta_pi1_inv tyP. subst.
    have{}ihm:=ihm _ _ agr1.
    have{}ihn:=ihn _ _ agr2.
    apply: era_conv.
    2:{ econstructor... }
    apply: sta_conv_beta.
    rewrite<-sta_csubst_cren.
    apply: sta_cren_conv0...
    apply: dyn_sta_agree_csubst...
    apply: sta_esubst... by []. }
  { move=>Θ Γ Δ A B m n n' t tyS tym tyn ihn Θ1 σ agr.
    have[s[r[ord[tyA[tyB _]]]]]:=sta_sig0_inv tyS.
    econstructor...
    apply: sta_csubstitution...
    apply: era_conv.
    apply: sta_conv_beta.
    rewrite<-sta_csubst_cren.
    apply: conv_sym. apply: sta_cren_conv0...
    apply: dyn_sta_agree_csubst...
    apply: ihn...
    apply: sta_esubst...
    by []. apply: sta_csubstitution... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m m' n n' t mrg1 mrg2 tyS tym ihm tyn ihn Θx σ agr.
    have[s[r[ord1[ord2[tyA[tyB _]]]]]]:=sta_sig1_inv tyS.
    have[Θa[Θb[mrg3[agr1 agr2]]]]:=dyn_agree_csubst_merge agr mrg1.
    econstructor...
    apply: era_conv.
    apply: sta_conv_beta.
    rewrite<-sta_csubst_cren.
    apply: conv_sym. apply: sta_cren_conv0...
    apply: dyn_sta_agree_csubst...
    apply: ihn...
    apply: sta_esubst...
    by []. }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m m' n n' s r t mrg1 mrg2 tyC tym ihm tyn ihn Θx σ agr.
    have[Θa[Θb[mrgx[agr1 agr2]]]]:=dyn_agree_csubst_merge agr mrg1.
    have{}ihm:=ihm _ _ agr1.
    have{}ihn:=ihn _ _ agr2.
    have wf:=sta_type_wf tyC. inv wf.
    have wf:=era_type_wf tyn. inv wf. inv H4.
    have[r0 tys]:=sta_valid tyC.
    have[s2[r1[ord[tyA[tyB/sort_inj e]]]]]:=sta_sig0_inv H2. subst.
    have h:(csubst σ C).[Pair0 (Var 1) (Var 0) t .: ren (+2)] =
            csubst σ C.[Pair0 (Var 1) (Var 0) t .: ren (+2)].
    { apply: sta_csubst_comm...
      apply: term_cren_subst_pair0. }
    apply: era_conv.
    2:{ apply: era_letin0...
        apply: sta_csubstitution...
        rewrite h.
        apply: era_conv.
        rewrite<-sta_csubst_cren.
        apply: conv_sym. apply: sta_cren_conv0...
        apply: dyn_sta_agree_csubst...
        apply: ihn.
        apply: sta_csubstitution...
        apply: sta_conv.
        2:{ apply: sta_substitution...
            constructor.
            replace (ren (+2)) with (ids >> ren (+1) >> ren (+1)) by autosubst.
            econstructor...
            econstructor...
            simpl.
            constructor.
            apply: sta_eweaken.
            4:{ eauto. }
            3:{ apply: sta_weaken. apply: H2. apply: H7. }
            by autosubst.
            by autosubst.
            replace A.[ren (+2)] with A.[ren (+1)].[ren (+1)] by autosubst.
            repeat constructor...
            asimpl. repeat constructor... }
        by simpl. constructor... }
    { apply: conv_trans.
      apply: sta_conv_subst.
      rewrite<-sta_csubst_cren.
      apply: sta_cren_conv0...
      apply: dyn_sta_agree_csubst...
      apply: sta_conv_beta.
      rewrite<-sta_csubst_cren.
      apply: sta_cren_conv0...
      apply: dyn_sta_agree_csubst... }
    { apply: sta_esubst... by []. } }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m m' n n' s r1 r2 t mrg1 mrg2 tyC tym ihm tyn ihn Θx σ agr.
    have[Θa[Θb[mrgx[agr1 agr2]]]]:=dyn_agree_csubst_merge agr mrg1.
    have{}ihm:=ihm _ _ agr1.
    have{}ihn:=ihn _ _ agr2.
    have wf:=sta_type_wf tyC. inv wf.
    have wf:=era_type_wf tyn. inv wf. inv H4.
    have[r0 tys]:=sta_valid tyC.
    have[s2[rx[ord1[ord2[tyA[tyB/sort_inj e]]]]]]:=sta_sig1_inv H2. subst.
    have h:(csubst σ C).[Pair1 (Var 1) (Var 0) t .: ren (+2)] =
            csubst σ C.[Pair1 (Var 1) (Var 0) t .: ren (+2)].
    { apply: sta_csubst_comm...
      apply: term_cren_subst_pair1. }
    apply: era_conv.
    2:{ apply: era_letin1...
        apply: sta_csubstitution...
        rewrite h.
        apply: era_conv.
        rewrite<-sta_csubst_cren.
        apply: conv_sym. apply: sta_cren_conv0...
        apply: dyn_sta_agree_csubst...
        apply: ihn.
        apply: sta_csubstitution...
        apply: sta_conv.
        2:{ apply: sta_substitution...
            constructor.
            replace (ren (+2)) with (ids >> ren (+1) >> ren (+1)) by autosubst.
            econstructor...
            econstructor...
            simpl.
            constructor.
            apply: sta_eweaken.
            4:{ eauto. }
            3:{ apply: sta_weaken. apply: H2. apply: H8. }
            by autosubst.
            by autosubst.
            replace A.[ren (+2)] with A.[ren (+1)].[ren (+1)] by autosubst.
            repeat constructor...
            asimpl. repeat constructor... }
        by simpl. constructor... }
    { apply: conv_trans.
      apply: sta_conv_subst.
      rewrite<-sta_csubst_cren.
      apply: sta_cren_conv0...
      apply: dyn_sta_agree_csubst...
      apply: sta_conv_beta.
      rewrite<-sta_csubst_cren.
      apply: sta_cren_conv0...
      apply: dyn_sta_agree_csubst... }
    { apply: sta_esubst... by []. } }
  { move=>Θ Γ Δ A m m' k1 k2 tym ihm Θx σ agr.
    have wf:=era_type_wf tym. inv wf.
    have[t tyA]:=era_valid tym.
    apply: era_conv.
    3:{ apply: H4. }
    2:{ constructor...
        apply: era_ctx_conv1.
        2:{ apply: sta_csubstitution... }
        rewrite<-sta_csubst_cren.
        apply: sta_cren_conv0...
        apply: dyn_sta_agree_csubst...
        rewrite sta_csubst_comp...
        apply: era_conv.
        2:{ apply: ihm... }
        rewrite<-sta_csubst_cren.
        apply: conv_sym. apply: sta_cren_conv0...
        apply: dyn_sta_agree_csubst...
        apply: sta_csubstitution... }
    rewrite<-sta_csubst_cren.
    apply: sta_cren_conv0...
    apply: dyn_sta_agree_csubst... }
  { move=>Θ Γ Δ emp wf k Θx σ agr. constructor... }
  { move=>Θ Γ Δ emp wf k Θx σ agr. constructor... }
  { move=>Θ Γ Δ emp wf k Θx σ agr. constructor... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m m' n1 n1' n2 n2' s mrg1 mrg2
           tyA tym ihm tyn1 ihn1 tyn2 ihn2 Θx σ agr.
    have[Θa[Θb[mrgx[agr1 arg2]]]]:=dyn_agree_csubst_merge agr mrg1.
    have wf:=sta_type_wf tyA. inv wf.
    apply: era_conv.
    2:{ apply: era_ifte...
        apply: sta_csubstitution...
        rewrite sta_csubst_comp'...
        2:{ move=>[|x] σ'//=. }
        apply: era_conv.
        2:{ apply: ihn1... }
        rewrite<-sta_csubst_cren.
        apply: conv_sym. apply: sta_cren_conv0...
        apply: dyn_sta_agree_csubst...
        apply: sta_csubstitution...
        apply: sta_esubst... by []. constructor...
        rewrite sta_csubst_comp'...
        2:{ move=>[|x] σ'//=. }
        apply: era_conv.
        2:{ apply: ihn2... }
        rewrite<-sta_csubst_cren.
        apply: conv_sym. apply: sta_cren_conv0...
        apply: dyn_sta_agree_csubst...
        apply: sta_csubstitution...
        apply: sta_esubst... by []. constructor... }
    { apply: conv_trans.
      apply: sta_conv_beta.
      rewrite<-sta_csubst_cren.
      apply: sta_cren_conv0...
      apply: dyn_sta_agree_csubst...
      apply: sta_conv_subst.
      rewrite<-sta_csubst_cren.
      apply: sta_cren_conv0...
      apply: dyn_sta_agree_csubst... }
    { apply: sta_esubst... by []. } }
  { move=>Θ Γ Δ m A tym ihm Θx σ agr. constructor... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m m' n n' A B s t mrg1 mrg2 tyB tym ihm tyn ihn Θx σ agr.
    have[Θa[Θb[mrgx[agr1 agr2]]]]:=dyn_agree_csubst_merge agr mrg1.
    econstructor... }
  { move=>Θ Γ Δ r x A js wf k tyA Θx σ agr.
    have tyx:=dyn_agree_csubst_just agr tyA js.
    have agr0:=dyn_sta_agree_csubst agr.
    have[c e]:=agr0 x. rewrite e. rewrite e in tyx. move=>{e}.
    have[r0[A0[js0[tyA0/ch_inj[e eq]]]]]:=dyn_cvar_inv tyx. subst.
    replace (Ch r0 A.[ren (+size Γ)]) with (Ch r0 A).[ren (+size Γ)] by eauto.
    replace (CVar c) with (CVar c).[ren (+size Γ)] by eauto.
    apply: era_rename...
    2:{ apply: dyn_wf_agree_ren... }
    apply: era_conv.
    2:{ constructor... }
    2:{ constructor... }
    apply: sta_conv_ch. asimpl. asimpl in eq. apply: conv_sym... }
  { move=>Θ Γ Δ m m' A tym ihm Θ1 σ agr. 
    have wf:=era_type_wf tym. inv wf.
    have[tyA _]:=sta_ch_inv H4.
    apply: era_conv.
    2:{ constructor.
        apply: era_ctx_conv1.
        3:{ apply: ihm... }
        apply: sta_conv_ch.
        rewrite<-sta_csubst_cren...
        apply: sta_cren_conv0...
        constructor.
        apply: sta_csubstitution... }
    apply: sta_conv_io.
    apply: sta_conv_ch.
    rewrite<-sta_csubst_cren...
    apply: sta_cren_conv0...
    econstructor.
    constructor... }
  { move=>Θ Γ Δ r1 r2 A B m m' xor tym ihm Θ1 σ agr. econstructor... }
  { move=>Θ Γ Δ r1 r2 A B m m' xor tym ihm Θ1 σ agr. econstructor... }
  { move=>Θ Γ Δ r1 r2 A B m m' xor tym ihm Θ1 σ agr. econstructor... }
  { move=>Θ Γ Δ r1 r2 A B m m' xor tym ihm Θ1 σ agr. econstructor... }
  { move=>Θ Γ Δ m m' tym ihm Θ1 σ agr. econstructor... }
  { move=>Θ Γ Δ m m' tym ihm Θ1 σ agr. econstructor... }
  { move=>Θ Γ Δ A B m m' s eq tym ihm tyB Θ1 σ agr. apply: era_conv... }
Qed.
