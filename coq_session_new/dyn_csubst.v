From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq zify.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS dyn_inv dyn_cren sta_csubst proc_type.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "Θ1 ⊩ σ ⫣ Θ2"
  (at level 50, σ, Θ2 at next level).
Inductive dyn_agree_csubst :
  dyn_ctx -> (var -> term) -> dyn_ctx -> Prop :=
| dyn_agree_csubst_nil Θ :
  proc_wf Θ ->
  Θ ⊩ cids ⫣ Θ
| dyn_agree_csubst_pad Θ1 σ Θ2 :
  Θ1 ⊩ σ ⫣ Θ2 ->
  _: Θ1 ⊩ (σ >>> term_cren^~(+1)) ⫣ Θ2
| dyn_agree_csubst_ty Θ1 σ Θ2 r A :
  Θ1 ⊩ σ ⫣ Θ2 ->
  nil ⊢ A : Proto ->
  Ch r (term_csubst A σ) :L Θ1 ⊩ upp σ ⫣ (Ch r A) :L Θ2
| dyn_agree_csubst_n Θ1 σ Θ2 :
  Θ1 ⊩ σ ⫣ Θ2 ->
  _: Θ1 ⊩ upp σ ⫣ _: Θ2
| dyn_agree_csubst_wk0 Θ1 σ Θ2 x :
  Θ1 ⊩ σ ⫣ Θ2 ->
  Θ1 ⊩ CVar x .: σ ⫣ _: Θ2
| dyn_agree_csubst_wk1 Θa Θb Θ1 σ Θ2 x r A :
  Θa ∘ Θb => Θ1 ->
  Θa ⊩ σ ⫣ Θ2 ->
  Θb ; nil ; nil ⊢ CVar x : Ch r A ->
  Θ1 ⊩ CVar x .: σ ⫣ Ch r A :L Θ2
| dyn_agree_csubst_conv Θ1 σ Θ2 A B r :
  A === B ->
  nil ⊢ B : Proto ->
  Θ1 ⊩ σ ⫣ Ch r A :L Θ2 ->
  Θ1 ⊩ σ ⫣ Ch r B :L Θ2
where "Θ1 ⊩ σ ⫣ Θ2" := (dyn_agree_csubst Θ1 σ Θ2).

Lemma dyn_sta_agree_csubst Θ1 Θ2 σ :
  Θ1 ⊩ σ ⫣ Θ2 -> sta_agree_csubst σ.
Proof with eauto.
  elim=>{Θ1 Θ2 σ}...
  { move=>Θ wf x. by exists x. }
  { move=>Θ1 σ Θ2 agr ih x. simpl.
    have[c->]//=:=ih x. by exists c.+1. }
  { move=>Θ1 σ Θ2 r A agr ih tyA.
    move=>[|x]//=. by exists 0.
    have[c->]//=:=ih x. by exists c.+1. }
  { move=>Θ1 σ Θ2 agr ih.
    move=>[|x]//=. by exists 0.
    have[c->]//=:=ih x. by exists c.+1. }
  { move=>Θ1 σ Θ2 x agr ih.
    move=>[|i]//=. by exists x. }
  { move=>Θa Θb Θ1 σ Θ2 x r A mrg agr ih ty.
    move=>[|i]//=. by exists x. }
Qed.

Lemma dyn_csubst_cren Θ1 Θ2 σ m :
  Θ1 ⊩ σ ⫣ Θ2 -> term_cren m (csubst_ren σ) = term_csubst m σ.
Proof.
  move=>agr. apply: sta_csubst_cren.
  apply: dyn_sta_agree_csubst.
  apply: agr.
Qed.

Lemma dyn_agree_csubst_empty Θ1 Θ2 σ :
  Θ1 ⊩ σ ⫣ Θ2 -> dyn_empty Θ2 -> dyn_empty Θ1.
Proof with eauto using dyn_empty.
  elim=>{Θ1 Θ2 σ}...
  { move=>Θ1 σ Θ2 r A agr ih tyA emp. inv emp. }
  { move=>Θ1 σ Θ2 agr ih emp. inv emp... }
  { move=>Θ1 σ Θ2 x agr ih emp. inv emp... }
  { move=>Θa Θb Θ1 σ Θ2 x r A mrg agr ih ty emp. inv emp. }
  { move=>Θ1 σ Θ2 A B s eq tyB agr ih emp. inv emp. }
Qed.

Lemma dyn_agree_csubst_key Θ1 Θ2 σ s :
  Θ1 ⊩ σ ⫣ Θ2 -> Θ2 ▷ s -> Θ1 ▷ s.
Proof with eauto using key.
  move=>agr. elim: agr s=>{Θ1 Θ2 σ}...
  { move=>Θ1 σ Θ2 r A agr ih tyA t k. inv k... }
  { move=>Θ1 σ Θ2 agr ih s k. inv k... }
  { move=>Θ1 σ Θ2 x agr ih s k. inv k... }
  { move=>Θa Θb Θ1 σ Θ2 x r A mrg agr ih ty s k. inv k.
    have{}ih:=ih _ H3.
    exact: key_impure. }
  { move=>Θ1 σ Θ2 A B s eq tyB agr ih t k. inv k.
    exact: key_impure. }
Qed.

Lemma proc_wf_merge_inv Θ1 Θ2 Θ :
  Θ1 ∘ Θ2 => Θ -> proc_wf Θ -> proc_wf Θ1 /\ proc_wf Θ2. 
Proof with eauto using proc_wf.
  elim=>{Θ1 Θ2 Θ}...
  { move=>Θ1 Θ2 Θ m mrg ih wf. inv wf. }
  { move=>Θ1 Θ2 Θ m mrg ih wf. inv wf.
    have[wf1 wf2]:=ih H1. repeat constructor... }
  { move=>Θ1 Θ2 Θ m mrg ih wf. inv wf.
    have[wf1 wf2]:=ih H1. repeat constructor... }
  { move=>Θ1 Θ2 Θ mrg ih wf. inv wf.
    have[wf1 wf2]:=ih H0. repeat constructor... }
Qed.

Lemma dyn_agree_csubst_merge Θ1 Θ2 Θa Θb σ :
  Θ1 ⊩ σ ⫣ Θ2 -> Θa ∘ Θb => Θ2 ->
  exists Θa' Θb',
    Θa' ∘ Θb' => Θ1 /\
    Θa' ⊩ σ ⫣ Θa /\
    Θb' ⊩ σ ⫣ Θb.
Proof with eauto 6 using merge, dyn_agree_csubst, dyn_agree_csubst_key.
  move=>agr. elim: agr Θa Θb=>{Θ1 Θ2 σ}...
  { move=>Θ wf Θa Θb mrg.
    have[wf1 wf2]:=proc_wf_merge_inv mrg wf.
    exists Θa. exists Θb. repeat split... }
  { move=>Θ1 σ Θ2 agr ih Θa Θb mrg.
    have[Θa'[Θb'[mrg'[agr1 agr2]]]]:=ih _ _ mrg.
    exists (_: Θa'). exists (_: Θb'). repeat split... }
  { move=>Θ1 σ Θ2 r A agr ih tyA Θa Θb mrg. inv mrg.
    { have[Θa[Θb[mrg'[agr1 agr2]]]]:=ih _ _ H2.
      exists (Ch r (term_csubst A σ) :L Θa). exists (_: Θb)... }
    { have[Θa[Θb[mrg'[agr1 agr2]]]]:=ih _ _ H2.
      exists (_: Θa). exists (Ch r (term_csubst A σ) :L Θb)... } }
  { move=>Θ1 σ Θ2 agr ih Θa Θb mrg. inv mrg.
    have[Θa[Θb[mrg'[agr1 agr2]]]]:=ih _ _ H2.
    exists (_: Θa). exists (_: Θb)... }
  { move=>Θ1 σ Θ2 x agr ih Θa Θb mrg. inv mrg.
    have[Θa[Θb[mrg'[agr1 agr2]]]]:=ih _ _ H2.
    exists Θa. exists Θb... }
  { move=>Θa Θb Θ1 σ Θ2 x r A mrg agr ih ty Θa' Θb' mrg'. inv mrg'.
    { have[Θa'[Θb'[mrg'[agr1 agr2]]]]:=ih _ _ H2.
      have[Θc[mrg1 mrg2]]:=merge_splitL mrg mrg'.
      exists Θc. exists Θb'. repeat split... }
    { have[Θa'[Θb'[mrg'[agr1 agr2]]]]:=ih _ _ H2.
      have[Θc[mrg1 mrg2]]:=merge_splitR mrg mrg'.
      exists Θa'. exists Θc. repeat split... apply: merge_sym... } }
  { move=>Θ1 σ Θ2 A B r eq tyB agr ih Θa Θb mrg. inv mrg.
    { have[Θa[Θb[mrg'[agr1 agr2]]]]:=ih _ _ (merge_right1 (Ch r A) H2).
      exists Θa. exists Θb... }
    { have[Θa[Θb[mrg'[agr1 agr2]]]]:=ih _ _ (merge_right2 (Ch r A) H2).
      exists Θa. exists Θb... } }
Qed.

Lemma dyn_agree_csubst_wf Θ1 Θ2 σ : Θ1 ⊩ σ ⫣ Θ2 -> proc_wf Θ2.
Proof with eauto using proc_wf.
  elim=>{Θ1 Θ2 σ}...
  { move=>Θa Θb Θ1 σ Θ2 x r A mrg agr wf tyx.
    have[s tyC]:=dyn_valid tyx.
    have[tyA/sort_inj e]:=sta_ch_inv tyC. subst.
    constructor... }
  { move=>Θ1 σ Θ2 A B r eq tyB agr wf. inv wf.
    constructor... }
Qed.

Lemma dyn_agree_csubst_just Θ1 Θ2 σ x r A :
  Θ1 ⊩ σ ⫣ Θ2 ->
  nil ⊢ A : Proto ->
  dyn_just Θ2 x (Ch r A) ->
  Θ1 ; nil ; nil ⊢ σ x : (Ch r A).
Proof with eauto using dyn_agree_csubst_empty, dyn_sta_agree_csubst, dyn_wf, key.
  move=>agr. elim: agr x r A=>{Θ1 Θ2 σ}.
  { move=>Θ x r A ty js. econstructor.
    2:{ constructor... }
    2:{ constructor... }
    by asimpl. }
  { move=>Θ1 σ Θ2 agr ih x r A tyA js. asimpl.
    apply: dyn_cweaken... }
  { move=>Θ1 σ Θ2 r A agr ih x tyA r0 A0 tyA0 js. inv js. asimpl.
    have/=js:dyn_just (Ch r0 (term_csubst A σ) :L Θ1) 0 (term_cren (Ch r0 (term_csubst A σ)) (+1)).
    {  constructor... } 
    apply: dyn_conv.
    2:{ constructor...
        apply: sta_crename.
        apply: sta_csubstitution... }
    asimpl. apply: sta_conv_ch.
    apply: conv_trans.
    apply: sta_cren_conv0.
    rewrite<-sta_csubst_cren.
    apply: sta_cren_conv0...
    apply: dyn_sta_agree_csubst...
    apply: conv_sym.
    apply: sta_cren_conv0...
    constructor... }
  { move=>Θ1 σ Θ2 agr ih x r A tyA js. inv js.
    destruct A0; inv H0. asimpl.
    have tyA0: [::] ⊢ A0 : Proto.
    { apply (sta_crename (-1)) in tyA.
      rewrite<-term_cren_comp in tyA.
      move:tyA. 
      have->:(+1) >>> ( - 1) = id.
      { f_ext. move=>x. asimpl. lia.}
      by rewrite term_cren_id. }
    have tyx:=ih _ _ _ tyA0 H2.
    apply: dyn_conv.
    2:{ apply: dyn_cweaken... }
    apply: sta_conv_ch. apply: conv_sym. apply: sta_cren_conv0...
    constructor... }
  { move=>Θ1 σ Θ2 x agr ih y r A tyA js. inv js.
    destruct A0; inv H0. asimpl.
    have tyA0: [::] ⊢ A0 : Proto.
    { apply (sta_crename (-1)) in tyA.
      rewrite<-term_cren_comp in tyA.
      move:tyA. 
      have->:(+1) >>> ( - 1) = id.
      { f_ext. move=>i. asimpl. lia.}
      by rewrite term_cren_id. }
    have tyx:=ih _ _ _ tyA0 H2.
    apply: dyn_conv.
    2:{ apply: tyx. }
    2:{ constructor... }
    apply: sta_conv_ch. apply: conv_sym. apply: sta_cren_conv0... }
  { move=>Θa Θb Θ1 σ Θ2 x r A mrg agr ih tyx y r0 A0 tyA0 js. inv js. asimpl.
    have tyA: [::] ⊢ A : Proto.
    { apply (sta_crename (-1)) in tyA0.
      rewrite<-term_cren_comp in tyA0.
      move:tyA0. 
      have->:(+1) >>> ( - 1) = id.
      { f_ext. move=>i. asimpl. lia.}
      by rewrite term_cren_id. }
    have emp:=dyn_agree_csubst_empty agr H2.
    have e:=merge_emptyL mrg emp. subst.
    apply: dyn_conv.
    2:{ apply: tyx. }
    apply: sta_conv_ch. 
    apply: conv_sym. apply: sta_cren_conv0...
    constructor... }
  { move=>Θ1 σ Θ2 A B s eq tyB agr ih x r A0 tyA0 js. inv js.
    have wf:=dyn_agree_csubst_wf agr. inv wf.
    have/=js:dyn_just (Ch r A :L Θ2) 0 (term_cren (Ch r A) (+1)).
    { constructor... }
    apply: dyn_conv.
    2:{ apply: ih. 2:{ apply: js. }
        apply: sta_crename... }
    apply: sta_conv_ch.
    apply: conv_trans. apply: sta_cren_conv0...
    apply: conv_sym. apply: sta_cren_conv0...
    constructor... }
Qed.

Lemma dyn_csubstitution Θ1 Θ2 Γ Δ m A σ :
  Θ2 ; Γ ; Δ ⊢ m : A -> Θ1 ⊩ σ ⫣ Θ2 ->
  Θ1 ; Γ ; Δ ⊢ term_csubst m σ : A.
Proof with eauto using dyn_agree_csubst_key, dyn_sta_agree_csubst, dyn_agree_csubst_empty.
  move=>ty. elim: ty Θ1 σ=>{Θ2 Γ Δ m A}//=.
  { move=>Θ Γ Δ x s A emp wf shs dhs Θ1 σ agr. econstructor... }
  { move=>Θ Γ Δ A B m s k1 k2 tym ihm Θ1 σ agr.
    have wf:=dyn_type_wf tym. inv wf.
    have[t tyB]:=dyn_valid tym.
    have agr0:=dyn_sta_agree_csubst agr.
    apply: dyn_conv.
    2:{ constructor...
        apply: dyn_ctx_conv0.
        2:{ apply: sta_csubstitution... }
        2:{ apply: ihm... }
        rewrite<-sta_csubst_cren...
        by apply: sta_cren_conv0. }
    { apply: sta_conv_pi0...
      rewrite<-sta_csubst_cren...
      by apply: sta_cren_conv0. }
    { econstructor... } }
  { move=>Θ Γ Δ A B m s t k1 k2 tym ihm Θ1 σ agr.
    have wf:=dyn_type_wf tym. inv wf.
    have[r tyB]:=dyn_valid tym.
    have agr0:=dyn_sta_agree_csubst agr.
    apply: dyn_conv.
    2:{ econstructor...
        apply: dyn_ctx_conv1.
        2:{ apply: sta_csubstitution... }
        2:{ apply: ihm... }
        rewrite<-sta_csubst_cren...
        by apply: sta_cren_conv0. }
    { apply: sta_conv_pi1...
      rewrite<-sta_csubst_cren...
      by apply: sta_cren_conv0. }
    { econstructor... } }
  { move=>Θ Γ Δ A B m n s tym ihm tyn Θ1 σ agr.
    have[t tyP]:=dyn_valid tym.
    have[r[tyB/sort_inj e]]:=sta_pi0_inv tyP. subst.
    have agr0:=dyn_sta_agree_csubst agr.
    apply: dyn_conv.
    2:{ econstructor...
        exact: sta_csubstitution. }
    { apply: sta_conv_beta.
      rewrite<-sta_csubst_cren...
      by apply: sta_cren_conv0. }
    { apply: sta_esubst... by []. } }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n s mrg1 mrg2 tym ihm tyn ihn Θx σ agr.
    have[Θa[Θb[mrg3[agr1 agr2]]]]:=dyn_agree_csubst_merge agr mrg1.
    have[t tyP]:=dyn_valid tym.
    have[r[tyB/sort_inj e]]:=sta_pi1_inv tyP. subst.
    have{}ihm:=ihm _ _ agr1.
    have{}ihn:=ihn _ _ agr2.
    apply: dyn_conv.
    2:{ econstructor... }
    apply: sta_conv_beta.
    rewrite<-sta_csubst_cren.
    apply: sta_cren_conv0...
    apply: dyn_sta_agree_csubst...
    apply: sta_esubst... by []. }
  { move=>Θ Γ Δ A B m n t tyS tym tyn ihn Θ1 σ agr.
    have[s[r[ord[tyA[tyB _]]]]]:=sta_sig0_inv tyS.
    econstructor...
    apply: sta_csubstitution...
    apply: dyn_conv.
    apply: sta_conv_beta.
    rewrite<-sta_csubst_cren.
    apply: conv_sym. apply: sta_cren_conv0...
    apply: dyn_sta_agree_csubst...
    apply: ihn...
    apply: sta_esubst...
    by []. apply: sta_csubstitution... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n t mrg1 mrg2 tyS tym ihm tyn ihn Θx σ agr.
    have[s[r[ord1[ord2[tyA[tyB _]]]]]]:=sta_sig1_inv tyS.
    have[Θa[Θb[mrg3[agr1 agr2]]]]:=dyn_agree_csubst_merge agr mrg1.
    econstructor...
    apply: dyn_conv.
    apply: sta_conv_beta.
    rewrite<-sta_csubst_cren.
    apply: conv_sym. apply: sta_cren_conv0...
    apply: dyn_sta_agree_csubst...
    apply: ihn...
    apply: sta_esubst...
    by []. }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r t mrg1 mrg2 tyC tym ihm tyn ihn Θx σ agr.
    have[Θa[Θb[mrgx[agr1 agr2]]]]:=dyn_agree_csubst_merge agr mrg1.
    have{}ihm:=ihm _ _ agr1.
    have{}ihn:=ihn _ _ agr2.
    have wf:=sta_type_wf tyC. inv wf.
    have wf:=dyn_type_wf tyn. inv wf. inv H4.
    have[r0 tys]:=sta_valid tyC.
    have[s2[r1[ord[tyA[tyB/sort_inj e]]]]]:=sta_sig0_inv H2. subst.
    have h:(term_csubst C σ).[Pair0 (Var 1) (Var 0) t .: ren (+2)] =
           term_csubst C.[Pair0 (Var 1) (Var 0) t .: ren (+2)] σ.
    { apply: sta_csubst_comm...
      apply: term_cren_subst_pair0. }
    apply: dyn_conv.
    2:{ apply: dyn_letin0...
        apply: sta_csubstitution...
        rewrite h.
        apply: dyn_conv.
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
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r1 r2 t mrg1 mrg2 tyC tym ihm tyn ihn Θx σ agr.
    have[Θa[Θb[mrgx[agr1 agr2]]]]:=dyn_agree_csubst_merge agr mrg1.
    have{}ihm:=ihm _ _ agr1.
    have{}ihn:=ihn _ _ agr2.
    have wf:=sta_type_wf tyC. inv wf.
    have wf:=dyn_type_wf tyn. inv wf. inv H4.
    have[r0 tys]:=sta_valid tyC.
    have[s2[rx[ord1[ord2[tyA[tyB/sort_inj e]]]]]]:=sta_sig1_inv H2. subst.
    have h:(term_csubst C σ).[Pair1 (Var 1) (Var 0) t .: ren (+2)] =
           term_csubst C.[Pair1 (Var 1) (Var 0) t .: ren (+2)] σ.
    { apply: sta_csubst_comm...
      apply: term_cren_subst_pair1. }
    apply: dyn_conv.
    2:{ apply: dyn_letin1...
        apply: sta_csubstitution...
        rewrite h.
        apply: dyn_conv.
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
  { move=>Θ Γ Δ A m k1 k2 tym ihm Θx σ agr.
    have wf:=dyn_type_wf tym. inv wf.
    have[t tyA]:=dyn_valid tym.
    apply: dyn_conv.
    3:{ apply: H4. }
    2:{ constructor...
        apply: dyn_ctx_conv1.
        2:{ apply: sta_csubstitution... }
        rewrite<-sta_csubst_cren.
        apply: sta_cren_conv0...
        apply: dyn_sta_agree_csubst...
        rewrite sta_csubst_comp...
        apply: dyn_conv.
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
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m n1 n2 s mrg1 mrg2 tyA tym ihm tyn1 ihn1 tyn2 ihn2 Θx σ agr.
    have[Θa[Θb[mrgx[agr1 arg2]]]]:=dyn_agree_csubst_merge agr mrg1.
    have wf:=sta_type_wf tyA. inv wf.
    apply: dyn_conv.
    2:{ apply: dyn_ifte...
        apply: sta_csubstitution...
        rewrite sta_csubst_comp'...
        2:{ move=>[|x] σ'//=. }
        apply: dyn_conv.
        2:{ apply: ihn1... }
        rewrite<-sta_csubst_cren.
        apply: conv_sym. apply: sta_cren_conv0...
        apply: dyn_sta_agree_csubst...
        apply: sta_csubstitution...
        apply: sta_esubst... by []. constructor...
        rewrite sta_csubst_comp'...
        2:{ move=>[|x] σ'//=. }
        apply: dyn_conv.
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
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m n A B s t mrg1 mrg2 tyB tym ihm tyn ihn Θx σ agr.
    have[Θa[Θb[mrgx[agr1 agr2]]]]:=dyn_agree_csubst_merge agr mrg1.
    econstructor... }
  { move=>Θ Γ Δ r x A js wf k tyA Θx σ agr.
    have tyx:=dyn_agree_csubst_just agr tyA js.
    have agr0:=dyn_sta_agree_csubst agr.
    have[c e]:=agr0 x. rewrite e. rewrite e in tyx. move=>{e}.
    replace (Ch r A.[ren (+size Γ)]) with (Ch r A).[ren (+size Γ)] by eauto.
    replace (CVar c) with (CVar c).[ren (+size Γ)] by eauto.
    apply: dyn_rename...
    apply: dyn_wf_agree_ren... }
  { move=>Θ Γ Δ m A tym ihm Θ1 σ agr. 
    have wf:=dyn_type_wf tym. inv wf.
    have[tyA _]:=sta_ch_inv H4.
    apply: dyn_conv.
    2:{ constructor.
        apply: dyn_ctx_conv1.
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
  { move=>Θ Γ Δ r1 r2 A B m xor tym ihm Θ1 σ agr. econstructor... }
  { move=>Θ Γ Δ r1 r2 A B m xor tym ihm Θ1 σ agr. econstructor... }
  { move=>Θ Γ Δ r1 r2 A B m xor tym ihm Θ1 σ agr. econstructor... }
  { move=>Θ Γ Δ r1 r2 A B m xor tym ihm Θ1 σ agr. econstructor... }
  { move=>Θ Γ Δ m tym ihm Θ1 σ agr. econstructor... }
  { move=>Θ Γ Δ m tym ihm Θ1 σ agr. econstructor... }
  { move=>Θ Γ Δ A B m s eq tym ihm tyB Θ1 σ agr. apply: dyn_conv... }
Qed.

Definition exch := CVar 1 .: CVar 0 .: (fun x => CVar x.+2).

Lemma dyn_csubst_exch Θ Γ Δ m A X Y :
  X :L Y :L Θ ; Γ ; Δ ⊢ m : A ->
  Y :L X :L Θ ; Γ ; Δ ⊢ term_csubst m exch : A.
Proof with eauto using key_impure, dyn_agree_csubst, dyn_wf, key.
  move=>ty. apply: dyn_csubstitution...
  have wf:=dyn_type_proc_wf ty. inv wf. inv H1.
  have[Θ0[emp mrg]]:=dyn_type_empty ty.
  inv mrg. inv H1. inv emp. inv H0.
  have agr0:sta_agree_csubst (λ x : var, CVar x.+2).
  { move=>x. by exists x.+2. }
  unfold exch.
  apply: dyn_agree_csubst_conv.
  apply: (sta_cren_conv0 (+1)).
  eauto. apply: H2.
  econstructor.
  2:{ apply: dyn_agree_csubst_conv.
      apply: (sta_cren_conv0 (+1)).
      eauto. apply: H4.
      econstructor.
      2:{ have->: (fun x => CVar x.+2) = (cids >>> term_cren^~ (+1)) >>> term_cren^~ (+1)
            by autosubst.
          apply: dyn_agree_csubst_pad.
          apply: dyn_agree_csubst_pad.
          constructor... }
      2:{ replace (term_cren A1 (+1))
            with (term_cren A1 (+1)).[ren (+0)] by autosubst.
          constructor...
          replace (Ch r0 (term_cren A1 (+1)))
            with (term_cren (Ch r0 A1) (+1)) by eauto.
          constructor. apply: dyn_empty_n. apply: H1.
          apply: sta_crename... }
      repeat constructor. apply: merge_sym... }
  repeat constructor. apply: merge_sym...
  replace (CVar 1) with (term_cren (CVar 0) (+1)) by eauto.
  apply: dyn_cweaken.
  replace (term_cren A0 (+1)) with (term_cren A0 (+1)).[ren (+0)] by autosubst.
  constructor... 
  replace (Ch r (term_cren A0 (+1))) with (term_cren (Ch r A0) (+1)) by eauto.
  constructor...
  apply: sta_crename...
Qed.
