From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS tll_cren sta_type.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive sta_agree_cren : (nat -> nat) -> sta_ctx -> sta_ctx -> Prop :=
| sta_agree_cren_nil ξ :
  sta_agree_cren ξ nil nil
| sta_agree_cren_cons Γ Γ' ξ m m' s :
  m' = term_cren m ξ ->
  Γ ⊢ m : Sort s ->
  sta_agree_cren ξ Γ Γ' ->
  sta_agree_cren ξ (m :: Γ) (m' :: Γ').

Lemma sta_agree_cren_size Γ Γ' ξ :
  sta_agree_cren ξ Γ Γ' -> size Γ = size Γ'.
Proof with eauto.
  elim=>{Γ Γ' ξ}...
  move=>Γ Γ' ξ m m' s e1 tym agr e2=>//=.
  by rewrite e2.
Qed.

Lemma sta_agree_cren_has Γ Γ' ξ x A :
  sta_agree_cren ξ Γ Γ' ->
  sta_has Γ x A ->
  sta_has Γ' x (term_cren A ξ).
Proof with eauto.
  move=>agr. elim: agr x A=>{Γ Γ' ξ}.
  { move=>ξ x A shs. inv shs. }
  { move=>Γ Γ' ξ m m' s e tym agr ih x A shs. subst.
    inv shs.
    { rewrite term_cren_ren.
      constructor. }
    { rewrite term_cren_ren.
      constructor... } }
Qed.

Lemma sta_crename Γ Γ' m A ξ :
  Γ ⊢ m : A -> sta_agree_cren ξ Γ Γ' ->
  Γ' ⊢ term_cren m ξ : term_cren A ξ.
Proof with eauto using sta_type, sta_agree_cren.
  move=>ty. move:Γ m A ty Γ' ξ.
  apply:(@sta_type_mut _ (fun Γ wf => forall Γ' ξ, sta_agree_cren ξ Γ Γ' -> sta_wf Γ')); simpl...
  { move=>Γ x A wf ih shs Γ' ξ agr.
    constructor...
    apply: sta_agree_cren_has... }
  { move=>Γ A B m s tym ihm Γ' ξ agr.
    have wf:=sta_type_wf tym. inv wf.
    econstructor.
    apply: ihm.
    econstructor... }
  { move=>Γ A B m s tym ihm Γ' ξ agr.
    have wf:=sta_type_wf tym. inv wf.
    econstructor.
    apply: ihm.
    econstructor... }
  { move=>Γ A B m n s tym ihm tyn ihn Γ' ξ agr.
    rewrite term_cren_beta1.
    apply: sta_app0... }
  { move=>Γ A B m n s tym ihm tyn ihn Γ' ξ agr.
    rewrite term_cren_beta1.
    apply: sta_app1... }
  { move=>Γ A B m n t tyS ihS tym ihm tyn ihn Γ' ξ agr.
    apply: sta_pair0...
    rewrite<-term_cren_beta1... }
  { move=>Γ A B m n t tyS ihS tym ihm tyn ihn Γ' ξ agr.
    apply: sta_pair1...
    rewrite<-term_cren_beta1... }
  { move=>Γ A B C m n s t tyC ihC tym ihm tyn ihn Γ' ξ agr.
    have wf:=sta_type_wf tyC. inv wf.
    have wf:=sta_type_wf tyn. inv wf. inv H3.
    rewrite term_cren_beta1.
    apply: sta_letin0...
    apply: ihC...
    rewrite<-(term_cren_subst _ (term_csubst_pair0 ξ t)).
    apply: ihn... }
  { move=>Γ A B C m n s t tyC ihC tym ihm tyn ihn Γ' ξ agr.
    have wf:=sta_type_wf tyC. inv wf.
    have wf:=sta_type_wf tyn. inv wf. inv H3.
    rewrite term_cren_beta1.
    apply: sta_letin1...
    apply: ihC...
    rewrite<-(term_cren_subst _ (term_csubst_pair1 ξ t)).
    apply: ihn... }
  { move=>Γ A m tym ihm Γ' ξ agr.
    have wf:=sta_type_wf tym. inv wf.
    constructor.
    rewrite<-term_cren_ren.
    apply: ihm... }
  { move=>Γ A m n1 n2 s tyA ihA tym ihm tyn1 ihn1 tyn2 ihn2 Γ' ξ
           agr.
    rewrite term_cren_beta1.
    apply: sta_ifte...
    replace TT with (term_cren TT ξ) by eauto.
    rewrite<-term_cren_beta1...
    replace FF with (term_cren FF ξ) by eauto.
    rewrite<-term_cren_beta1... }
  { move=>Γ m n A B s tyB ihB tym ihm tyn ihn Γ' ξ agr.
    have wf:=sta_type_wf tyn. inv wf.
    apply: sta_bind...
    rewrite<-term_cren_ren... }
  { move=>Γ r A B tyB ihB Γ' ξ agr.
    have wf:=sta_type_wf tyB. inv wf.
    apply: sta_act0. apply: ihB... }
  { move=>Γ r A B tyB ihB Γ' ξ agr.
    have wf:=sta_type_wf tyB. inv wf.
    apply: sta_act1. apply: ihB... }
  { move=>Γ r x A wf ih tyA ihA Γ' ξ agr.
    rewrite term_cren_ren.
    rewrite (sta_agree_cren_size agr).
    apply: sta_cvar... }
  { move=>Γ m A tym ihm Γ' ξ agr.
    have wf:=sta_type_wf tym. inv wf.
    constructor... }
  { move=>Γ A B m s eq tym ihm tyB ihB Γ' ξ agr.
    apply: sta_conv.
    apply: term_cren_sta_conv...
    apply: ihm...
    apply: ihB... }
  { move=>Γ' ξ agr. inv agr. constructor. }
  { move=>Γ A s wf ih tyA ihA Γ' ξ agr. inv agr.
    econstructor... }
Qed.

Lemma sta_ecrename Γ Γ' m m' A A' ξ :
  m' = term_cren m ξ ->
  A' = term_cren A ξ ->
  Γ ⊢ m : A -> sta_agree_cren ξ Γ Γ' ->
  Γ' ⊢ m' : A'.
Proof. move=>->->. apply: sta_crename. Qed.
