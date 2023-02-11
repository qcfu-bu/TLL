From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS tll_cren sta_type.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive ctx_cren : (cvar -> cvar) -> dyn_ctx -> dyn_ctx -> Prop :=
| ctx_cren_O Θ :
  ctx_cren id Θ Θ
| ctx_cren_ty ξ r A Θ Θ' :
  Θ ; nil ⊢ A : Proto ->
  ctx_cren ξ Θ Θ' ->
  ctx_cren (upren ξ) (Ch r A :L Θ) (Ch r (term_cren A ξ) :L Θ')
| ctx_cren_n ξ Θ Θ' :
  ctx_cren ξ Θ Θ' ->
  ctx_cren (upren ξ) (_: Θ) (_: Θ')
| ctx_cren_plus ξ Θ Θ' :
  ctx_cren ξ Θ Θ' ->
  ctx_cren (ξ >>> (+1)) Θ (_: Θ')
| ctx_cren_minus ξ Θ Θ' :
  ctx_cren ξ Θ Θ' ->
  ctx_cren ((-1) >>> ξ) (_: Θ) Θ'.

Inductive sta_agree_cren : (cvar -> cvar) ->
  dyn_ctx -> sta_ctx -> dyn_ctx -> sta_ctx -> Prop :=
| sta_agree_cren_nil ξ Θ Θ' :
  ctx_cren ξ Θ Θ' ->
  sta_agree_cren ξ Θ nil Θ' nil
| sta_agree_cren_cons Θ Θ' Γ Γ' ξ m m' s :
  m' = term_cren m ξ ->
  Θ ; Γ ⊢ m : Sort s ->
  sta_agree_cren ξ Θ Γ Θ' Γ' ->
  sta_agree_cren ξ Θ (m :: Γ) Θ' (m' :: Γ').

Lemma sta_agree_cren_size Θ Θ' Γ Γ' ξ :
  sta_agree_cren ξ Θ Γ Θ' Γ' -> size Γ = size Γ'.
Proof with eauto.
  elim=>{Θ Θ' Γ Γ' ξ}...
  move=>Θ Θ' Γ Γ' ξ m m' s e1 tym agr e2=>//=.
  by rewrite e2.
Qed.

Lemma sta_agree_cren_inv Θ Θ' Γ Γ' ξ :
  sta_agree_cren ξ Θ Γ Θ' Γ' -> ctx_cren ξ Θ Θ'.
Proof with eauto. elim... Qed.

Lemma sta_agree_cren_has Θ Θ' Γ Γ' ξ x A :
  sta_agree_cren ξ Θ Γ Θ' Γ' ->
  sta_has Γ x A ->
  sta_has Γ' x (term_cren A ξ).
Proof with eauto.
  move=>agr. elim: agr x A=>{Θ Θ' Γ Γ' ξ}.
  { move=>ξ Θ Θ' agr x A shs. inv shs. }
  { move=>Θ Θ' Γ Γ' ξ m m' s e tym agr ih x A shs. subst.
    inv shs.
    { rewrite term_cren_ren.
      constructor. }
    { rewrite term_cren_ren.
      constructor... } }
Qed.

Lemma ctx_cren_pos Θ Θ' ξ x :
  ctx_cren ξ Θ Θ' -> cvar_pos Θ x true -> cvar_pos Θ' (ξ x) true.
Proof with eauto using cvar_pos.
  move=>agr. elim: agr x=>{Θ Θ' ξ}...
  { move=>ξ r A Θ Θ' tyA agr ih x pos. inv pos; asimpl... }
  { move=>ξ Θ Θ' cr ih x pos. inv pos. asimpl... }
  { move=>ξ Θ Θ' cr ih x pos. inv pos.
    asimpl. fold subn. rewrite subn0... }
Qed.

Lemma sta_agree_cren_pos Θ Θ' Γ Γ' ξ x :
  sta_agree_cren ξ Θ Γ Θ' Γ' ->
  cvar_pos Θ x true -> cvar_pos Θ' (ξ x) true.
Proof with eauto.
  move=>agr. elim: agr x=>{Θ Θ' Γ Γ' ξ}...
  move=>ξ Θ Θ' agr x pos. apply: ctx_cren_pos...
Qed.

Lemma sta_crename Θ Θ' Γ Γ' m A ξ :
  Θ ; Γ ⊢ m : A -> sta_agree_cren ξ Θ Γ Θ' Γ' ->
  Θ' ; Γ' ⊢ term_cren m ξ : term_cren A ξ.
Proof with eauto using sta_type, sta_agree_cren.
  move=>ty. move:Θ Γ m A ty Θ' Γ' ξ.
  apply:(@sta_type_mut _
           (fun Θ Γ wf => forall Θ' Γ' ξ,
                sta_agree_cren ξ Θ Γ Θ' Γ' -> sta_wf Θ' Γ')); simpl...
  { move=>Θ Γ x A wf ih shs Θ' Γ' ξ agr.
    constructor...
    apply: sta_agree_cren_has... }
  { move=>Θ Γ A B m s tym ihm Θ' Γ' ξ agr.
    have wf:=sta_type_wf tym. inv wf.
    econstructor.
    apply: ihm.
    econstructor... }
  { move=>Θ Γ A B m s tym ihm Θ' Γ' ξ agr.
    have wf:=sta_type_wf tym. inv wf.
    econstructor.
    apply: ihm.
    econstructor... }
  { move=>Θ Γ A B m n s tym ihm tyn ihn Θ' Γ' ξ agr.
    rewrite term_cren_beta1.
    apply: sta_app0... }
  { move=>Θ Γ A B m n s tym ihm tyn ihn Θ' Γ' ξ agr.
    rewrite term_cren_beta1.
    apply: sta_app1... }
  { move=>Θ Γ A B m n t tyS ihS tym ihm tyn ihn Θ' Γ' ξ agr.
    apply: sta_pair0...
    rewrite<-term_cren_beta1... }
  { move=>Θ Γ A B m n t tyS ihS tym ihm tyn ihn Θ' Γ' ξ agr.
    apply: sta_pair1...
    rewrite<-term_cren_beta1... }
  { move=>Θ Γ A B C m n s t tyC ihC tym ihm tyn ihn Θ' Γ' ξ agr.
    have wf:=sta_type_wf tyC. inv wf.
    have wf:=sta_type_wf tyn. inv wf. inv H4.
    rewrite term_cren_beta1.
    apply: sta_letin0...
    apply: ihC...
    rewrite<-(term_cren_subst _ (term_csubst_pair0 ξ t)).
    apply: ihn... }
  { move=>Θ Γ A B C m n s t tyC ihC tym ihm tyn ihn Θ' Γ' ξ agr.
    have wf:=sta_type_wf tyC. inv wf.
    have wf:=sta_type_wf tyn. inv wf. inv H4.
    rewrite term_cren_beta1.
    apply: sta_letin1...
    apply: ihC...
    rewrite<-(term_cren_subst _ (term_csubst_pair1 ξ t)).
    apply: ihn... }
  { move=>Θ Γ A m tym ihm Θ' Γ' ξ agr.
    have wf:=sta_type_wf tym. inv wf.
    constructor.
    rewrite<-term_cren_ren.
    apply: ihm... }
  { move=>Θ Γ A m n1 n2 s tyA ihA tym ihm tyn1 ihn1 tyn2 ihn2 Θ' Γ' ξ agr.
    rewrite term_cren_beta1.
    apply: sta_ifte...
    replace TT with (term_cren TT ξ) by eauto.
    rewrite<-term_cren_beta1...
    replace FF with (term_cren FF ξ) by eauto.
    rewrite<-term_cren_beta1... }
  { move=>Θ Γ m n A B s tyB ihB tym ihm tyn ihn Θ' Γ' ξ agr.
    have wf:=sta_type_wf tyn. inv wf.
    apply: sta_bind...
    rewrite<-term_cren_ren... }
  { move=>Θ Γ r A B tyB ihB Θ' Γ' ξ agr.
    have wf:=sta_type_wf tyB. inv wf.
    apply: sta_act0. apply: ihB... }
  { move=>Θ Γ r A B tyB ihB Θ' Γ' ξ agr.
    have wf:=sta_type_wf tyB. inv wf.
    apply: sta_act1. apply: ihB... }
  { move=>Θ Γ r x A wf ih pos tyA ihA Θ' Γ' ξ agr.
    rewrite term_cren_ren.
    rewrite (sta_agree_cren_size agr).
    apply: sta_cvar...
    apply: sta_agree_cren_pos...
    apply: ihA.
    constructor.
    apply: sta_agree_cren_inv... }
  { move=>Θ Γ m A tym ihm Θ' Γ' ξ agr.
    have wf:=sta_type_wf tym. inv wf.
    constructor... }
  { move=>Θ Γ A B m s eq tym ihm tyB ihB Θ' Γ' ξ agr.
    apply: sta_conv.
    apply: term_cren_sta_conv...
    apply: ihm...
    apply: ihB... }
  { move=>Θ1 Θ' Γ' ξ agr. inv agr. constructor. }
  { move=>Θ Γ A s wf ih tyA ihA Θ' Γ' ξ agr. inv agr.
    econstructor... }
Qed.

Lemma sta_ecrename Θ Θ' Γ Γ' m m' A A' ξ :
  m' = term_cren m ξ ->
  A' = term_cren A ξ ->
  Θ ; Γ ⊢ m : A -> sta_agree_cren ξ Θ Γ Θ' Γ' ->
  Θ' ; Γ' ⊢ m' : A'.
Proof. move=>->->. apply: sta_crename. Qed.
