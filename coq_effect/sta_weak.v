From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_ctx sta_type sta_conf.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive sta_agree_ren : (var -> var) ->
  sta_ctx -> sta_ctx -> Prop :=
| sta_agree_ren_nil ξ :
  sta_agree_ren ξ nil nil
| sta_agree_ren_cons Γ Γ' ξ m :
  Γ ⊢ m : Ty ->
  sta_agree_ren ξ Γ Γ' ->
  sta_agree_ren (upren ξ) (m :: Γ) (m.[ren ξ] :: Γ')
| sta_agree_ren_wk Γ Γ' ξ m :
  Γ' ⊢ m : Ty ->
  sta_agree_ren ξ Γ Γ' ->
  sta_agree_ren (ξ >>> (+1)) (Γ) (m :: Γ').

Lemma sta_agree_ren_refl Γ : sta_wf Γ -> sta_agree_ren id Γ Γ.
Proof with eauto using sta_agree_ren.
  move=>wf. elim: wf=>{Γ}...
  move=>Γ A wf agr tyA.
  have:(sta_agree_ren (upren id) (A :: Γ) (A.[ren id] :: Γ))...
  by asimpl.
Qed.

Lemma sta_agree_ren_has Γ Γ' ξ x A :
  sta_agree_ren ξ Γ Γ' -> sta_has Γ x A -> sta_has Γ' (ξ x) A.[ren ξ].
Proof with eauto.
  move=>agr. elim: agr x A=>{Γ Γ' ξ}.
  { move=>ξ x A hs. inv hs. }
  { move=>Γ Γ' ξ m tym agr ih x A hs. inv hs; asimpl.
    { replace m.[ren (ξ >>> (+1))] with m.[ren ξ].[ren (+1)] by autosubst.
      constructor. }
    { replace A0.[ren (ξ >>> (+1))] with A0.[ren ξ].[ren (+1)] by autosubst.
      constructor... } }
  { move=>Γ Γ' ξ m tym agr ih x B /ih hs. asimpl.
    replace B.[ren (ξ >>> (+1))] with B.[ren ξ].[ren (+1)] by autosubst.
    constructor... }
Qed.

Lemma sta_agree_weak_wf_nil Γ' ξ : sta_agree_ren ξ nil Γ' -> sta_wf Γ'.
Proof with eauto using sta_wf.
  move e:(nil)=>Γ agr. elim: agr e=>//{Γ Γ' ξ}...
Qed.

Lemma sta_agree_weak_wf_cons Γ Γ' A ξ :
  sta_agree_ren ξ (A :: Γ) Γ' -> sta_wf Γ -> 
  (∀ Γ' ξ, sta_agree_ren ξ Γ Γ' → sta_wf Γ') ->
  (∀ Γ' ξ, sta_agree_ren ξ Γ Γ' → Γ' ⊢ A.[ren ξ] : Ty) ->
  sta_wf Γ'.
Proof with eauto using sta_wf.
  move e:(A :: Γ)=>Γ0 agr. elim: agr Γ A e=>//{Γ0 Γ' ξ}...
  move=>Γ Γ' ξ m tym agr _ Γ0 A [e1 e2] wf h1 h2; subst.
  have tym':=h2 _ _ agr.
  apply: sta_wf_cons...
Qed.

Lemma sta_rename Γ Γ' m A ξ :
  Γ ⊢ m : A -> sta_agree_ren ξ Γ Γ' -> Γ' ⊢ m.[ren ξ] : A.[ren ξ].
Proof with eauto using sta_type, sta_wf, sta_agree_ren.
  move=>tym. move:Γ m A tym Γ' ξ.
  apply:(@sta_type_mut _ (fun Γ wf => forall Γ' ξ, sta_agree_ren ξ Γ Γ' -> sta_wf Γ'))...
  { move=>Γ x A wf h hs Γ' ξ agr. asimpl.
    apply: sta_var...
    apply: sta_agree_ren_has... }
  { move=>Γ A B tyA ihA tyB ihB Γ' ξ agr. asimpl.
    have wf:=sta_type_wf tyB. inv wf.
    apply: sta_forall... }
  { move=>Γ A B tyA ihA tyB ihB Γ' ξ agr. asimpl.
    have wf:=sta_type_wf tyB. inv wf.
    have{}ihB:=ihB _ _ (sta_agree_ren_cons H2 agr).
    asimpl in ihB.
    apply: sta_arrow...
    by asimpl. }
  { move=>Γ A B m tyA ihA tym ihm Γ' ξ agr. asimpl.
    have wf:=sta_type_wf tym. inv wf.
    apply: sta_lam... }
  { move=>Γ A B m tyA ihA tym ihm Γ' ξ agr. asimpl.
    have wf:=sta_type_wf tym. inv wf.
    have{}ihm:=ihm _ _ (sta_agree_ren_cons H2 agr).
    asimpl in ihm.
    apply: sta_fun...
    by asimpl. }
  { move=>Γ A B m n tym ihm tyn ihn Γ' ξ agr. asimpl.
    replace B.[n.[ren ξ] .: ren ξ] with B.[ren (upren ξ)].[n.[ren ξ]/]
      by autosubst.
    have{}ihm:=ihm _ _ agr.
    have{}ihn:=ihn _ _ agr.
    apply: sta_inst...
    asimpl in ihm... }
  { move=>Γ A B m eq tym ihm tyB ihB Γ' ξ agr.
    apply: sta_conv.
    apply: sta_conv_subst.
    apply: eq.
    by apply: ihm.
    have:=ihB _ _ agr.
    asimpl... }
  { exact: sta_agree_weak_wf_nil. }
  { move=>Γ A wf ih tyA ihA Γ' ξ agr.
    apply: sta_agree_weak_wf_cons... }
Qed.

Lemma sta_rename_wf Γ Γ' ξ :
  sta_wf Γ -> sta_agree_ren ξ Γ Γ' -> sta_wf Γ'.
Proof with eauto using sta_wf.
  move=>wf. elim: wf Γ' ξ=>{Γ}.
  { move=>*. apply: sta_agree_weak_wf_nil... }
  { move=>Γ A wf ih tyA Γ' ξ agr.
    apply: sta_agree_weak_wf_cons...
    move=>Γ'0 ξ0 agr0.
    have:= sta_rename tyA agr0.
    by autosubst. }
Qed.

Lemma sta_wf_ok Γ x A :
  sta_wf Γ -> sta_has Γ x A -> Γ ⊢ A : Ty.
Proof with eauto using sta_agree_ren, sta_agree_ren_refl.
  move=>wf. elim: wf x A=>{Γ}.
  { move=>x A hs. inv hs. }
  { move=>Γ A wf ih tyA x B hs. inv hs.
    { replace Ty with Ty.[ren (+1)] by autosubst.
      apply: sta_rename... }
    { have tyA0:=ih _ _ H3.
      replace Ty with Ty.[ren (+1)] by autosubst.
      apply: sta_rename... } }
Qed.

Lemma sta_weaken Γ m A B :
  Γ ⊢ m : A ->
  Γ ⊢ B : Ty ->
  (B :: Γ) ⊢ m.[ren (+1)] : A.[ren (+1)].
Proof with eauto using sta_agree_ren, sta_agree_ren_refl.
  move=>tym tyB. apply: sta_rename...
Qed.

Lemma sta_eweaken Γ m m' A A' B :
  m' = m.[ren (+1)] ->
  A' = A.[ren (+1)] ->
  Γ ⊢ m : A ->
  Γ ⊢ B : Ty ->
  (B :: Γ) ⊢ m' : A'.
Proof with eauto using sta_agree_ren, sta_agree_ren_refl.
  move=>*; subst. apply: sta_weaken...
Qed.
