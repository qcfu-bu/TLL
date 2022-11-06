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
  sta_agree_ren ξ Γ Γ' ->
  sta_agree_ren (upren ξ) (m :: Γ) (m.[ren ξ] :: Γ')
| sta_agree_ren_wk Γ Γ' ξ m :
  sta_agree_ren ξ Γ Γ' ->
  sta_agree_ren (ξ >>> (+1)) (Γ) (m :: Γ').

Lemma sta_agree_ren_refl Γ : sta_agree_ren id Γ Γ.
Proof with eauto using sta_agree_ren.
  elim: Γ...
  move=>A Γ ih.
  have:(sta_agree_ren (upren id) (A :: Γ) (A.[ren id] :: Γ))...
  by asimpl.
Qed.

Lemma sta_agree_ren_has Γ Γ' ξ x A :
  sta_agree_ren ξ Γ Γ' -> sta_has Γ x A -> sta_has Γ' (ξ x) A.[ren ξ].
Proof with eauto.
  move=>agr. elim: agr x A=>{Γ Γ' ξ}.
  { move=>ξ x A hs. inv hs. }
  { move=>Γ Γ' ξ m agr ih x A hs. inv hs; asimpl.
    { replace m.[ren (ξ >>> (+1))] with m.[ren ξ].[ren (+1)] by autosubst.
      constructor. }
    { replace A0.[ren (ξ >>> (+1))] with A0.[ren ξ].[ren (+1)] by autosubst.
      constructor... } }
  { move=>Γ Γ' ξ m agr ih x A /ih hs. asimpl.
    replace A.[ren (ξ >>> (+1))] with A.[ren ξ].[ren (+1)] by autosubst.
    constructor... }
Qed.

Lemma sta_rename Γ Γ' m A ξ :
  Γ ⊢ m : A -> sta_agree_ren ξ Γ Γ' -> Γ' ⊢ m.[ren ξ] : A.[ren ξ].
Proof with eauto using sta_type, sta_agree_ren.
  move=>ty. elim: ty Γ' ξ=>{Γ m A}...
  { move=>Γ x A hs Γ' ξ agr. asimpl.
    apply: sta_var.
    apply: sta_agree_ren_has... }
  { move=>Γ A B s r t tyA ihA tyB ihB Γ' ξ agr. asimpl.
    apply: sta_pi0... }
  { move=>Γ A B s r t tyA ihA tyB ihB Γ' ξ agr. asimpl.
    apply: sta_pi1... }
  { move=>Γ A B m s t tyP ihP tym ihm Γ' ξ agr. asimpl.
    apply: sta_lam0...
    have:=(ihP _ _ agr).
    by asimpl. }
  { move=>Γ A B m s t tyP ihP tym ihm Γ' ξ agr. asimpl.
    apply: sta_lam1...
    have:=(ihP _ _ agr).
    by asimpl. }
  { move=>Γ A B m n s t tym ihm tyn ihn Γ' ξ agr. asimpl.
    replace B.[n.[ren ξ] .: ren ξ] with B.[ren (upren ξ)].[n.[ren ξ]/]
      by autosubst.
    have{}ihm:=ihm _ _ agr.
    have{}ihn:=ihn _ _ agr.
    apply: sta_app0...
    asimpl in ihm... }
  { move=>Γ A B m n s t tym ihm tyn ihn Γ' ξ agr. asimpl.
    replace B.[n.[ren ξ] .: ren ξ] with B.[ren (upren ξ)].[n.[ren ξ]/]
      by autosubst.
    have{}ihm:=ihm _ _ agr.
    have{}ihn:=ihn _ _ agr.
    apply: sta_app1...
    asimpl in ihm... }
  { move=>Γ A B m s eq tym ihm tyB ihB Γ' ξ agr.
    apply: sta_conv.
    apply: sta_conv_subst.
    apply: eq.
    by apply: ihm.
    have:=ihB _ _ agr.
    asimpl... }
Qed.

Lemma sta_wf_ok Γ x A :
  sta_wf Γ -> sta_has Γ x A -> exists s, Γ ⊢ A : @s.
Proof with eauto using sta_agree_ren, sta_agree_ren_refl.
  move=>wf. elim: wf x A=>{Γ}.
  { move=>x A hs. inv hs. }
  { move=>Γ A s wf ih tyA x B hs. inv hs.
    { exists s.
      replace (@s) with (@s).[ren (+1)] by autosubst.
      apply: sta_rename... }
    { have[t tyA0]:=ih _ _ H3.
      exists t.
      replace (@t) with (@t).[ren (+1)] by autosubst.
      apply: sta_rename... } }
Qed.

Lemma sta_weaken Γ m A B :
  Γ ⊢ m : A -> (B :: Γ) ⊢ m.[ren (+1)] : A.[ren (+1)].
Proof with eauto using sta_agree_ren, sta_agree_ren_refl.
  move=>ty. apply: sta_rename...
Qed.

Lemma sta_eweaken Γ m m' A A' B :
  m' = m.[ren (+1)] ->
  A' = A.[ren (+1)] ->
  Γ ⊢ m : A -> (B :: Γ) ⊢ m' : A'.
Proof with eauto using sta_agree_ren, sta_agree_ren_refl.
  move=>*; subst. exact: sta_weaken.
Qed.
