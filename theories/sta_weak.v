From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_ctx sta_type sta_conf.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive agree_ren : (var -> var) ->
  sta_ctx term -> sta_ctx term -> Prop :=
| agree_ren_nil ξ :
  agree_ren ξ nil nil
| agree_ren_cons Γ Γ' ξ m :
  agree_ren ξ Γ Γ' ->
  agree_ren (upren ξ) (m :: Γ) (m.[ren ξ] :: Γ')
| agree_ren_wk Γ Γ' ξ m :
  agree_ren ξ Γ Γ' ->
  agree_ren (ξ >>> (+1)) (Γ) (m :: Γ').

Lemma agree_ren_refl Γ : agree_ren id Γ Γ.
Proof with eauto using agree_ren.
  elim: Γ...
  move=>A Γ ih.
  have:(agree_ren (upren id) (A :: Γ) (A.[ren id] :: Γ))...
  by asimpl.
Qed.

Lemma agree_ren_sta_has Γ Γ' ξ x A :
  agree_ren ξ Γ Γ' -> sta_has Γ x A -> sta_has Γ' (ξ x) A.[ren ξ].
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
  Γ ⊢ m : A -> agree_ren ξ Γ Γ' -> Γ' ⊢ m.[ren ξ] : A.[ren ξ].
Proof with eauto using sta_type, agree_ren.
  move=>ty. elim: ty Γ' ξ=>{Γ m A}...
  { move=>Γ x A hs Γ' ξ agr. asimpl.
    apply: sta_var.
    apply: agree_ren_sta_has... }
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
Proof with eauto using agree_ren, agree_ren_refl.
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
Proof with eauto using agree_ren, agree_ren_refl.
  move=>ty. apply: sta_rename...
Qed.

Lemma sta_eweaken Γ m m' A A' B :
  m' = m.[ren (+1)] ->
  A' = A.[ren (+1)] ->
  Γ ⊢ m : A -> (B :: Γ) ⊢ m' : A'.
Proof with eauto using agree_ren, agree_ren_refl.
  move=>*; subst. by apply: sta_weaken.
Qed.
