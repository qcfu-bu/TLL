From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_weak.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "Γ1 ⊢ σ ⊣ Γ2" (at level 50, σ, Γ2 at next level).

Inductive sta_agree_subst :
  sta_ctx -> (var -> term) -> sta_ctx -> Prop :=
| sta_agree_subst_nil σ :
  nil ⊢ σ ⊣ nil
| sta_agree_subst_ty Γ1 σ Γ2 A :
  Γ1 ⊢ σ ⊣ Γ2 ->
  Γ2 ⊢ A : Ty ->
  (A.[σ] :: Γ1) ⊢ up σ ⊣ (A :: Γ2)
| sta_agree_subst_wk Γ1 σ Γ2 n A :
  Γ1 ⊢ σ ⊣ Γ2 ->
  Γ1 ⊢ n : A.[σ] ->
  Γ1 ⊢ n .: σ ⊣ (A :: Γ2)
| sta_agree_subst_conv Γ1 σ Γ2 A B :
  A === B ->
  Γ1 ⊢ B.[ren (+1)].[σ] : Ty ->
  Γ2 ⊢ B : Ty ->
  Γ1 ⊢ σ ⊣ (A :: Γ2) ->
  Γ1 ⊢ σ ⊣ (B :: Γ2)
where "Γ1 ⊢ σ ⊣ Γ2" := (sta_agree_subst Γ1 σ Γ2).

Lemma sta_agree_subst_refl Γ : sta_wf Γ -> Γ ⊢ ids ⊣ Γ.
Proof with eauto using sta_agree_subst.
  elim=>{Γ}...
  move=>Γ A wf agr tyA.
  have: (A.[ids] :: Γ) ⊢ up ids ⊣ (A :: Γ)...
  by asimpl...
Qed.
#[global] Hint Resolve sta_agree_subst_refl.

Lemma sta_agree_subst_has Γ1 σ Γ2 x A :
  Γ1 ⊢ σ ⊣ Γ2 -> sta_wf Γ1 -> sta_has Γ2 x A -> Γ1 ⊢ σ x : A.[σ].
Proof with eauto using sta_agree_subst.
  move=>agr. elim: agr x A=>{Γ1 σ Γ2}.
  { move=>σ x A wf hs. inv hs. }
  { move=>Γ1 σ Γ2 A agr ih tyA x B wf hs.
    inv hs; asimpl.
    replace A.[σ >> ren (+1)] with A.[σ].[ren (+1)] by autosubst.
    apply: sta_var...
    constructor.
    replace A0.[σ >> ren (+1)] with A0.[σ].[ren (+1)] by autosubst.
    inv wf. apply: sta_eweaken... }
  { move=>Γ1 σ Γ2 n A agr ih tyn x B wf hs. inv hs; asimpl... }
  { move=>Γ1 σ Γ2 A B eq tyB1 tyB2 agr ih x C wf hs. inv hs.
    { apply: sta_conv.
      apply: sta_conv_subst.
      apply: sta_conv_subst.
      apply: eq.
      apply: ih...
      constructor.
      exact: tyB1. }
    { apply: ih...
      constructor... } }
Qed.

Lemma sta_agree_subst_wf_nil Γ1 σ : Γ1 ⊢ σ ⊣ nil -> sta_wf Γ1.
Proof with eauto using sta_wf.
  move e:(nil)=>Γ2 agr. elim: agr e=>//{Γ1 Γ2 σ}...
Qed.

Lemma sta_agree_subst_wf_cons Γ1 Γ2 A σ :
  Γ1 ⊢ σ ⊣ (A :: Γ2) -> sta_wf Γ2 ->
  (∀ Γ1 σ, Γ1 ⊢ σ ⊣ Γ2 → sta_wf Γ1) ->
  (∀ Γ1 σ, Γ1 ⊢ σ ⊣ Γ2 → Γ1 ⊢ A.[σ] : Ty) ->
  sta_wf Γ1.
Proof with eauto using sta_wf.
  move e:(A :: Γ2)=>Γ0 agr. elim: agr Γ2 A e=>//{Γ0 Γ1 σ}...
  move=>Γ1 σ Γ2 A agr ih tyA Γ0 A0 [e1 e2] wf h1 h2; subst.
  have tyA':=h2 _ _ agr.
  apply: sta_wf_cons...
Qed.

Lemma sta_substitution Γ1 Γ2 m A σ :
  Γ2 ⊢ m : A -> Γ1 ⊢ σ ⊣ Γ2 -> Γ1 ⊢ m.[σ] : A.[σ].
Proof with eauto using sta_agree_subst, sta_type.
  move=>ty. move: Γ2 m A ty Γ1 σ.
  apply: (@sta_type_mut _ (fun Γ2 wf => forall Γ1 σ, Γ1 ⊢ σ ⊣ Γ2 -> sta_wf Γ1))...
  { move=>Γ2 x A wf h hs Γ1 σ agr. asimpl.
    apply: sta_agree_subst_has... }
  { move=>Γ2 A B tyA ihA tyB ihB Γ1 σ agr. asimpl.
    have{}ihB:=ihB _ _ (sta_agree_subst_ty agr tyA).
    apply: sta_arrow...
    asimpl in ihB. by asimpl. }
  { move=>Γ2 A B m tyA ihA tym ihm Γ1 σ agr. asimpl.
    have{}ihm:=ihm _ _ (sta_agree_subst_ty agr tyA).
    apply: sta_fun...
    asimpl in ihm. by asimpl. }
  { move=>Γ2 A B m n tym ihm tyn ihn Γ1 σ agr. asimpl.
    replace B.[n.[σ] .: σ] with B.[up σ].[n.[σ]/] by autosubst.
    have{}ihm:=ihm _ _ agr.
    have{}ihn:=ihn _ _ agr.
    apply: sta_inst.
    asimpl in ihm...
    asimpl in ihn... }
  { move=>Γ2 A B m eq tym ihm tyB ihB Γ1 σ agr.
    apply: sta_conv.
    apply: sta_conv_subst.
    apply: eq.
    apply: ihm...
    apply: ihB... }
  { move=>Γ1 σ agr.
    apply: sta_agree_subst_wf_nil... }
  { move=>Γ A wf ih tyA h Γ1 σ agr.
    apply: sta_agree_subst_wf_cons... }
Qed.

Lemma sta_subst Γ m n A B :
  (A :: Γ) ⊢ m : B -> Γ ⊢ n : A -> Γ ⊢ m.[n/] : B.[n/].
Proof with eauto using sta_agree_subst_refl.
  move=>tym tyn.
  apply: sta_substitution...
  apply: sta_agree_subst_wk...
  by asimpl.
Qed.

Lemma sta_esubst Γ m m' n A B B' :
  m' = m.[n/] ->
  B' = B.[n/] ->
  (A :: Γ) ⊢ m : B -> Γ ⊢ n : A -> Γ ⊢ m' : B'.
Proof.
  move=>*; subst. apply: sta_subst; eauto.
Qed.

Lemma sta_ctx_conv Γ m A B C :
  B === A ->
  Γ ⊢ B : Ty -> (A :: Γ) ⊢ m : C -> (B :: Γ) ⊢ m : C.
Proof with eauto using sta_wf, sta_agree_subst_refl.
  move=>eq tyB tym.
  have wf:=sta_type_wf tym. inv wf.
  have:(B :: Γ) ⊢ m.[ids] : C.[ids].
  apply: sta_substitution...
  apply: sta_agree_subst_conv...
  apply: sta_eweaken...
  asimpl...
  asimpl...
  asimpl...
Qed.
