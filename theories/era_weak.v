From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS era_type.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma era_rename Γ Γ' Δ Δ' m m' A ξ :
  Γ ; Δ ⊨ m ~ m' : A -> dyn_agree_ren ξ Γ Δ Γ' Δ' ->
  Γ' ; Δ' ⊨ m.[ren ξ] ~ m'.[ren ξ] : A.[ren ξ].
Proof with eauto using era_type, dyn_agree_ren, dyn_agree_ren_key.
  move=>ty. elim: ty Γ' Δ' ξ=>{Γ Δ m m' A}.
  { move=>Γ Δ x A shs dhs Γ' Δ' ξ agr. asimpl.
    apply: era_var.
    apply: sta_agree_ren_has...
    apply: dyn_sta_agree_ren...
    apply: dyn_agree_ren_has... }
  { move=>Γ Δ A B m m' s t k tyP tym ihm Γ' Δ' ξ agr. asimpl.
    apply: era_lam0...
    have:=sta_rename tyP (dyn_sta_agree_ren agr).
    by autosubst. }
  { move=>Γ Δ A B m m' s t k tyP tym ihm Γ' Δ' ξ agr. asimpl.
    apply: era_lam1...
    have:=sta_rename tyP (dyn_sta_agree_ren agr).
    by autosubst. }
  { move=>Γ Δ A B m m' n s t tym ihm tyn Γ' Δ' ξ agr. asimpl.
    replace B.[n.[ren ξ] .: ren ξ] with B.[ren (upren ξ)].[n.[ren ξ]/]
      by autosubst.
    have{}ihm:=ihm _ _ _ agr.
    have{}ihn:=sta_rename tyn (dyn_sta_agree_ren agr).
    apply: era_app0...
    asimpl in ihm... }
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' s t mrg tym ihm tyn ihn Γ' Δ' ξ agr. asimpl.
    replace B.[n.[ren ξ] .: ren ξ] with B.[ren (upren ξ)].[n.[ren ξ]/]
      by autosubst.
    have[Δ1'[Δ2'[mrg'[agr1 agr2]]]]:=dyn_agree_ren_merge agr mrg.
    have{}ihm:=ihm _ _ _ agr1.
    have{}ihn:=ihn _ _ _ agr2.
    apply: era_app1...
    asimpl in ihm... }
  { move=>Γ Δ A B m m' s eq tym ihm tyB Γ' Δ' ξ agr.
    apply: era_conv.
    apply: sta_conv_subst...
    apply: ihm...
    have:=sta_rename tyB (dyn_sta_agree_ren agr).
    asimpl... }
Qed.

Lemma era_weakenU Γ Δ m m' A B :
  dyn_wf Γ Δ -> Γ ; Δ ⊨ m ~ m' : A ->
  (B :: Γ) ; (B :U Δ) ⊨ m.[ren (+1)] ~ m'.[ren (+1)] : A.[ren (+1)].
Proof with eauto using dyn_agree_ren, dyn_agree_ren_refl.
  move=>wf ty. apply: era_rename...
Qed.

Lemma era_weakenN Γ Δ m m' A B :
  dyn_wf Γ Δ -> Γ ; Δ ⊨ m ~ m' : A ->
  (B :: Γ) ; (_: Δ) ⊨ m.[ren (+1)] ~ m'.[ren (+1)] : A.[ren (+1)].
Proof with eauto using dyn_agree_ren, dyn_agree_ren_refl.
  move=>wf ty. apply: era_rename...
Qed.

Lemma era_eweakenU Γ Δ m m' n n' A A' B :
  m' = m.[ren (+1)] ->
  n' = n.[ren (+1)] ->
  A' = A.[ren (+1)] ->
  dyn_wf Γ Δ ->
  Γ ; Δ ⊨ m ~ n : A ->
  (B :: Γ) ; (B :U Δ) ⊨ m' ~ n' : A'.
Proof.
  move=>*; subst. exact: era_weakenU.
Qed.

Lemma era_eweakenN Γ Δ m m' n n' A A' B :
  m' = m.[ren (+1)] ->
  n' = n.[ren (+1)] ->
  A' = A.[ren (+1)] ->
  dyn_wf Γ Δ ->
  Γ ; Δ ⊨ m ~ n : A ->
  (B :: Γ) ; (_: Δ) ⊨ m' ~ n' : A'.
Proof.
  move=>*; subst. exact: era_weakenN.
Qed.
