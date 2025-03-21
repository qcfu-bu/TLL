From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_weak dyn_type.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive dyn_agree_ren : (var -> var) ->
  sta_ctx -> dyn_ctx -> sta_ctx -> dyn_ctx -> Prop :=
| dyn_agree_ren_nil ξ :
  dyn_agree_ren ξ nil nil nil nil
| dyn_agree_ren_ty Γ Γ' Δ Δ' ξ m s :
  dyn_agree_ren ξ Γ Δ Γ' Δ' ->
  dyn_agree_ren (upren ξ)
    (m :: Γ) (m :{s} Δ) (m.[ren ξ] :: Γ') (m.[ren ξ] :{s} Δ')
| dyn_agree_ren_n Γ Γ' Δ Δ' ξ m :
  dyn_agree_ren ξ Γ Δ Γ' Δ' ->
  dyn_agree_ren (upren ξ)
    (m :: Γ) (_: Δ) (m.[ren ξ] :: Γ') (_: Δ')
| dyn_agree_ren_wkU Γ Γ' Δ Δ' ξ m :
  dyn_agree_ren ξ Γ Δ Γ' Δ' ->
  dyn_agree_ren (ξ >>> (+1)) Γ Δ (m :: Γ') (m :U Δ')
| dyn_agree_ren_wkN Γ Γ' Δ Δ' ξ m :
  dyn_agree_ren ξ Γ Δ Γ' Δ' ->
  dyn_agree_ren (ξ >>> (+1)) Γ Δ (m :: Γ') (_: Δ').

Lemma dyn_sta_agree_ren Γ Γ' Δ Δ' ξ :
  dyn_agree_ren ξ Γ Δ Γ' Δ' -> sta_agree_ren ξ Γ Γ'.
Proof with eauto using sta_agree_ren.
  elim=>{Γ Γ' Δ Δ' ξ}...
Qed.

Lemma dyn_agree_ren_refl Γ Δ :
  dyn_wf Γ Δ -> dyn_agree_ren id Γ Δ Γ Δ.
Proof with eauto using dyn_agree_ren.
  elim: Γ Δ.
  { move=>Δ wf. inv wf... }
  { move=>A Γ ih Δ wf. inv wf.
    { have agr:=ih _ H1.
      have:dyn_agree_ren (upren id)
        (A :: Γ) (A :{s} Δ0) (A.[ren id] :: Γ) (A.[ren id] :{s} Δ0)...
      by asimpl. }
    { have agr:=ih _ H1.
      have:dyn_agree_ren (upren id)
        (A :: Γ) (_: Δ0) (A.[ren id] :: Γ) (_: Δ0)...
      by asimpl. } }
Qed.

Lemma dyn_agree_ren_key Γ Γ' Δ Δ' ξ s :
  dyn_agree_ren ξ Γ Δ Γ' Δ' -> Δ ▷ s -> Δ' ▷ s.
Proof with eauto using key.
  move=>agr. elim: agr s=>{Γ Γ' Δ Δ' ξ}...
  { move=>Γ Γ' Δ Δ' ξ m s agr ih t k. inv k... }
  { move=>Γ Γ' Δ Δ' ξ _ agr ih s k. inv k... }
  { move=>Γ Γ' Δ Δ' ξ m agr ih [] /ih... }
Qed.

Lemma dyn_agree_ren_has Γ Γ' Δ Δ' ξ x A :
  dyn_agree_ren ξ Γ Δ Γ' Δ' -> dyn_has Δ x A -> dyn_has Δ' (ξ x) A.[ren ξ].
Proof with eauto using dyn_agree_ren_key.
  move=>agr. elim: agr x A=>{Γ Γ' Δ Δ' ξ}.
  { move=>ξ x A hs. inv hs. }
  { move=>Γ Γ' Δ Δ' ξ m s agr ih x A hs. inv hs; asimpl.
    { replace m.[ren (ξ >>> (+1))] with m.[ren ξ].[ren (+1)] by autosubst.
      constructor... }
    { replace A0.[ren (ξ >>> (+1))] with A0.[ren ξ].[ren (+1)] by autosubst.
      constructor... } }
  { move=>Γ Γ' Δ Δ' ξ _ agr ih x A hs. inv hs; asimpl.
    replace A0.[ren (ξ >>> (+1))] with A0.[ren ξ].[ren (+1)] by autosubst.
     constructor... }
  { move=>Γ Γ' Δ Δ' ξ m agr ih x A hs.
    replace A.[ren (ξ >>> (+1))] with A.[ren ξ].[ren (+1)] by autosubst.
    constructor... }
  { move=>Γ Γ' Δ Δ' ξ _ agr ih x A hs.
    replace A.[ren (ξ >>> (+1))] with A.[ren ξ].[ren (+1)] by autosubst.
    constructor... }
Qed.

Lemma dyn_agree_ren_merge Γ Γ' Δ Δ' Δ1 Δ2 ξ :
  dyn_agree_ren ξ Γ Δ Γ' Δ' -> Δ1 ∘ Δ2 => Δ ->
  ∃ Δ1' Δ2',
    Δ1' ∘ Δ2' => Δ' /\
    dyn_agree_ren ξ Γ Δ1 Γ' Δ1' /\
    dyn_agree_ren ξ Γ Δ2 Γ' Δ2'.
Proof with eauto 6 using merge, dyn_agree_ren.
  move=>agr. elim: agr Δ1 Δ2=>{Γ Γ' Δ Δ' ξ}.
  { move=>ξ Δ1 Δ2 mrg. inv mrg.
    exists nil. exists nil... }
  { move=>Γ Γ' Δ Δ' ξ m s agr ih Δ1 Δ2 mrg. inv mrg.
    { have[Δ1'[Δ2'[mrg'[agr1 agr2]]]]:=ih _ _ H2.
      exists (m.[ren ξ] :U Δ1').
      exists (m.[ren ξ] :U Δ2')... }
    { have[Δ1'[Δ2'[mrg'[agr1 agr2]]]]:=ih _ _ H2.
      exists (m.[ren ξ] :L Δ1').
      exists (_: Δ2')... }
    { have[Δ1'[Δ2'[mrg'[agr1 agr2]]]]:=ih _ _ H2.
      exists (_: Δ1').
      exists (m.[ren ξ] :L Δ2')... } }
  { move=>Γ Γ' Δ Δ' ξ m agr ih Δ1 Δ2 mrg. inv mrg.
    have[Δ1'[Δ2'[mrg'[agr1 agr2]]]]:=ih _ _ H2.
      exists (_: Δ1'). exists (_: Δ2')... }
  { move=>Γ Γ' Δ Δ' ξ m agr ih Δ1 Δ2 mrg.
    have[Δ1'[Δ2'[mrg'[agr1 agr2]]]]:=ih _ _ mrg.
    exists (m :U Δ1'). exists (m :U Δ2')... }
  { move=>Γ Γ' Δ Δ' ξ m agr ih Δ1 Δ2 mrg.
    have[Δ1'[Δ2'[mrg'[agr1 agr2]]]]:=ih _ _ mrg.
    exists (_: Δ1'). exists (_: Δ2')... }
Qed.

Lemma dyn_rename Γ Γ' Δ Δ' m A ξ :
  Γ ; Δ ⊢ m : A -> dyn_agree_ren ξ Γ Δ Γ' Δ' -> Γ' ; Δ' ⊢ m.[ren ξ] : A.[ren ξ].
Proof with eauto using dyn_type, dyn_agree_ren, dyn_agree_ren_key.
  move=>ty. elim: ty Γ' Δ' ξ=>{Γ Δ m A}.
  { move=>Γ Δ x A shs dhs Γ' Δ' ξ agr. asimpl.
    apply: dyn_var.
    apply: sta_agree_ren_has...
    apply: dyn_sta_agree_ren...
    apply: dyn_agree_ren_has... }
  { move=>Γ Δ A B m s t k tyP tym ihm Γ' Δ' ξ agr. asimpl.
    apply: dyn_lam0...
    have:=sta_rename tyP (dyn_sta_agree_ren agr).
    by autosubst. }
  { move=>Γ Δ A B m s t k tyP tym ihm Γ' Δ' ξ agr. asimpl.
    apply: dyn_lam1...
    have:=sta_rename tyP (dyn_sta_agree_ren agr).
    by autosubst. }
  { move=>Γ Δ A B m n s t tym ihm tyn Γ' Δ' ξ agr. asimpl.
    replace B.[n.[ren ξ] .: ren ξ] with B.[ren (upren ξ)].[n.[ren ξ]/]
      by autosubst.
    have{}ihm:=ihm _ _ _ agr.
    have{}ihn:=sta_rename tyn (dyn_sta_agree_ren agr).
    apply: dyn_app0...
    asimpl in ihm... }
  { move=>Γ Δ1 Δ2 Δ A B m n s t mrg tym ihm tyn ihn Γ' Δ' ξ agr. asimpl.
    replace B.[n.[ren ξ] .: ren ξ] with B.[ren (upren ξ)].[n.[ren ξ]/]
      by autosubst.
    have[Δ1'[Δ2'[mrg'[agr1 agr2]]]]:=dyn_agree_ren_merge agr mrg.
    have{}ihm:=ihm _ _ _ agr1.
    have{}ihn:=ihn _ _ _ agr2.
    apply: dyn_app1...
    asimpl in ihm... }
  { move=>Γ Δ A B m s eq tym ihm tyB Γ' Δ' ξ agr.
    apply: dyn_conv.
    apply: sta_conv_subst...
    apply: ihm...
    have:=sta_rename tyB (dyn_sta_agree_ren agr).
    asimpl... }
Qed.

Lemma dyn_weakenU Γ Δ m A B :
  dyn_wf Γ Δ ->
  Γ ; Δ ⊢ m : A -> (B :: Γ) ; (B :U Δ) ⊢ m.[ren (+1)] : A.[ren (+1)].
Proof with eauto using dyn_agree_ren, dyn_agree_ren_refl.
  move=>wf ty. apply: dyn_rename...
Qed.

Lemma dyn_weakenN Γ Δ m A B :
  dyn_wf Γ Δ ->
  Γ ; Δ ⊢ m : A -> (B :: Γ) ; (_: Δ) ⊢ m.[ren (+1)] : A.[ren (+1)].
Proof with eauto using dyn_agree_ren, dyn_agree_ren_refl.
  move=>wf ty. apply: dyn_rename...
Qed.

Lemma dyn_eweakenU Γ Δ m m' A A' B :
  m' = m.[ren (+1)] ->
  A' = A.[ren (+1)] ->
  dyn_wf Γ Δ ->
  Γ ; Δ ⊢ m : A ->
  (B :: Γ) ; (B :U Δ) ⊢ m' : A'.
Proof.
  move=>*; subst. exact: dyn_weakenU.
Qed.

Lemma dyn_eweakenN Γ Δ m m' A A' B :
  m' = m.[ren (+1)] ->
  A' = A.[ren (+1)] ->
  dyn_wf Γ Δ ->
  Γ ; Δ ⊢ m : A ->
  (B :: Γ) ; (_: Δ) ⊢ m' : A'.
Proof.
  move=>*; subst. exact: dyn_weakenN.
Qed.
