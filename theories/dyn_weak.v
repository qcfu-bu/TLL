From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_weak dyn_type.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive dyn_agree_ren : (var -> var) ->
  sta_ctx term -> dyn_ctx term -> sta_ctx term -> dyn_ctx term -> Prop :=
| dyn_agree_ren_nil ξ :
  dyn_agree_ren ξ nil nil nil nil
| dyn_agree_ren_ty Γ Γ' Δ Δ' ξ m s :
  dyn_agree_ren ξ Γ Δ Γ' Δ' ->
  dyn_agree_ren (upren ξ)
    (m :: Γ) (m :{s} Δ) (m.[ren ξ] :: Γ) (m.[ren ξ] :{s} Δ')
| dyn_agree_ren_n Γ Γ' Δ Δ' ξ m :
  dyn_agree_ren ξ Γ Δ Γ' Δ' ->
  dyn_agree_ren (upren ξ)
    (m :: Γ) (_: Δ) (m.[ren ξ] :: Γ) (_: Δ')
| dyn_agree_ren_wkU Γ Γ' Δ Δ' ξ m :
  dyn_agree_ren ξ Γ Δ Γ' Δ' ->
  dyn_agree_ren (ξ >>> (+1)) Γ Δ (m :: Γ') (m :U Δ')
| dyn_agree_ren_wkN Γ Γ' Δ Δ' ξ m :
  dyn_agree_ren ξ Γ Δ Γ' Δ' ->
  dyn_agree_ren (ξ >>> (+1)) Γ Δ (m :: Γ') (_: Δ').

Lemma dyn_agree_ren_refl Γ Δ :
  dyn_wf Γ Δ -> dyn_agree_ren id Γ Δ Γ Δ.
Proof with eauto using dyn_agree_ren.
  elim: Γ Δ.
  { move=>Δ wf. inv wf... }
  { move=>A Γ ih Δ wf. inv wf.
    have agr:=ih _ H1.
    have:dyn_agree_ren (upren id)
      (A :: Γ) (A :{s} Δ0) (A.[ren id] :: Γ) (A.[ren id] :{s} Δ0)...
    by asimpl. }
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
