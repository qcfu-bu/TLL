From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_subst dyn_valid dyn_weak.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "Γ1 ; Δ1 ⊨ σ ⫤ Γ2 ; Δ2" (at level 50, σ, Γ2 at next level).
Inductive dyn_agree_subst :
  sta_ctx -> dyn_ctx -> (var -> term) -> sta_ctx -> dyn_ctx -> Prop :=
| dyn_agree_subst_nil σ :
  nil ; nil ⊨ σ ⫤ nil ; nil
| dyn_agree_subst_ty Γ1 Δ1 σ Γ2 Δ2 A s :
  Γ1 ; Δ1 ⊨ σ ⫤ Γ2 ; Δ2 ->
  (A.[σ] :: Γ1) ; (A.[σ] :{s} Δ1) ⊨ up σ ⫤ (A :: Γ2) ; (A :{s} Δ2)
| dyn_agree_subst_n Γ1 Δ1 σ Γ2 Δ2 A :
  Γ1 ; Δ1 ⊨ σ ⫤ Γ2 ; Δ2 ->
  (A.[σ] :: Γ1) ; (_: Δ1) ⊨ up σ ⫤ (A :: Γ2) ; (_: Δ2)
| dyn_agree_subst_wk0 Γ1 Δ1 σ Γ2 Δ2 n A :
  Γ1 ; Δ1 ⊨ σ ⫤ Γ2 ; Δ2 ->
  Γ1 ⊢ n : A.[σ] ->
  Γ1 ; Δ1 ⊨ n .: σ ⫤ (A :: Γ2) ; (_: Δ2)
| dyn_agree_subst_wk1 Γ1 Γ2 σ Δ1 Δ2 Δa Δb n A s :
  Δb ▷ s ->
  Δa ∘ Δb => Δ1 ->
  Γ1 ; Δa ⊨ σ ⫤ Γ2 ; Δ2 ->
  Γ1 ; Δb ⊨ n : A.[σ] ->
  Γ1 ; Δ1 ⊨ n .: σ ⫤ (A :: Γ2) ; (A :{s} Δ2)
| dyn_agree_subst_conv0 Γ1 Δ1 σ Γ2 Δ2 A B s :
  A === B ->
  Γ1 ⊢ B.[ren (+1)].[σ] : @s ->
  Γ2 ⊢ B : @s ->
  Γ1 ; Δ1 ⊨ σ ⫤ (A :: Γ2) ; (_: Δ2) ->
  Γ1 ; Δ1 ⊨ σ ⫤ (B :: Γ2) ; (_: Δ2)
| dyn_agree_subst_conv1 Γ1 Δ1 σ Γ2 Δ2 A B s :
  A === B ->
  Γ1 ⊢ B.[ren (+1)].[σ] : @s ->
  Γ2 ⊢ B : @s ->
  Γ1 ; Δ1 ⊨ σ ⫤ (A :: Γ2) ; (A :{s} Δ2) ->
  Γ1 ; Δ1 ⊨ σ ⫤ (B :: Γ2) ; (B :{s} Δ2)
where "Γ1 ; Δ1 ⊨ σ ⫤ Γ2 ; Δ2" := (dyn_agree_subst Γ1 Δ1 σ Γ2 Δ2).

Lemma dyn_agree_subst_key Γ1 Γ2 Δ1 Δ2 σ s :
  Γ1 ; Δ1 ⊨ σ ⫤ Γ2 ; Δ2 -> Δ2 ▷ s -> Δ1 ▷ s.
Proof with eauto using key.
  move=>agr. elim: agr s=>{Γ1 Γ2 Δ1 Δ2 σ}...
  { move=>Γ1 Δ1 σ Γ2 Δ2 A s agr ih r k. inv k... }
  { move=>Γ1 Δ1 σ Γ2 Δ2 _ agr ih s k. inv k... }
  { move=>Γ1 Δ1 σ Γ2 Δ2 n A agr ih tyn s k. inv k... }
  { move=>Γ1 Γ2 σ Δ1 Δ2 Δa Δb n A s k1 mrg agr ih tyn r k2. inv k2...
    apply: key_merge...
    apply: key_impure. }
  { move=>Γ1 Δ1 σ Γ2 Δ2 A B s eq tyB1 tyB2 agr ih r k. inv k... }
Qed.

Lemma dyn_sta_agree_subst Γ1 Γ2 Δ1 Δ2 σ :
  Γ1 ; Δ1 ⊨ σ ⫤ Γ2 ; Δ2 -> Γ1 ⊢ σ ⊣ Γ2.
Proof with eauto using sta_agree_subst.
  elim=>{Γ1 Γ2 Δ1 Δ2 σ}...
  move=>Γ1 Γ2 σ Δ1 Δ2 Δa Δb n A s _ _ _ agr tyn.
  constructor...
  apply: dyn_sta_type...
Qed.

Lemma dyn_agree_subst_refl Γ Δ : dyn_wf Γ Δ -> Γ ; Δ ⊨ ids ⫤ Γ ; Δ.
Proof with eauto using dyn_agree_subst.
  elim: Γ Δ.
  { move=>Δ wf. inv wf... }
  { move=>A Γ ih Δ wf. inv wf.
    { have agr:=ih _ H1.
      have:(A.[ids] :: Γ); A.[ids] :{s} Δ0 ⊨ up ids ⫤ (A :: Γ); A :{s} Δ0...
      by asimpl. }
    { have agr:=ih _ H1.
      have:(A.[ids] :: Γ); _: Δ0 ⊨ up ids ⫤ (A :: Γ); _: Δ0...
      by asimpl. } }
Qed.

Lemma dyn_wf_merge Γ Δ Δ1 Δ2 :
  Δ1 ∘ Δ2 => Δ -> dyn_wf Γ Δ -> dyn_wf Γ Δ1 /\ dyn_wf Γ Δ2.
Proof with eauto using dyn_wf.
  move=>mrg agr. elim: agr Δ1 Δ2 mrg=>{Γ Δ}.
  { move=>Δ1 Δ2 mrg. inv mrg... }
  { move=>Γ Δ A s wf ih tyA Δ1 Δ2 mrg. inv mrg.
    { have[wf1 wf2]:=ih _ _ H2... }
    { have[wf1 wf2]:=ih _ _ H2... }
    { have[wf1 wf2]:=ih _ _ H2... } }
  { move=>Γ Δ A s wf ih tyA Δ1 Δ2 mrg. inv mrg.
    have[wf1 wf2]:=ih _ _ H2... }
Qed.

Lemma dyn_agree_subst_has Γ1 Γ2 σ Δ1 Δ2 x A :
  dyn_wf Γ1 Δ1 ->
  Γ1 ; Δ1 ⊨ σ ⫤ Γ2 ; Δ2 -> dyn_has Δ2 x A -> Γ1 ; Δ1 ⊨ (σ x) : A.[σ].
Proof with eauto using dyn_agree_subst, dyn_agree_subst_key.
  move=>wf agr. elim: agr wf x A=>{Γ1 Γ2 σ Δ1 Δ2}...
  { move=>σ _ x A hs. inv hs. }
  { move=>Γ1 Δ1 σ Γ2 Δ2 A s agr ih wf x B hs.
    inv wf. inv hs; asimpl.
    replace A.[σ >> ren (+1)] with A.[σ].[ren (+1)] by autosubst.
    apply: dyn_var; constructor...
    replace A0.[σ >> ren (+1)] with A0.[σ].[ren (+1)] by autosubst.
    apply: dyn_eweakenU... }
  { move=>Γ1 Δ1 σ Γ2 Δ2 A agr ih wf x B hs.
    inv wf. inv hs; asimpl...
    replace A0.[σ >> ren (+1)] with A0.[σ].[ren (+1)]
      by autosubst.
    apply: dyn_eweakenN... }
  { move=>Γ1 Δ1 σ Γ2 Δ2 n A agr ih tyn wf x B hs. inv hs; asimpl... }
  { move=>Γ1 Γ2 σ Δ1 Δ2 Δa Δb n A s k mrg agr ih tyn wf x B hs.
    inv hs; asimpl.
    { have ka:=dyn_agree_subst_key agr H4.
      have->//:=merge_pureL mrg ka. }
    { have->:=merge_pureR mrg k.
      apply: ih...
      have[]//:=dyn_wf_merge mrg wf. } }
  { move=>Γ1 Δ1 σ Γ2 Δ2 A B s eq tyB1 tyB2 agr ih wf x C hs. inv hs.
    { apply: dyn_conv.
      apply: sta_conv_subst.
      apply: sta_conv_subst...
      apply: ih...
      constructor...
      exact: tyB1. }
    { apply: ih...
      constructor... } }
Qed.

Lemma dyn_agree_subst_merge Γ1 Γ2 Δ1 Δ2 Δa Δb σ :
  Γ1 ; Δ1 ⊨ σ ⫤ Γ2 ; Δ2 -> Δa ∘ Δb => Δ2 ->
  exists Δa' Δb',
    Δa' ∘ Δb' => Δ1 /\ Γ1 ; Δa' ⊨ σ ⫤ Γ2 ; Δa /\ Γ1 ; Δb' ⊨ σ ⫤ Γ2 ; Δb.
Proof with eauto 6 using merge, dyn_agree_subst, dyn_agree_subst_key.
  move=>agr. elim: agr Δa Δb=>{Γ1 Γ2 Δ1 Δ2 σ}.
  { move=>σ Δa Δb mrg. inv mrg.
    exists nil. exists nil... }
  { move=>Γ1 Δ1 σ Γ2 Δ2 A s agr ih Δa Δb mrg. inv mrg.
    { have[Δa[Δb[mrg[agra agrb]]]]:=ih _ _ H2.
      exists (A.[σ] :U Δa). exists (A.[σ] :U Δb)... }
    { have[Δa[Δb[mrg[agra agrb]]]]:=ih _ _ H2.
      exists (A.[σ] :L Δa). exists (_: Δb)... }
    { have[Δa[Δb[mrg[agra agrb]]]]:=ih _ _ H2.
      exists (_: Δa). exists (A.[σ] :L Δb)... } }
  { move=>Γ1 Δ1 σ Γ2 Δ2 A agr ih Δa Δb mrg. inv mrg.
    have[Δa[Δb[mrg[agra agrb]]]]:=ih _ _ H2.
    exists (_: Δa). exists (_: Δb)... }
  { move=>Γ1 Δ1 σ Γ2 Δ2 n A agr ih tyn Δa Δb mrg. inv mrg.
    have[Δa[Δb[mrg[agra agrb]]]]:=ih _ _ H2.
    exists Δa. exists Δb... }
  { move=>Γ1 Γ2 σ Δ1 Δ2 Δa Δb n A s k mrg agr ih tyn Δa' Δb' mrg'. inv mrg'.
    { have[Δa'[Δb'[mrg'[agra agrb]]]]:=ih _ _ H2.
      have[Δc[mrg1 mrg2]]:=merge_splitL mrg mrg'.
      exists Δc. exists Δb'.
      repeat split...
      apply: dyn_agree_subst_wk1...
      have[Δd[mrg3 mrg4]]:=merge_splitR mrg mrg'.
      have e:=merge_pureR mrg3 k.
      by subst. }
    { have[Δa'[Δb'[mrg'[agra agrb]]]]:=ih _ _ H2.
      have[Δc[mrg1 mrg2]]:=merge_splitL mrg mrg'.
      exists Δc. exists Δb'.
      repeat split...
      apply: dyn_agree_subst_wk0...
      apply: dyn_sta_type... }
    { have[Δa'[Δb'[mrg'[agra agrb]]]]:=ih _ _ H2.
      have[Δc[mrg1 mrg2]]:=merge_splitR mrg mrg'.
      exists Δa'. exists Δc.
      repeat split...
      exact: merge_sym.
      apply: dyn_agree_subst_wk0...
      apply: dyn_sta_type... } }
  { move=>Γ1 Δ1 σ Γ2 Δ2 A B s eq tyB1 tyB2 agr ih Δa Δb mrg. inv mrg.
    have[Δa'[Δb'[mrg'[agra agrb]]]]:=ih _ _ (merge_null H2).
    exists Δa'. exists Δb'... }
  { move=>Γ1 Δ1 σ Γ2 Δ2 A B s eq tyB1 tyB2 agr ih Δa Δb mrg. inv mrg.
    { have[Δa'[Δb'[mrg'[agra agrb]]]]:=ih _ _ (merge_left A H2).
      exists Δa'. exists Δb'... }
    { have[Δa'[Δb'[mrg'[agra agrb]]]]:=ih _ _ (merge_right1 A H2).
      exists Δa'. exists Δb'... }
    { have[Δa'[Δb'[mrg'[agra agrb]]]]:=ih _ _ (merge_right2 A H2).
      exists Δa'. exists Δb'... } }
Qed.
