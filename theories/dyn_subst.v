From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_subst sta_inv dyn_valid dyn_weak.

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
Hint Resolve dyn_agree_subst_refl.

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

Lemma dyn_substitution Γ1 Γ2 m A Δ1 Δ2 σ :
  dyn_wf Γ1 Δ1 ->
  Γ2 ; Δ2 ⊨ m : A -> Γ1 ; Δ1 ⊨ σ ⫤ Γ2 ; Δ2 -> Γ1 ; Δ1 ⊨ m.[σ] : A.[σ].
Proof with eauto using dyn_agree_subst, dyn_agree_subst_key, dyn_type.
  move=>wf ty. elim: ty Γ1 Δ1 σ wf=>{Γ2 Δ2 m A}.
  { move=>Γ Δ x A shs dhs Γ1 Δ1 σ wf agr. asimpl.
    apply: dyn_agree_subst_has... }
  { move=>Γ Δ A B m s t k tyP tym ihm Γ1 Δ1 σ wf agr. asimpl.
    have[r tyA _]:=sta_pi0_inv tyP.
    apply: dyn_lam0...
    have//:=sta_substitution tyP (dyn_sta_agree_subst agr).
    apply: ihm...
    apply: dyn_wf_n...
    have:=sta_substitution tyA (dyn_sta_agree_subst agr).
    asimpl... }
  { move=>Γ Δ A B m s t k tyP tym ihm Γ1 Δ1 σ wf agr. asimpl.
    have[r tyA _]:=sta_pi1_inv tyP.
    apply: dyn_lam1...
    have//:=sta_substitution tyP (dyn_sta_agree_subst agr).
    apply: ihm...
    apply: dyn_wf_ty...
    have:=sta_substitution tyA (dyn_sta_agree_subst agr).
    asimpl... }
  { move=>Γ Δ A B m n s t tym ihm tyn Γ1 Δ1 σ wf agr. asimpl.
    replace B.[n.[σ] .: σ] with B.[up σ].[n.[σ]/] by autosubst.
    have{}ihm:=ihm _ _ _ wf agr.
    apply: dyn_app0...
    have//:=sta_substitution tyn (dyn_sta_agree_subst agr). }
  { move=>Γ Δ1 Δ2 Δ A B m n s t mrg tym ihm tyn ihn Γ1 Δ0 σ wf agr. asimpl.
    replace B.[n.[σ] .: σ] with B.[up σ].[n.[σ]/] by autosubst.
    have[Δa[Δb[mrg0[agra agrb]]]]:=dyn_agree_subst_merge agr mrg.
    have[wfa wfb]:=dyn_wf_merge mrg0 wf.
    have{}ihm:=ihm _ _ _ wfa agra.
    have{}ihn:=ihn _ _ _ wfb agrb.
    apply: dyn_app1... }
  { move=>Γ Δ A B m s eq tym ihm tyB Γ1 Δ1 σ wf agr.
    apply: dyn_conv.
    apply: sta_conv_subst...
    apply: ihm...
    have:=sta_substitution tyB (dyn_sta_agree_subst agr).
    asimpl... }
Qed.

Lemma dyn_subst0 Γ Δ m n A B :
  dyn_wf Γ Δ ->
  (A :: Γ) ; _: Δ ⊨ m : B -> Γ ⊢ n : A -> Γ ; Δ ⊨ m.[n/] : B.[n/].
Proof with eauto using dyn_agree_subst_refl.
  move=>wf tym tyn.
  apply: dyn_substitution...
  apply: dyn_agree_subst_wk0...
  by asimpl.
Qed.

Lemma dyn_subst1 Γ Δ1 Δ2 Δ m n A B s :
  dyn_wf Γ Δ -> Δ2 ▷ s -> Δ1 ∘ Δ2 => Δ ->
  (A :: Γ) ; A :{s} Δ1 ⊨ m : B -> Γ ; Δ2 ⊨ n : A -> Γ ; Δ ⊨ m.[n/] : B.[n/].
Proof with eauto using dyn_agree_subst_refl.
  move=>wf k mrg tym tyn.
  apply: dyn_substitution...
  apply: dyn_agree_subst_wk1...
  have[wf1 wf2]:=dyn_wf_merge mrg wf...
  by asimpl.
Qed.

Lemma dyn_esubst0 Γ Δ m m' n A B B' :
  m' = m.[n/] ->
  B' = B.[n/] ->
  dyn_wf Γ Δ ->
  (A :: Γ) ; _: Δ ⊨ m : B -> Γ ⊢ n : A -> Γ ; Δ ⊨ m': B'.
Proof.
  move=>*; subst. apply: dyn_subst0; eauto.
Qed.

Lemma dyn_esubst1 Γ Δ1 Δ2 Δ m m' n A B B' s :
  m' = m.[n/] ->
  B' = B.[n/] ->
  dyn_wf Γ Δ -> Δ2 ▷ s -> Δ1 ∘ Δ2 => Δ ->
  (A :: Γ) ; A :{s} Δ1 ⊨ m : B -> Γ ; Δ2 ⊨ n : A -> Γ ; Δ ⊨ m' : B'.
Proof.
  move=>*; subst. apply: dyn_subst1; eauto.
Qed.

Lemma dyn_ctx_conv0 Γ Δ m A B C s :
  dyn_wf (B :: Γ) (_: Δ) -> B === A ->
  Γ ⊢ A : @s -> (A :: Γ) ; _: Δ ⊨ m : C -> (B :: Γ) ; _: Δ ⊨ m : C.
Proof with eauto.
  move=>wf eq tyA tym.
  have:(B :: Γ) ; _: Δ ⊨ m.[ids] : C.[ids].
  apply: dyn_substitution...
  apply: dyn_agree_subst_conv0...
  apply: sta_eweaken...
  asimpl...
  asimpl...
  asimpl...
Qed.
