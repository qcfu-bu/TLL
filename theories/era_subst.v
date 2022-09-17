From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS era_weak.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "Γ1 ; Δ1 ⊨ σ1 ~ σ2 ⫤ Γ2 ; Δ2"
  (at level 50, σ1, σ2, Γ2 at next level).
Inductive era_agree_subst :
  sta_ctx -> dyn_ctx -> (var -> term) -> (var -> term) -> sta_ctx -> dyn_ctx -> Prop :=
| era_agree_subst_nil σ :
  nil ; nil ⊨ σ ~ σ ⫤ nil ; nil
| era_agree_subst_ty Γ1 Δ1 σ1 σ2 Γ2 Δ2 A s :
  Γ1 ; Δ1 ⊨ σ1 ~ σ2 ⫤ Γ2 ; Δ2 ->
  (A.[σ1] :: Γ1) ; (A.[σ1] :{s} Δ1) ⊨ up σ1 ~ up σ2 ⫤ (A :: Γ2) ; (A :{s} Δ2)
| era_agree_subst_n Γ1 Δ1 σ1 σ2 Γ2 Δ2 A :
  Γ1 ; Δ1 ⊨ σ1 ~ σ2 ⫤ Γ2 ; Δ2 ->
  (A.[σ1] :: Γ1) ; (_: Δ1) ⊨ up σ1 ~ up σ2 ⫤ (A :: Γ2) ; (_: Δ2)
| era_agree_subst_wk0 Γ1 Δ1 σ1 σ2 Γ2 Δ2 n n' A :
  Γ1 ; Δ1 ⊨ σ1 ~ σ2 ⫤ Γ2 ; Δ2 ->
  Γ1 ⊢ n : A.[σ1] ->
  Γ1 ; Δ1 ⊨ n .: σ1 ~ n' .: σ2 ⫤ (A :: Γ2) ; (_: Δ2)
| era_agree_subst_wk1 Γ1 Γ2 σ1 σ2 Δ1 Δ2 Δa Δb n n' A s :
  Δb ▷ s ->
  Δa ∘ Δb => Δ1 ->
  Γ1 ; Δa ⊨ σ1 ~ σ2 ⫤ Γ2 ; Δ2 ->
  Γ1 ; Δb ⊨ n ~ n' : A.[σ1] ->
  Γ1 ; Δ1 ⊨ n .: σ1 ~ n' .: σ2 ⫤ (A :: Γ2) ; (A :{s} Δ2)
| era_agree_subst_conv0 Γ1 Δ1 σ1 σ2 Γ2 Δ2 A B s :
  A === B ->
  Γ1 ⊢ B.[ren (+1)].[σ1] : @s ->
  Γ2 ⊢ B : @s ->
  Γ1 ; Δ1 ⊨ σ1 ~ σ2 ⫤ (A :: Γ2) ; (_: Δ2) ->
  Γ1 ; Δ1 ⊨ σ1 ~ σ2 ⫤ (B :: Γ2) ; (_: Δ2)
| era_agree_subst_conv1 Γ1 Δ1 σ1 σ2 Γ2 Δ2 A B s :
  A === B ->
  Γ1 ⊢ B.[ren (+1)].[σ1] : @s ->
  Γ2 ⊢ B : @s ->
  Γ1 ; Δ1 ⊨ σ1 ~ σ2 ⫤ (A :: Γ2) ; (A :{s} Δ2) ->
  Γ1 ; Δ1 ⊨ σ1 ~ σ2 ⫤ (B :: Γ2) ; (B :{s} Δ2)
where "Γ1 ; Δ1 ⊨ σ1 ~ σ2 ⫤ Γ2 ; Δ2" := (era_agree_subst Γ1 Δ1 σ1 σ2 Γ2 Δ2).

Lemma era_agree_subst_key Γ1 Γ2 Δ1 Δ2 σ1 σ2 s :
  Γ1 ; Δ1 ⊨ σ1 ~ σ2 ⫤ Γ2 ; Δ2 -> Δ2 ▷ s -> Δ1 ▷ s.
Proof with eauto using key.
  move=>agr. elim: agr s=>{Γ1 Γ2 Δ1 Δ2 σ1 σ2}...
  { move=>Γ1 Δ1 σ1 σ2 Γ2 Δ2 A s agr ih r k. inv k... }
  { move=>Γ1 Δ1 σ1 σ2 Γ2 Δ2 _ agr ih s k. inv k... }
  { move=>Γ1 Δ1 σ1 σ2 Γ2 Δ2 n n' A agr ih tyn s k. inv k... }
  { move=>Γ1 Γ2 σ1 σ2 Δ1 Δ2 Δa Δb n n' A s k1 mrg agr ih tyn r k2.
    inv k2... apply: key_merge... apply: key_impure. }
  { move=>Γ1 Δ1 σ1 σ2 Γ2 Δ2 A B s eq tyB1 tyB2 agr ih r k. inv k... }
Qed.

Lemma era_sta_agree_subst Γ1 Γ2 Δ1 Δ2 σ1 σ2 :
  Γ1 ; Δ1 ⊨ σ1 ~ σ2 ⫤ Γ2 ; Δ2 -> Γ1 ⊢ σ1 ⊣ Γ2.
Proof with eauto using sta_agree_subst.
  elim=>{Γ1 Γ2 Δ1 Δ2 σ1 σ2}...
  move=>Γ1 Γ2 σ1 σ2 Δ1 Δ2 Δa Δb n n' A s _ _ _ agr tyn.
  constructor...
  apply: dyn_sta_type...
  apply: era_dyn_type...
Qed.

Lemma era_agree_subst_refl Γ Δ : dyn_wf Γ Δ -> Γ ; Δ ⊨ ids ~ ids ⫤ Γ ; Δ.
Proof with eauto using era_agree_subst.
  elim: Γ Δ.
  { move=>Δ wf. inv wf... }
  { move=>A Γ ih Δ wf. inv wf.
    { have agr:=ih _ H1.
      have:(A.[ids] :: Γ); A.[ids] :{s} Δ0 ⊨
       up ids ~ up ids ⫤ (A :: Γ); A :{s} Δ0...
      by asimpl. }
    { have agr:=ih _ H1.
      have:(A.[ids] :: Γ); _: Δ0 ⊨ up ids ~ up ids ⫤ (A :: Γ); _: Δ0...
      by asimpl. } }
Qed.
Hint Resolve era_agree_subst_refl.

Lemma era_agree_subst_has Γ1 Γ2 σ1 σ2 Δ1 Δ2 x A :
  dyn_wf Γ1 Δ1 -> Γ1 ; Δ1 ⊨ σ1 ~ σ2 ⫤ Γ2 ; Δ2 -> dyn_has Δ2 x A ->
  Γ1 ; Δ1 ⊨ (σ1 x) ~ (σ2 x) : A.[σ1].
Proof with eauto using era_agree_subst, era_agree_subst_key.
  move=>wf agr. elim: agr wf x A=>{Γ1 Γ2 σ1 σ2 Δ1 Δ2}...
  { move=>σ _ x A hs. inv hs. }
  { move=>Γ1 Δ1 σ1 σ2 Γ2 Δ2 A s agr ih wf x B hs.
    inv wf. inv hs; asimpl.
    replace A.[σ1 >> ren (+1)] with A.[σ1].[ren (+1)] by autosubst.
    apply: era_var; constructor...
    replace A0.[σ1 >> ren (+1)] with A0.[σ1].[ren (+1)] by autosubst.
    apply: era_eweakenU... }
  { move=>Γ1 Δ1 σ1 σ2 Γ2 Δ2 A agr ih wf x B hs.
    inv wf. inv hs; asimpl...
    replace A0.[σ1 >> ren (+1)] with A0.[σ1].[ren (+1)]
      by autosubst.
    apply: era_eweakenN... }
  { move=>Γ1 Δ1 σ1 σ2 Γ2 Δ2 n n' A agr ih tyn wf x B hs. inv hs; asimpl... }
  { move=>Γ1 Γ2 σ1 σ2 Δ1 Δ2 Δa Δb n n' A s k mrg agr ih tyn wf x B hs.
    inv hs; asimpl.
    { have ka:=era_agree_subst_key agr H4.
      have->//:=merge_pureL mrg ka. }
    { have->:=merge_pureR mrg k.
      apply: ih...
      have[]//:=dyn_wf_merge mrg wf. } }
  { move=>Γ1 Δ1 σ1 σ2 Γ2 Δ2 A B s eq tyB1 tyB2 agr ih wf x C hs. inv hs.
    { apply: era_conv.
      apply: sta_conv_subst.
      apply: sta_conv_subst...
      apply: ih...
      constructor...
      exact: tyB1. }
    { apply: ih...
      constructor... } }
Qed.

Lemma era_agree_subst_merge Γ1 Γ2 Δ1 Δ2 Δa Δb σ1 σ2 :
  Γ1 ; Δ1 ⊨ σ1 ~ σ2 ⫤ Γ2 ; Δ2 -> Δa ∘ Δb => Δ2 ->
  exists Δa' Δb',
    Δa' ∘ Δb' => Δ1 /\
    Γ1 ; Δa' ⊨ σ1 ~ σ2 ⫤ Γ2 ; Δa /\ Γ1 ; Δb' ⊨ σ1 ~ σ2 ⫤ Γ2 ; Δb.
Proof with eauto 6 using merge, era_agree_subst, era_agree_subst_key.
  move=>agr. elim: agr Δa Δb=>{Γ1 Γ2 Δ1 Δ2 σ1 σ2}.
  { move=>σ Δa Δb mrg. inv mrg.
    exists nil. exists nil... }
  { move=>Γ1 Δ1 σ1 σ2 Γ2 Δ2 A s agr ih Δa Δb mrg. inv mrg.
    { have[Δa[Δb[mrg[agra agrb]]]]:=ih _ _ H2.
      exists (A.[σ1] :U Δa). exists (A.[σ1] :U Δb)... }
    { have[Δa[Δb[mrg[agra agrb]]]]:=ih _ _ H2.
      exists (A.[σ1] :L Δa). exists (_: Δb)... }
    { have[Δa[Δb[mrg[agra agrb]]]]:=ih _ _ H2.
      exists (_: Δa). exists (A.[σ1] :L Δb)... } }
  { move=>Γ1 Δ1 σ1 σ2 Γ2 Δ2 A agr ih Δa Δb mrg. inv mrg.
    have[Δa[Δb[mrg[agra agrb]]]]:=ih _ _ H2.
    exists (_: Δa). exists (_: Δb)... }
  { move=>Γ1 Δ1 σ1 σ2 Γ2 Δ2 n n' A agr ih tyn Δa Δb mrg. inv mrg.
    have[Δa[Δb[mrg[agra agrb]]]]:=ih _ _ H2.
    exists Δa. exists Δb... }
  { move=>Γ1 Γ2 σ1 σ2 Δ1 Δ2 Δa Δb n n' A s k mrg agr ih tyn Δa' Δb' mrg'.
    inv mrg'.
    { have[Δa'[Δb'[mrg'[agra agrb]]]]:=ih _ _ H2.
      have[Δc[mrg1 mrg2]]:=merge_splitL mrg mrg'.
      exists Δc. exists Δb'.
      repeat split...
      apply: era_agree_subst_wk1...
      have[Δd[mrg3 mrg4]]:=merge_splitR mrg mrg'.
      have e:=merge_pureR mrg3 k.
      by subst. }
    { have[Δa'[Δb'[mrg'[agra agrb]]]]:=ih _ _ H2.
      have[Δc[mrg1 mrg2]]:=merge_splitL mrg mrg'.
      exists Δc. exists Δb'.
      repeat split...
      apply: era_agree_subst_wk0...
      apply: dyn_sta_type...
      apply: era_dyn_type... }
    { have[Δa'[Δb'[mrg'[agra agrb]]]]:=ih _ _ H2.
      have[Δc[mrg1 mrg2]]:=merge_splitR mrg mrg'.
      exists Δa'. exists Δc.
      repeat split...
      exact: merge_sym.
      apply: era_agree_subst_wk0...
      apply: dyn_sta_type...
      apply: era_dyn_type... } }
  { move=>Γ1 Δ1 σ1 σ2 Γ2 Δ2 A B s eq tyB1 tyB2 agr ih Δa Δb mrg. inv mrg.
    have[Δa'[Δb'[mrg'[agra agrb]]]]:=ih _ _ (merge_null H2).
    exists Δa'. exists Δb'... }
  { move=>Γ1 Δ1 σ1 σ2 Γ2 Δ2 A B s eq tyB1 tyB2 agr ih Δa Δb mrg. inv mrg.
    { have[Δa'[Δb'[mrg'[agra agrb]]]]:=ih _ _ (merge_left A H2).
      exists Δa'. exists Δb'... }
    { have[Δa'[Δb'[mrg'[agra agrb]]]]:=ih _ _ (merge_right1 A H2).
      exists Δa'. exists Δb'... }
    { have[Δa'[Δb'[mrg'[agra agrb]]]]:=ih _ _ (merge_right2 A H2).
      exists Δa'. exists Δb'... } }
Qed.

Lemma era_substitution Γ1 Γ2 m m' A Δ1 Δ2 σ1 σ2 :
  dyn_wf Γ1 Δ1 -> Γ2 ; Δ2 ⊨ m ~ m' : A -> Γ1 ; Δ1 ⊨ σ1 ~ σ2 ⫤ Γ2 ; Δ2 ->
  Γ1 ; Δ1 ⊨ m.[σ1] ~ m'.[σ2] : A.[σ1].
Proof with eauto using era_agree_subst, era_agree_subst_key, era_type.
  move=>wf ty. elim: ty Γ1 Δ1 σ1 σ2 wf=>{Γ2 Δ2 m m' A}.
  { move=>Γ Δ x A shs dhs Γ1 Δ1 σ1 σ2 wf agr. asimpl.
    apply: era_agree_subst_has... }
  { move=>Γ Δ A B m m' s t k tyP tym ihm Γ1 Δ1 σ1 σ2 wf agr. asimpl.
    have[r[tyA _]]:=sta_pi0_inv tyP.
    apply: era_lam0...
    have//:=sta_substitution tyP (era_sta_agree_subst agr).
    apply: ihm...
    apply: dyn_wf_n...
    have:=sta_substitution tyA (era_sta_agree_subst agr).
    asimpl... }
  { move=>Γ Δ A B m m' s t k tyP tym ihm Γ1 Δ1 σ1 σ2 wf agr. asimpl.
    have[r[tyA _]]:=sta_pi1_inv tyP.
    apply: era_lam1...
    have//:=sta_substitution tyP (era_sta_agree_subst agr).
    apply: ihm...
    apply: dyn_wf_ty...
    have:=sta_substitution tyA (era_sta_agree_subst agr).
    asimpl... }
  { move=>Γ Δ A B m m' n s t tym ihm tyn Γ1 Δ1 σ1 σ2 wf agr. asimpl.
    replace B.[n.[σ1] .: σ1] with B.[up σ1].[n.[σ1]/] by autosubst.
    have{}ihm:=ihm _ _ _ _ wf agr.
    apply: era_app0...
    have//:=sta_substitution tyn (era_sta_agree_subst agr). }
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' s t mrg tym ihm tyn ihn
      Γ1 Δ0 σ1 σ2 wf agr. asimpl.
    replace B.[n.[σ1] .: σ1] with B.[up σ1].[n.[σ1]/] by autosubst.
    have[Δa[Δb[mrg0[agra agrb]]]]:=era_agree_subst_merge agr mrg.
    have[wfa wfb]:=dyn_wf_merge mrg0 wf.
    have{}ihm:=ihm _ _ _ _ wfa agra.
    have{}ihn:=ihn _ _ _ _ wfb agrb.
    apply: era_app1... }
  { move=>Γ Δ A B m m' s eq tym ihm tyB Γ1 Δ1 σ1 σ2 wf agr.
    apply: era_conv.
    apply: sta_conv_subst...
    apply: ihm...
    have:=sta_substitution tyB (era_sta_agree_subst agr).
    asimpl... }
Qed.

Lemma era_subst0 Γ Δ m m' n A B :
  dyn_wf Γ Δ -> (A :: Γ) ; _: Δ ⊨ m ~ m' : B -> Γ ⊢ n : A ->
  Γ ; Δ ⊨ m.[n/] ~ m'.[Box/] : B.[n/].
Proof with eauto using era_agree_subst_refl.
  move=>wf tym tyn.
  apply: era_substitution...
  apply: era_agree_subst_wk0...
  by asimpl.
Qed.

Lemma era_subst1 Γ Δ1 Δ2 Δ m m' n n' A B s :
  dyn_wf Γ Δ -> Δ2 ▷ s -> Δ1 ∘ Δ2 => Δ ->
  (A :: Γ) ; A :{s} Δ1 ⊨ m ~ m' : B -> Γ ; Δ2 ⊨ n ~ n' : A ->
  Γ ; Δ ⊨ m.[n/] ~ m'.[n'/] : B.[n/].
Proof with eauto using era_agree_subst_refl.
  move=>wf k mrg tym tyn.
  apply: era_substitution...
  apply: era_agree_subst_wk1...
  have[wf1 wf2]:=dyn_wf_merge mrg wf...
  by asimpl.
Qed.

Lemma era_esubst0 Γ Δ m m' n n' v A B B' :
  m' = m.[v/] ->
  n' = n.[Box/] ->
  B' = B.[v/] ->
  dyn_wf Γ Δ ->
  (A :: Γ) ; _: Δ ⊨ m ~ n : B -> Γ ⊢ v : A ->
  Γ ; Δ ⊨ m' ~ n' : B'.
Proof.
  move=>*; subst. apply: era_subst0; eauto.
Qed.

Lemma era_esubst1 Γ Δ1 Δ2 Δ m m' n n' v v' A B B' s :
  m' = m.[v/] ->
  n' = n.[v'/] ->
  B' = B.[v/] ->
  dyn_wf Γ Δ -> Δ2 ▷ s -> Δ1 ∘ Δ2 => Δ ->
  (A :: Γ) ; A :{s} Δ1 ⊨ m ~ n : B ->
  Γ ; Δ2 ⊨ v ~ v' : A ->
  Γ ; Δ ⊨ m' ~ n' : B'.
Proof.
  move=>*; subst. apply: era_subst1; eauto.
Qed.

Lemma era_ctx_conv0 Γ Δ m m' A B C s :
  dyn_wf (B :: Γ) (_: Δ) -> B === A ->
  Γ ⊢ A : @s -> (A :: Γ) ; _: Δ ⊨ m ~ m' : C ->
  (B :: Γ) ; _: Δ ⊨ m ~ m' : C.
Proof with eauto.
  move=>wf eq tyA tym.
  have:(B :: Γ) ; _: Δ ⊨ m.[ids] ~ m'.[ids] : C.[ids].
  apply: era_substitution...
  apply: era_agree_subst_conv0...
  apply: sta_eweaken...
  asimpl...
  asimpl...
  asimpl...
Qed.

Lemma era_ctx_conv1 Γ Δ m m' A B C s :
  dyn_wf (B :: Γ) (B :{s} Δ) -> B === A ->
  Γ ⊢ A : @s -> (A :: Γ) ; A :{s} Δ ⊨ m ~ m' : C ->
  (B :: Γ) ; B :{s} Δ ⊨ m ~ m' : C.
Proof with eauto.
  move=>wf eq tyA tym.
  have:(B :: Γ) ; B :{s} Δ ⊨ m.[ids] ~ m'.[ids] : C.[ids].
  apply: era_substitution...
  apply: era_agree_subst_conv1...
  apply: sta_eweaken...
  asimpl...
  asimpl...
  asimpl...
Qed.

