From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS era_weak.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "Θ1 ; Γ1 ; Δ1 ⊢ σ1 ~ σ2 ⊣ Γ2 ; Δ2"
  (at level 50, Γ1, Δ1, σ1, σ2, Γ2, Δ2 at next level).
Inductive era_agree_subst :
  dyn_ctx -> sta_ctx -> dyn_ctx -> (var -> term) -> (var -> term) -> sta_ctx -> dyn_ctx -> Prop :=
| era_agree_subst_nil Θ1 :
  dyn_empty Θ1 ->
  Θ1 ; nil ; nil ⊢ ids ~ ids ⊣ nil ; nil
| era_agree_subst_ty Θ1 Γ1 Δ1 σ1 σ2 Γ2 Δ2 A s :
  Θ1 ; Γ1 ; Δ1 ⊢ σ1 ~ σ2 ⊣ Γ2 ; Δ2 ->
  Γ2 ⊢ A : Sort s ->
  Θ1 ; (A.[σ1] :: Γ1) ; (A.[σ1] .{s} Δ1) ⊢ up σ1 ~ up σ2 ⊣ (A :: Γ2) ; (A .{s} Δ2)
| era_agree_subst_n Θ1 Γ1 Δ1 σ1 σ2 Γ2 Δ2 A s :
  Θ1 ; Γ1 ; Δ1 ⊢ σ1 ~ σ2 ⊣ Γ2 ; Δ2 ->
  Γ2 ⊢ A : Sort s ->
  Θ1 ; (A.[σ1] :: Γ1) ; (_: Δ1) ⊢ up σ1 ~ up σ2 ⊣ (A :: Γ2) ; (_: Δ2)
| era_agree_subst_wk0 Θ1 Γ1 Δ1 σ1 σ2 Γ2 Δ2 n n' A :
  Θ1 ; Γ1 ; Δ1 ⊢ σ1 ~ σ2 ⊣ Γ2 ; Δ2 ->
  Γ1 ⊢ n : A.[σ1] ->
  Θ1 ; Γ1 ; Δ1 ⊢ n .: σ1 ~ n' .: σ2 ⊣ (A :: Γ2) ; (_: Δ2)
| era_agree_subst_wk1 Θa Θb Θ1 Γ1 Γ2 σ1 σ2 Δ1 Δ2 Δa Δb n n' A s :
  Θb ▷ s ->
  Δb ▷ s ->
  Θa ∘ Θb => Θ1 ->
  Δa ∘ Δb => Δ1 ->
  Θa ; Γ1 ; Δa ⊢ σ1 ~ σ2 ⊣ Γ2 ; Δ2 ->
  Θb ; Γ1 ; Δb ⊢ n ~ n' : A.[σ1] ->
  Θ1 ; Γ1 ; Δ1 ⊢ n .: σ1 ~ n' .: σ2 ⊣ (A :: Γ2) ; (A .{s} Δ2)
| era_agree_subst_conv0 Θ1 Γ1 Δ1 σ1 σ2 Γ2 Δ2 A B s :
  A ≃ B ->
  Γ1 ⊢ B.[ren (+1)].[σ1] : Sort s ->
  Γ2 ⊢ B : Sort s ->
  Θ1 ; Γ1 ; Δ1 ⊢ σ1 ~ σ2 ⊣ (A :: Γ2) ; (_: Δ2) ->
  Θ1 ; Γ1 ; Δ1 ⊢ σ1 ~ σ2 ⊣ (B :: Γ2) ; (_: Δ2)
| era_agree_subst_conv1 Θ1 Γ1 Δ1 σ1 σ2 Γ2 Δ2 A B s :
  A ≃ B ->
  Γ1 ⊢ B.[ren (+1)].[σ1] : Sort s ->
  Γ2 ⊢ B : Sort s ->
  Θ1 ; Γ1 ; Δ1 ⊢ σ1 ~ σ2 ⊣ (A :: Γ2) ; (A .{s} Δ2) ->
  Θ1 ; Γ1 ; Δ1 ⊢ σ1 ~ σ2 ⊣ (B :: Γ2) ; (B .{s} Δ2)
where "Θ1 ; Γ1 ; Δ1 ⊢ σ1 ~ σ2 ⊣ Γ2 ; Δ2" := (era_agree_subst Θ1 Γ1 Δ1 σ1 σ2 Γ2 Δ2).

Lemma era_agree_subst_key Θ1 Γ1 Γ2 Δ1 Δ2 σ1 σ2 s :
  Θ1 ; Γ1 ; Δ1 ⊢ σ1 ~ σ2 ⊣ Γ2 ; Δ2 -> Δ2 ▷ s -> Θ1 ▷ s /\ Δ1 ▷ s.
Proof with eauto using key, key_empty, key_merge, key_impure.
  move=>agr. elim: agr s=>{Θ1 Γ1 Γ2 Δ1 Δ2 σ1 σ2}...
  { move=>Θ1 Γ1 Δ1 σ1 σ2 Γ2 Δ2 A s agr ih tyA r k. inv k... have[]:=ih _ H3... }
  { move=>Θ1 Γ1 Δ1 σ1 σ2 Γ2 Δ2 A s agr ih tyA r k. inv k... have[]:=ih _ H0... }
  { move=>Θ1 Γ1 Δ1 σ1 σ2 Γ2 Δ2 n n' A agr ih tyn s k. inv k... }
  { move=>Θa Θb Θ1 Γ1 Γ2 σ1 σ2 Δ1 Δ2 Δa Δb n n' A s k1 k2 mrg1 mrg2 agr ih tyn r k3. inv k3...
    have[]:=ih _ H3... }
  { move=>Θ1 Γ1 Δ1 σ1 σ2 Γ2 Δ2 A B s eq tyB1 tyB2 agr ih r k. inv k... }
Qed.

Lemma era_sta_agree_subst Θ1 Γ1 Γ2 Δ1 Δ2 σ1 σ2 :
  Θ1 ; Γ1 ; Δ1 ⊢ σ1 ~ σ2 ⊣ Γ2 ; Δ2 -> Γ1 ⊢ σ1 ⊣ Γ2.
Proof with eauto using sta_agree_subst. elim... Qed.

Lemma era_dyn_agree_subst Θ1 Γ1 Γ2 Δ1 Δ2 σ1 σ2 :
  Θ1 ; Γ1 ; Δ1 ⊢ σ1 ~ σ2 ⊣ Γ2 ; Δ2 -> Θ1 ; Γ1 ; Δ1 ⊢ σ1 ⊣ Γ2 ; Δ2.
Proof with eauto using dyn_agree_subst. elim... Qed.

Lemma era_agree_subst_refl Θ Γ Δ :
  dyn_empty Θ -> dyn_wf Γ Δ -> Θ ; Γ ; Δ ⊢ ids ~ ids ⊣ Γ ; Δ.
Proof with eauto using era_agree_subst.
  elim: Γ Θ Δ.
  { move=>Θ Δ emp wf. inv wf... }
  { move=>A Γ ih Θ Δ emp wf. inv wf.
    { have agr:=ih Θ _ emp H1.
      have:Θ ; (A.[ids] :: Γ); A.[ids] .{s} Δ0 ⊢ up ids ~ up ids ⊣ (A :: Γ); A .{s} Δ0...
      by asimpl. }
    { have agr:=ih Θ _ emp H1.
      have:Θ ; (A.[ids] :: Γ); _: Δ0 ⊢ up ids ~ up ids ⊣ (A :: Γ); _: Δ0...
      by asimpl. } }
Qed.
#[global] Hint Resolve era_agree_subst_refl.

Lemma era_type_empty Θ1 Γ Δ m m' A :
  Θ1 ; Γ ; Δ ⊢ m ~ m' : A -> exists Θ, dyn_empty Θ /\ Θ ∘ Θ1 => Θ1.
Proof with eauto.
  move=>erm. apply: dyn_type_empty.
  apply: era_dyn_type...
Qed.

Lemma era_agree_subst_has Θ1 Θ2 Θ Γ1 Γ2 σ1 σ2 Δ1 Δ2 x s A :
  Θ1 ; Γ1 ; Δ1 ⊢ σ1 ~ σ2 ⊣ Γ2 ; Δ2 -> dyn_empty Θ2 -> Θ1 ∘ Θ2 => Θ ->
  dyn_wf Γ1 Δ1 -> dyn_has Δ2 x s A -> Θ ; Γ1 ; Δ1 ⊢ (σ1 x) ~ (σ2 x) : A.[σ1].
Proof with eauto using era_agree_subst, era_agree_subst_key.
  move=>agr. elim: agr x Θ2 Θ s A=>{Θ1 Γ1 Γ2 σ1 σ2 Δ1 Δ2}...
  { move=>Θ1 emp1 x Θ2 Θ s A emp2 mrg wf hs. inv hs. }
  { move=>Θ1 Γ1 Δ1 σ1 σ2 Γ2 Δ2 A s agr ih tyA x Θ2 Θ r B emp2 mrg wf hs.
    inv wf. inv hs; asimpl.
    { replace A.[σ1 >> ren (+1)] with A.[σ1].[ren (+1)] by autosubst.
      have[k1 k2]:=era_agree_subst_key agr H7.
      apply: era_var.
      have e:=merge_pureL mrg k1. subst...
      constructor...
      constructor...
      constructor... }
    { replace A0.[σ1 >> ren (+1)] with A0.[σ1].[ren (+1)] by autosubst.
      apply: era_eweakenU... } }
  { move=>Θ1 Γ1 Δ1 σ1 σ2 Γ2 Δ2 A s agr ih tyA x Θ2 Θ t B emp mrg wf hs.
    inv wf. inv hs; asimpl...
    replace A0.[σ1 >> ren (+1)] with A0.[σ1].[ren (+1)] by autosubst.
    apply: era_eweakenN... }
  { move=>Θ1 Γ1 Δ1 σ1 σ2 Γ2 Δ2 n n' A agr ih tyn x Θ2 Θ s B emp mrg wf hs. inv hs; asimpl... }
  { move=>Θa Θb Θ1 Γ1 Γ2 σ1 σ2 Δ1 Δ2 Δa Δb n n' A s k1 k2 mrg1 mrg2 agr ih tyn x Θ2 Θ t B emp mrg wf hs.
    inv hs; asimpl.
    { have[k3 k4]:=era_agree_subst_key agr H5.
      have e:=merge_pureL mrg1 k3. subst.
      have e:=merge_pureL mrg2 k4. subst.
      have e:=merge_emptyR mrg emp. subst... }
    { have e:=merge_pureR mrg1 k1. subst.
      have e:=merge_pureR mrg2 k2. subst.
      apply: ih... } }
  { move=>Θ1 Γ1 Δ1 σ1 σ2 Γ2 Δ2 A B s eq tyB1 tyB2 agr ih x Θ2 Θ t C emp mrg wf hs. inv hs.
    { apply: era_conv.
      apply: sta_conv_subst.
      apply: sta_conv_subst...
      apply: ih...
      constructor...
      exact: tyB1. }
    { apply: ih...
      constructor... } }
Qed.

Lemma era_agree_subst_merge Θ1 Γ1 Γ2 Δ1 Δ2 Δa Δb σ1 σ2 :
  Θ1 ; Γ1 ; Δ1 ⊢ σ1 ~ σ2 ⊣ Γ2 ; Δ2 -> Δa ∘ Δb => Δ2 ->
  exists Θa' Θb' Δa' Δb',
    Θa' ∘ Θb' => Θ1 /\
    Δa' ∘ Δb' => Δ1 /\
    Θa' ; Γ1 ; Δa' ⊢ σ1 ~ σ2 ⊣ Γ2 ; Δa /\
    Θb' ; Γ1 ; Δb' ⊢ σ1 ~ σ2 ⊣ Γ2 ; Δb.
Proof with eauto 6 using merge, era_agree_subst, era_agree_subst_key.
  move=>agr. elim: agr Δa Δb=>{Θ1 Γ1 Γ2 Δ1 Δ2 σ1 σ2}.
  { move=>Θ1 emp Δa Δb mrg. inv mrg.
    exists Θ1. exists Θ1. exists nil. exists nil. repeat split... apply: empty_merge_self... }
  { move=>Θ1 Γ1 Δ1 σ1 σ2 Γ2 Δ2 A s agr ih tyA Δa Δb mrg. inv mrg.
    { have[Θa[Θb[Δa[Δb[mrg1[mrg2[agra agrb]]]]]]]:=ih _ _ H2.
      exists Θa. exists Θb. exists (A.[σ1] :U Δa). exists (A.[σ1] :U Δb).
      repeat split... }
    { have[Θa[Θb[Δa[Δb[mrg1[mrg2[agra agrb]]]]]]]:=ih _ _ H2.
      exists Θa. exists Θb. exists (A.[σ1] :L Δa). exists (_: Δb).
      repeat split... }
    { have[Θa[Θb[Δa[Δb[mrg1[mrg2[agra agrb]]]]]]]:=ih _ _ H2.
      exists Θa. exists Θb. exists (_: Δa). exists (A.[σ1] :L Δb).
      repeat split... } }
  { move=>Θ1 Γ1 Δ1 σ1 σ2 Γ2 Δ2 A s agr ih tyA Δa Δb mrg. inv mrg.
    have[Θa[Θb[Δa[Δb[mrg1[mrg2[agra agrb]]]]]]]:=ih _ _ H2.
    exists Θa. exists Θb. exists (_: Δa). exists (_: Δb).
    repeat split... }
  { move=>Θ1 Γ1 Δ1 σ1 σ2 Γ2 Δ2 n n' A agr ih tyn Δa Δb mrg. inv mrg.
    have[Θa[Θb[Δa[Δb[mrg1[mrg2[agra agrb]]]]]]]:=ih _ _ H2.
    exists Θa. exists Θb. exists Δa. exists Δb.
    repeat split... }
  { move=>Θa Θb Θ1 Γ1 Γ2 σ1 σ2 Δ1 Δ2 Δa Δb n n' A s k1 k2 mrg1 mrg2 agr ih tyn Δa' Δb' mrg'. inv mrg'.
    { have[Θa'[Θb'[Δa'[Δb'[mrg1'[mrg2'[agra agrb]]]]]]]:=ih _ _ H2.
      have[Θc[mrg1a mrg1b]]:=merge_splitL mrg1 mrg1'.
      have[Δc[mrg2a mrg2b]]:=merge_splitL mrg2 mrg2'.
      exists Θc. exists Θb'. exists Δc. exists Δb'.
      repeat split...
      have[Θd[mrg3 _]]:=merge_splitR mrg1 mrg1'.
      have[Δd[mrg4 _]]:=merge_splitR mrg2 mrg2'.
      have e:=merge_pureR mrg3 k1. subst.
      have e:=merge_pureR mrg4 k2. subst.
      apply: era_agree_subst_wk1. apply: k1. apply: k2.
      apply: mrg3. apply: mrg4. apply: agrb. apply: tyn. }
    { have[Θa'[Θb'[Δa'[Δb'[mrg1'[mrg2'[agra agrb]]]]]]]:=ih _ _ H2.
      have[Θc[mrg1a mrg1b]]:=merge_splitL mrg1 mrg1'.
      have[Δc[mrg2a mrg2b]]:=merge_splitL mrg2 mrg2'.
      exists Θc. exists Θb'. exists Δc. exists Δb'.
      repeat split... }
    { have[Θa'[Θb'[Δa'[Δb'[mrg1'[mrg2'[agra agrb]]]]]]]:=ih _ _ H2.
      have[Θc[mrg1a mrg1b]]:=merge_splitR mrg1 mrg1'.
      have[Δc[mrg2a mrg2b]]:=merge_splitR mrg2 mrg2'.
      exists Θa'. exists Θc. exists Δa'. exists Δc.
      repeat split...
      apply: merge_sym...
      apply: merge_sym... } }
  { move=>Θ1 Γ1 Δ1 σ1 σ2 Γ2 Δ2 A B s eq tyB1 tyB2 agr ih Δa Δb mrg. inv mrg.
    have[Θa'[Θb'[Δa'[Δb'[mrg1'[mrg2'[agra agrb]]]]]]]:=ih _ _ (merge_null H2).
    exists Θa'. exists Θb'. exists Δa'. exists Δb'... }
  { move=>Θ1 Γ1 Δ1 σ1 σ2 Γ2 Δ2 A B s eq tyB1 tyB2 agr ih Δa Δb mrg. inv mrg.
    { have[Θa'[Θb'[Δa'[Δb'[mrg1'[mrg2'[agra agrb]]]]]]]:=ih _ _ (merge_left A H2).
      exists Θa'. exists Θb'... exists Δa'. exists Δb'... }
    { have[Θa'[Θb'[Δa'[Δb'[mrg1'[mrg2'[agra agrb]]]]]]]:=ih _ _ (merge_right1 A H2).
      exists Θa'. exists Θb'... exists Δa'. exists Δb'... }
    { have[Θa'[Θb'[Δa'[Δb'[mrg1'[mrg2'[agra agrb]]]]]]]:=ih _ _ (merge_right2 A H2).
      exists Θa'. exists Θb'... exists Δa'. exists Δb'... } }
Qed.

Lemma era_substitution_wf Θ1 Γ1 Γ2 Δ1 Δ2 σ1 σ2 :
  dyn_wf Γ2 Δ2 -> Θ1 ; Γ1 ; Δ1 ⊢ σ1 ~ σ2 ⊣ Γ2 ; Δ2 -> dyn_wf Γ1 Δ1.
Proof with eauto using dyn_wf.
  move=>wf agr. 
  apply: dyn_substitution_wf wf (era_dyn_agree_subst agr).
Qed.

Lemma era_substitution Θ1 Θ2 Θ Γ1 Γ2 m m' A Δ1 Δ2 σ1 σ2 :
  Θ2 ; Γ2 ; Δ2 ⊢ m ~ m' : A -> Θ1 ∘ Θ2 => Θ ->
  Θ1 ; Γ1 ; Δ1 ⊢ σ1 ~ σ2 ⊣ Γ2 ; Δ2 -> Θ ; Γ1 ; Δ1 ⊢ m.[σ1] ~ m'.[σ2] : A.[σ1].
Proof with eauto using era_agree_subst, era_type, key_merge.
  move=>ty. elim: ty Θ1 Θ Γ1 Δ1 σ1 σ2=>{Θ2 Γ2 Δ2 m m' A}. 
  { move=>Θ2 Γ Δ x s A emp wf shs dhs Θ1 Θ Γ1 Δ1 σ1 σ2 mrg agr. asimpl.
    have wf':=era_substitution_wf wf agr.
    apply: era_agree_subst_has... }
  { move=>Θ Γ Δ A B m m' s k1 k2 tym ihm Θ1 Θ0 Γ1 Δ1 σ1 σ2 mrg agr. asimpl.
    have wf:=era_type_wf tym. inv wf.
    have[ka kb]:=era_agree_subst_key agr k2.
    apply: era_lam0... }
  { move=>Θ Γ Δ A B m m' s r k1 k2 tym ihm Θ1 Θ0 Γ1 Δ1 σ1 σ2 mrg agr. asimpl.
    have wf:=era_type_wf tym. inv wf.
    have[ka kb]:=era_agree_subst_key agr k2.
    apply: era_lam1... }
  { move=>Θ Γ Δ A B m m' n s tym ihm tyn Θ1 Θ0 Γ1 Δ1 σ1 σ2 mrg agr. asimpl.
    replace B.[n.[σ1] .: σ1] with B.[up σ1].[n.[σ1]/] by autosubst.
    have{}ihm:=ihm _ _ _ _ _ _ mrg agr.
    apply: era_app0...
    apply: sta_substitution...
    apply: era_sta_agree_subst... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m m' n n' s mrg1 mrg2 tym ihm tyn ihn
           Θ0 Θ3 Γ1 Δ0 σ1 σ2 mrg agr. asimpl.
    replace B.[n.[σ1] .: σ1] with B.[up σ1].[n.[σ1]/] by autosubst.
    have[Θa[Θb[Δa[Δb[mrgx[mrgy[agra agrb]]]]]]]:=era_agree_subst_merge agr mrg2.
    have[Θx[Θy[mrg3[mrg4 mrg5]]]]:=merge_distr mrg mrgx mrg1.
    have{}ihm:=ihm _ _ _ _ _ _ mrg4 agra.
    have{}ihn:=ihn _ _ _ _ _ _ mrg5 agrb.
    apply: era_app1... }
  { move=>Θ Γ Δ A B m n n' t tyS tym tyn ihn Θ1 Θ2 Γ1 Δ1 σ1 σ2 mrg agr. asimpl.
    have{}tyS:=sta_substitution tyS (era_sta_agree_subst agr).
    have{}tym:=sta_substitution tym (era_sta_agree_subst agr).
    have{}ihn:=ihn _ _ _ _ _ _ mrg agr.
    apply: era_pair0...
    asimpl. asimpl in ihn... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m m' n n' t mrg1 mrg2 tyS tym ihm tyn ihn
           Θ0 Θ3 Γ1 Δ0 σ1 σ2 mrg agr. asimpl.
    have[Θa[Θb[Δa[Δb[mrgx[mrgy[agra agrb]]]]]]]:=era_agree_subst_merge agr mrg2.
    have{}ihS:=sta_substitution tyS (era_sta_agree_subst agr).
    have[Θx[Θy[mrg3[mrg4 mrg5]]]]:=merge_distr mrg mrgx mrg1.
    have{}ihm:=ihm _ _ _ _ _ _ mrg4 agra.
    have{}ihn:=ihn _ _ _ _ _ _ mrg5 agrb.
    apply: era_pair1...
    asimpl. asimpl in ihn... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m m' n n' s r t mrg1 mrg2 tyC tym ihm tyn ihn
           Θ0 Θ3 Γ1 Δ0 σ1 σ2 mrg agr. asimpl.
    replace C.[m.[σ1] .: σ1] with C.[up σ1].[m.[σ1]/] by autosubst.
    have[Θa[Θb[Δa[Δb[mrgx[mrgy[agra agrb]]]]]]]:=era_agree_subst_merge agr mrg2.
    have wf:=sta_type_wf tyC. inv wf.
    have wf:=era_type_wf tyn. inv wf. inv H4.
    have{}ihC:=sta_substitution tyC (sta_agree_subst_ty (era_sta_agree_subst agr) H2).
    have[Θx[Θy[mrg3[mrg4 mrg5]]]]:=merge_distr mrg mrgx mrg1.
    have{}ihm:=ihm _ _ _ _ _ _ mrg4 agra.
    have{}ihn:=ihn _ _ _ _ _ _ mrg5
                 (era_agree_subst_ty (era_agree_subst_n agrb H7) H6).
    apply: era_letin0...
    asimpl. asimpl in ihn... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m m' n n' s r1 r2 t mrg1 mrg2 tyC tym ihm tyn ihn
           Θ0 Θ3 Γ1 Δ0 σ1 σ2 mrg agr. asimpl.
    replace C.[m.[σ1] .: σ1] with C.[up σ1].[m.[σ1]/] by autosubst.
    have[Θa[Θb[Δa[Δb[mrgx[mrgy[agra agrb]]]]]]]:=era_agree_subst_merge agr mrg2.
    have wf:=sta_type_wf tyC. inv wf.
    have wf:=era_type_wf tyn. inv wf. inv H4.
    have{}ihC:=sta_substitution tyC (sta_agree_subst_ty (era_sta_agree_subst agr) H2).
    have[Θx[Θy[mrg3[mrg4 mrg5]]]]:=merge_distr mrg mrgx mrg1.
    have{}ihm:=ihm _ _ _ _ _ _ mrg4 agra.
    have{}ihn:=ihn _ _ _ _ _ _ mrg5
                 (era_agree_subst_ty (era_agree_subst_ty agrb H8) H6).
    apply: era_letin1...
    asimpl. asimpl in ihn... }
  { move=>Θ Γ Δ emp wf k Θ1 Θ0 Γ1 Δ1 σ1 σ2 mrg agr. asimpl.
    have wf':=era_substitution_wf wf agr.
    have[ka kb]:=era_agree_subst_key agr k.
    have e:=merge_pureL mrg ka. subst.
    apply: era_ii... }
  { move=>Θ Γ Δ emp wf k Θ1 Θ0 Γ1 Δ1 σ1 σ2 mrg agr. asimpl.
    have wf':=era_substitution_wf wf agr.
    have[ka kb]:=era_agree_subst_key agr k.
    have e:=merge_pureL mrg ka. subst.
    apply: era_tt... }
  { move=>Θ Γ Δ emp wf k Θ1 Θ0 Γ1 Δ1 σ1 σ2 mrg agr. asimpl.
    have wf':=era_substitution_wf wf agr.
    have[ka kb]:=era_agree_subst_key agr k.
    have e:=merge_pureL mrg ka. subst.
    apply: era_ff... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m m' n1 n1' n2 n2' s mrg1 mrg2 tyA tym ihm
           tyn1 ihn1 tyn2 ihn2 Θ0 Θ3 Γ1 Δ0 σ1 σ2 mrg agr. asimpl.
    replace (A.[m.[σ1] .: σ1]) with A.[up σ1].[m.[σ1]/] by autosubst.
    have[Θa[Θb[Δa[Δb[mrgx[mrgy[agra agrb]]]]]]]:=era_agree_subst_merge agr mrg2.
    have wf:=sta_type_wf tyA. inv wf.
    have{}tyA:=sta_substitution tyA (sta_agree_subst_ty (era_sta_agree_subst agr) H2).
    have[Θx[Θy[mrg3[mrg4 mrg5]]]]:=merge_distr mrg mrgx mrg1.
    have{}ihm:=ihm _ _ _ _ _ _ mrg4 agra.
    have{}ihn1:=ihn1 _ _ _ _ _ _ mrg5 agrb.
    have{}ihn2:=ihn2 _ _ _ _ _ _ mrg5 agrb.
    apply: era_ifte...
    asimpl. asimpl in ihn1...
    asimpl. asimpl in ihn2... }
  { move=>Θ Γ Δ m m' A tym ihm Θ1 Θ0 Γ1 Δ1 σ1 σ2 mrg agr. asimpl.
    apply: era_return... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m m' n n' A B s t mrg1 mrg2 tyB tym ihm tyn ihn
           Θ0 Θ3 Γ3 Δ0 σ1 σ2 mrg agr. asimpl.
    have[Θa[Θb[Δa[Δb[mrgx[mrgy[agra agrb]]]]]]]:=era_agree_subst_merge agr mrg2.
    have wf:=era_type_wf tyn. inv wf.
    have[Θx[Θy[mrg3[mrg4 mrg5]]]]:=merge_distr mrg mrgx mrg1.
    have{}tyB:=sta_substitution tyB (era_sta_agree_subst agr).
    have{}ihm:=ihm _ _ _ _ _ _ mrg4 agra.
    have{}ihn:=ihn _ _ _ _ _ _ mrg5 (era_agree_subst_ty agrb H4).
    apply: era_bind...
    asimpl. asimpl in ihn... }
  { move=>Θ Γ Δ r x A js wf k tyA Θ1 Θ0 Γ1 Δ1 σ1 σ2 mrg agr. asimpl.
    have wf':=dyn_substitution_wf wf (era_dyn_agree_subst agr).
    have[k1 k2]:=era_agree_subst_key agr k.
    have e:=merge_pureL mrg k1. subst.
    rewrite (sta_agree_subst_size (era_sta_agree_subst agr)).
    apply: era_cvar... }
  { move=>Θ Γ Δ m m' A tym ihm Θ1 Θ0 Γ1 Δ1 σ1 σ2 mrg agr. asimpl.
    have wf:=era_type_wf tym. inv wf.
    have{}ihm:=ihm _ _ _ _ _ _ mrg (era_agree_subst_ty agr H4).
    apply: era_fork... }
  { move=>Θ Γ Δ r1 r2 A B m m' xor tym ihm Θ1 Θ0 Γ1 Δ1 σ1 σ2 mrg agr. asimpl.
    apply: era_recv0... }
  { move=>Θ Γ Δ r1 r2 A B m m' xor tym ihm Θ1 Θ0 Γ1 Δ1 σ1 σ2 mrg agr. asimpl.
    apply: era_recv1... }
  { move=>Θ Γ Δ r1 r2 A B m m' xor tym ihm Θ1 Θ0 Γ1 Δ1 σ1 σ2 mrg agr. asimpl.
    apply: era_send0... }
  { move=>Θ Γ Δ r1 r2 A B m m' xor tym ihm Θ1 Θ0 Γ1 Δ1 σ1 σ2 mrg agr. asimpl.
    apply: era_send1... }
  { move=>Θ Γ Δ m m' tym ihm Θ1 Θ0 Γ1 Δ1 σ1 σ2 mrg agr. asimpl.
    apply: era_wait... }
  { move=>Θ Γ Δ m m' tym ihm Θ1 Θ0 Γ1 Δ1 σ1 σ2 mrg agr. asimpl.
    apply: era_close... }
  { move=>Θ Γ Δ A B m m' s eq tym ihm tyB Θ1 Θ0 Γ1 Δ1 σ1 σ2 mrg agr.
    apply: era_conv.
    apply: sta_conv_subst...
    apply: ihm...
    have:=sta_substitution tyB (era_sta_agree_subst agr).
    asimpl... }
Qed.

Lemma era_subst0 Θ Γ Δ m m' n A B :
  Θ ; (A :: Γ) ; _: Δ ⊢ m ~ m' : B -> Γ ⊢ n : A -> Θ ; Γ ; Δ ⊢ m.[n/] ~ m'.[Box/] : B.[n/].
Proof with eauto using era_agree_subst_refl.
  move=>tym tyn.
  have wf:=era_type_wf tym. inv wf.
  have[Θ0[emp mrg]]:=era_type_empty tym.
  apply: era_substitution...
  apply: era_agree_subst_wk0...
  by asimpl.
Qed.

Lemma era_subst1 Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m m' n n' A B s :
  Θ2 ▷ s -> Θ1 ∘ Θ2 => Θ ->
  Δ2 ▷ s -> Δ1 ∘ Δ2 => Δ ->
  Θ1 ; (A :: Γ) ; A .{s} Δ1 ⊢ m ~ m' : B ->
  Θ2 ; Γ ; Δ2 ⊢ n ~ n' : A ->
  Θ ; Γ ; Δ ⊢ m.[n/] ~ m'.[n'/] : B.[n/].
Proof with eauto using era_agree_subst_refl.
  move=>k1 mrg1 k2 mrg2 tym tyn.
  have wf:=era_type_wf tym. inv wf.
  have[Θ0[emp mrg]]:=era_type_empty tyn.
  apply: era_substitution...
  apply: merge_sym...
  apply: era_agree_subst_wk1.
  apply: k1. apply: k2.
  apply: mrg.
  apply: mrg2.
  apply: era_agree_subst_refl...
  by asimpl.
Qed.

Lemma era_esubst0 Θ Γ Δ m m' n n' v A B B' :
  m' = m.[v/] ->
  n' = n.[Box/] ->
  B' = B.[v/] ->
  Θ ; (A :: Γ) ; _: Δ ⊢ m ~ n : B ->
  Γ ⊢ v : A ->
  Θ ; Γ ; Δ ⊢ m' ~ n' : B'.
Proof.
  move=>*; subst. apply: era_subst0; eauto.
Qed.

Lemma era_esubst1 Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m m' n n' v v' A B B' s :
  m' = m.[v/] ->
  n' = n.[v'/] ->
  B' = B.[v/] ->
  Θ2 ▷ s -> Θ1 ∘ Θ2 => Θ ->
  Δ2 ▷ s -> Δ1 ∘ Δ2 => Δ ->
  Θ1 ; (A :: Γ) ; A .{s} Δ1 ⊢ m ~ n : B ->
  Θ2 ; Γ ; Δ2 ⊢ v ~ v' : A ->
  Θ ; Γ ; Δ ⊢ m' ~ n' : B'.
Proof.
  move=>e1 e2 e3 k1 mrg1 k2 mrg2 tym tyv. subst.
  apply: era_subst1.
  apply: k1. apply: mrg1.
  apply: k2. apply: mrg2.
  apply: tym. apply: tyv.
Qed.

Lemma era_ctx_conv0 Θ Γ Δ m m' A B C s :
  B ≃ A ->
  Γ ⊢ B : Sort s ->
  Θ ; (A :: Γ) ; _: Δ ⊢ m ~ m' : C ->
  Θ ; (B :: Γ) ; _: Δ ⊢ m ~ m' : C.
Proof with eauto using dyn_wf, era_agree_subst_refl.
  move=>eq tyB tym.
  have wf:=era_type_wf tym. inv wf.
  have[Θ0[emp mrg]]:=era_type_empty tym.
  have:Θ ; (B :: Γ) ; _: Δ ⊢ m.[ids] ~ m'.[ids] : C.[ids].
  apply: era_substitution...
  apply: era_agree_subst_conv0...
  apply: sta_eweaken...
  all: asimpl...
Qed.

Lemma era_ctx_conv1 Θ Γ Δ m m' A B C s :
  B ≃ A ->
  Γ ⊢ B : Sort s ->
  Θ ; (A :: Γ) ; A .{s} Δ ⊢ m ~ m' : C ->
  Θ ; (B :: Γ) ; B .{s} Δ ⊢ m ~ m' : C.
Proof with eauto using dyn_wf, era_agree_subst_refl.
  move=>eq tyB tym.
  have wf:=era_type_wf tym. inv wf.
  have[Θ0[emp mrg]]:=era_type_empty tym.
  have:Θ ; (B :: Γ) ; B .{s} Δ ⊢ m.[ids] ~ m'.[ids] : C.[ids].
  apply: era_substitution...
  apply: era_agree_subst_conv1...
  apply: sta_eweaken...
  all: asimpl...
Qed.
