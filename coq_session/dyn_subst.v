From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_subst sta_inv dyn_valid dyn_weak.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "Θ1 ; Γ1 ; Δ1 ⊢ σ ⊣ Γ2 ; Δ2"
  (at level 50, Γ1, Δ1, σ, Γ2, Δ2 at next level).
Inductive dyn_agree_subst :
  dyn_ctx -> sta_ctx -> dyn_ctx -> (var -> term) -> sta_ctx -> dyn_ctx -> Prop :=
| dyn_agree_subst_nil Θ1 :
  dyn_empty Θ1 ->
  Θ1 ; nil ; nil ⊢ ids ⊣ nil ; nil
| dyn_agree_subst_ty Θ1 Γ1 Δ1 σ Γ2 Δ2 A s :
  Θ1 ; Γ1 ; Δ1 ⊢ σ ⊣ Γ2 ; Δ2 ->
  Γ2 ⊢ A : Sort s ->
  Θ1 ; (A.[σ] :: Γ1) ; (A.[σ] .{s} Δ1) ⊢ up σ ⊣ (A :: Γ2) ; (A .{s} Δ2)
| dyn_agree_subst_n Θ1 Γ1 Δ1 σ Γ2 Δ2 A s :
  Θ1 ; Γ1 ; Δ1 ⊢ σ ⊣ Γ2 ; Δ2 ->
  Γ2 ⊢ A : Sort s ->
  Θ1 ; (A.[σ] :: Γ1) ; (_: Δ1) ⊢ up σ ⊣ (A :: Γ2) ; (_: Δ2)
| dyn_agree_subst_wk0 Θ1 Γ1 Δ1 σ Γ2 Δ2 n A :
  Θ1 ; Γ1 ; Δ1 ⊢ σ ⊣ Γ2 ; Δ2 ->
  Γ1 ⊢ n : A.[σ] ->
  Θ1 ; Γ1 ; Δ1 ⊢ n .: σ ⊣ (A :: Γ2) ; (_: Δ2)
| dyn_agree_subst_wk1 Θa Θb Θ1 Γ1 Γ2 σ Δ1 Δ2 Δa Δb n A s :
  Θb ▷ s ->
  Δb ▷ s ->
  Θa ∘ Θb => Θ1 ->
  Δa ∘ Δb => Δ1 ->
  Θa ; Γ1 ; Δa ⊢ σ ⊣ Γ2 ; Δ2 ->
  Θb ; Γ1 ; Δb ⊢ n : A.[σ] ->
  Θ1 ; Γ1 ; Δ1 ⊢ n .: σ ⊣ (A :: Γ2) ; (A .{s} Δ2)
| dyn_agree_subst_conv0 Θ1 Γ1 Δ1 σ Γ2 Δ2 A B s :
  A === B ->
  Γ1 ⊢ B.[ren (+1)].[σ] : Sort s ->
  Γ2 ⊢ B : Sort s ->
  Θ1 ; Γ1 ; Δ1 ⊢ σ ⊣ (A :: Γ2) ; (_: Δ2) ->
  Θ1 ; Γ1 ; Δ1 ⊢ σ ⊣ (B :: Γ2) ; (_: Δ2)
| dyn_agree_subst_conv1 Θ1 Γ1 Δ1 σ Γ2 Δ2 A B s :
  A === B ->
  Γ1 ⊢ B.[ren (+1)].[σ] : Sort s ->
  Γ2 ⊢ B : Sort s ->
  Θ1 ; Γ1 ; Δ1 ⊢ σ ⊣ (A :: Γ2) ; (A .{s} Δ2) ->
  Θ1 ; Γ1 ; Δ1 ⊢ σ ⊣ (B :: Γ2) ; (B .{s} Δ2)
where "Θ1 ; Γ1 ; Δ1 ⊢ σ ⊣ Γ2 ; Δ2" := (dyn_agree_subst Θ1 Γ1 Δ1 σ Γ2 Δ2).

Lemma dyn_agree_subst_key Θ1 Γ1 Γ2 Δ1 Δ2 σ s :
  Θ1 ; Γ1 ; Δ1 ⊢ σ ⊣ Γ2 ; Δ2 -> Δ2 ▷ s -> Θ1 ▷ s /\ Δ1 ▷ s.
Proof with eauto using key, key_empty, key_merge, key_impure.
  move=>agr. elim: agr s=>{Θ1 Γ1 Γ2 Δ1 Δ2 σ}...
  { move=>Θ1 Γ1 Δ1 σ Γ2 Δ2 A s agr ih tyA r k. inv k... have[]:=ih _ H3... }
  { move=>Θ1 Γ1 Δ1 σ Γ2 Δ2 A s agr ih tyA r k. inv k... have[]:=ih _ H0... }
  { move=>Θ1 Γ1 Δ1 σ Γ2 Δ2 n A agr ih tyn s k. inv k... }
  { move=>Θa Θb Θ1 Γ1 Γ2 σ Δ1 Δ2 Δa Δb n A s k1 k2 mrg1 mrg2 agr ih tyn r k3. inv k3...
    have[]:=ih _ H3... }
  { move=>Θ1 Γ1 Δ1 σ Γ2 Δ2 A B s eq tyB1 tyB2 agr ih r k. inv k... }
Qed.

Lemma dyn_sta_agree_subst Θ1 Γ1 Γ2 Δ1 Δ2 σ :
  Θ1 ; Γ1 ; Δ1 ⊢ σ ⊣ Γ2 ; Δ2 -> Γ1 ⊢ σ ⊣ Γ2.
Proof with eauto using sta_agree_subst. elim... Qed.

Lemma dyn_agree_subst_refl Θ Γ Δ :
  dyn_empty Θ -> dyn_wf Γ Δ -> Θ ; Γ ; Δ ⊢ ids ⊣ Γ ; Δ.
Proof with eauto using dyn_agree_subst.
  elim: Γ Θ Δ.
  { move=>Θ Δ emp wf. inv wf... }
  { move=>A Γ ih Θ Δ emp wf. inv wf.
    { have agr:=ih Θ _ emp H1.
      have:Θ ; (A.[ids] :: Γ); A.[ids] .{s} Δ0 ⊢ up ids ⊣ (A :: Γ); A .{s} Δ0...
      by asimpl. }
    { have agr:=ih Θ _ emp H1.
      have:Θ ; (A.[ids] :: Γ); _: Δ0 ⊢ up ids ⊣ (A :: Γ); _: Δ0...
      by asimpl. } }
Qed.
#[global] Hint Resolve dyn_agree_subst_refl.

Lemma dyn_type_empty Θ1 Γ Δ m A :
  Θ1 ; Γ ; Δ ⊢ m : A -> exists Θ, dyn_empty Θ /\ Θ ∘ Θ1 => Θ1.
Proof with eauto using dyn_type, key_empty.
  move=>ty. elim: ty=>{Θ1 Γ Δ m A}...
  { move=>Θ Γ Δ x s A emp wf shs dhs. exists Θ. split... apply: empty_merge_self... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n s mrg1 mrg2 tym[Θm[empm mrgm]]tyn[Θn[empn mrgn]].
    have[Θx[Θy[mrgx[mrgy mrgz]]]]:=merge_distr mrg1 mrgm mrgn.
    have e:=merge_inj mrg1 mrgz. subst.
    exists Θx. split... apply: merge_empty... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n t mrg1 mrg2 tyS
           tym[Θm[empm mrgm]]tyn[Θn[empn mrgn]].
    have[Θx[Θy[mrgx[mrgy mrgz]]]]:=merge_distr mrg1 mrgm mrgn.
    have e:=merge_inj mrg1 mrgz. subst.
    exists Θx. split... apply: merge_empty... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r t mrg1 mrg2 tyC
           tym[Θm[empm mrgm]]tyn[Θn[empn mrgn]].
    have[Θx[Θy[mrgx[mrgy mrgz]]]]:=merge_distr mrg1 mrgm mrgn.
    have e:=merge_inj mrg1 mrgz. subst.
    exists Θx. split... apply: merge_empty... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r1 r2 t mrg1 mrg2 tyC
           tym[Θm[empm mrgm]]tyn[Θn[empn mrgn]].
    have[Θx[Θy[mrgx[mrgy mrgz]]]]:=merge_distr mrg1 mrgm mrgn.
    have e:=merge_inj mrg1 mrgz. subst.
    exists Θx. split... apply: merge_empty... }
  { move=>Θ Γ Δ emp wf k. exists Θ. split... apply: empty_merge_self... }
  { move=>Θ Γ Δ emp wf k. exists Θ. split... apply: empty_merge_self... }
  { move=>Θ Γ Δ emp wf k. exists Θ. split... apply: empty_merge_self... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m n1 n2 s mrg1 mrg2 tyA
     tym[Θm[empm mrgm]]tyn1[Θn1[empn1 mrgn1]]tyn2[Θn2[empn2 mrgn2]].
    have[Θx[Θy[mrgx[mrgy mrgz]]]]:=merge_distr mrg1 mrgm mrgn1.
    have e:=merge_inj mrg1 mrgz. subst.
    exists Θx. split... apply: merge_empty... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m n A B s t mrg1 mrg2 tyB
           tym[Θm[empm mrgm]]tyn[Θn[empn mrgn]].
    have[Θx[Θy[mrgx[mrgy mrgz]]]]:=merge_distr mrg1 mrgm mrgn.
    have e:=merge_inj mrg1 mrgz. subst.
    exists Θx. split... apply: merge_empty... }
  { move=>Θ Γ Δ r x A js wf k tyA. apply: just_empty... }
Qed.

Lemma dyn_agree_subst_has Θ1 Θ2 Θ Γ1 Γ2 σ Δ1 Δ2 x s A :
  Θ1 ; Γ1 ; Δ1 ⊢ σ ⊣ Γ2 ; Δ2 -> dyn_empty Θ2 -> Θ1 ∘ Θ2 => Θ ->
  dyn_wf Γ1 Δ1 -> dyn_has Δ2 x s A -> Θ ; Γ1 ; Δ1 ⊢ (σ x) : A.[σ].
Proof with eauto using dyn_agree_subst, dyn_agree_subst_key.
  move=>agr. elim: agr x Θ2 Θ s A=>{Θ1 Γ1 Γ2 σ Δ1 Δ2}...
  { move=>Θ1 emp1 x Θ2 Θ s A emp2 mrg wf hs. inv hs. }
  { move=>Θ1 Γ1 Δ1 σ Γ2 Δ2 A s agr ih tyA x Θ2 Θ r B emp2 mrg wf hs.
    inv wf. inv hs; asimpl.
    { replace A.[σ >> ren (+1)] with A.[σ].[ren (+1)] by autosubst.
      have[k1 k2]:=dyn_agree_subst_key agr H7.
      apply: dyn_var.
      have e:=merge_pureL mrg k1. subst...
      constructor...
      constructor...
      constructor... }
    { replace A0.[σ >> ren (+1)] with A0.[σ].[ren (+1)] by autosubst.
      apply: dyn_eweakenU... } }
  { move=>Θ1 Γ1 Δ1 σ Γ2 Δ2 A s agr ih tyA x Θ2 Θ t B emp mrg wf hs.
    inv wf. inv hs; asimpl...
    replace A0.[σ >> ren (+1)] with A0.[σ].[ren (+1)] by autosubst.
    apply: dyn_eweakenN... }
  { move=>Θ1 Γ1 Δ1 σ Γ2 Δ2 n A agr ih tyn x Θ2 Θ s B emp mrg wf hs. inv hs; asimpl... }
  { move=>Θa Θb Θ1 Γ1 Γ2 σ Δ1 Δ2 Δa Δb n A s k1 k2 mrg1 mrg2 agr ih tyn x Θ2 Θ t B emp mrg wf hs.
    inv hs; asimpl.
    { have[k3 k4]:=dyn_agree_subst_key agr H5.
      have e:=merge_pureL mrg1 k3. subst.
      have e:=merge_pureL mrg2 k4. subst.
      have e:=merge_emptyR mrg emp. subst... }
    { have e:=merge_pureR mrg1 k1. subst.
      have e:=merge_pureR mrg2 k2. subst.
      apply: ih... } }
  { move=>Θ1 Γ1 Δ1 σ Γ2 Δ2 A B s eq tyB1 tyB2 agr ih x Θ2 Θ t C emp mrg wf hs. inv hs.
    { apply: dyn_conv.
      apply: sta_conv_subst.
      apply: sta_conv_subst...
      apply: ih...
      constructor...
      exact: tyB1. }
    { apply: ih...
      constructor... } }
Qed.

Lemma dyn_agree_subst_merge Θ1 Γ1 Γ2 Δ1 Δ2 Δa Δb σ :
  Θ1 ; Γ1 ; Δ1 ⊢ σ ⊣ Γ2 ; Δ2 -> Δa ∘ Δb => Δ2 ->
  exists Θa' Θb' Δa' Δb',
    Θa' ∘ Θb' => Θ1 /\
    Δa' ∘ Δb' => Δ1 /\
    Θa' ; Γ1 ; Δa' ⊢ σ ⊣ Γ2 ; Δa /\
    Θb' ; Γ1 ; Δb' ⊢ σ ⊣ Γ2 ; Δb.
Proof with eauto 6 using merge, dyn_agree_subst, dyn_agree_subst_key.
  move=>agr. elim: agr Δa Δb=>{Θ1 Γ1 Γ2 Δ1 Δ2 σ}.
  { move=>Θ1 emp Δa Δb mrg. inv mrg.
    exists Θ1. exists Θ1. exists nil. exists nil. repeat split... apply: empty_merge_self... }
  { move=>Θ1 Γ1 Δ1 σ Γ2 Δ2 A s agr ih tyA Δa Δb mrg. inv mrg.
    { have[Θa[Θb[Δa[Δb[mrg1[mrg2[agra agrb]]]]]]]:=ih _ _ H2.
      exists Θa. exists Θb. exists (A.[σ] :U Δa). exists (A.[σ] :U Δb).
      repeat split... }
    { have[Θa[Θb[Δa[Δb[mrg1[mrg2[agra agrb]]]]]]]:=ih _ _ H2.
      exists Θa. exists Θb. exists (A.[σ] :L Δa). exists (_: Δb).
      repeat split... }
    { have[Θa[Θb[Δa[Δb[mrg1[mrg2[agra agrb]]]]]]]:=ih _ _ H2.
      exists Θa. exists Θb. exists (_: Δa). exists (A.[σ] :L Δb).
      repeat split... } }
  { move=>Θ1 Γ1 Δ1 σ Γ2 Δ2 A s agr ih tyA Δa Δb mrg. inv mrg.
    have[Θa[Θb[Δa[Δb[mrg1[mrg2[agra agrb]]]]]]]:=ih _ _ H2.
    exists Θa. exists Θb. exists (_: Δa). exists (_: Δb).
    repeat split... }
  { move=>Θ1 Γ1 Δ1 σ Γ2 Δ2 A s agr ih tyA Δa Δb mrg. inv mrg.
    have[Θa[Θb[Δa[Δb[mrg1[mrg2[agra agrb]]]]]]]:=ih _ _ H2.
    exists Θa. exists Θb. exists Δa. exists Δb.
    repeat split... }
  { move=>Θa Θb Θ1 Γ1 Γ2 σ Δ1 Δ2 Δa Δb n A s k1 k2 mrg1 mrg2 agr ih tyn Δa' Δb' mrg'. inv mrg'.
    { have[Θa'[Θb'[Δa'[Δb'[mrg1'[mrg2'[agra agrb]]]]]]]:=ih _ _ H2.
      have[Θc[mrg1a mrg1b]]:=merge_splitL mrg1 mrg1'.
      have[Δc[mrg2a mrg2b]]:=merge_splitL mrg2 mrg2'.
      exists Θc. exists Θb'. exists Δc. exists Δb'.
      repeat split...
      have[Θd[mrg3 _]]:=merge_splitR mrg1 mrg1'.
      have[Δd[mrg4 _]]:=merge_splitR mrg2 mrg2'.
      have e:=merge_pureR mrg3 k1. subst.
      have e:=merge_pureR mrg4 k2. subst.
      apply: dyn_agree_subst_wk1. apply: k1. apply: k2.
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
  { move=>Θ1 Γ1 Δ1 σ Γ2 Δ2 A B s eq tyB1 tyB2 agr ih Δa Δb mrg. inv mrg.
    have[Θa'[Θb'[Δa'[Δb'[mrg1'[mrg2'[agra agrb]]]]]]]:=ih _ _ (merge_null H2).
    exists Θa'. exists Θb'. exists Δa'. exists Δb'... }
  { move=>Θ1 Γ1 Δ1 σ Γ2 Δ2 A B s eq tyB1 tyB2 agr ih Δa Δb mrg. inv mrg.
    { have[Θa'[Θb'[Δa'[Δb'[mrg1'[mrg2'[agra agrb]]]]]]]:=ih _ _ (merge_left A H2).
      exists Θa'. exists Θb'... exists Δa'. exists Δb'... }
    { have[Θa'[Θb'[Δa'[Δb'[mrg1'[mrg2'[agra agrb]]]]]]]:=ih _ _ (merge_right1 A H2).
      exists Θa'. exists Θb'... exists Δa'. exists Δb'... }
    { have[Θa'[Θb'[Δa'[Δb'[mrg1'[mrg2'[agra agrb]]]]]]]:=ih _ _ (merge_right2 A H2).
      exists Θa'. exists Θb'... exists Δa'. exists Δb'... } }
Qed.

Lemma dyn_agree_subst_wf_nil Θ1 Γ1 Δ1 σ : Θ1 ; Γ1; Δ1 ⊢ σ ⊣ [::]; [::] → dyn_wf Γ1 Δ1.
Proof with eauto using dyn_wf.
  move e1:(nil)=>Γ2.
  move e2:(nil)=>Δ2 agr.
  elim: agr e1 e2=>//{Γ1 Γ2 Δ1 Δ2 σ}...
Qed.

Lemma dyn_agree_subst_wf_ty Θ1 Γ1 Γ2 Δ1 Δ2 A s σ :
  Θ1 ; Γ1; Δ1 ⊢ σ ⊣ (A :: Γ2); A .{s} Δ2 -> dyn_wf Γ2 Δ2 ->
  (∀ Θ1 Γ1 Δ1 σ, Θ1 ; Γ1; Δ1 ⊢ σ ⊣ Γ2; Δ2 → dyn_wf Γ1 Δ1) ->
  dyn_wf Γ1 Δ1.
Proof with eauto using dyn_wf.
  move e1:(A :: Γ2)=>Γ0.
  move e2:(A .{s} Δ2)=>Δ0 agr.
  elim: agr A Γ2 Δ2 s e1 e2=>//{Θ1 Γ0 Δ0 Γ1 Δ1 σ}...
  { move=>Θ1 Γ1 Δ1 σ Γ2 Δ2 A s agr _ tyA A0 Γ0 Δ0 s0[e1 e2][_ e3 e4]wf h; subst.
    apply: dyn_wf_ty...
    replace (Sort s) with (Sort s).[σ] by eauto.
    apply: sta_substitution...
    apply: dyn_sta_agree_subst... }
  { move=>Θa Θb Θ1 Γ1 Γ2 σ Δ1 Δ2 Δa Δb n A s k1 k2 mrg1 mrg2 agr _ tyn A0 Γ0 Δ0 s0
      [e1 e2][_ e3 e4]wf h; subst.
    apply: dyn_wf_merge... }
  { move=>Θ1 Γ1 Δ1 σ Γ2 Δ2 A B s eq tyB1 tyB2 agr ih A0 Γ0 Δ0 s0
      [e1 e2][_ e3 e4]wf h; subst... }
Qed.

Lemma dyn_agree_subst_wf_n Θ1 Γ1 Γ2 Δ1 Δ2 A σ :
  Θ1 ; Γ1; Δ1 ⊢ σ ⊣ (A :: Γ2); _: Δ2 -> dyn_wf Γ2 Δ2 ->
  (∀ Θ1 Γ1 Δ1 σ, Θ1 ; Γ1; Δ1 ⊢ σ ⊣ Γ2; Δ2 → dyn_wf Γ1 Δ1) ->
  dyn_wf Γ1 Δ1.
Proof with eauto using dyn_wf.
  move e1:(A :: Γ2)=>Γ0.
  move e2:(_: Δ2)=>Δ0 agr.
  elim: agr A Γ2 Δ2 e1 e2=>//{Θ1 Γ0 Δ0 Γ1 Δ1 σ}...
  { move=>Θ1 Γ1 Δ1 σ Γ2 Δ2 A s agr _ tyA A0 Γ0 Δ0[e1 e2][e3]wf h; subst.
    apply: dyn_wf_n...
    have:=sta_substitution tyA (dyn_sta_agree_subst agr).
    asimpl... }
  { move=>Θ1 Γ1 Δ1 σ Γ2 Δ2 n A agr ih tyn A0 Γ0 Δ0[e1 e2][e3]wf h; subst... }
  { move=>Θ1 Γ1 Δ1 σ Γ2 Δ2 A B s eq tyB1 tyB2 agr ih A0 Γ0 Δ0
      [e1 e2][e3]wf h; subst... }
Qed.

Lemma dyn_substitution Θ1 Θ2 Θ Γ1 Γ2 m A Δ1 Δ2 σ :
  Θ2 ; Γ2 ; Δ2 ⊢ m : A -> Θ1 ∘ Θ2 => Θ ->
  Θ1 ; Γ1 ; Δ1 ⊢ σ ⊣ Γ2 ; Δ2 -> Θ ; Γ1 ; Δ1 ⊢ m.[σ] : A.[σ].
Proof with eauto using dyn_agree_subst, dyn_type, key_merge.
  move=>ty. move:Θ2 Γ2 Δ2 m A ty Θ1 Θ Γ1 Δ1 σ.
  apply:(@dyn_type_mut _
           (fun Γ2 Δ2 wf => forall Θ1 Γ1 Δ1 σ, Θ1 ; Γ1 ; Δ1 ⊢ σ ⊣ Γ2 ; Δ2 -> dyn_wf Γ1 Δ1)).
  { move=>Θ2 Γ Δ x s A emp wf ih shs dhs Θ1 Θ Γ1 Δ1 σ mrg agr. asimpl.
    apply: dyn_agree_subst_has... }
  { move=>Θ Γ Δ A B m s k1 k2 tym ihm Θ1 Θ0 Γ1 Δ1 σ mrg agr. asimpl.
    have wf:=dyn_type_wf tym. inv wf.
    have[ka kb]:=dyn_agree_subst_key agr k2.
    apply: dyn_lam0... }
  { move=>Θ Γ Δ A B m s r k1 k2 tym ihm Θ1 Θ0 Γ1 Δ1 σ mrg agr. asimpl.
    have wf:=dyn_type_wf tym. inv wf.
    have[ka kb]:=dyn_agree_subst_key agr k2.
    apply: dyn_lam1... }
  { move=>Θ Γ Δ A B m n s tym ihm tyn Θ1 Θ0 Γ1 Δ1 σ mrg agr. asimpl.
    replace B.[n.[σ] .: σ] with B.[up σ].[n.[σ]/] by autosubst.
    have{}ihm:=ihm _ _ _ _ _ mrg agr.
    apply: dyn_app0...
    apply: sta_substitution...
    apply: dyn_sta_agree_subst... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n s mrg1 mrg2 tym ihm tyn ihn
           Θ0 Θ3 Γ1 Δ0 σ mrg agr. asimpl.
    replace B.[n.[σ] .: σ] with B.[up σ].[n.[σ]/] by autosubst.
    have[Θa[Θb[Δa[Δb[mrgx[mrgy[agra agrb]]]]]]]:=dyn_agree_subst_merge agr mrg2.
    have[Θx[Θy[mrg3[mrg4 mrg5]]]]:=merge_distr mrg mrgx mrg1.
    have{}ihm:=ihm _ _ _ _ _ mrg4 agra.
    have{}ihn:=ihn _ _ _ _ _ mrg5 agrb.
    apply: dyn_app1... }
  { move=>Θ Γ Δ A B m n t tyS tym tyn ihn Θ1 Θ2 Γ1 Δ1 σ mrg agr. asimpl.
    have{}tyS:=sta_substitution tyS (dyn_sta_agree_subst agr).
    have{}tym:=sta_substitution tym (dyn_sta_agree_subst agr).
    have{}ihn:=ihn _ _ _ _ _ mrg agr.
    apply: dyn_pair0...
    asimpl. asimpl in ihn... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n t mrg1 mrg2 tyS tym ihm tyn ihn
           Θ0 Θ3 Γ1 Δ0 σ mrg agr. asimpl.
    have[Θa[Θb[Δa[Δb[mrgx[mrgy[agra agrb]]]]]]]:=dyn_agree_subst_merge agr mrg2.
    have{}ihS:=sta_substitution tyS (dyn_sta_agree_subst agr).
    have[Θx[Θy[mrg3[mrg4 mrg5]]]]:=merge_distr mrg mrgx mrg1.
    have{}ihm:=ihm _ _ _ _ _ mrg4 agra.
    have{}ihn:=ihn _ _ _ _ _ mrg5 agrb.
    apply: dyn_pair1...
    asimpl. asimpl in ihn... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r t mrg1 mrg2 tyC tym ihm tyn ihn
           Θ0 Θ3 Γ1 Δ0 σ mrg agr. asimpl.
    replace C.[m.[σ] .: σ] with C.[up σ].[m.[σ]/] by autosubst.
    have[Θa[Θb[Δa[Δb[mrgx[mrgy[agra agrb]]]]]]]:=dyn_agree_subst_merge agr mrg2.
    have wf:=sta_type_wf tyC. inv wf.
    have wf:=dyn_type_wf tyn. inv wf. inv H4.
    have{}ihC:=sta_substitution tyC (sta_agree_subst_ty (dyn_sta_agree_subst agr) H2).
    have[Θx[Θy[mrg3[mrg4 mrg5]]]]:=merge_distr mrg mrgx mrg1.
    have{}ihm:=ihm _ _ _ _ _ mrg4 agra.
    have{}ihn:=ihn _ _ _ _ _ mrg5
                 (dyn_agree_subst_ty (dyn_agree_subst_n agrb H7) H6).
    apply: dyn_letin0...
    asimpl. asimpl in ihn... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r1 r2 t mrg1 mrg2 tyC tym ihm tyn ihn
           Θ0 Θ3 Γ1 Δ0 σ mrg agr. asimpl.
    replace C.[m.[σ] .: σ] with C.[up σ].[m.[σ]/] by autosubst.
    have[Θa[Θb[Δa[Δb[mrgx[mrgy[agra agrb]]]]]]]:=dyn_agree_subst_merge agr mrg2.
    have wf:=sta_type_wf tyC. inv wf.
    have wf:=dyn_type_wf tyn. inv wf. inv H4.
    have{}ihC:=sta_substitution tyC (sta_agree_subst_ty (dyn_sta_agree_subst agr) H2).
    have[Θx[Θy[mrg3[mrg4 mrg5]]]]:=merge_distr mrg mrgx mrg1.
    have{}ihm:=ihm _ _ _ _ _ mrg4 agra.
    have{}ihn:=ihn _ _ _ _ _ mrg5
                 (dyn_agree_subst_ty (dyn_agree_subst_ty agrb H8) H6).
    apply: dyn_letin1...
    asimpl. asimpl in ihn... }
  { move=>Θ Γ Δ A m k1 k2 tym ihm Θ1 Θ0 Γ1 Δ1 σ mrg agr. asimpl.
    have wf:=dyn_type_wf tym. inv wf.
    have[ka kb]:=dyn_agree_subst_key agr k2.
    have agr':=dyn_agree_subst_ty agr H4.
    have{}ihm:=ihm _ _ _ _ _ mrg agr'.
    apply: dyn_fix...
    asimpl. asimpl in ihm... }
  { move=>Θ Γ Δ emp wf ih k Θ1 Θ0 Γ1 Δ1 σ mrg agr. asimpl.
    have[ka kb]:=dyn_agree_subst_key agr k.
    have e:=merge_pureL mrg ka. subst.
    apply: dyn_ii... }
  { move=>Θ Γ Δ emp wf ih k Θ1 Θ0 Γ1 Δ1 σ mrg agr. asimpl.
    have[ka kb]:=dyn_agree_subst_key agr k.
    have e:=merge_pureL mrg ka. subst.
    apply: dyn_tt... }
  { move=>Θ Γ Δ emp wf ih k Θ1 Θ0 Γ1 Δ1 σ mrg agr. asimpl.
    have[ka kb]:=dyn_agree_subst_key agr k.
    have e:=merge_pureL mrg ka. subst.
    apply: dyn_ff... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m n1 n2 s mrg1 mrg2 tyA tym ihm
           tyn1 ihn1 tyn2 ihn2 Θ0 Θ3 Γ1 Δ0 σ mrg agr. asimpl.
    replace (A.[m.[σ] .: σ]) with A.[up σ].[m.[σ]/] by autosubst.
    have[Θa[Θb[Δa[Δb[mrgx[mrgy[agra agrb]]]]]]]:=dyn_agree_subst_merge agr mrg2.
    have wf:=sta_type_wf tyA. inv wf.
    have{}tyA:=sta_substitution tyA (sta_agree_subst_ty (dyn_sta_agree_subst agr) H2).
    have[Θx[Θy[mrg3[mrg4 mrg5]]]]:=merge_distr mrg mrgx mrg1.
    have{}ihm:=ihm _ _ _ _ _ mrg4 agra.
    have{}ihn1:=ihn1 _ _ _ _ _ mrg5 agrb.
    have{}ihn2:=ihn2 _ _ _ _ _ mrg5 agrb.
    apply: dyn_ifte...
    asimpl. asimpl in ihn1...
    asimpl. asimpl in ihn2... }
  { move=>Θ Γ Δ m A tym ihm Θ1 Θ0 Γ1 Δ1 σ mrg agr. asimpl.
    apply: dyn_return... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m n A B s t mrg1 mrg2 tyB tym ihm tyn ihn
           Θ0 Θ3 Γ3 Δ0 σ mrg agr. asimpl.
    have[Θa[Θb[Δa[Δb[mrgx[mrgy[agra agrb]]]]]]]:=dyn_agree_subst_merge agr mrg2.
    have wf:=dyn_type_wf tyn. inv wf.
    have[Θx[Θy[mrg3[mrg4 mrg5]]]]:=merge_distr mrg mrgx mrg1.
    have{}tyB:=sta_substitution tyB (dyn_sta_agree_subst agr).
    have{}ihm:=ihm _ _ _ _ _ mrg4 agra.
    have{}ihn:=ihn _ _ _ _ _ mrg5 (dyn_agree_subst_ty agrb H4).
    apply: dyn_bind...
    asimpl. asimpl in ihn... }
  { move=>Θ Γ Δ r x A js wf ih k tyA Θ1 Θ0 Γ1 Δ1 σ mrg agr. asimpl.
    have[k1 k2]:=dyn_agree_subst_key agr k.
    have e:=merge_pureL mrg k1. subst.
    rewrite (sta_agree_subst_size (dyn_sta_agree_subst agr)).
    apply: dyn_cvar... }
  { move=>Θ Γ Δ m A tym ihm Θ1 Θ0 Γ1 Δ1 σ mrg agr. asimpl.
    have wf:=dyn_type_wf tym. inv wf.
    have{}ihm:=ihm _ _ _ _ _ mrg (dyn_agree_subst_ty agr H4).
    apply: dyn_fork... }
  { move=>Θ Γ Δ r1 r2 A B m xor tym ihm Θ1 Θ0 Γ1 Δ1 σ mrg agr. asimpl.
    apply: dyn_recv0... }
  { move=>Θ Γ Δ r1 r2 A B m xor tym ihm Θ1 Θ0 Γ1 Δ1 σ mrg agr. asimpl.
    apply: dyn_recv1... }
  { move=>Θ Γ Δ r1 r2 A B m xor tym ihm Θ1 Θ0 Γ1 Δ1 σ mrg agr. asimpl.
    apply: dyn_send0... }
  { move=>Θ Γ Δ r1 r2 A B m xor tym ihm Θ1 Θ0 Γ1 Δ1 σ mrg agr. asimpl.
    apply: dyn_send1... }
  { move=>Θ Γ Δ m tym ihm Θ1 Θ0 Γ1 Δ1 σ mrg agr. asimpl.
    apply: dyn_wait... }
  { move=>Θ Γ Δ m tym ihm Θ1 Θ0 Γ1 Δ1 σ mrg agr. asimpl.
    apply: dyn_close... }
  { move=>Θ Γ Δ A B m s eq tym ihm tyB Θ1 Θ0 Γ1 Δ1 σ mrg agr.
    apply: dyn_conv.
    apply: sta_conv_subst...
    apply: ihm...
    have:=sta_substitution tyB (dyn_sta_agree_subst agr).
    asimpl... }
  { exact: dyn_agree_subst_wf_nil. }
  { move=>Γ Δ A s wf h tyA Θ1 Γ1 Δ1 σ agr.
    apply: dyn_agree_subst_wf_ty... }
  { move=>Γ Δ A s wf ih tyA Θ1 Γ1 Δ1 σ agr.
    apply: dyn_agree_subst_wf_n... }
Qed.

Lemma dyn_substitution_wf Θ1 Γ1 Γ2 Δ1 Δ2 σ :
  dyn_wf Γ2 Δ2 -> Θ1 ; Γ1 ; Δ1 ⊢ σ ⊣ Γ2 ; Δ2 -> dyn_wf Γ1 Δ1.
Proof with eauto using dyn_wf.
  move=>wf. elim: wf Θ1 Γ1 Δ1 σ=>{Γ2 Δ2}.
  { move=>*. apply: dyn_agree_subst_wf_nil... }
  { move=>*. apply: dyn_agree_subst_wf_ty... }
  { move=>*. apply: dyn_agree_subst_wf_n... }
Qed.

Lemma dyn_subst0 Θ Γ Δ m n A B :
  Θ ; (A :: Γ) ; _: Δ ⊢ m : B -> Γ ⊢ n : A -> Θ ; Γ ; Δ ⊢ m.[n/] : B.[n/].
Proof with eauto using dyn_agree_subst_refl.
  move=>tym tyn.
  have wf:=dyn_type_wf tym. inv wf.
  have[Θ0[emp mrg]]:=dyn_type_empty tym.
  apply: dyn_substitution...
  apply: dyn_agree_subst_wk0...
  by asimpl.
Qed.

Lemma dyn_subst1 Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m n A B s :
  Θ2 ▷ s -> Θ1 ∘ Θ2 => Θ ->
  Δ2 ▷ s -> Δ1 ∘ Δ2 => Δ ->
  Θ1 ; (A :: Γ) ; A .{s} Δ1 ⊢ m : B ->
  Θ2 ; Γ ; Δ2 ⊢ n : A ->
  Θ ; Γ ; Δ ⊢ m.[n/] : B.[n/].
Proof with eauto using dyn_agree_subst_refl.
  move=>k1 mrg1 k2 mrg2 tym tyn.
  have wf:=dyn_type_wf tym. inv wf.
  have[Θ0[emp mrg]]:=dyn_type_empty tyn.
  apply: dyn_substitution...
  apply: merge_sym...
  apply: dyn_agree_subst_wk1.
  apply: k1. apply: k2.
  apply: mrg.
  apply: mrg2.
  apply: dyn_agree_subst_refl...
  by asimpl.
Qed.

Lemma dyn_esubst0 Θ Γ Δ m m' n A B B' :
  m' = m.[n/] ->
  B' = B.[n/] ->
  Θ ; (A :: Γ) ; _: Δ ⊢ m : B ->
  Γ ⊢ n : A ->
  Θ ; Γ ; Δ ⊢ m': B'.
Proof.
  move=>*; subst. apply: dyn_subst0; eauto.
Qed.

Lemma dyn_esubst1 Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m m' n A B B' s :
  m' = m.[n/] ->
  B' = B.[n/] ->
  Θ2 ▷ s -> Θ1 ∘ Θ2 => Θ ->
  Δ2 ▷ s -> Δ1 ∘ Δ2 => Δ ->
  Θ1 ; (A :: Γ) ; A .{s} Δ1 ⊢ m : B ->
  Θ2 ; Γ ; Δ2 ⊢ n : A ->
  Θ ; Γ ; Δ ⊢ m' : B'.
Proof.
  move=>e1 e2 k1 mrg1 k2 mrg2 tym tyn. subst.
  apply: dyn_subst1.
  apply: k1. apply: mrg1.
  apply: k2. apply: mrg2.
  apply: tym. apply: tyn.
Qed.

Lemma dyn_ctx_conv0 Θ Γ Δ m A B C s :
  B === A ->
  Γ ⊢ B : Sort s ->
  Θ ; (A :: Γ) ; _: Δ ⊢ m : C ->
  Θ ; (B :: Γ) ; _: Δ ⊢ m : C.
Proof with eauto using dyn_wf, dyn_agree_subst_refl.
  move=>eq tyB tym.
  have wf:=dyn_type_wf tym. inv wf.
  have[Θ0[emp mrg]]:=dyn_type_empty tym.
  have:Θ ; (B :: Γ) ; _: Δ ⊢ m.[ids] : C.[ids].
  apply: dyn_substitution...
  apply: dyn_agree_subst_conv0...
  apply: sta_eweaken...
  all: asimpl...
Qed.

Lemma dyn_ctx_conv1 Θ Γ Δ m A B C s :
  B === A ->
  Γ ⊢ B : Sort s ->
  Θ ; (A :: Γ) ; A .{s} Δ ⊢ m : C ->
  Θ ; (B :: Γ) ; B .{s} Δ ⊢ m : C.
Proof with eauto using dyn_wf, dyn_agree_subst_refl.
  move=>eq tyB tym.
  have wf:=dyn_type_wf tym. inv wf.
  have[Θ0[emp mrg]]:=dyn_type_empty tym.
  have:Θ ; (B :: Γ) ; B .{s} Δ ⊢ m.[ids] : C.[ids].
  apply: dyn_substitution...
  apply: dyn_agree_subst_conv1...
  apply: sta_eweaken...
  all: asimpl...
Qed.
