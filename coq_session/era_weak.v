From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS era_valid.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma era_rename Θ Γ Γ' Δ Δ' m m' A ξ :
  Θ ; Γ ; Δ ⊢ m ~ m' : A -> dyn_agree_ren ξ Γ Δ Γ' Δ' -> 
  Θ ; Γ' ; Δ' ⊢ m.[ren ξ] ~ m'.[ren ξ] : A.[ren ξ].
Proof with eauto using 
  era_type, sta_agree_ren, dyn_agree_ren, dyn_agree_ren_key.
  move=>ty. elim: ty Γ' Δ' ξ=>{Θ Γ Δ m m' A}.
  { move=>Θ Γ Δ x s A chs wf shs dhs Γ' Δ' ξ agr. asimpl.
    apply: era_var...
    apply: dyn_rename_wf...
    apply: sta_agree_ren_has...
    apply: dyn_sta_agree_ren...
    apply: dyn_agree_ren_has... }
  { move=>Θ Γ Δ A B m m' s k1 k2 erm ihm Γ' Δ' ξ agr. asimpl.
    have wf:=dyn_type_wf (era_dyn_type erm). inv wf.
    apply: era_lam0... }
  { move=>Θ Γ Δ A B m m' s t k1 k2 erm ihm Γ' Δ' ξ agr. asimpl.
    have wf:=dyn_type_wf (era_dyn_type erm). inv wf.
    apply: era_lam1... }
  { move=>Θ Γ Δ A B m m' n s erm ihm tyn Γ' Δ' ξ agr. asimpl.
    replace B.[n.[ren ξ] .: ren ξ] with B.[ren (upren ξ)].[n.[ren ξ]/]
      by autosubst.
    have{}ihm:=ihm _ _ _ agr.
    have{}ihn:=sta_rename tyn (dyn_sta_agree_ren agr).
    apply: era_app0...
    asimpl in ihm... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m m' n n' s mrg1 mrg2 erm ihm ern ihn Γ' Δ' ξ agr. asimpl.
    replace B.[n.[ren ξ] .: ren ξ] with B.[ren (upren ξ)].[n.[ren ξ]/]
      by autosubst.
    have[Δ1'[Δ2'[mrg'[agr1 agr2]]]]:=dyn_agree_ren_merge agr mrg2.
    have{}ihm:=ihm _ _ _ agr1.
    have{}ihn:=ihn _ _ _ agr2.
    apply: era_app1...
    asimpl in ihm... }
  { move=>Θ Γ Δ A B m n n' t tyS tym ern ihn Γ' Δ' ξ agr. asimpl.
    have{}ihm:=sta_rename tym (dyn_sta_agree_ren agr).
    have{}ihn:=ihn _ _ _ agr.
    have{}ihS:=sta_rename tyS (dyn_sta_agree_ren agr).
    apply: era_pair0...
    asimpl in ihS...
    asimpl. asimpl in ihn... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m m' n n' t mrg1 mrg2 tyS erm ihm ern ihn Γ' Δ' ξ agr. asimpl.
    have[Δ1'[Δ2'[mrg'[agr1 agr2]]]]:=dyn_agree_ren_merge agr mrg2.
    have{}ihm:=ihm _ _ _ agr1.
    have{}ihn:=ihn _ _ _ agr2.
    have{}ihS:=sta_rename tyS (dyn_sta_agree_ren agr).
    apply: era_pair1...
    asimpl in ihS...
    asimpl. asimpl in ihn... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m m' n n' s r t mrg1 mrg2 tyC erm ihm ern ihn Γ' Δ' ξ agr. asimpl.
    have wf:=sta_type_wf tyC. inv wf.
    have wf:=dyn_type_wf (era_dyn_type ern). inv wf. inv H4.
    have[Δ1'[Δ2'[mrg'[agr1 agr2]]]]:=dyn_agree_ren_merge agr mrg2.
    have{}ihC:=sta_rename tyC (sta_agree_ren_cons H2 (dyn_sta_agree_ren agr)).
    have{}ihm:=ihm _ _ _ agr1.
    have/ihn{}ihn:dyn_agree_ren (upren (upren ξ)) (B :: A :: Γ) (B .{r} _: Δ2)
      (B.[ren (upren ξ)] :: A.[ren ξ] :: Γ') (B.[ren (upren ξ)] .{r} _: Δ2')...
    asimpl in ihC.
    asimpl in ihm.
    replace C.[Pair0 (Var 1) (Var 0) t .: ren (+2)].[ren (upren (upren ξ))]
      with C.[ren (upren ξ)].[Pair0 (Var 1) (Var 0) t .: ren (+2)]
        in ihn by autosubst.
    have:=era_letin0 mrg1 mrg' ihC ihm ihn.
    by autosubst. }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m m' n n' s r1 r2 t mrg1 mrg2 tyC erm ihm ern ihn Γ' Δ' ξ agr. asimpl.
    have wf:=sta_type_wf tyC. inv wf.
    have wf:=era_type_wf ern. inv wf. inv H4.
    have[Δ1'[Δ2'[mrg'[agr1 agr2]]]]:=dyn_agree_ren_merge agr mrg2.
    have{}ihC:=sta_rename tyC (sta_agree_ren_cons H2 (dyn_sta_agree_ren agr)).
    have{}ihm:=ihm _ _ _ agr1.
    have/ihn{}ihn:dyn_agree_ren (upren (upren ξ)) (B :: A :: Γ) (B .{r2} A .{r1} Δ2)
      (B.[ren (upren ξ)] :: A.[ren ξ] :: Γ') (B.[ren (upren ξ)] .{r2} A.[ren ξ] .{r1} Δ2')...
    asimpl in ihC.
    asimpl in ihm.
    replace C.[Pair1 (Var 1) (Var 0) t .: ren (+2)].[ren (upren (upren ξ))]
      with C.[ren (upren ξ)].[Pair1 (Var 1) (Var 0) t .: ren (+2)]
        in ihn by autosubst.
    have:=era_letin1 mrg1 mrg' ihC ihm ihn.
    by autosubst. }
  { move=>Θ Γ Δ emp wf k Γ' Δ' ξ agr.
    have:=dyn_rename_wf wf agr. asimpl... }
  { move=>Θ Γ Δ emp wf k Γ' Δ' ξ agr.
    have:=dyn_rename_wf wf agr. asimpl... }
  { move=>Θ Γ Δ emp wf k Γ' Δ' ξ agr.
    have:=dyn_rename_wf wf agr. asimpl... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m m' n1 n1' n2 n2' s mrg1 mrg2
      tyA tym ihm tyn1 ihn1 tyn2 ihn2 Γ' Δ' ξ agr. asimpl.
    replace A.[m.[ren ξ] .: ren ξ] with A.[ren (upren ξ)].[m.[ren ξ]/] by autosubst.
    have wf:=sta_type_wf tyA. inv wf.
    have[Δ1'[Δ2'[mrg'[agr1 agr2]]]]:=dyn_agree_ren_merge agr mrg2.
    have{}ihn1:=ihn1 _ _ _ agr2.
    have{}ihn2:=ihn2 _ _ _ agr2.
    have agr':=sta_agree_ren_cons H2 (dyn_sta_agree_ren agr).
    have/=tyA':=sta_rename tyA agr'.
    apply: era_ifte...
    asimpl in ihn1. asimpl...
    asimpl in ihn2. asimpl... }
  { move=>Θ Γ Δ m m' A tym ihm Γ' Δ' ξ agr. asimpl... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m m' n n' A B s t mrg1 mrg2 tyB tym ihm tyn ihn Γ' Δ' ξ agr. asimpl.
    have[Δ1'[Δ2'[mrg'[agr1 agr2]]]]:=dyn_agree_ren_merge agr mrg2.
    have wf:=era_type_wf tyn. inv wf.
    have{}ihn:=ihn _ _ _ (dyn_agree_ren_ty H4 agr2).
    have/=tyB':=sta_rename tyB (dyn_sta_agree_ren agr).
    apply: era_bind...
    asimpl in ihn. asimpl... }
  { move=>Θ Γ Δ r x A js wf k tyA Γ' Δ' ξ agr. asimpl.
    rewrite (dyn_agree_ren_size agr).
    apply: era_cvar...
    apply: dyn_rename_wf... }
  { move=>Θ Γ Δ m m' A erm ihm Γ' Δ' ξ agr. asimpl.
    have wf:=era_type_wf erm. inv wf.
    have{}ihm:=ihm _ _ _ (dyn_agree_ren_ty H4 agr).
    apply: era_fork. asimpl in ihm... }
  { move=>Θ Γ Δ r1 r2 A B m m' xor erm ihm Γ' Δ' ξ agr... }
  { move=>Θ Γ Δ r1 r2 A B m m' xor erm ihm Γ' Δ' ξ agr... }
  { move=>Θ Γ Δ r1 r2 A B m m' xor erm ihm Γ' Δ' ξ agr... }
  { move=>Θ Γ Δ r1 r2 A B m m' xor erm ihm Γ' Δ' ξ agr... }
  { move=>Θ Γ Δ m m' erm ihm Γ' Δ' ξ agr... }
  { move=>Θ Γ Δ m m' erm ihm Γ' Δ' ξ agr... }
  { move=>Θ Γ Δ A B m m' s eq tym ihm tyB Γ' Δ' ξ agr.
    apply: era_conv.
    apply: sta_conv_subst...
    apply: ihm...
    have:=sta_rename tyB (dyn_sta_agree_ren agr).
    asimpl... }
Qed.

Lemma era_weakenU Θ Γ Δ m m' A B :
  Γ ⊢ B : Sort U ->
  Θ ; Γ ; Δ ⊢ m ~ m' : A ->
  Θ ; (B :: Γ) ; B :U Δ ⊢ m.[ren (+1)] ~ m'.[ren (+1)] : A.[ren (+1)].
Proof with eauto using dyn_agree_ren, dyn_agree_ren_refl.
  move=>tyB erm. apply: era_rename...
Qed.

Lemma era_weakenN Θ Γ Δ m m' A B s :
  Γ ⊢ B : Sort s ->
  Θ ; Γ ; Δ ⊢ m ~ m' : A ->
  Θ ; (B :: Γ) ; _: Δ ⊢ m.[ren (+1)] ~ m'.[ren (+1)] : A.[ren (+1)].
Proof with eauto using dyn_agree_ren, dyn_agree_ren_refl.
  move=>tyB erm. apply: era_rename...
Qed.

Lemma era_eweakenU Θ Γ Δ m m' n n' A A' B :
  m' = m.[ren (+1)] ->
  n' = n.[ren (+1)] ->
  A' = A.[ren (+1)] ->
  Γ ⊢ B : Sort U ->
  Θ ; Γ ; Δ ⊢ m ~ n : A ->
  Θ ; (B :: Γ) ; B :U Δ ⊢ m' ~ n' : A'.
Proof.
  move=>*; subst. exact: era_weakenU.
Qed.

Lemma era_eweakenN Θ Γ Δ m m' n n' A A' B s :
  m' = m.[ren (+1)] ->
  n' = n.[ren (+1)] ->
  A' = A.[ren (+1)] ->
  Γ ⊢ B : Sort s ->
  Θ ; Γ ; Δ ⊢ m ~ n : A ->
  Θ ; (B :: Γ) ; _: Δ ⊢ m' ~ n' : A'.
Proof.
  move=>*; subst. apply: era_weakenN; eauto.
Qed.

