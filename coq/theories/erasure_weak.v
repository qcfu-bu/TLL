From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Stdlib Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS erasure_type.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma erasure_rename Γ Γ' Δ Δ' m m' A ξ :
  Γ ; Δ ⊢ m ~ m' : A -> program_agree_ren ξ Γ Δ Γ' Δ' ->
  Γ' ; Δ' ⊢ m.[ren ξ] ~ m'.[ren ξ] : A.[ren ξ].
Proof with eauto using
  erasure_type, logical_agree_ren, program_agree_ren, program_agree_ren_key.
  move=>ty. elim: ty Γ' Δ' ξ=>{Γ Δ m m' A}.
  { move=>Γ Δ x s A wf shs dhs Γ' Δ' ξ agr. asimpl.
    apply: erasure_var.
    apply: program_rename_wf...
    apply: logical_agree_ren_has...
    apply: program_logical_agree_ren...
    apply: program_agree_ren_has... }
  { move=>Γ Δ A B m m' s k tym ihm Γ' Δ' ξ agr. asimpl.
    have wf:=program_type_wf (erasure_program_type tym). inv wf.
    apply: erasure_lam0... }
  { move=>Γ Δ A B m m' s t k tym ihm Γ' Δ' ξ agr. asimpl.
    have wf:=program_type_wf (erasure_program_type tym). inv wf.
    apply: erasure_lam1... }
  { move=>Γ Δ A B m m' n s tym ihm tyn Γ' Δ' ξ agr. asimpl.
    replace B.[n.[ren ξ] .: ren ξ] with B.[ren (upren ξ)].[n.[ren ξ]/]
      by autosubst.
    have{}ihm:=ihm _ _ _ agr.
    have{}ihn:=logical_rename tyn (program_logical_agree_ren agr).
    apply: erasure_app0...
    asimpl in ihm... }
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' s mrg tym ihm tyn ihn Γ' Δ' ξ agr. asimpl.
    replace B.[n.[ren ξ] .: ren ξ] with B.[ren (upren ξ)].[n.[ren ξ]/]
      by autosubst.
    have[Δ1'[Δ2'[mrg'[agr1 agr2]]]]:=program_agree_ren_merge agr mrg.
    have{}ihm:=ihm _ _ _ agr1.
    have{}ihn:=ihn _ _ _ agr2.
    apply: erasure_app1...
    asimpl in ihm... }
  { move=>Γ Δ A B m m' n t l tyS tym ihm tyn Γ' Δ' ξ agr. asimpl.
    have{}ihm:=ihm _ _ _ agr.
    have{}ihn:=logical_rename tyn (program_logical_agree_ren agr).
    have{}ihS:=logical_rename tyS (program_logical_agree_ren agr).
    apply: erasure_pair0...
    asimpl in ihS...
    asimpl. asimpl in ihn... }
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' t l mrg tyS tym ihm tyn ihn Γ' Δ' ξ agr. asimpl.
    have[Δ1'[Δ2'[mrg'[agr1 agr2]]]]:=program_agree_ren_merge agr mrg.
    have{}ihm:=ihm _ _ _ agr1.
    have{}ihn:=ihn _ _ _ agr2.
    have{}ihS:=logical_rename tyS (program_logical_agree_ren agr).
    apply: erasure_pair1...
    asimpl in ihS...
    asimpl. asimpl in ihn... }
  { move=>Γ Δ1 Δ2 Δ A B C m m' n n' s r t l mrg tyC tym ihm tyn ihn Γ' Δ' ξ agr. asimpl.
    have wf:=logical_type_wf tyC. inv wf.
    have wf:=program_type_wf (erasure_program_type tyn). inv wf. inv H4.
    have[Δ1'[Δ2'[mrg'[agr1 agr2]]]]:=program_agree_ren_merge agr mrg.
    have{}ihC:=logical_rename tyC (logical_agree_ren_cons H2 (program_logical_agree_ren agr)).
    have{}ihm:=ihm _ _ _ agr1.
    have/ihn{}ihn:program_agree_ren (upren (upren ξ)) (B :: A :: Γ) (_: A .{r} Δ2)
      (B.[ren (upren ξ)] :: A.[ren ξ] :: Γ') (_: A.[ren ξ] .{r} Δ2')...
    asimpl in ihC.
    asimpl in ihm.
    replace C.[Pair0 (Var 1) (Var 0) t .: ren (+2)].[ren (upren (upren ξ))]
      with C.[ren (upren ξ)].[Pair0 (Var 1) (Var 0) t .: ren (+2)]
        in ihn by autosubst.
    have:=erasure_letin0 mrg' ihC ihm ihn.
    by autosubst. }
  { move=>Γ Δ1 Δ2 Δ A B C m m' n n' s r1 r2 t l mrg tyC tym ihm tyn ihn Γ' Δ' ξ agr. asimpl.
    have wf:=logical_type_wf tyC. inv wf.
    have wf:=program_type_wf (erasure_program_type tyn). inv wf. inv H4.
    have[Δ1'[Δ2'[mrg'[agr1 agr2]]]]:=program_agree_ren_merge agr mrg.
    have{}ihC:=logical_rename tyC (logical_agree_ren_cons H2 (program_logical_agree_ren agr)).
    have{}ihm:=ihm _ _ _ agr1.
    have/ihn{}ihn:program_agree_ren (upren (upren ξ)) (B :: A :: Γ) (B .{r2} A .{r1} Δ2)
      (B.[ren (upren ξ)] :: A.[ren ξ] :: Γ') (B.[ren (upren ξ)] .{r2} A.[ren ξ] .{r1} Δ2')...
    asimpl in ihC.
    asimpl in ihm.
    replace C.[Pair1 (Var 1) (Var 0) t .: ren (+2)].[ren (upren (upren ξ))]
      with C.[ren (upren ξ)].[Pair1 (Var 1) (Var 0) t .: ren (+2)]
        in ihn by autosubst.
    have:=erasure_letin1 mrg' ihC ihm ihn.
    by autosubst. }
  { move=>Γ Δ wf k Γ' Δ' ξ agr. asimpl. apply:erasure_tt... apply: program_rename_wf... }
  { move=>Γ Δ wf k Γ' Δ' ξ agr. asimpl. apply:erasure_ff... apply: program_rename_wf... }
  { move=>Γ Δ1 Δ2 Δ A m m' n1 n1' n2 n2' s l
           mrg tyA tym ihm tyn1 ihn1 tyn2 ihn2 Γ' Δ' ξ agr. asimpl.
    replace A.[m.[ren ξ] .: ren ξ] with A.[ren (upren ξ)].[m.[ren ξ]/] by autosubst.
    have wf:=logical_type_wf tyA. inv wf.
    have[Δ1'[Δ2'[mrg'[agr1 agr2]]]]:=program_agree_ren_merge agr mrg.
    have{}ihn1:=ihn1 _ _ _ agr2.
    have{}ihn2:=ihn2 _ _ _ agr2.
    have agr':=logical_agree_ren_cons H2 (program_logical_agree_ren agr).
    have/=tyA':=logical_rename tyA agr'.
    apply: erasure_ifte...
    asimpl in ihn1. asimpl...
    asimpl in ihn2. asimpl... }
  { move=>Γ Δ A B H H' P m n s l tyB erH ihH tyP Γ' Δ' ξ agr. asimpl.
    have wf:=logical_type_wf tyB. inv wf. inv H2.
    have ihP:=logical_rename tyP (program_logical_agree_ren agr).
    have agr':=program_logical_agree_ren agr.
    have{}agr':
      logical_agree_ren (upren (upren ξ))
        (Id A.[ren (+1)] m.[ren (+1)] (Var 0) :: A :: Γ)
        ((Id A.[ren (+1)] m.[ren (+1)] (Var 0)).[ren (upren ξ)] :: A.[ren ξ] :: Γ')...
    have ihB:=logical_rename tyB agr'.
    have{}ihH:=ihH _ _ _ agr.
    asimpl in ihP.
    asimpl in ihB.
    asimpl in ihH.
    replace A.[ren (ξ >>> (+1))] with A.[ren ξ].[ren (+1)] in ihB by autosubst.
    replace m.[ren (ξ >>> (+1))] with m.[ren ξ].[ren (+1)] in ihB by autosubst.
    have pf:=erasure_rw ihB. asimpl in pf.
    have:=pf _ _ _ _ _ ihH ihP.
    by autosubst. }
  { move=>Γ Δ A B m m' s l eq tym ihm tyB Γ' Δ' ξ agr.
    apply: erasure_conv.
    apply: logical_conv_subst...
    apply: ihm...
    have:=logical_rename tyB (program_logical_agree_ren agr).
    asimpl... }
Qed.

Lemma erasure_weakenU Γ Δ m m' A B l :
  Γ ⊢ B : Sort U l ->
  Γ ; Δ ⊢ m ~ m' : A ->
  (B :: Γ) ; B :U Δ ⊢ m.[ren (+1)] ~ m'.[ren (+1)] : A.[ren (+1)].
Proof with eauto using program_agree_ren, program_agree_ren_refl.
  move=>tyB tym. apply: erasure_rename...
Qed.

Lemma erasure_weakenN Γ Δ m m' A B s l :
  Γ ⊢ B : Sort s l ->
  Γ ; Δ ⊢ m ~ m' : A ->
  (B :: Γ) ; _: Δ ⊢ m.[ren (+1)] ~ m'.[ren (+1)] : A.[ren (+1)].
Proof with eauto using program_agree_ren, program_agree_ren_refl.
  move=>tyB tym. apply: erasure_rename...
Qed.

Lemma erasure_eweakenU Γ Δ m m' n n' A A' B l :
  m' = m.[ren (+1)] ->
  n' = n.[ren (+1)] ->
  A' = A.[ren (+1)] ->
  Γ ⊢ B : Sort U l ->
  Γ ; Δ ⊢ m ~ n : A ->
  (B :: Γ) ; B :U Δ ⊢ m' ~ n' : A'.
Proof.
  move=>*; subst. apply: erasure_weakenU; eauto.
Qed.

Lemma erasure_eweakenN Γ Δ m m' n n' A A' B s l :
  m' = m.[ren (+1)] ->
  n' = n.[ren (+1)] ->
  A' = A.[ren (+1)] ->
  Γ ⊢ B : Sort s l ->
  Γ ; Δ ⊢ m ~ n : A ->
  (B :: Γ) ; (_: Δ) ⊢ m' ~ n' : A'.
Proof.
  move=>*; subst. apply: erasure_weakenN; eauto.
Qed.
