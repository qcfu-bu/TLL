From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq zify.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS dyn_cren era_subst.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma era_crename Θ Θ' Γ Δ m m' A ξ :
  Θ ; Γ ; Δ ⊢ m ~ m' : A -> dyn_ctx_cren ξ Θ Θ' ->
  Θ' ; Γ ; Δ ⊢ cren ξ m ~ cren ξ m' : A.
Proof with eauto using era_type, dyn_empty, dyn_ctx_cren.
  move=>er. elim: er Θ' ξ=>/={Θ Γ Δ m m' A}...
  { move=>Θ Γ Δ x s A wmp wf shs dhs Θ' ξ agr.
    econstructor... apply: dyn_ctx_cren_empty... }
  { move=>Θ Γ Δ A B m m' s k1 k2 tym ihm Θ' ξ agr.
    have wf:=era_type_wf tym. inv wf.
    have[r tyB]:=era_valid tym.
    apply: era_conv.
    apply: sta_cren_conv0...
    simpl. constructor...
    apply: dyn_ctx_cren_key...
    apply: era_ctx_conv0.
    apply: sta_cren_conv0...
    apply: sta_crename...
    apply: era_conv.
    apply: conv_sym.
    apply: sta_cren_conv0...
    apply: ihm...
    apply: sta_crename...
    econstructor... }
  { move=>Θ Γ Δ A B m m' s t k1 k2 tym ihm Θ' ξ agr.
    have wf:=era_type_wf tym. inv wf.
    have[r tyB]:=era_valid tym.
    apply: era_conv.
    apply: sta_cren_conv0...
    simpl. econstructor...
    apply: dyn_ctx_cren_key...
    apply: era_ctx_conv1.
    apply: sta_cren_conv0...
    apply: sta_crename...
    apply: era_conv.
    apply: conv_sym.
    apply: sta_cren_conv0...
    apply: ihm...
    apply: sta_crename...
    econstructor... }
  { move=>Θ Γ Δ A B m m' n s tym ihm tyn Θ' ξ agr.
    have[r tyP]:=era_valid tym.
    have[t[tyB/sort_inj e]]:=sta_pi0_inv tyP. subst.
    have eq:B.[cren ξ n/] ≃ B.[n/].
    apply: sta_conv_beta.
    apply: sta_cren_conv0...
    apply: era_conv...
    econstructor...
    apply: sta_crename...
    have:=sta_subst tyB tyn... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m m' n n' s mrg1 mrg2 tym ihm tyn ihn Θ' ξ agr.
    have[Θ1'[Θ2'[mrg'[agr1 agr2]]]]:=dyn_ctx_cren_merge agr mrg1.
    have[r tyP]:=era_valid tym.
    have[t[tyB/sort_inj e]]:=sta_pi1_inv tyP. subst.
    have eq:B.[cren ξ n/] ≃ B.[n/].
    apply: sta_conv_beta.
    apply: sta_cren_conv0...
    apply: era_conv...
    have:=sta_subst tyB (era_sta_type tyn)... }
  { move=>Θ Γ Δ A B m n n' t tyS tym tyn ihn Θ' ξ agr.
    have[s[r[ord[tyA[tyB _]]]]]:=sta_sig0_inv tyS.
    have eq: B.[m/] ≃ B.[cren ξ m/].
    apply: sta_conv_beta.
    apply: conv_sym.
    apply: sta_cren_conv0...
    econstructor...
    apply: sta_crename...
    apply: era_conv...
    have:=sta_subst tyB (sta_crename ξ tym)... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m m' n n' t mrg1 mrg2 tyS tym ihm tyn ihn Θ' ξ agr.
    have[s[r[ord1[ord2[tyA[tyB _]]]]]]:=sta_sig1_inv tyS.
    have[Θ1'[Θ2'[mrg'[agr1 agr2]]]]:=dyn_ctx_cren_merge agr mrg1.
    have eq: B.[m/] ≃ B.[cren ξ m/].
    apply: sta_conv_beta.
    apply: conv_sym.
    apply: sta_cren_conv0...
    econstructor...
    apply: era_conv...
    have:=sta_subst tyB (sta_crename ξ (era_sta_type tym))... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m m' n n' s r t mrg1 mrg2 tyC tym ihm tyn ihn Θ' ξ agr.
    have wf:=sta_type_wf tyC. inv wf.
    have[s1[r1[ord[tyA[tyB/sort_inj e]]]]]:=sta_sig0_inv H2. subst.
    have[Θ1'[Θ2'[mrg'[agr1 agr2]]]]:=dyn_ctx_cren_merge agr mrg1.
    have eq: (cren ξ C).[cren ξ m/] ≃ C.[m/].
    apply: conv_trans.
    apply: sta_conv_beta.
    apply: sta_cren_conv0...
    apply: sta_conv_subst.
    apply: sta_cren_conv0...
    apply: era_conv...
    apply: era_letin0...
    apply: sta_crename...
    apply: era_conv.
    erewrite<-term_cren_subst.
    apply: conv_sym.
    apply: sta_cren_conv0...
    2:{ apply: ihn... }
    move=>[|x]/=...
    have agr':sta_agree_subst (B :: A :: Γ) (Pair0 (Var 1) (Var 0) t .: ren (+2)) (Sig0 A B t :: Γ).
    { econstructor.
      replace (ren (+2)) with (ids >> (ren (+1)) >> (ren (+1))) by autosubst.
      econstructor...
      econstructor...
      asimpl.
      econstructor.
      replace (Sig0 A.[ren (+2)] B.[ren (0 .: (+3))] t)
        with (Sig0 A B t).[ren (+2)] by autosubst.
      replace (Sort t) with (Sort t).[ren (+2)] by eauto.
      apply: sta_rename...
      replace (+2) with ((+1) >>> (+1) >>> id) by autosubst.
      econstructor...
      econstructor...
      apply: sta_agree_ren_refl...
      repeat constructor...
      replace A.[ren (+2)] with A.[ren (+1)].[ren (+1)] by autosubst.
      repeat constructor.
      asimpl.
      repeat constructor... }
    have/=:=sta_substitution (sta_crename ξ tyC) agr'...
    have/=:=sta_subst tyC (era_sta_type tym)... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m m' n n' s r1 r2 t mrg1 mrg2 tyC tym ihm tyn ihn Θ' ξ agr.
    have wf:=sta_type_wf tyC. inv wf.
    have[s1[r3[ord1[ord2[tyA[tyB/sort_inj e]]]]]]:=sta_sig1_inv H2. subst.
    have[Θ1'[Θ2'[mrg'[agr1 agr2]]]]:=dyn_ctx_cren_merge agr mrg1.
    have eq: (cren ξ C).[cren ξ m/] ≃ C.[m/].
    apply: conv_trans.
    apply: sta_conv_beta.
    apply: sta_cren_conv0...
    apply: sta_conv_subst.
    apply: sta_cren_conv0...
    apply: era_conv...
    apply: era_letin1...
    apply: sta_crename...
    apply: era_conv.
    erewrite<-term_cren_subst.
    apply: conv_sym.
    apply: sta_cren_conv0...
    2:{ apply: ihn... }
    move=>[|x]/=...
    have agr':sta_agree_subst (B :: A :: Γ) (Pair1 (Var 1) (Var 0) t .: ren (+2)) (Sig1 A B t :: Γ).
    { econstructor.
      replace (ren (+2)) with (ids >> (ren (+1)) >> (ren (+1))) by autosubst.
      econstructor...
      econstructor...
      asimpl.
      econstructor.
      replace (Sig1 A.[ren (+2)] B.[ren (0 .: (+3))] t)
        with (Sig1 A B t).[ren (+2)] by autosubst.
      replace (Sort t) with (Sort t).[ren (+2)] by eauto.
      apply: sta_rename...
      replace (+2) with ((+1) >>> (+1) >>> id) by autosubst.
      econstructor...
      econstructor...
      apply: sta_agree_ren_refl...
      repeat constructor...
      replace A.[ren (+2)] with A.[ren (+1)].[ren (+1)] by autosubst.
      repeat constructor.
      asimpl.
      repeat constructor... }
    have/=:=sta_substitution (sta_crename ξ tyC) agr'...
    have/=:=sta_subst tyC (era_sta_type tym)... }
  { move=>Θ Γ Δ A m m' k1 k2 tym ihm Θ' ξ agr.
    have wf:=era_type_wf tym. inv wf.
    apply: era_conv.
    apply: sta_cren_conv0...
    constructor...
    apply: dyn_ctx_cren_key...
    apply: era_ctx_conv1.
    apply: sta_cren_conv0...
    apply: sta_crename...
    apply: era_conv.
    apply: sta_conv_subst.
    apply: conv_sym.
    apply: sta_cren_conv0...
    apply: ihm...
    apply: sta_eweaken...
    2:{ apply: sta_crename... } 
    simpl. eauto. eauto. }
  { move=>Θ Γ Δ emp wf k Θ' ξ agr.
    constructor... apply: dyn_ctx_cren_empty... }
  { move=>Θ Γ Δ emp wf k Θ' ξ agr.
    constructor... apply: dyn_ctx_cren_empty... }
  { move=>Θ Γ Δ emp wf k Θ' ξ agr.
    constructor... apply: dyn_ctx_cren_empty... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m m' n1 n1' n2 n2' s mrg1 mrg2
           tyA tym ihm tyn1 ihn1 tyn2 ihn2 Θ' ξ agr.
    have wf:=sta_type_wf (era_sta_type tym).
    have[Θ1'[Θ2'[mrg'[agr1 agr2]]]]:=dyn_ctx_cren_merge agr mrg1.
    have eq:(cren ξ A).[cren ξ m/] ≃ A.[m/].
    apply: conv_trans.
    apply: sta_conv_beta.
    apply: sta_cren_conv0...
    apply: sta_conv_subst.
    apply: sta_cren_conv0...
    apply: era_conv...
    econstructor...
    apply: sta_crename...
    apply: era_conv.
    apply: sta_conv_subst.
    apply: conv_sym.
    apply: sta_cren_conv0...
    eauto.
    have:=sta_subst (sta_crename ξ tyA) (sta_tt wf)...
    apply: era_conv.
    apply: sta_conv_subst.
    apply: conv_sym.
    apply: sta_cren_conv0...
    eauto.
    have:=sta_subst (sta_crename ξ tyA) (sta_ff wf)...
    have//=:=sta_subst tyA (era_sta_type tym)... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m m' n n' A B s t mrg1 mrg2
           tyB tym ihm tyn ihn Θ' ξ agr.
    have[Θ1'[Θ2'[mrg'[agr1 agr2]]]]:=dyn_ctx_cren_merge agr mrg1.
    econstructor... }
  { move=>Θ Γ Δ r x A js wf k tyA Θ' ξ agr.
    have/={}js:=dyn_ctx_cren_just agr js.
    apply: era_conv.
    2:{econstructor... apply: sta_crename... }
    apply: sta_conv_ch.
    rewrite<-term_cren_ren.
    apply: sta_cren_conv0...
    constructor.
    replace Proto with Proto.[ren (+size Γ)] by eauto.
    apply: sta_rename...
    apply: sta_wf_agree_ren.
    apply: dyn_sta_wf... }
  { move=>Θ Γ Δ m m' A tym ihm Θ' ξ agr.
    have wf:=era_type_wf tym. inv wf.
    have[tyA _]:=sta_ch_inv H4.
    apply: era_conv.
    apply: sta_conv_io.
    apply: sta_conv_ch.
    apply: sta_cren_conv0...
    econstructor.
    apply: era_ctx_conv1.
    apply: sta_conv_ch.
    apply: sta_cren_conv0...
    constructor.
    apply: sta_crename...
    apply: ihm...
    econstructor.
    econstructor.
    eauto. }
Qed.

Lemma era_cstrengthen Θ Γ Δ m m' A :
  _: Θ ; Γ ; Δ ⊢ cren (+1) m ~ cren (+1) m' : A ->
  Θ ; Γ ; Δ ⊢ m ~ m' : A.
Proof with eauto using dyn_empty, era_type, dyn_ctx_cren.
  move=>ty.
  have e:((+1) >>> (-1)) = id.
  { f_ext. move=>x. asimpl. fold subn. lia. }
  replace m with (cren ((-1) >>> id) (cren (+1) m)).
  replace m' with (cren ((-1) >>> id) (cren (+1) m')).
  apply: era_crename.
  apply: ty. constructor. constructor.
  rewrite<-term_cren_comp. asimpl. rewrite e. apply: term_cren_id.
  rewrite<-term_cren_comp. asimpl. rewrite e. apply: term_cren_id.
Qed.

Lemma era_cweaken Θ Γ Δ m m' A :
  Θ ; Γ ; Δ ⊢ m ~ m' : A ->
  _: Θ ; Γ ; Δ ⊢ cren (+1) m ~ cren (+1) m' : A.
Proof with eauto using dyn_empty, era_type, dyn_ctx_cren.
  move=>ty. apply: era_crename...
Qed.

Lemma era_cren_inv Θ Γ Δ m x A ξ :
  Θ ; Γ ; Δ ⊢ cren ξ m ~ x : A -> exists m', x = cren ξ m'.
Proof with eauto.
  move e:(cren ξ m)=>n er. elim: er m ξ e=>{Θ Γ Δ n x A}...
  { move=>Θ Γ Δ A B m m' s k1 k2 erm ihm m0 ξ e. destruct m0; inv e.
    have[n' e]:=ihm _ _ erefl. subst. by exists (Lam0 Box n' s). }
  { move=>Θ Γ Δ A B m m' s t k1 k2 erm ihm m0 ξ e. destruct m0; inv e.
    have[n' e]:=ihm _ _ erefl. subst. by exists (Lam1 Box n' s). }
  { move=>Θ Γ Δ A B m m' n s erm ihm tyn m0 ξ e. destruct m0; inv e.
    have[n' e]:=ihm _ _ erefl. subst. by exists (App0 n' Box). }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m m' n n' s mrg1 mrg2
           erm ihm ern ihn m0 ξ e. destruct m0; inv e.
    have[m1 e]:=ihm _ _ erefl. subst.
    have[n1 e]:=ihn _ _ erefl. subst.
    by exists (App1 m1 n1). }
  { move=>Θ Γ Δ A B m n n' t tyS tym ern ihn m0 ξ e. destruct m0; inv e.
    have[n1 e]:=ihn _ _ erefl. subst. by exists (Pair0 Box n1 t). }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m m' n n' t mrg1 mrg2 tyS erm ihm ern ihn m0 ξ e.
    destruct m0; inv e.
    have[m1 e]:=ihm _ _ erefl. subst.
    have[n1 e]:=ihn _ _ erefl. subst.
    by exists (Pair1 m1 n1 t). }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m m' n n' s r t mrg1 mrg2 tyS erm ihm ern ihn m0 ξ e.
    destruct m0; inv e.
    have[m1 e]:=ihm _ _ erefl. subst.
    have[n1 e]:=ihn _ _ erefl. subst.
    by exists (LetIn Box m1 n1). }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m m' n n' s r1 r2 t mrg1 mrg2 tyC erm ihm ern ihn m0 ξ e.
    destruct m0; inv e.
    have[m1 e]:=ihm _ _ erefl. subst.
    have[n1 e]:=ihn _ _ erefl. subst.
    by exists (LetIn Box m1 n1). }
  { move=>Θ Γ Δ A m m' k1 k2 erm ihm m0 ξ e. destruct m0; inv e.
    have[m2 e]:=ihm _ _ erefl. subst. by exists (Fix Box m2). }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m m' n1 n1' n2 n2' s mrg1 mrg2
           tyA erm ihm ern1 ihn1 ern2 ihn2 m0 ξ e. destruct m0; inv e.
    have[m1 e]:=ihm _ _ erefl. subst.
    have[n1 e]:=ihn1 _ _ erefl. subst.
    have[n2 e]:=ihn2 _ _ erefl. subst.
    by exists (Ifte Box m1 n1 n2). }
  { move=>Θ Γ Δ m m' A erm ihm m0 ξ e. destruct m0; inv e.
    have[m1 e]:=ihm _ _ erefl. subst. by exists (Return m1). }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m m' n n' A B s t mrg1 mrg2 tyB erm ihm ern ihn m0 ξ e.
    destruct m0; inv e.
    have[m1 e]:=ihm _ _ erefl. subst.
    have[n1 e]:=ihn _ _ erefl. subst.
    by exists (Bind m1 n1). }
  { move=>Θ Γ Δ m m' A erm ihm m0 ξ e. destruct m0; inv e.
    have[m e]:=ihm _ _ erefl. subst. by exists (Fork Box m). }
  { move=>Θ Γ Δ r1 r2 A B m m' xor erm ihm m0 ξ e. destruct m0; inv e.
    have[m e]:=ihm _ _ erefl. subst. by exists (Recv0 m). }
  { move=>Θ Γ Δ r1 r2 A B m m' xor erm ihm m0 ξ e. destruct m0; inv e.
    have[m e]:=ihm _ _ erefl. subst. by exists (Recv1 m). }
  { move=>Θ Γ Δ r1 r2 A B m m' xor erm ihm m0 ξ e. destruct m0; inv e.
    have[m e]:=ihm _ _ erefl. subst. by exists (Send0 m). }
  { move=>Θ Γ Δ r1 r2 A B m m' xor erm ihm m0 ξ e. destruct m0; inv e.
    have[m e]:=ihm _ _ erefl. subst. by exists (Send1 m). }
  { move=>Θ Γ Δ m m' erm ihm m0 ξ e. destruct m0; inv e.
    have[m e]:=ihm _ _ erefl. subst. by exists (Wait m). }
  { move=>Θ Γ Δ m m' erm ihm m0 ξ e. destruct m0; inv e.
    have[m e]:=ihm _ _ erefl. subst. by exists (Close m). }
Qed.
