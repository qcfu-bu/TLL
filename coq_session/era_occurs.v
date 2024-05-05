From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq zify.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS dyn_occurs era_subst.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma era_dyn_occurs Θ Γ Δ m m' A i x :
  Θ ; Γ ; Δ ⊢ m ~ m' : A -> dyn_occurs i m = x -> dyn_occurs i m' = x. 
Proof.
  move=>er. elim: er i x=>{Θ Γ Δ m m' A}//=.
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m m' n n' s mrg1 mrg2 erm ihm ern ihn i x.
    move e1:(dyn_occurs i m)=>v1.
    move e2:(dyn_occurs i n)=>v2 e0.
    have->:=ihm _ _ e1.
    have->:=ihn _ _ e2.
    by []. }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m m' n n' t mrg1 mrg2 tyS erm ihm ern ihn i x.
    move e1:(dyn_occurs i m)=>v1.
    move e2:(dyn_occurs i n)=>v2 e0.
    have->:=ihm _ _ e1.
    have->:=ihn _ _ e2.
    by []. }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m m' n n' s r t mrg1 mrg2 tyS erm ihm ern ihn i x.
    move e1:(dyn_occurs i m)=>v1.
    move e2:(dyn_occurs i n)=>v2 e0.
    have->:=ihm _ _ e1.
    have->:=ihn _ _ e2.
    by []. }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m m' n n' s r1 r2 t mrg1 mrg2 tyS erm ihm ern ihn i x.
    move e1:(dyn_occurs i m)=>v1.
    move e2:(dyn_occurs i n)=>v2 e0.
    have->:=ihm _ _ e1.
    have->:=ihn _ _ e2.
    by []. }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m m' n1 n1' n2 n2' s mrg1 mrg2 tyA erm ihm ern1 ihn1 ern2 ihn2 i x.
    move e1:(dyn_occurs i m)=>v1.
    move e2:(dyn_occurs i n1)=>v2.
    move e3:(dyn_occurs i n2)=>v3 e0.
    have->:=ihm _ _ e1.
    have->:=ihn1 _ _ e2.
    have->:=ihn2 _ _ e3.
    by []. }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m m' n n' A B s t mrg1 mrg2 tyB erm ihm ern ihn i x.
    move e1:(dyn_occurs i m)=>v1.
    move e2:(dyn_occurs i n)=>v2 e0.
    have->:=ihm _ _ e1.
    have->:=ihn _ _ e2.
    by []. }
Qed.
  
Lemma era_type_occurs0 Θ Γ Δ m m' A i :
  Θ ; Γ ; Δ ⊢ m ~ m' : A -> cvar_pos Θ i false ->
  dyn_occurs i m = 0 /\ dyn_occurs i m' = 0.
Proof with eauto using era_dyn_occurs.
  move=>erm h.
  have oc:=dyn_type_occurs0 (era_dyn_type erm) h.
  split...
Qed.

Lemma era_type_occurs1 Θ Γ Δ m m' A i :
  Θ ; Γ ; Δ ⊢ m ~ m' : A -> cvar_pos Θ i true ->
  dyn_occurs i m = 1 /\ dyn_occurs i m' = 1.
Proof with eauto using era_dyn_occurs.
  move=>erm h.
  have oc:=dyn_type_occurs1 (era_dyn_type erm) h.
  split...
Qed.

Lemma era_occurs_iren Θ Γ Δ m m' A i ξ :
  Θ ; Γ ; Δ ⊢ cren ξ m ~ cren ξ m' : A -> iren i ξ ->
  dyn_occurs i (cren ξ m) = 0 /\ dyn_occurs i (cren ξ m') = 0.
Proof with eauto using era_dyn_occurs.
  move=>erm h.
  have oc:=dyn_occurs_iren (era_dyn_type erm) h.
  split...
Qed.

Lemma era_occurs_cren_id Θ Γ Δ m m' A i j ξ :
  Θ ; Γ ; Δ ⊢ cren ξ m ~ cren ξ m' : A ->
  dyn_occurs i m = 0 ->
  dyn_occurs j m = 0 ->
  dyn_occurs i m' = 0 ->
  dyn_occurs j m' = 0 ->
  (forall x, x == i = false -> x == j = false -> ξ x = x) ->
  Θ ; Γ ; Δ ⊢ m ~ m' : A.
Proof with eauto using era_type.
  move e1:(cren ξ m)=>m1.
  move e2:(cren ξ m')=>m2 er.
  elim: er m m' ξ e1 e2 i j=>{Θ Γ Δ m1 m2 A}.
  { move=>Θ Γ Δ x s A emp wf shs dhs m m' ξ e1 e2 i j oc1 oc2 oc3 oc4 h0.
    destruct m; inv e1. destruct m'; inv e2... }
  { move=>Θ Γ Δ A B m m' s k1 k2 tym ihm m1 m2 ξ e1 e2 i j oc1 oc2 oc3 oc4 h.
    destruct m1; inv e1. destruct m2; inv e2. destruct m2; inv H0.
    simpl in oc1, oc2, oc3, oc4.
    have[r tyB]:=era_valid tym.
    have wf:=sta_type_wf tyB. inv wf.
    apply: era_conv.
    apply: sta_conv_pi0.
    apply: conv_sym.
    apply: sta_cren_conv0...
    eauto.
    econstructor...
    apply: era_ctx_conv0.
    apply: conv_sym.
    apply: sta_cren_conv0...
    apply: sta_crename_inv...
    apply: (ihm _ _ _ erefl erefl _ _ oc1 oc2 oc3 oc4 h).
    econstructor... }
  { move=>Θ Γ Δ A B m m' s t k1 k2 tym ihm m1 m2 ξ e1 e2 i j oc1 oc2 oc3 oc4 h.
    destruct m1; inv e1. destruct m2; inv e2. destruct m2; inv H0.
    simpl in oc1, oc2, oc3, oc4.
    have[r tyB]:=era_valid tym.
    have wf:=era_type_wf tym. inv wf.
    apply: era_conv.
    apply: sta_conv_pi1.
    apply: conv_sym.
    apply: sta_cren_conv0...
    eauto.
    econstructor...
    apply: era_ctx_conv1.
    apply: conv_sym.
    apply: sta_cren_conv0...
    apply: sta_crename_inv...
    apply: (ihm _ _ _ erefl erefl _ _ oc1 oc2 oc3 oc4 h).
    econstructor... }
  { move=>Θ Γ Δ A B m m' n s tym ihm tyn m1 m2 ξ e1 e2 i j oc1 oc2 oc3 oc4 h.
    destruct m1; inv e1. destruct m2; inv e2. destruct m2_2; inv H1.
    simpl in oc1, oc2, oc3, oc4.
    have[r tyP]:=era_valid tym.
    have[t[tyB/sort_inj e]]:=sta_pi0_inv tyP. subst.
    apply: era_conv.
    apply: sta_conv_beta.
    apply: conv_sym.
    apply: sta_cren_conv0...
    econstructor...
    apply: sta_crename_inv...
    have:=sta_subst tyB tyn... }
  { move=>Θ1 Θ2 θ Γ Δ1 Δ2 Δ A B m m' n n' s mrg1 mrg2
           tym ihm tyn ihn m1 m2 ξ e1 e2 i j oc1 oc2 oc3 oc4 h.
    destruct m1; inv e1. destruct m2; inv e2.
    simpl in oc1, oc2, oc3, oc4.
    have[r tyP]:=era_valid tym.
    have[t[tyB/sort_inj e]]:=sta_pi1_inv tyP. subst.
    move:oc1. case_eq (dyn_occurs i m1_1); case_eq (dyn_occurs i m1_2)=>//e1 e2 _.
    move:oc2. case_eq (dyn_occurs j m1_1); case_eq (dyn_occurs j m1_2)=>//e3 e4 _.
    move:oc3. case_eq (dyn_occurs i m2_1); case_eq (dyn_occurs i m2_2)=>//e5 e6 _.
    move:oc4. case_eq (dyn_occurs j m2_1); case_eq (dyn_occurs j m2_2)=>//e7 e8 _.
    apply: era_conv.
    apply: sta_conv_beta.
    apply: conv_sym.
    apply: sta_cren_conv0...
    econstructor...
    have:=sta_subst tyB (era_sta_type tyn)... }
  { move=>Θ Γ Δ A B m n n' t tyS tym tyn ihn m1 m2 ξ e1 e2 i j oc1 oc2 oc3 oc4 h.
    destruct m1; inv e1. destruct m2; inv e2. destruct m2_1; inv H0.
    simpl in oc1, oc2, oc3, oc4.
    have[s[r[ord[tyA[tyB _]]]]]:=sta_sig0_inv tyS.
    econstructor...
    apply: sta_crename_inv...
    apply: era_conv.
    apply: sta_conv_beta.
    apply: sta_cren_conv0...
    apply: (ihn _ _ _ erefl erefl _ _ oc1 oc2 oc3 oc4 h).
    have/=:=sta_subst tyB (sta_crename_inv tym)... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m m' n n' t mrg1 mrg2
           tyS tym ihm tyn ihn m1 m2 ξ e1 e2 i j oc1 oc2 oc3 oc4 h.
    destruct m1; inv e1. destruct m2; inv e2.
    simpl in oc1, oc2, oc3, oc4.
    have[s[r[ord1[ord2[tyA[tyB _]]]]]]:=sta_sig1_inv tyS.
    move:oc1. case_eq (dyn_occurs i m1_1); case_eq (dyn_occurs i m1_2)=>//e1 e2 _.
    move:oc2. case_eq (dyn_occurs j m1_1); case_eq (dyn_occurs j m1_2)=>//e3 e4 _.
    move:oc3. case_eq (dyn_occurs i m2_1); case_eq (dyn_occurs i m2_2)=>//e5 e6 _.
    move:oc4. case_eq (dyn_occurs j m2_1); case_eq (dyn_occurs j m2_2)=>//e7 e8 _.
    econstructor...
    apply: era_conv.
    apply: sta_conv_beta.
    apply: sta_cren_conv0...
    apply: (ihn _ _ _ erefl erefl _ _ e1 e3 e5 e7 h).
    have/=:=sta_subst tyB (sta_crename_inv (era_sta_type tym))... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m m' n n' s r t mrg1 mrg2
           tyC tym ihm tyn ihn m1 m2 ξ e1 e2 i j oc1 oc2 oc3 oc4 h.
    destruct m1; inv e1. destruct m2; inv e2. destruct A1; inv H0.
    simpl in oc1, oc2, oc3, oc4.
    have tyA0:=sta_crename_inv tyC.
    move:oc1. case_eq (dyn_occurs i m1); case_eq (dyn_occurs i n0)=>//e1 e2 _.
    move:oc2. case_eq (dyn_occurs j m1); case_eq (dyn_occurs j n0)=>//e3 e4 _.
    move:oc3. case_eq (dyn_occurs i m2); case_eq (dyn_occurs i n)=>//e5 e6 _.
    move:oc4. case_eq (dyn_occurs j m2); case_eq (dyn_occurs j n)=>//e7 e8 _.
    have wf:=sta_type_wf tyA0. inv wf.
    have[s1[r1[ord[tyA[tyB/sort_inj e]]]]]:=sta_sig0_inv H2. subst.
    have agr:sta_agree_subst (B :: A :: Γ) (Pair0 (Var 1) (Var 0) t .: ren (+2)) (Sig0 A B t :: Γ).
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
    have eq: A0.[m1/] ≃ (cren ξ A0).[cren ξ m1/].
    apply: conv_trans.
    apply: sta_conv_beta.
    apply: conv_sym.
    apply: sta_cren_conv0...
    apply: sta_conv_subst.
    apply: conv_sym.
    apply: sta_cren_conv0...
    apply: era_conv...
    econstructor...
    apply: era_conv.
    apply: sta_conv_subst.
    apply: sta_cren_conv0...
    apply: (ihn _ _ _ erefl erefl _ _ e1 e3 e5 e7 h).
    have/=:=sta_substitution tyA0 agr...
    have/=:=sta_subst tyC (era_sta_type tym)... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m m' n n' s r1 r2 t mrg1 mrg2
           tyC tym ihm tyn ihn m1 m2 ξ e1 e2 i j oc1 oc2 oc3 oc4 h.
    destruct m1; inv e1. destruct m2; inv e2. destruct A1; inv H0.
    simpl in oc1, oc2, oc3, oc4.
    have tyA0:=sta_crename_inv tyC.
    move:oc1. case_eq (dyn_occurs i m1); case_eq (dyn_occurs i n0)=>//e1 e2 _.
    move:oc2. case_eq (dyn_occurs j m1); case_eq (dyn_occurs j n0)=>//e3 e4 _.
    move:oc3. case_eq (dyn_occurs i m2); case_eq (dyn_occurs i n)=>//e5 e6 _.
    move:oc4. case_eq (dyn_occurs j m2); case_eq (dyn_occurs j n)=>//e7 e8 _.
    have wf:=sta_type_wf tyA0. inv wf.
    have[s1[t1[ord1[ord[tyA[tyB/sort_inj e]]]]]]:=sta_sig1_inv H2. subst.
    have agr:sta_agree_subst (B :: A :: Γ) (Pair1 (Var 1) (Var 0) t .: ren (+2)) (Sig1 A B t :: Γ).
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
    have eq: A0.[m1/] ≃ (cren ξ A0).[cren ξ m1/].
    apply: conv_trans.
    apply: sta_conv_beta.
    apply: conv_sym.
    apply: sta_cren_conv0...
    apply: sta_conv_subst.
    apply: conv_sym.
    apply: sta_cren_conv0...
    apply: era_conv...
    apply: era_letin1...
    apply: era_conv.
    apply: sta_conv_subst.
    apply: sta_cren_conv0...
    apply: (ihn _ _ _ erefl erefl _ _ e1 e3 e5 e7 h).
    have/=:=sta_substitution tyA0 agr...
    have/=:=sta_subst tyC (era_sta_type tym)... }
  { move=>Θ Γ Δ emp wf k m1 m2 ξ e1 e2 i j oc1 oc2 oc3 oc4 h.
    destruct m1; inv e1. destruct m2; inv e2.
    simpl in oc1, oc2, oc3, oc4... }
  { move=>Θ Γ Δ emp wf k m1 m2 ξ e1 e2 i j oc1 oc2 oc3 oc4 h.
    destruct m1; inv e1. destruct m2; inv e2.
    simpl in oc1, oc2, oc3, oc4... }
  { move=>Θ Γ Δ emp wf k m1 m2 ξ e1 e2 i j oc1 oc2 oc3 oc4 h.
    destruct m1; inv e1. destruct m2; inv e2.
    simpl in oc1, oc2, oc3, oc4... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m m' n1 n1' n2 n2' s mrg1 mrg2 tyA
           tym ihm tyn1 ihn1 tyn2 ihn2 m1 m2 ξ e1 e2 i j oc1 oc2 oc3 oc4 h.
    destruct m1; inv e1. destruct m2; inv e2. destruct A; inv H0.
    simpl in oc1, oc2, oc3, oc4.
    have wf:=sta_type_wf tyA. inv wf.
    move:oc1.
    case_eq (dyn_occurs i m1_1);
      case_eq (dyn_occurs i m1_2);
      case_eq (dyn_occurs i m1_3)=>//=.
    2:{ move=>n1 e1 n2 e2 e3 e4.
        rewrite maxnSS in e4. inv e4. }
    move=>e11 e12 e13 _.
    move:oc2.
    case_eq (dyn_occurs j m1_1);
      case_eq (dyn_occurs j m1_2);
      case_eq (dyn_occurs j m1_3)=>//=.
    2:{ move=>n1 e1 n2 e2 e3 e4.
        rewrite maxnSS in e4. inv e4. }
    move=>e21 e22 e23 _.
    move:oc3.
    case_eq (dyn_occurs i m2_1);
      case_eq (dyn_occurs i m2_2);
      case_eq (dyn_occurs i m2_3)=>//=.
    2:{ move=>n1 e1 n2 e2 e3 e4.
        rewrite maxnSS in e4. inv e4. }
    move=>e31 e32 e33 _.
    move:oc4.
    case_eq (dyn_occurs j m2_1);
      case_eq (dyn_occurs j m2_2);
      case_eq (dyn_occurs j m2_3)=>//=.
    2:{ move=>n1 e1 n2 e2 e3 e4.
        rewrite maxnSS in e4. inv e4. }
    move=>e41 e42 e43 _.
    have{}ihm:=ihm _ _ _ erefl erefl _ _ e13 e23 e33 e43 h.
    have{}ihn1:=ihn1 _ _ _ erefl erefl _ _ e12 e22 e32 e42 h.
    have{}ihn2:=ihn2 _ _ _ erefl erefl _ _ e11 e21 e31 e41 h.
    have eq: A0.[m1_1/] ≃ (cren ξ A0).[cren ξ m1_1/].
    apply: conv_trans.
    apply: sta_conv_beta.
    apply: conv_sym.
    apply: sta_cren_conv0...
    apply: sta_conv_subst.
    apply: conv_sym.
    apply: sta_cren_conv0...
    apply: era_conv...
    econstructor...
    apply: sta_crename_inv...
    apply: era_conv.
    apply: sta_conv_subst.
    apply: sta_cren_conv0...
    eauto.
    have/=:=sta_subst (sta_crename_inv tyA) (sta_tt H1)...
    apply: era_conv.
    apply: sta_conv_subst.
    apply: sta_cren_conv0...
    eauto.
    have/=:=sta_subst (sta_crename_inv tyA) (sta_ff H1)...
    have/=:=sta_subst tyA (era_sta_type tym)... }
  { move=>Θ Γ Δ m m' A erm ihm m1 m2 ξ e1 e2 i j oc1 oc2 oc3 oc4 h.
    destruct m1; inv e1. destruct m2; inv e2.
    simpl in oc1, oc2, oc3, oc4.
    have{}ihm:=ihm _ _ _ erefl erefl i j oc1 oc2 oc3 oc4 h... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m m' n n' A B s t mrg1 mrg2
           tyB tym ihm tyn ihn m1 m2 ξ e1 e2 i j oc1 oc2 oc3 oc4 h.
    destruct m1; inv e1. destruct m2; inv e2.
    simpl in oc1, oc2, oc3, oc4.
    move:oc1. case_eq (dyn_occurs i m1); case_eq (dyn_occurs i n0)=>//e1 e2 _.
    move:oc2. case_eq (dyn_occurs j m1); case_eq (dyn_occurs j n0)=>//e3 e4 _.
    move:oc3. case_eq (dyn_occurs i m2); case_eq (dyn_occurs i n)=>//e5 e6 _.
    move:oc4. case_eq (dyn_occurs j m2); case_eq (dyn_occurs j n)=>//e7 e8 _.
    have{}ihm:=ihm _ _ _ erefl erefl _ _ e2 e4 e6 e8 h.
    have{}ihn:=ihn _ _ _ erefl erefl _ _ e1 e3 e5 e7 h.
    econstructor... }
  { move=>Θ Γ Δ r x A js wf k tyA m1 m2 ξ e1 e2 i j oc1 oc2 oc3 oc4 h.
    destruct m1; inv e1. destruct m2; inv e2.
    simpl in oc1, oc2, oc3, oc4.
    move: oc1 oc2 oc3 oc4=>/=.
    case_eq (x0 == i); case_eq (x0 == j)=>// e1 e2 _ _.
    case_eq (x == i); case_eq (x == j)=>// e3 e4 _ _.
    move:H0. have->:=h _ e2 e1. have->:=h _ e4 e3. move=>->.
    econstructor...
    rewrite h in js... }
  { move=>Θ Γ Δ m m' A erm ihm m1 m2 ξ e1 e2 i j oc1 oc2 oc3 oc4 h.
    destruct m1; inv e1. destruct m2; inv e2. destruct m2; inv H0.
    simpl in oc1, oc2, oc3, oc4.
    have wf:=era_type_wf erm. inv wf.
    have[tym1 _]:=sta_ch_inv H4.
    have{}ihm:=ihm _ _ _ erefl erefl _ _ oc1 oc2 oc3 oc4 h.
    apply: era_conv.
    apply: sta_conv_io.
    apply: sta_conv_ch.
    apply: conv_sym.
    apply: sta_cren_conv0...
    2:{ econstructor. constructor... }
    constructor.
    apply: era_ctx_conv1.
    apply: conv_sym.
    apply: sta_conv_ch.
    apply (sta_cren_conv0 ξ (convR _ _)).
    constructor.
    apply: sta_crename_inv...
    apply: ihm. }
  { move=>Θ Γ Δ r1 r2 A B m m' xor erm ihm m1 m2 ξ e1 e2 i j oc1 oc2 oc3 oc4 h.
    destruct m1; inv e1. destruct m2; inv e2... }
  { move=>Θ Γ Δ r1 r2 A B m m' xor erm ihm m1 m2 ξ e1 e2 i j oc1 oc2 oc3 oc4 h.
    destruct m1; inv e1. destruct m2; inv e2... }
  { move=>Θ Γ Δ r1 r2 A B m m' xor erm ihm m1 m2 ξ e1 e2 i j oc1 oc2 oc3 oc4 h.
    destruct m1; inv e1. destruct m2; inv e2... }
  { move=>Θ Γ Δ r1 r2 A B m m' xor erm ihm m1 m2 ξ e1 e2 i j oc1 oc2 oc3 oc4 h.
    destruct m1; inv e1. destruct m2; inv e2... }
  { move=>Θ Γ Δ m m' erm ihm m1 m2 ξ e1 e2 i j oc1 oc2 oc3 oc4 h.
    destruct m1; inv e1. destruct m2; inv e2... }
  { move=>Θ Γ Δ m m' erm ihm m1 m2 ξ e1 e2 i j oc1 oc2 oc3 oc4 h.
    destruct m1; inv e1. destruct m2; inv e2... }
  { move=>Θ Γ Δ A B m m' s eq erm ihm tyB m1 m2 ξ e1 e2 i j oc1 oc2 oc3 oc4 h.
    have{}ihm:=ihm _ _ _ e1 e2 i j oc1 oc2 oc3 oc4 h.
    apply: era_conv... }
Qed.
