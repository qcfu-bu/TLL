From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS tll_cren sta_valid.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma sta_cren_pstep0 m n ξ : m ≈> n -> cren ξ m ≈> n.
Proof with eauto using sta_pstep. move=>st. elim: st ξ=>//={m n}... Qed.

Lemma sta_cren_pstep m n ξ : m ≈> n -> cren ξ m ≈> cren ξ n.
Proof with eauto using sta_pstep.
  move=>st. elim: st ξ=>//={m n}...
  { move=>A m m' n n' s pm ihm pn ihn ξ.
    rewrite term_cren_beta1.
    constructor... }
  { move=>A m m' n n' s pm ihm pn ihn ξ.
    rewrite term_cren_beta1.
    constructor... }
  { move=>A m1 m1' m2 m2' n n' s pm1 ihm1 pm2 ihm2 pn ihn ξ.
    rewrite term_cren_beta2.
    constructor... }
  { move=>A m1 m1' m2 m2' n n' s pm1 ihm1 pm2 ihm2 pn ihn ξ.
    rewrite term_cren_beta2.
    constructor... }
  { move=>A A' m m' pA ihA pm ihm ξ.
    rewrite term_cren_beta1.
    constructor... }
  { move=>m m' n n' pm ihm pn ihn ξ.
    rewrite term_cren_beta1.
    constructor... }
Qed.

Lemma sta_cren_pred0 m n ξ : m ≈>* n -> cren ξ m ≈>* n.
Proof with eauto using sta_pstep.
  move=>rd. elim: rd ξ=>{n}...
  move=>ξ. apply: star1. apply: sta_cren_pstep0...
  move=>y z rd ih st ξ.
  apply: starSE...
Qed.

Lemma sta_cren_pred m n ξ : m ≈>* n -> cren ξ m ≈>* cren ξ n.
Proof with eauto using sta_pstep.
  move=>rd. elim: rd ξ=>{n}...
  move=>y z rd ih st ξ.
  apply: starSE.
  apply: ih.
  by apply: sta_cren_pstep.
Qed.

Lemma sta_cren_conv0 m n ξ : m ≃ n -> cren ξ m ≃ n.
Proof with eauto using sta_pstep.
  move=>rd. elim: rd ξ=>{n}...
  { move=>ξ. apply: conv1. apply:sta_cren_pstep0... }
  { move=>y z rd ih st ξ.
    by apply: convSE. }
  { move=>y z rd ih st ξ.
    apply: conv_trans.
    apply: ih.
    by apply: conv1i. }
Qed.

Lemma sta_cren_conv m n ξ : m ≃ n -> cren ξ m ≃ cren ξ n.
Proof with eauto using sta_pstep.
  move=>rd. elim: rd ξ=>{n}...
  { move=>y z rd ih st ξ.
    apply: convSE.
    apply: ih.
    by apply: sta_cren_pstep. }
  { move=>y z rd ih st ξ.
    apply: conv_trans.
    apply: ih.
    apply: conv1i.
    by apply: sta_cren_pstep. }
Qed.

Lemma sta_cren_arity_proto A ξ : arity_proto A -> arity_proto (cren ξ A).
Proof with eauto. elim: A ξ=>//=. Qed.

Lemma sta_cren_guarded i m ξ : guarded i m -> guarded i (cren ξ m).
Proof with eauto.
  elim: m i ξ=>//=...
  all: try solve[intros;
                 repeat match goal with
                 | [ H : _ /\ _ |- _ ] => inv H; split; eauto
                 end].
Qed.

Lemma sta_crename Γ m A ξ :
  Γ ⊢ m : A -> Γ ⊢ cren ξ m : A.
Proof with eauto using sta_type, sta0_sta_wf.
  move=>ty. have{}ty:=sta_sta0_type ty.
  elim: ty ξ=>//={Γ m A}...
  { move=>Γ A B s r t/sta0_sta_type tyA ihA/sta0_sta_type tyB ihB ξ.
    econstructor...
    apply: sta_ctx_conv.
    apply: sta_cren_conv0...
    all: eauto. }
  { move=>Γ A B s r t/sta0_sta_type tyA ihA/sta0_sta_type tyB ihB ξ.
    econstructor...
    apply: sta_ctx_conv.
    apply: sta_cren_conv0...
    all: eauto. }
  { move=>Γ A B m s r/sta0_sta_type tyA ihA/sta0_sta_type tym ihm ξ.
    have[t tyB]:=sta_valid tym.
    econstructor.
    apply: sta_conv_pi0.
    apply: sta_cren_conv0.
    apply: ξ.
    eauto.
    eauto.
    constructor.
    apply: sta_ctx_conv.
    apply: sta_cren_conv0...
    eauto.
    eauto.
    econstructor... }
  { move=>Γ A B m s r/sta0_sta_type tyA ihA/sta0_sta_type tym ihm ξ.
    have[t tyB]:=sta_valid tym.
    econstructor.
    apply: sta_conv_pi1.
    apply: sta_cren_conv0.
    apply: ξ.
    eauto.
    eauto.
    constructor.
    apply: sta_ctx_conv.
    apply: sta_cren_conv0...
    eauto.
    eauto.
    econstructor... }
  { move=>Γ A B m n s/sta0_sta_type tym ihm/sta0_sta_type tyn ihn ξ.
    have[r tyPi0]:=sta_valid tym.
    have[t[tyB/sort_inj e]]:=sta_pi0_inv tyPi0. subst.
    have/=tyBn:=sta_subst tyB tyn.
    apply: sta_conv.
    apply: sta_conv_beta.
    apply: sta_cren_conv0...
    econstructor...
    eauto. }
  { move=>Γ A B m n s/sta0_sta_type tym ihm/sta0_sta_type tyn ihn ξ.
    have[r tyPi1]:=sta_valid tym.
    have[t[tyB/sort_inj e]]:=sta_pi1_inv tyPi1. subst.
    have/=tyBn:=sta_subst tyB tyn.
    apply: sta_conv.
    apply: sta_conv_beta.
    apply: sta_cren_conv0...
    econstructor...
    eauto. }
  { move=>Γ A B s r t ord/sta0_sta_type tyA ihA/sta0_sta_type tyB ihB ξ.
    econstructor...
    apply: sta_ctx_conv.
    apply: sta_cren_conv0...
    all: eauto. }
  { move=>Γ A B s r t ord1 ord2/sta0_sta_type tyA ihA/sta0_sta_type tyB ihB ξ.
    econstructor.
    apply: ord1.
    apply: ord2.
    eauto.
    apply: sta_ctx_conv.
    apply: sta_cren_conv0...
    all: eauto. }
  { move=>Γ A B m n t/sta0_sta_type tyS ihS/sta0_sta_type tym ihm/sta0_sta_type tyn ihn ξ.
    have[s[r[ord[tyA[tyB _]]]]]:=sta_sig0_inv tyS.
    have/=tyBm:=sta_subst tyB (ihm ξ).
    econstructor...
    apply: sta_conv.
    apply: sta_conv_beta.
    apply: conv_sym.
    apply: sta_cren_conv0...
    eauto.
    eauto. }
  { move=>Γ A B m n t/sta0_sta_type tyS ihS/sta0_sta_type tym ihm/sta0_sta_type tyn ihn ξ.
    have[s[r[ord1[ord2[tyA[tyB _]]]]]]:=sta_sig1_inv tyS.
    have/=tyBm:=sta_subst tyB (ihm ξ).
    econstructor...
    apply: sta_conv.
    apply: sta_conv_beta.
    apply: conv_sym.
    apply: sta_cren_conv0...
    eauto.
    eauto. }
  { move=>Γ A B C m n s t/sta0_sta_type tyS ihS/sta0_sta_type tym ihm/sta0_sta_type tyn ihn ξ.
    have wf:=sta_type_wf tyS. inv wf.
    have[s1[r[ord[tyA[tyB/sort_inj e]]]]]:=sta_sig0_inv H2. subst.
    have eq: (cren ξ C).[cren ξ m/] ≃ C.[m/].
    apply: conv_trans.
    apply: sta_conv_beta.
    apply: sta_cren_conv0...
    apply: conv_trans.
    apply: sta_conv_subst.
    apply: sta_cren_conv0...
    eauto.
    apply: sta_conv...
    econstructor...
    apply: sta_conv.
    erewrite<-term_cren_subst.
    apply: conv_sym.
    apply: sta_cren_conv0...
    2:{ apply: ihn. }
    move=>[|x]/=...
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
    have//=:=sta_substitution (ihS ξ) agr.
    eauto.
    have//=:=sta_subst tyS tym... }
  { move=>Γ A B C m n s t/sta0_sta_type tyS ihS/sta0_sta_type tym ihm/sta0_sta_type tyn ihn ξ.
    have wf:=sta_type_wf tyS. inv wf.
    have[s1[r[ord1[ord2[tyA[tyB/sort_inj e]]]]]]:=sta_sig1_inv H2. subst.
    have eq: (cren ξ C).[cren ξ m/] ≃ C.[m/].
    apply: conv_trans.
    apply: sta_conv_beta.
    apply: sta_cren_conv0...
    apply: conv_trans.
    apply: sta_conv_subst.
    apply: sta_cren_conv0...
    eauto.
    apply: sta_conv...
    apply: sta_letin1...
    apply: sta_conv.
    erewrite<-term_cren_subst.
    apply: conv_sym.
    apply: sta_cren_conv0...
    2:{ apply: ihn. }
    move=>[|x]/=...
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
    have//=:=sta_substitution (ihS ξ) agr.
    eauto.
    have//=:=sta_subst tyS tym... }
  { move=>Γ A m ar gr s/sta0_sta_type tyA ihA/sta0_sta_type tym ihm ξ.
    apply: sta_conv.
    apply: sta_cren_conv0...
    constructor.
    apply: sta_cren_arity_proto...
    apply: sta_cren_guarded...
    apply: sta_ctx_conv.
    apply: sta_cren_conv0...
    apply: ihA.
    apply: sta_conv.
    apply: sta_conv_subst.
    apply: conv_sym.
    apply: sta_cren_conv0...
    apply: ihm.
    have//=:=sta_weaken (ihA ξ) tyA...
    eauto. }
  { move=>Γ A m n1 n2 s/sta0_sta_type tyA ihA/sta0_sta_type tym ihm
           /sta0_sta_type tyn1 ihn1/sta0_sta_type tyn2 ihn2 ξ.
    have wf:=sta_type_wf tym.
    have eq:(cren ξ A).[cren ξ m/] ≃ A.[m/].
    apply: conv_trans.
    apply: sta_conv_beta.
    apply: sta_cren_conv0...
    apply: sta_conv_subst.
    apply: sta_cren_conv0...
    apply: sta_conv...
    econstructor...
    apply: sta_conv.
    apply: sta_conv_subst.
    apply: conv_sym.
    apply: sta_cren_conv0...
    eauto.
    have//=:=sta_subst (ihA ξ) (sta_tt wf)...
    apply: sta_conv.
    apply: sta_conv_subst.
    apply: conv_sym.
    apply: sta_cren_conv0...
    eauto.
    have//=:=sta_subst (ihA ξ) (sta_ff wf)...
    have//=:=sta_subst tyA tym... }
  { move=>Γ m n A B s/sta0_sta_type tyB ihB/sta0_sta_type tym ihm/sta0_sta_type tyn ihn ξ.
    econstructor... }
  { move=>Γ r A B s/sta0_sta_type tyA ihA/sta0_sta_type tyB ihB ξ.
    econstructor.
    apply: sta_ctx_conv.
    apply: sta_cren_conv0...
    apply: ihA.
    apply: ihB. }
  { move=>Γ r A B s/sta0_sta_type tyA ihA/sta0_sta_type tyB ihB ξ.
    econstructor.
    apply: sta_ctx_conv.
    apply: sta_cren_conv0...
    apply: ihA.
    apply: ihB. }
  { move=>Γ r x A/sta0_sta_wf wf/sta0_sta_type tyA ihA ξ.
    econstructor... }
  { move=>Γ A m s/sta0_sta_type tyCh ihCh/sta0_sta_type tym ihm ξ.
    have[tyA _]:=sta_ch_inv tyCh.
    apply: sta_conv.
    apply: sta_conv_io.
    apply: sta_conv_ch.
    apply: sta_cren_conv0...
    econstructor.
    apply: sta_ctx_conv.
    apply: sta_conv_ch.
    apply: sta_cren_conv0...
    all: eauto.
    econstructor.
    econstructor... }
  { move=>Γ A B m s eq1/sta0_sta_type tym ihm/sta0_sta_type tyB ihB ξ.
    apply: sta_conv.
    apply: eq1.
    all: eauto. }
Qed.

Lemma sta_ecrename Γ m m' A ξ :
  m' = cren ξ m ->
  Γ ⊢ m : A -> Γ ⊢ m' : A.
Proof. move=>->. apply: sta_crename. Qed.

Ltac sta0_to_sta :=
  repeat match goal with
    | [ H : sta0_wf _ |- _ ] => apply sta0_sta_wf in H
    | [ H : sta0_type _ _ _ |- _ ] => apply sta0_sta_type in H
    end.

Lemma sta_cren_arity_proto_inv A ξ : arity_proto (cren ξ A) -> arity_proto A.
Proof with eauto. elim: A ξ=>//. Qed.

Lemma sta_cren_guarded_inv i m ξ : guarded i (cren ξ m) -> guarded i m.
Proof with eauto.
  elim: m i ξ=>//=...
  all: try solve[intros;
                 repeat match goal with
                 | [ H : _ /\ _ |- _ ] => inv H; split; eauto
                 end].
Qed.

Lemma sta_crename_inv Γ m A ξ :
  Γ ⊢ cren ξ m : A -> Γ ⊢ m : A.
Proof with eauto using sta_type, sta0_sta_wf.
  move e:(cren ξ m)=>n/sta_sta0_type ty.
  elim: ty m ξ e=>//={Γ n A}...
  all: try solve[intros; sta0_to_sta;
                 match goal with
                 | [ H : cren _ ?m = _ |- _ ] =>
                     destruct m; inv H; eauto using sta_type, sta_wf
                 end].
  { move=>Γ A B s r t tyA ihA tyB ihB m ξ e. sta0_to_sta.
    destruct m ; inv e.
    econstructor...
    apply: sta_ctx_conv.
    apply: conv_sym.
    apply: sta_cren_conv0...
    apply: ihA...
    eauto. }
  { move=>Γ A B s r t tyA ihA tyB ihB m ξ e. sta0_to_sta.
    destruct m ; inv e.
    econstructor...
    apply: sta_ctx_conv.
    apply: conv_sym.
    apply: sta_cren_conv0...
    apply: ihA...
    eauto. }
  { move=>Γ A B m s r tyA ihA tym ihm m0 ξ e. sta0_to_sta.
    destruct m0; inv e.
    have[s0 tyB]:=sta_valid tym.
    apply: sta_conv.
    apply: sta_conv_pi0.
    apply: conv_sym.
    apply: sta_cren_conv0...
    eauto.
    econstructor.
    apply: sta_ctx_conv.
    apply: conv_sym.
    apply: sta_cren_conv0...
    apply: ihA...
    apply: ihm...
    econstructor... }
  { move=>Γ A B m s r tyA ihA tym ihm m0 ξ e. sta0_to_sta.
    destruct m0; inv e.
    have[s0 tyB]:=sta_valid tym.
    apply: sta_conv.
    apply: sta_conv_pi1.
    apply: conv_sym.
    apply: sta_cren_conv0...
    eauto.
    econstructor.
    apply: sta_ctx_conv.
    apply: conv_sym.
    apply: sta_cren_conv0...
    apply: ihA...
    apply: ihm...
    econstructor... }
  { move=>Γ A B m n s tym ihm tyn ihn m0 ξ e. sta0_to_sta.
    destruct m0; inv e.
    have[s0 tyP]:=sta_valid tym.
    have[t[tyB/sort_inj e]]:=sta_pi0_inv tyP. subst.
    apply: sta_conv.
    apply: sta_conv_beta.
    apply: conv_sym.
    apply: sta_cren_conv0...
    econstructor...
    have/=:=sta_subst tyB tyn... }
  { move=>Γ A B m n s tym ihm tyn ihn m0 ξ e. sta0_to_sta.
    destruct m0; inv e.
    have[s0 tyP]:=sta_valid tym.
    have[t[tyB/sort_inj e]]:=sta_pi1_inv tyP. subst.
    apply: sta_conv.
    apply: sta_conv_beta.
    apply: conv_sym.
    apply: sta_cren_conv0...
    econstructor...
    have/=:=sta_subst tyB tyn... }
  { move=>Γ A B s r t ord tyA ihA tyB ihB m ξ e. sta0_to_sta.
    destruct m; inv e.
    econstructor...
    apply: sta_ctx_conv.
    apply: conv_sym.
    apply: sta_cren_conv0...
    eauto.
    eauto. }
  { move=>Γ A B s r t ord1 ord2 tyA ihA tyB ihB m ξ e. sta0_to_sta.
    destruct m; inv e.
    econstructor.
    apply: ord1.
    apply: ord2.
    eauto.
    apply: sta_ctx_conv.
    apply: conv_sym.
    apply: sta_cren_conv0...
    eauto.
    eauto. }
  { move=>Γ A B m n t tyS ihS tym ihm tyn ihn m0 ξ e. sta0_to_sta.
    destruct m0; inv e.
    have[s[r[ord[tyA[tyB _]]]]]:=sta_sig0_inv tyS.
    econstructor...
    apply: sta_conv.
    apply: sta_conv_beta.
    apply: sta_cren_conv0...
    eauto.
    have:=sta_subst tyB (ihm _ _ erefl)... }
  { move=>Γ A B m n t tyS ihS tym ihm tyn ihn m0 ξ e. sta0_to_sta.
    destruct m0; inv e.
    have[s[r[ord1[ord2[tyA[tyB _]]]]]]:=sta_sig1_inv tyS.
    econstructor...
    apply: sta_conv.
    apply: sta_conv_beta.
    apply: sta_cren_conv0...
    eauto.
    have:=sta_subst tyB (ihm _ _ erefl)... }
  { move=>Γ A B C m n s t tyS ihS tym ihm tyn ihn m0 ξ e. sta0_to_sta.
    destruct m0; inv e.
    have wf:=sta_type_wf tyS. inv wf.
    have[s1[r[ord[tyA[tyB/sort_inj e]]]]]:=sta_sig0_inv H2. subst.
    have cs: cren_subst_agree (m0 .: ids) (cren ξ m0 .: ids) ξ.
    move=>[|x]...
    erewrite<-(term_cren_subst _ cs).
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
    apply: sta_conv.
    apply: conv_sym.
    apply: sta_cren_conv0...
    econstructor...
    2:{ have/=:=sta_subst tyS tym.
        rewrite<-term_cren_beta1... }
    apply: sta_conv.
    apply: sta_conv_subst.
    2:{ apply: ihn... }
    apply: sta_cren_conv0...
    have/=:=sta_substitution (ihS _ _ erefl) agr... }
  { move=>Γ A B C m n s t tyS ihS tym ihm tyn ihn m0 ξ e. sta0_to_sta.
    destruct m0; inv e.
    have wf:=sta_type_wf tyS. inv wf.
    have[s1[r[ord1[ord2[tyA[tyB/sort_inj e]]]]]]:=sta_sig1_inv H2. subst.
    have cs: cren_subst_agree (m0 .: ids) (cren ξ m0 .: ids) ξ.
    move=>[|x]...
    erewrite<-(term_cren_subst _ cs).
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
    apply: sta_conv.
    apply: conv_sym.
    apply: sta_cren_conv0...
    apply: sta_letin1...
    2:{ have/=:=sta_subst tyS tym.
        rewrite<-term_cren_beta1... }
    apply: sta_conv.
    apply: sta_conv_subst.
    2:{ apply: ihn... }
    apply: sta_cren_conv0...
    have/=:=sta_substitution (ihS _ _ erefl) agr... }
  { move=>Γ A m ar gr s tyA ihA tym ihm m0 ξ e. sta0_to_sta.
    destruct m0; inv e.
    apply: sta_conv.
    apply: conv_sym.
    apply: sta_cren_conv0...
    constructor.
    apply: sta_cren_arity_proto_inv...
    apply: sta_cren_guarded_inv...
    apply: sta_ctx_conv.
    apply: conv_sym.
    apply: sta_cren_conv0...
    apply: ihA...
    apply: sta_conv.
    2:{ apply: ihm... }
    apply: sta_conv_subst.
    apply: sta_cren_conv0...
    have/=:=sta_weaken (ihA _ _ erefl) tyA...
    eauto. }
  { move=>Γ A m n1 n2 s tyA ihA tym ihm tyn1 ihn1 tyn2 ihn2 m0 ξ e. sta0_to_sta.
    destruct m0; inv e.
    have wf:=sta_type_wf tyA. inv wf.
    rewrite<-term_cren_beta1.
    apply: sta_conv.
    apply: conv_sym.
    apply: sta_cren_conv0...
    econstructor...
    apply: sta_conv.
    apply: sta_conv_subst.
    apply: sta_cren_conv0...
    apply: ihn1...
    have:=sta_subst (ihA _ _ erefl) (sta_tt H1)...
    apply: sta_conv.
    apply: sta_conv_subst.
    apply: sta_cren_conv0...
    apply: ihn2...
    have:=sta_subst (ihA _ _ erefl) (sta_ff H1)...
    have/=:=sta_subst tyA tym.
    rewrite<-term_cren_beta1... }
  { move=>Γ r A B s tyA ihA tyB ihB m ξ e. sta0_to_sta.
    destruct m; inv e.
    constructor.
    apply: sta_ctx_conv.
    apply: conv_sym.
    apply: sta_cren_conv0...
    apply: ihA...
    apply: ihB... }
  { move=>Γ r A B s tyA ihA tyB ihB m ξ e. sta0_to_sta.
    destruct m; inv e.
    constructor.
    apply: sta_ctx_conv.
    apply: conv_sym.
    apply: sta_cren_conv0...
    apply: ihA...
    apply: ihB... }
  { move=>Γ A m s tyC ihC tym ihm m0 ξ e. sta0_to_sta.
    destruct m0; inv e.
    have tyC':=ihC (Ch true m0) ξ erefl.
    have[tym0/sort_inj e]:=sta_ch_inv tyC. subst.
    apply: sta_conv.
    apply: sta_conv_io.
    apply: sta_conv_ch.
    apply: conv_sym.
    apply: sta_cren_conv0...
    econstructor.
    apply: sta_ctx_conv.
    3:{ apply: ihm... }
    apply: sta_conv_ch.
    apply: conv_sym.
    apply: sta_cren_conv0...
    eauto.
    econstructor.
    econstructor... }
Qed.
