From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq zify.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_cren dyn_subst.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive dyn_ctx_cren : (cvar -> cvar) -> dyn_ctx -> dyn_ctx -> Prop :=
| dyn_ctx_cren_O Θ :
  dyn_ctx_cren id Θ Θ
| dyn_ctx_cren_ty ξ r A Θ Θ' :
  nil ⊢ A : Proto ->
  dyn_ctx_cren ξ Θ Θ' ->
  dyn_ctx_cren (upren ξ) (Ch r A :L Θ) (Ch r (cren ξ A) :L Θ')
| dyn_ctx_cren_n ξ Θ Θ' :
  dyn_ctx_cren ξ Θ Θ' ->
  dyn_ctx_cren (upren ξ) (_: Θ) (_: Θ')
| dyn_ctx_cren_plus ξ Θ Θ' :
  dyn_ctx_cren ξ Θ Θ' ->
  dyn_ctx_cren (ξ >>> (+1)) Θ (_: Θ')
| dyn_ctx_cren_minus ξ Θ Θ' :
  dyn_ctx_cren ξ Θ Θ' ->
  dyn_ctx_cren ((-1) >>> ξ) (_: Θ) Θ'.

Lemma dyn_ctx_cren_empty Θ Θ' ξ :
  dyn_ctx_cren ξ Θ Θ' -> dyn_empty Θ -> dyn_empty Θ'.
Proof with eauto using dyn_empty.
  elim=>{ξ Θ Θ'}...
  { move=>ξ r A Θ Θ' tyA agr ih emp. inv emp. }
  { move=>ξ Θ Θ' agr ih emp. inv emp... }
  { move=>ξ Θ Θ' agr ih emp. inv emp... }
Qed.

Lemma dyn_ctx_cren_key Θ Θ' ξ s :
  dyn_ctx_cren ξ Θ Θ' -> Θ ▷ s -> Θ' ▷ s.
Proof with eauto using key.
  move=>agr. elim: agr s=>{Θ Θ' ξ}...
  { move=>ξ r A Θ Θ' tyA agr ih s k. inv k... }
  { move=>ξ Θ Θ' agr ih s k. inv k... }
  { move=>ξ Θ Θ' agr ih s k. inv k... }
Qed.

Lemma dyn_ctx_cren_just Θ Θ' A x ξ :
  dyn_ctx_cren ξ Θ Θ' ->
  dyn_just Θ x A ->
  dyn_just Θ' (ξ x) (cren ξ A).
Proof with eauto.
  move=>agr. elim: agr A x=>//={Θ Θ' ξ}...
  { move=>Θ A x js.
    by rewrite term_cren_id. }
  { move=>ξ r A Θ Θ' tyA agr ih A0 x js. inv js.
    asimpl.
    rewrite<-term_cren_comp.
    have->:((+1) >>> upren ξ) = (ξ >>> (+1)) by autosubst.
    have->:(cren (ξ >>> (+1)) A) = (cren (+1) (cren ξ A)).
    by rewrite<-term_cren_comp.
    constructor.
    apply: dyn_ctx_cren_empty... }
  { move=>ξ Θ Θ' agr ih A x js. inv js.
    asimpl.
    rewrite<-term_cren_comp.
    have->:((+1) >>> upren ξ) = (ξ >>> (+1)) by autosubst.
    have->:(cren (ξ >>> (+1)) A0) = (cren (+1) (cren ξ A0)).
    by rewrite<-term_cren_comp.
    constructor... }
  { move=>ξ Θ Θ' agr ih A x js.
    rewrite term_cren_comp.
    constructor... }
  { move=>ξ Θ Θ' agr ih A x js. inv js.
    have{}ih:=ih _ _ H0.
    rewrite<-term_cren_comp.
    replace (x0.+1 - 1) with x0 by lia. asimpl.
    have->:((+1) >>> (-1) >>> ξ) = ξ.
    f_ext. move=>x/=. fold subn. f_equal. lia.
    eauto. }
Qed.

Lemma dyn_ctx_cren_merge Θ1 Θ2 Θ Θ' ξ :
  dyn_ctx_cren ξ Θ Θ' -> 
  Θ1 ∘ Θ2 => Θ ->
  exists Θ1' Θ2',
    Θ1' ∘ Θ2' => Θ' /\
    dyn_ctx_cren ξ Θ1 Θ1' /\
    dyn_ctx_cren ξ Θ2 Θ2'.
Proof with eauto using dyn_ctx_cren.
  move=>agr. elim: agr Θ1 Θ2=>{Θ Θ' ξ}.
  { move=>Θ Θ1 Θ2 mrg. exists Θ1. exists Θ2... }
  { move=>ξ r A Θ Θ' tyA agr ih Θ1 Θ2 mrg. inv mrg.
    { have[Θ1'[Θ2'[mrg'[agr1 agr2]]]]:=ih _ _ H2.
      exists (Ch r (cren ξ A) :L Θ1'). exists (_: Θ2').
      repeat constructor... }
    { have[Θ1'[Θ2'[mrg'[agr1 agr2]]]]:=ih _ _ H2.
      exists (_: Θ1'). exists (Ch r (cren ξ A) :L Θ2').
      repeat constructor... } }
  { move=>ξ Θ Θ' agr ih Θ1 Θ2 mrg. inv mrg.
    have[Θ1'[Θ2'[mrg'[agr1 agr2]]]]:=ih _ _ H2.
    exists (_: Θ1'). exists (_: Θ2').
    repeat constructor... }
  { move=>ξ Θ Θ' agr ih Θ1 Θ2 mrg.
    have[Θ1'[Θ2'[mrg'[agr1 agr2]]]]:=ih _ _ mrg.
    exists (_: Θ1'). exists (_: Θ2').
    repeat constructor... }
  { move=>ξ Θ Θ' agr ih Θ1 Θ2 mrg. inv mrg.
    have[Θ1'[Θ2'[mrg'[agr1 agr2]]]]:=ih _ _ H2.
    exists Θ1'. exists Θ2'.
    repeat constructor... }
Qed.

Lemma dyn_crename Θ Θ' Γ Δ m A ξ :
  Θ ; Γ ; Δ ⊢ m : A -> dyn_ctx_cren ξ Θ Θ' ->
  Θ' ; Γ ; Δ ⊢ cren ξ m : A.
Proof with eauto using dyn_empty, dyn_type, dyn_ctx_cren.
  move=>ty. elim: ty Θ' ξ=>/={Θ Γ Δ m A}...
  { move=>Θ Γ Δ x s A wmp wf shs dhs Θ' ξ agr.
    econstructor... apply: dyn_ctx_cren_empty... }
  { move=>Θ Γ Δ A B m s k1 k2 tym ihm Θ' ξ agr.
    have wf:=dyn_type_wf tym. inv wf.
    have[r tyB]:=dyn_valid tym.
    apply: dyn_conv.
    apply: sta_cren_conv0...
    simpl. constructor...
    apply: dyn_ctx_cren_key...
    apply: dyn_ctx_conv0.
    apply: sta_cren_conv0...
    apply: sta_crename...
    apply: dyn_conv.
    apply: conv_sym.
    apply: sta_cren_conv0...
    apply: ihm...
    apply: sta_crename...
    econstructor... }
  { move=>Θ Γ Δ A B m s t k1 k2 tym ihm Θ' ξ agr.
    have wf:=dyn_type_wf tym. inv wf.
    have[r tyB]:=dyn_valid tym.
    apply: dyn_conv.
    apply: sta_cren_conv0...
    simpl. econstructor...
    apply: dyn_ctx_cren_key...
    apply: dyn_ctx_conv1.
    apply: sta_cren_conv0...
    apply: sta_crename...
    apply: dyn_conv.
    apply: conv_sym.
    apply: sta_cren_conv0...
    apply: ihm...
    apply: sta_crename...
    econstructor... }
  { move=>Θ Γ Δ A B m n s tym ihm tyn Θ' ξ agr.
    have[r tyP]:=dyn_valid tym.
    have[t[tyB/sort_inj e]]:=sta_pi0_inv tyP. subst.
    have eq:B.[cren ξ n/] === B.[n/].
    apply: sta_conv_beta.
    apply: sta_cren_conv0...
    apply: dyn_conv...
    econstructor...
    apply: sta_crename...
    have:=sta_subst tyB tyn... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n s mrg1 mrg2 tym ihm tyn ihn Θ' ξ agr.
    have[Θ1'[Θ2'[mrg'[agr1 agr2]]]]:=dyn_ctx_cren_merge agr mrg1.
    have[r tyP]:=dyn_valid tym.
    have[t[tyB/sort_inj e]]:=sta_pi1_inv tyP. subst.
    have eq:B.[cren ξ n/] === B.[n/].
    apply: sta_conv_beta.
    apply: sta_cren_conv0...
    apply: dyn_conv...
    have:=sta_subst tyB (dyn_sta_type tyn)... }
  { move=>Θ Γ Δ A B m n t tyS tym tyn ihn Θ' ξ agr.
    have[s[r[ord[tyA[tyB _]]]]]:=sta_sig0_inv tyS.
    have eq: B.[m/] === B.[cren ξ m/].
    apply: sta_conv_beta.
    apply: conv_sym.
    apply: sta_cren_conv0...
    econstructor...
    apply: sta_crename...
    apply: dyn_conv...
    have:=sta_subst tyB (sta_crename ξ tym)... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n t mrg1 mrg2 tyS tym ihm tyn ihn Θ' ξ agr.
    have[s[r[ord1[ord2[tyA[tyB _]]]]]]:=sta_sig1_inv tyS.
    have[Θ1'[Θ2'[mrg'[agr1 agr2]]]]:=dyn_ctx_cren_merge agr mrg1.
    have eq: B.[m/] === B.[cren ξ m/].
    apply: sta_conv_beta.
    apply: conv_sym.
    apply: sta_cren_conv0...
    econstructor...
    apply: dyn_conv...
    have:=sta_subst tyB (sta_crename ξ (dyn_sta_type tym))... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r t mrg1 mrg2 tyC tym ihm tyn ihn Θ' ξ agr.
    have wf:=sta_type_wf tyC. inv wf.
    have[s1[r1[ord[tyA[tyB/sort_inj e]]]]]:=sta_sig0_inv H2. subst.
    have[Θ1'[Θ2'[mrg'[agr1 agr2]]]]:=dyn_ctx_cren_merge agr mrg1.
    have eq: (cren ξ C).[cren ξ m/] === C.[m/].
    apply: conv_trans.
    apply: sta_conv_beta.
    apply: sta_cren_conv0...
    apply: sta_conv_subst.
    apply: sta_cren_conv0...
    apply: dyn_conv...
    apply: dyn_letin0...
    apply: sta_crename...
    apply: dyn_conv.
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
    have/=:=sta_subst tyC (dyn_sta_type tym)... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r1 r2 t mrg1 mrg2 tyC tym ihm tyn ihn Θ' ξ agr.
    have wf:=sta_type_wf tyC. inv wf.
    have[s1[r3[ord1[ord2[tyA[tyB/sort_inj e]]]]]]:=sta_sig1_inv H2. subst.
    have[Θ1'[Θ2'[mrg'[agr1 agr2]]]]:=dyn_ctx_cren_merge agr mrg1.
    have eq: (cren ξ C).[cren ξ m/] === C.[m/].
    apply: conv_trans.
    apply: sta_conv_beta.
    apply: sta_cren_conv0...
    apply: sta_conv_subst.
    apply: sta_cren_conv0...
    apply: dyn_conv...
    apply: dyn_letin1...
    apply: sta_crename...
    apply: dyn_conv.
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
    have/=:=sta_subst tyC (dyn_sta_type tym)... }
  { move=>Θ Γ Δ A m k1 k2 tym ihm Θ' ξ agr.
    have wf:=dyn_type_wf tym. inv wf.
    apply: dyn_conv.
    apply: sta_cren_conv0...
    constructor...
    apply: dyn_ctx_cren_key...
    apply: dyn_ctx_conv1.
    apply: sta_cren_conv0...
    apply: sta_crename...
    apply: dyn_conv.
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
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m n1 n2 s mrg1 mrg2 tyA tym ihm tyn1 ihn1 tyn2 ihn2 Θ' ξ agr.
    have wf:=sta_type_wf (dyn_sta_type tym).
    have[Θ1'[Θ2'[mrg'[agr1 agr2]]]]:=dyn_ctx_cren_merge agr mrg1.
    have eq:(cren ξ A).[cren ξ m/] === A.[m/].
    apply: conv_trans.
    apply: sta_conv_beta.
    apply: sta_cren_conv0...
    apply: sta_conv_subst.
    apply: sta_cren_conv0...
    apply: dyn_conv...
    econstructor...
    apply: sta_crename...
    apply: dyn_conv.
    apply: sta_conv_subst.
    apply: conv_sym.
    apply: sta_cren_conv0...
    eauto.
    have:=sta_subst (sta_crename ξ tyA) (sta_tt wf)...
    apply: dyn_conv.
    apply: sta_conv_subst.
    apply: conv_sym.
    apply: sta_cren_conv0...
    eauto.
    have:=sta_subst (sta_crename ξ tyA) (sta_ff wf)...
    have//=:=sta_subst tyA (dyn_sta_type tym)... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m n A B s t mrg1 mrg2
           tyB tym ihm tyn ihn Θ' ξ agr.
    have[Θ1'[Θ2'[mrg'[agr1 agr2]]]]:=dyn_ctx_cren_merge agr mrg1.
    econstructor... }
  { move=>Θ Γ Δ r x A js wf k tyA Θ' ξ agr.
    have/={}js:=dyn_ctx_cren_just agr js.
    apply: dyn_conv.
    2:{econstructor... apply: sta_crename... }
    apply: sta_conv_ch.
    rewrite<-term_cren_ren.
    apply: sta_cren_conv0...
    constructor.
    replace Proto with Proto.[ren (+size Γ)] by eauto.
    apply: sta_rename...
    apply: sta_wf_agree_ren.
    apply: dyn_sta_wf... }
  { move=>Θ Γ Δ m A tym ihm Θ' ξ agr.
    have wf:=dyn_type_wf tym. inv wf.
    have[tyA _]:=sta_ch_inv H4.
    apply: dyn_conv.
    apply: sta_conv_io.
    apply: sta_conv_ch.
    apply: sta_cren_conv0...
    econstructor.
    apply: dyn_ctx_conv1.
    apply: sta_conv_ch.
    apply: sta_cren_conv0...
    constructor.
    apply: sta_crename...
    apply: ihm...
    econstructor.
    econstructor.
    eauto. }
Qed.

Lemma dyn_cstrengthen Θ Γ Δ m A :
  _: Θ ; Γ ; Δ ⊢ cren (+1) m : A -> Θ ; Γ ; Δ ⊢ m : A.
Proof with eauto using dyn_empty, dyn_type, dyn_ctx_cren.
  move=>ty.
  have e:((+1) >>> (-1)) = id.
  { f_ext. move=>x. asimpl. fold subn. lia. }
  replace m with (cren ((-1) >>> id) (cren (+1) m)).
  apply: dyn_crename.
  apply: ty.
  constructor.
  constructor.
  rewrite<-term_cren_comp. asimpl.
  rewrite e. apply: term_cren_id.
Qed.

Lemma dyn_cweaken Θ Γ Δ m A :
  Θ ; Γ ; Δ ⊢ m : A -> _: Θ ; Γ ; Δ ⊢ cren (+1) m : A.
Proof with eauto using dyn_empty, dyn_type, dyn_ctx_cren.
  move=>ty. apply: dyn_crename...
Qed.
