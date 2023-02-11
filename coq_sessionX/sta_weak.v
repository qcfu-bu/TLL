From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_ctx sta_type sta_conf.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive sta_agree_ren : (var -> var) ->
  dyn_ctx -> sta_ctx -> sta_ctx -> Prop :=
| sta_agree_ren_nil Θ :
  sta_agree_ren id Θ nil nil
| sta_agree_ren_cons Θ Γ Γ' ξ m s :
  Θ ; Γ ⊢ m : Sort s ->
  sta_agree_ren ξ Θ Γ Γ' ->
  sta_agree_ren (upren ξ) Θ (m :: Γ) (m.[ren ξ] :: Γ')
| sta_agree_ren_wk Θ Γ Γ' ξ m s :
  Θ ; Γ' ⊢ m : Sort s ->
  sta_agree_ren ξ Θ Γ Γ' ->
  sta_agree_ren (ξ >>> (+1)) Θ (Γ) (m :: Γ').

Lemma sta_agree_ren_refl Θ Γ : sta_wf Θ Γ -> sta_agree_ren id Θ Γ Γ.
Proof with eauto using sta_agree_ren.
  move=>wf. elim: wf=>{Θ Γ}...
  move=>Θ Γ A s wf agr tyA.
  have:(sta_agree_ren (upren id) Θ (A :: Γ) (A.[ren id] :: Γ))...
  by asimpl.
Qed.

Lemma sta_agree_ren_has Θ Γ Γ' ξ x A :
  sta_agree_ren ξ Θ Γ Γ' -> sta_has Γ x A -> sta_has Γ' (ξ x) A.[ren ξ].
Proof with eauto.
  move=>agr. elim: agr x A=>{Θ Γ Γ' ξ}.
  { move=>Θ x A hs. inv hs. }
  { move=>Θ Γ Γ' ξ m s tym agr ih x A hs. inv hs; asimpl.
    { replace m.[ren (ξ >>> (+1))] with m.[ren ξ].[ren (+1)] by autosubst.
      constructor. }
    { replace A0.[ren (ξ >>> (+1))] with A0.[ren ξ].[ren (+1)] by autosubst.
      constructor... } }
  { move=>Θ Γ Γ' ξ m A tym agr ih x B /ih hs. asimpl.
    replace B.[ren (ξ >>> (+1))] with B.[ren ξ].[ren (+1)] by autosubst.
    constructor... }
Qed.

Lemma sta_agree_weak_nil_wf Θ Γ' ξ : sta_agree_ren ξ Θ nil Γ' -> sta_wf Θ Γ'.
Proof with eauto using sta_wf.
  move e:(nil)=>Γ agr. elim: agr e=>//{Θ Γ Γ' ξ}...
Qed.

Lemma sta_agree_weak_wf_nil Θ Γ' : sta_wf Θ Γ' -> sta_agree_ren (+size Γ') Θ nil Γ'.
Proof with eauto using sta_agree_ren. elim=>//={Γ'}... Qed.

Lemma sta_agree_weak_wf_cons Θ Γ Γ' A s ξ :
  sta_agree_ren ξ Θ (A :: Γ) Γ' -> sta_wf Θ Γ ->
  (∀ Γ' ξ, sta_agree_ren ξ Θ Γ Γ' → sta_wf Θ Γ') ->
  (∀ Γ' ξ, sta_agree_ren ξ Θ Γ Γ' → Θ ; Γ' ⊢ A.[ren ξ] : Sort s) ->
  sta_wf Θ Γ'.
Proof with eauto using sta_wf.
  move e:(A :: Γ)=>Γ0 agr. elim: agr Γ A s e=>//{Θ Γ0 Γ' ξ}...
  move=>Θ Γ Γ' ξ m s tym agr _ Γ0 A s0 [e1 e2] wf h1 h2; subst.
  apply: sta_wf_cons...
Qed.

Lemma sta_agree_ren_size ξ Θ Γ Γ' :
  sta_agree_ren ξ Θ Γ Γ' -> ((+size Γ) >>> ξ) = (+size Γ').
Proof.
  elim=>//={ξ Θ Γ Γ'}.
  { move=>Θ Γ Γ' ξ m s tym agr ih. asimpl.
    rewrite ih. by asimpl. }
  { move=>Θ Γ Γ' ξ m s tym agr ih. asimpl.
    rewrite ih. by asimpl. }
Qed.

Lemma sta_rename Θ Γ Γ' m A ξ :
  Θ ; Γ ⊢ m : A -> sta_agree_ren ξ Θ Γ Γ' -> Θ ; Γ' ⊢ m.[ren ξ] : A.[ren ξ].
Proof with eauto using sta_type, sta_wf, sta_agree_ren.
  move=>tym. move:Θ Γ m A tym Γ' ξ.
  apply:(@sta_type_mut _
           (fun Θ Γ wf => forall Γ' ξ, sta_agree_ren ξ Θ Γ Γ' -> sta_wf Θ Γ'))...
  { move=>Θ Γ x A wf h hs Γ' ξ agr. asimpl.
    apply: sta_var...
    apply: sta_agree_ren_has... }
  { move=>Θ Γ A B s r t tyA ihA tyB ihB Γ' ξ agr. asimpl.
    have wf:=sta_type_wf tyB. inv wf.
    apply: sta_pi0... }
  { move=>Θ Γ A B s r t tyA ihA tyB ihB Γ' ξ agr. asimpl.
    have wf:=sta_type_wf tyB. inv wf.
    apply: sta_pi1... }
  { move=>Θ Γ A B m s tym ihm Γ' ξ agr. asimpl.
    have wf:=sta_type_wf tym. inv wf.
    apply: sta_lam0... }
  { move=>Θ Γ A B m s tym ihm Γ' ξ agr. asimpl.
    have wf:=sta_type_wf tym. inv wf.
    apply: sta_lam1... }
  { move=>Θ Γ A B m n s tym ihm tyn ihn Γ' ξ agr. asimpl.
    replace B.[n.[ren ξ] .: ren ξ] with B.[ren (upren ξ)].[n.[ren ξ]/]
      by autosubst.
    have{}ihm:=ihm _ _ agr.
    have{}ihn:=ihn _ _ agr.
    apply: sta_app0...
    asimpl in ihm... }
  { move=>Θ Γ A B m n s tym ihm tyn ihn Γ' ξ agr. asimpl.
    replace B.[n.[ren ξ] .: ren ξ] with B.[ren (upren ξ)].[n.[ren ξ]/]
      by autosubst.
    have{}ihm:=ihm _ _ agr.
    have{}ihn:=ihn _ _ agr.
    apply: sta_app1...
    asimpl in ihm... }
  { move=>Θ Γ A B s r t ord tyA ihA tyB ihB Γ' ξ agr. asimpl.
    have{}ihA:=ihA _ _ agr.
    have{}ihB:=ihB _ _ (sta_agree_ren_cons tyA agr).
    apply: sta_sig0... }
  { move=>Θ Γ A B s r t ord1 ord2 tyA ihA tyB ihB Γ' ξ agr. asimpl.
    have{}ihA:=ihA _ _ agr.
    have{}ihB:=ihB _ _ (sta_agree_ren_cons tyA agr).
    apply: sta_sig1.
    exact: ord1. exact: ord2. all: eauto. }
  { move=>Θ Γ A B m n t tyS ihS tym ihm tyn ihn Γ' ξ agr. asimpl.
    have{}ihS:=ihS _ _ agr.
    have{}ihm:=ihm _ _ agr.
    have{}ihn:=ihn _ _ agr.
    asimpl in ihS.
    asimpl in ihn.
    apply: sta_pair0...
    by autosubst. }
  { move=>Θ Γ A B m n t tyS ihS tym ihm tyn ihn Γ' ξ agr. asimpl.
    have{}ihS:=ihS _ _ agr.
    have{}ihm:=ihm _ _ agr.
    have{}ihn:=ihn _ _ agr.
    asimpl in ihS.
    asimpl in ihn.
    apply: sta_pair1...
    by autosubst. }
  { move=>Θ Γ A B C m n s t tyC ihC tym ihm tyn ihn Γ' ξ agr. asimpl.
    have wf:=sta_type_wf tyC. inv wf.
    have wf:=sta_type_wf tyn. inv wf. inv H4.
    have{}ihC:=ihC _ _ (sta_agree_ren_cons H3 agr).
    have{}ihm:=ihm _ _ agr.
    have/ihn{}ihn:
      sta_agree_ren (upren (upren ξ)) Θ (B :: A :: Γ)
        (B.[ren (upren ξ)] :: A.[ren ξ] :: Γ')...
    asimpl in ihC.
    asimpl in ihm.
    replace C.[Pair0 (Var 1) (Var 0) t .: ren (+2)].[ren (upren (upren ξ))]
      with C.[ren (upren ξ)].[Pair0 (Var 1) (Var 0) t .: ren (+2)]
        in ihn by autosubst.
    have:=sta_letin0 ihC ihm ihn.
    by autosubst. }
  { move=>Θ Γ A B C m n s t tyC ihC tym ihm tyn ihn Γ' ξ agr. asimpl.
    have wf:=sta_type_wf tyC. inv wf.
    have wf:=sta_type_wf tyn. inv wf. inv H4.
    have{}ihC:=ihC _ _ (sta_agree_ren_cons H3 agr).
    have{}ihm:=ihm _ _ agr.
    have/ihn{}ihn:
      sta_agree_ren (upren (upren ξ)) Θ (B :: A :: Γ)
        (B.[ren (upren ξ)] :: A.[ren ξ] :: Γ')...
    asimpl in ihC.
    asimpl in ihm.
    replace C.[Pair1 (Var 1) (Var 0) t .: ren (+2)].[ren (upren (upren ξ))]
      with C.[ren (upren ξ)].[Pair1 (Var 1) (Var 0) t .: ren (+2)]
        in ihn by autosubst.
    have:=sta_letin1 ihC ihm ihn.
    by autosubst. }
  { move=>Θ Γ A m tym ihm Γ' ξ agr. asimpl.
    have wf:=sta_type_wf tym. inv wf.
    have{}ihm:=ihm _ _ (sta_agree_ren_cons H3 agr).
    apply: sta_fix...
    asimpl in ihm.
    by asimpl. }
  { move=>Θ Γ A m n1 n2 s tyA ihA
           tym ihm tyn1 ihn1 tyn2 ihn2 Γ' ξ agr. asimpl.
    have wf:=sta_type_wf tym.
    have tyBool:=sta_bool wf.
    have{}ihm:=ihm _ _ agr.
    have{}ihA:=ihA _ _ (sta_agree_ren_cons tyBool agr).
    have{}ihn1:=ihn1 _ _ agr.
    have{}ihn2:=ihn2 _ _ agr.
    asimpl in ihm.
    asimpl in ihA.
    asimpl in ihn1.
    asimpl in ihn2.
    replace A.[m.[ren ξ] .: ren ξ]
      with A.[ren (upren ξ)].[m.[ren ξ]/] by autosubst.
    apply: sta_ifte...
    by asimpl.
    by asimpl. }
  { move=>Θ Γ m n A B s tyB ihB tym ihm tyn ihn Γ' ξ agr. asimpl.
    have wf:=sta_type_wf tyn. inv wf.
    have{}ihB:=ihB _ _ agr.
    have{}ihm:=ihm _ _ agr.
    have{}ihn:=ihn _ _ (sta_agree_ren_cons H3 agr).
    apply: sta_bind...
    asimpl in ihn. by asimpl. }
  { move=>Θ Γ r A B tyB ihB Γ' ξ agr. asimpl.
    have wf:=sta_type_wf tyB. inv wf.
    have{}ihB:=ihB _ _ (sta_agree_ren_cons H3 agr).
    apply: sta_act0... }
  { move=>Θ Γ r A B tyB ihB Γ' ξ agr. asimpl.
    have wf:=sta_type_wf tyB. inv wf.
    have{}ihB:=ihB _ _ (sta_agree_ren_cons H3 agr).
    apply: sta_act1... }
  { move=>Θ Γ r x A wf ih pos tyA ihA Γ' ξ agr. asimpl.
    rewrite (sta_agree_ren_size agr).
    apply: sta_cvar... }
  { move=>Θ Γ m A tym ihm Γ' ξ agr. asimpl.
    have wf:=sta_type_wf tym. inv wf.
    have{}ihm:=ihm _ _ (sta_agree_ren_cons H3 agr).
    asimpl in ihm.
    apply: sta_fork... }
  { move=>Θ Γ A B m s eq tym ihm tyB ihB Γ' ξ agr.
    apply: sta_conv.
    apply: sta_conv_subst.
    apply: eq.
    by apply: ihm.
    have:=ihB _ _ agr.
    asimpl... }
  { exact: sta_agree_weak_nil_wf. }
  { move=>Θ Γ A s wf ih tyA ihA Γ' ξ agr.
    apply: sta_agree_weak_wf_cons... }
Qed.

Lemma sta_wf_ok Θ Γ x A :
  sta_wf Θ Γ -> sta_has Γ x A -> exists s, Θ ; Γ ⊢ A : Sort s.
Proof with eauto using sta_agree_ren, sta_agree_ren_refl.
  move=>wf. elim: wf x A=>{Θ Γ}.
  { move=>Θ x A hs. inv hs. }
  { move=>Θ Γ A s wf ih tyA x B hs. inv hs.
    { exists s.
      replace (Sort s) with (Sort s).[ren (+1)] by autosubst.
      apply: sta_rename... }
    { have[t tyA0]:=ih _ _ H3.
      exists t.
      replace (Sort t) with (Sort t).[ren (+1)] by autosubst.
      apply: sta_rename... } }
Qed.

Lemma sta_weaken Θ Γ m A B s :
  Θ ; Γ ⊢ m : A ->
  Θ ; Γ ⊢ B : Sort s ->
  Θ ; (B :: Γ) ⊢ m.[ren (+1)] : A.[ren (+1)].
Proof with eauto using sta_agree_ren, sta_agree_ren_refl.
  move=>tym tyB. apply: sta_rename...
Qed.

Lemma sta_eweaken Θ Γ m m' A A' B s :
  m' = m.[ren (+1)] ->
  A' = A.[ren (+1)] ->
  Θ ; Γ ⊢ m : A ->
  Θ ; Γ ⊢ B : Sort s ->
  Θ ; (B :: Γ) ⊢ m' : A'.
Proof with eauto using sta_agree_ren, sta_agree_ren_refl.
  move=>*; subst. apply: sta_weaken...
Qed.

Lemma cvar_pos_mergeL Θ1 Θ2 Θ x :
  Θ1 ∘ Θ2 => Θ -> cvar_pos Θ1 x true -> cvar_pos Θ x true.
Proof with eauto using cvar_pos.
  move=>mrg. elim: mrg x=>{Θ1 Θ2 Θ}...
  { move=>Θ1 Θ2 Θ m mrg ih x pos. inv pos... }
  { move=>Θ1 Θ2 Θ m mrg ih x pos. inv pos... }
  { move=>Θ1 Θ2 Θ m mrg ih x pos. inv pos... }
  { move=>Θ1 Θ2 Θ mrg ih x pos. inv pos... }
Qed.

Lemma sta_type_expand Θ1 Θ2 Θ Γ m A :
  Θ1 ; Γ ⊢ m : A -> Θ1 ∘ Θ2 => Θ -> Θ ; Γ ⊢ m : A.
Proof with eauto using sta_type.
  move=>ty. move:Θ1 Γ m A ty Θ2 Θ.
  apply:(@sta_type_mut _
           (fun Θ1 Γ wf => forall Θ2 Θ, Θ1 ∘ Θ2 => Θ -> sta_wf Θ Γ))...
  { move=>Θ1 Γ A m n1 n2 s tyA ihA tym ihm tyn1 ihn1 tyn2 ihn2 Θ2 Θ mrg.
    econstructor... }
  { move=>Θ1 Γ r x A wf ih pos tyA ihA Θ2 Θ mrg.
    constructor...
    apply: cvar_pos_mergeL... }
  { move=>Θ1 Θ2 Θ mrg. constructor. }
  { move=>Θ1 Γ A s wf ih tyA ihA Θ2 Θ mrg.
    econstructor... }
Qed.
