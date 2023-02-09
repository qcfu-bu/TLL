From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq zify.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_cren dyn_type.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive dyn_ctx_cren : (nat -> nat) -> dyn_ctx -> dyn_ctx -> Prop :=
| dyn_ctx_cren_O Θ :
  dyn_ctx_cren id Θ Θ
| dyn_ctx_cren_plus ξ Θ Θ' :
  dyn_ctx_cren ξ Θ Θ' ->
  dyn_ctx_cren (ξ >>> (+1)) Θ (_: Θ')
| dyn_ctx_cren_minus ξ Θ Θ' :
  dyn_ctx_cren ξ Θ Θ' ->
  dyn_ctx_cren ((subn^~ 1) >>> ξ) (_: Θ) Θ'.

Inductive dyn_agree_cren : (nat -> nat) ->
  dyn_ctx -> sta_ctx -> dyn_ctx -> dyn_ctx -> sta_ctx -> dyn_ctx -> Prop :=
| dyn_agree_cren_nil ξ Θ Θ' :
  dyn_ctx_cren ξ Θ Θ' ->
  dyn_agree_cren ξ Θ nil nil Θ' nil nil
| dyn_agree_cren_ty Θ Θ' Γ Γ' Δ Δ' ξ m m' s :
  m' = term_cren m ξ ->
  Γ ⊢ m : Sort s ->
  dyn_agree_cren ξ Θ Γ Δ Θ' Γ' Δ' ->
  dyn_agree_cren ξ
    Θ (m :: Γ) (m :{s} Δ) Θ' (m' :: Γ') (m' :{s} Δ')
| dyn_agree_cren_n Θ Θ' Γ Γ' Δ Δ' ξ m m' s :
  m' = term_cren m ξ ->
  Γ ⊢ m : Sort s ->
  dyn_agree_cren ξ Θ Γ Δ Θ' Γ' Δ' ->
  dyn_agree_cren ξ
    Θ (m :: Γ) (_: Δ) Θ' (m' :: Γ') (_: Δ').

Lemma dyn_sta_agree_cren Θ Θ' Γ Γ' Δ Δ' ξ :
  dyn_agree_cren ξ Θ Γ Δ Θ' Γ' Δ' -> sta_agree_cren ξ Γ Γ'.
Proof with eauto using sta_agree_cren. elim... Qed.

Lemma dyn_ctx_cren_empty Θ Θ' ξ :
  dyn_ctx_cren ξ Θ Θ' -> dyn_empty Θ -> dyn_empty Θ'.
Proof with eauto using dyn_empty.
  elim=>{ξ Θ Θ'}...
  { move=>ξ Θ Θ' agr ih emp. inv emp... }
Qed.

Lemma dyn_agree_cren_empty Θ Θ' Γ Γ' Δ Δ' ξ :
  dyn_agree_cren ξ Θ Γ Δ Θ' Γ' Δ' -> dyn_empty Θ -> dyn_empty Θ'.
Proof with eauto.
  elim=>{Θ Θ' Γ Γ' Δ Δ' ξ}...
  move=>ξ Θ Θ' agr emp.
  apply: dyn_ctx_cren_empty...
Qed.

Lemma dyn_ctx_cren_key Θ Θ' ξ s :
  dyn_ctx_cren ξ Θ Θ' -> Θ ▷ s -> Θ' ▷ s.
Proof with eauto using key.
  move=>agr. elim: agr s=>{Θ Θ' ξ}...
  { move=>ξ Θ Θ' agr ih s k. inv k... }
Qed.

Lemma dyn_agree_cren_key1 Θ Θ' Γ Γ' Δ Δ' ξ s :
  dyn_agree_cren ξ Θ Γ Δ Θ' Γ' Δ' -> Θ ▷ s -> Θ' ▷ s.
Proof with eauto using key.
  move=>agr. elim: agr s=>{Θ Θ' Γ Γ' Δ Δ' ξ}...
  move=>ξ Θ Θ' agr s. apply: dyn_ctx_cren_key...
Qed.

Lemma dyn_agree_cren_key2 Θ Θ' Γ Γ' Δ Δ' ξ s :
  dyn_agree_cren ξ Θ Γ Δ Θ' Γ' Δ' -> Δ ▷ s -> Δ' ▷ s.
Proof with eauto using key.
  move=>agr. elim: agr s=>{Θ Θ' Γ Γ' Δ Δ' ξ}...
  { move=>Θ Θ' Γ Γ' Δ Δ' ξ m m' s e tym agr ih r k. inv k... }
  { move=>Θ Θ' Γ Γ' Δ Δ' ξ m m' s e tym agr ih r k. inv k... }
Qed.

Lemma dyn_agree_cren_has Θ Θ' Γ Γ' Δ Δ' A x s ξ :
  dyn_agree_cren ξ Θ Γ Δ Θ' Γ' Δ' ->
  dyn_has Δ x s A ->
  dyn_has Δ' x s (term_cren A ξ).
Proof with eauto.
  move=>agr. elim: agr A x s=>{Θ Θ' Γ Γ' Δ Δ' ξ}.
  { move=>ξ Θ Θ' agr A x s dhs. inv dhs. }
  { move=>Θ Θ' Γ Γ' Δ Δ' ξ m m' s e tym agr ih A x s0 dhs. inv dhs.
    { rewrite term_cren_ren.
      constructor.
      apply: dyn_agree_cren_key2... }
    { rewrite term_cren_ren.
      constructor... } }
  { move=>Θ Θ' Γ Γ' Δ Δ' ξ m m' s e tym agr ih A x s0 dhs. inv dhs.
    rewrite term_cren_ren.
    constructor... }
Qed.

Lemma dyn_ctx_cren_just Θ Θ' A x ξ :
  dyn_ctx_cren ξ Θ Θ' ->
  dyn_just Θ x A ->
  dyn_just Θ' (ξ x) (term_cren A ξ).
Proof with eauto.
  move=>agr. elim: agr A x=>//={Θ Θ' ξ}...
  { move=>Θ A x js.
    by rewrite term_cren_id. }
  { move=>ξ Θ Θ' agr ih A x js.
    rewrite term_cren_comp.
    constructor... }
  { move=>ξ Θ Θ' agr ih A x js. inv js.
    have{}ih:=ih _ _ H0.
    rewrite<-term_cren_comp.
    replace (x0.+1 - 1) with x0 by lia. asimpl.
    have->:((+1) >>> subn_rec^~ 1 >>> ξ) = ξ.
    f_ext. move=>x/=. fold subn. f_equal. lia.
    eauto. }
Qed.

Lemma dyn_agree_cren_just Θ Θ' Γ Γ' Δ Δ' A x ξ :
  dyn_agree_cren ξ Θ Γ Δ Θ' Γ' Δ' ->
  dyn_just Θ x A ->
  dyn_just Θ' (ξ x) (term_cren A ξ).
Proof with eauto.
  move=>agr. elim: agr A x=>{Θ Θ' Γ Γ' Δ Δ' ξ}...
  move=>ξ Θ Θ' agr A x js.
  apply: dyn_ctx_cren_just...
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
  { move=>ξ Θ Θ' agr ih Θ1 Θ2 mrg.
    have[Θ1'[Θ2'[mrg'[agr1 agr2]]]]:=ih _ _ mrg.
    exists (_: Θ1'). exists (_: Θ2').
    repeat constructor... }
  { move=>ξ Θ Θ' agr ih Θ1 Θ2 mrg. inv mrg.
    have[Θ1'[Θ2'[mrg'[agr1 agr2]]]]:=ih _ _ H2.
    exists Θ1'. exists Θ2'.
    repeat constructor... }
Qed.

Lemma dyn_agree_cren_merge Θ1 Θ2 Θ Θ' Γ Γ' Δ1 Δ2 Δ Δ' ξ :
  dyn_agree_cren ξ Θ Γ Δ Θ' Γ' Δ' -> 
  Θ1 ∘ Θ2 => Θ ->
  Δ1 ∘ Δ2 => Δ ->
  exists Θ1' Θ2' Δ1' Δ2',
    Θ1' ∘ Θ2' => Θ' /\
    Δ1' ∘ Δ2' => Δ' /\
    dyn_agree_cren ξ Θ1 Γ Δ1 Θ1' Γ' Δ1' /\
    dyn_agree_cren ξ Θ2 Γ Δ2 Θ2' Γ' Δ2'.
Proof with eauto using dyn_agree_cren.
  move=>agr. elim: agr Θ1 Θ2 Δ1 Δ2=>{Θ Θ' Γ Γ' Δ Δ' ξ}.
  { move=>ξ Θ Θ' agr Θ1 Θ2 Δ1 Δ2 mrg1 mrg2. inv mrg2.
    have[Θ1'[Θ2'[mrg1'[agr1 agr2]]]]:=dyn_ctx_cren_merge agr mrg1.
    exists Θ1'. exists Θ2'. exists nil. exists nil.
    repeat constructor... }
  { move=>Θ Θ' Γ Γ' Δ Δ' ξ m m' s e tym agr ih Θ1 Θ2 Δ1 Δ2 mrg1 mrg2.
    inv mrg2.
    { have[Θ1'[Θ2'[Δ1'[Δ2'[mrg1'[mrg2'[arg1 arg2]]]]]]]:=
        ih _ _ _ _ mrg1 H2.
      exists Θ1'. exists Θ2'.
      exists (term_cren m ξ :U Δ1').
      exists (term_cren m ξ :U Δ2').
      repeat constructor... }
    { have[Θ1'[Θ2'[Δ1'[Δ2'[mrg1'[mrg2'[arg1 arg2]]]]]]]:=
        ih _ _ _ _ mrg1 H2.
      exists Θ1'. exists Θ2'.
      exists (term_cren m ξ :L Δ1').
      exists (_: Δ2').
      repeat constructor... }
    { have[Θ1'[Θ2'[Δ1'[Δ2'[mrg1'[mrg2'[arg1 arg2]]]]]]]:=
        ih _ _ _ _ mrg1 H2.
      exists Θ1'. exists Θ2'.
      exists (_: Δ1').
      exists (term_cren m ξ :L Δ2').
      repeat constructor... } }
  { move=>Θ Θ' Γ Γ' Δ Δ' ξ m m' s e tym agr ih Θ1 Θ2 Δ1 Δ2 mrg1 mrg2.
    inv mrg2.
    have[Θ1'[Θ2'[Δ1'[Δ2'[mrg1'[mrg2'[arg1 arg2]]]]]]]:=
        ih _ _ _ _ mrg1 H2.
    exists Θ1'. exists Θ2'.
    exists (_: Δ1'). exists (_: Δ2').
    repeat constructor... }
Qed.

Lemma dyn_agree_cren_wf_nil Θ Θ' Γ' Δ' ξ :
  dyn_agree_cren ξ Θ [::] [::] Θ' Γ' Δ' -> dyn_wf Γ' Δ'.
Proof with eauto using dyn_wf.
  move e1:(nil)=>Γ.
  move e2:(nil)=>Δ agr.
  elim: agr e1 e2=>//{Γ Γ' Δ Δ' ξ}...
Qed.

Lemma dyn_agree_cren_wf_ty Θ Θ' Γ Γ' Δ Δ' A s ξ :
  dyn_agree_cren ξ Θ (A :: Γ) (A :{s} Δ) Θ' Γ' Δ' -> dyn_wf Γ Δ ->
  (∀ Θ Θ' Γ' Δ' ξ, dyn_agree_cren ξ Θ Γ Δ Θ' Γ' Δ' → dyn_wf Γ' Δ') ->
  dyn_wf Γ' Δ'.
Proof with eauto using dyn_wf.
  move e1:(A :: Γ)=>Γ0.
  move e2:(A :{s} Δ)=>Δ0 agr.
  elim: agr A Γ Δ s e1 e2=>//{Θ Θ' Γ0 Δ0 Γ' Δ' ξ}...
  move=>Θ Θ' Γ Γ' Δ Δ' ξ m m' s e tym agr _ A Γ0 Δ0 s0
         [e1 e2][_ e4 e5]wf h; subst.
  apply: dyn_wf_ty...
  replace (Sort s) with (term_cren (Sort s) ξ) by eauto.
  apply: sta_crename...
  apply: dyn_sta_agree_cren...
Qed.

Lemma dyn_agree_cren_wf_n Θ Θ' Γ Γ' Δ Δ' A ξ :
  dyn_agree_cren ξ Θ (A :: Γ) (_: Δ) Θ' Γ' Δ' -> dyn_wf Γ Δ ->
  (∀ Θ Θ' Γ' Δ' ξ, dyn_agree_cren ξ Θ Γ Δ Θ' Γ' Δ' → dyn_wf Γ' Δ') ->
  dyn_wf Γ' Δ'.
Proof with eauto using dyn_wf.
  move e1:(A :: Γ)=>Γ0.
  move e2:(_: Δ)=>Δ0 agr.
  elim: agr A Γ Δ e1 e2=>//{Θ Θ' Γ0 Δ0 Γ' Δ' ξ}...
  move=>Θ Θ' Γ Γ' Δ Δ' ξ m m' s e tym agr _ A Γ0 Δ0
         [e1 e2][e4] wf h; subst.
  apply: dyn_wf_n...
  apply: sta_ecrename...
  simpl. eauto.
  apply: dyn_sta_agree_cren...
Qed.

Lemma dyn_crename Θ Θ' Γ Γ' Δ Δ' m A ξ :
  Θ ; Γ ; Δ ⊢ m : A -> dyn_agree_cren ξ Θ Γ Δ Θ' Γ' Δ' ->
  Θ' ; Γ' ; Δ' ⊢ term_cren m ξ : term_cren A ξ.
Proof with eauto using dyn_empty, dyn_type, dyn_agree_cren.
  move=>ty. move: Θ Γ Δ m A ty Θ' Δ' Γ' ξ.
  apply:(@dyn_type_mut _
           (fun Γ Δ wf => forall Θ Θ' Γ' Δ' ξ,
                dyn_agree_cren ξ Θ Γ Δ Θ' Γ' Δ' -> dyn_wf Γ' Δ'))=>/=.
  { move=>Θ Γ Δ x s A emp wf ih shs dhs Θ' Δ' Γ' ξ agr.
    econstructor...
    apply: dyn_agree_cren_empty...
    apply: sta_agree_cren_has...
    apply: dyn_sta_agree_cren...
    apply: dyn_agree_cren_has... }
  { move=>Θ Γ Δ A B m s k1 k2 tym ihm Θ' Δ' Γ' ξ agr.
    have wf:=dyn_type_wf tym. inv wf.
    econstructor.
    apply: dyn_agree_cren_key1...
    apply: dyn_agree_cren_key2...
    apply: ihm... }
  { move=>Θ Γ Δ A B m s t k1 k2 tym ihm Θ' Δ' Γ' ξ agr.
    have wf:=dyn_type_wf tym. inv wf.
    econstructor.
    apply: dyn_agree_cren_key1...
    apply: dyn_agree_cren_key2...
    apply: ihm... }
  { move=>Θ Γ Δ A B m n s tym ihm tyn Θ' Δ' Γ' ξ agr.
    rewrite term_cren_beta1.
    apply: dyn_app0...
    apply: sta_crename...
    apply: dyn_sta_agree_cren... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n s mrg1 mrg2 tym ihm tyn ihn
           Θ' Δ' Γ' ξ agr.
    have[Θ1'[Θ2'[Δ1'[Δ2'[mrg1'[mrg2'[agr1 agr2]]]]]]]:=
      dyn_agree_cren_merge agr mrg1 mrg2.
    rewrite term_cren_beta1.
    apply: dyn_app1... }
  { move=>Θ Γ Δ A B m n t tyS tym tyn ihn Θ' Δ' Γ' ξ agr.
    apply: dyn_pair0.
    replace (Sort t) with (term_cren (Sort t) ξ) by eauto.
    apply: sta_ecrename...
    eauto.
    apply: dyn_sta_agree_cren...
    apply: sta_ecrename...
    apply: dyn_sta_agree_cren...
    rewrite<-term_cren_beta1... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n t mrg1 mrg2
           tyS tym ihm tyn ihn Θ' Δ' Γ' ξ agr.
    have[Θ1'[Θ2'[Δ1'[Δ2'[mrg1'[mrg2'[agr1 agr2]]]]]]]:=
      dyn_agree_cren_merge agr mrg1 mrg2.
    apply: dyn_pair1...
    replace (Sort t) with (term_cren (Sort t) ξ) by eauto.
    apply: sta_ecrename...
    eauto.
    apply: dyn_sta_agree_cren...
    rewrite<-term_cren_beta1... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r t mrg1 mrg2
           tyC tym ihm tyn ihn Θ' Δ' Γ' ξ agr.
    have[Θ1'[Θ2'[Δ1'[Δ2'[mrg1'[mrg2'[agr1 agr2]]]]]]]:=
      dyn_agree_cren_merge agr mrg1 mrg2.
    have wf:=sta_type_wf tyC. inv wf.
    have wf:=dyn_type_wf tyn. inv wf. inv H4.
    rewrite term_cren_beta1.
    apply: dyn_letin0...
    apply: sta_ecrename...
    simpl. eauto.
    econstructor...
    apply: dyn_sta_agree_cren...
    rewrite<-(term_cren_subst _ (term_csubst_pair0 ξ t)).
    apply: ihn.
    constructor... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r1 r2 t mrg1 mrg2
           tyC tym ihm tyn ihn Θ' Δ' Γ' ξ agr.
    have[Θ1'[Θ2'[Δ1'[Δ2'[mrg1'[mrg2'[agr1 agr2]]]]]]]:=
      dyn_agree_cren_merge agr mrg1 mrg2.
    have wf:=sta_type_wf tyC. inv wf.
    have wf:=dyn_type_wf tyn. inv wf. inv H4.
    rewrite term_cren_beta1.
    apply: dyn_letin1...
    apply: sta_ecrename...
    simpl. eauto.
    econstructor...
    apply: dyn_sta_agree_cren...
    rewrite<-(term_cren_subst _ (term_csubst_pair1 ξ t)).
    apply: ihn.
    constructor... }
  { move=>Θ Γ Δ A m k1 k2 tym ihm Θ' Δ' Γ' ξ agr.
    have wf:=dyn_type_wf tym. inv wf.
    apply: dyn_fix.
    apply: dyn_agree_cren_key1...
    apply: dyn_agree_cren_key2...
    rewrite<-term_cren_ren.
    apply: ihm.
    constructor... }
  { move=>Θ Γ Δ emp wf ih k Θ' Δ' Γ' ξ agr.
    apply: dyn_ii...
    apply: dyn_agree_cren_empty...
    apply: dyn_agree_cren_key2... }
  { move=>Θ Γ Δ emp wf ih k Θ' Δ' Γ' ξ agr.
    apply: dyn_tt...
    apply: dyn_agree_cren_empty...
    apply: dyn_agree_cren_key2... }
  { move=>Θ Γ Δ emp wf ih k Θ' Δ' Γ' ξ agr.
    apply: dyn_ff...
    apply: dyn_agree_cren_empty...
    apply: dyn_agree_cren_key2... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m n1 n2 s mrg1 mrg2
           tyA tym ihm tyn1 ihn1 tyn2 ihn2 Θ' Δ' Γ' ξ agr.
    have[Θ1'[Θ2'[Δ1'[Δ2'[mrg1'[mrg2'[agr1 agr2]]]]]]]:=
      dyn_agree_cren_merge agr mrg1 mrg2.
    have wf:=sta_type_wf tyA. inv wf.
    rewrite term_cren_beta1.
    apply: dyn_ifte...
    apply: sta_ecrename...
    simpl. eauto.
    econstructor...
    apply: dyn_sta_agree_cren...
    replace TT with (term_cren TT ξ) by eauto.
    rewrite<-term_cren_beta1...
    replace FF with (term_cren FF ξ) by eauto.
    rewrite<-term_cren_beta1... }
  { move=>Θ Γ Δ m A tym ihm Θ' Δ' Γ' ξ agr... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m n A B s t mrg1 mrg2
           tyB tym ihm tyn ihn Θ' Δ' Γ' ξ agr.
    have[Θ1'[Θ2'[Δ1'[Δ2'[mrg1'[mrg2'[agr1 agr2]]]]]]]:=
      dyn_agree_cren_merge agr mrg1 mrg2.
    have wf:=dyn_type_wf tyn. inv wf.
    apply: dyn_bind...
    apply: sta_ecrename...
    simpl. eauto.
    apply: dyn_sta_agree_cren...
    rewrite<-term_cren_ren... }
  { move=>Θ Γ Δ r x A js wf ih k tyA Θ' Δ' Γ' ξ agr.
    rewrite (sta_agree_cren_size (dyn_sta_agree_cren agr)).
    rewrite term_cren_ren.
    apply: dyn_cvar...
    have//:=dyn_agree_cren_just agr js.
    apply: dyn_agree_cren_key2...
    apply: sta_ecrename...
    eauto. constructor. }
  { move=>Θ Γ Δ m A tym ihm Θ' Δ' Γ' ξ agr.
    have wf:=dyn_type_wf tym. inv wf.
    apply: dyn_fork... }
  { move=>Θ Γ Δ r1 r2 A B m xor tym ihm Θ' Δ' Γ' ξ agr... }
  { move=>Θ Γ Δ r1 r2 A B m xor tym ihm Θ' Δ' Γ' ξ agr... }
  { move=>Θ Γ Δ r1 r2 A B m xor tym ihm Θ' Δ' Γ' ξ agr... }
  { move=>Θ Γ Δ r1 r2 A B m xor tym ihm Θ' Δ' Γ' ξ agr... }
  { move=>Θ Γ Δ r1 r2 m xor tym ihm Θ' Δ' Γ' ξ agr... }
  { move=>Θ Γ Δ r1 r2 m xor tym ihm Θ' Δ' Γ' ξ agr... }
  { move=>Θ Γ Δ A B m s eq tym ihm tyB Θ' Δ' Γ' ξ agr.
    apply: dyn_conv.
    apply: term_cren_sta_conv...
    apply: ihm...
    apply: sta_ecrename...
    simpl. eauto. 
    apply: dyn_sta_agree_cren... }
  { move=>Θ Θ' Γ' Δ' ξ agr.
    apply: dyn_agree_cren_wf_nil... }
  { move=>Γ Δ A s wf ih tyA Θ Θ' Γ' Δ' ξ agr.
    apply: dyn_agree_cren_wf_ty... }
  { move=>Γ Δ A s wf ih tyA Θ Θ' Γ' Δ' ξ agr.
    apply: dyn_agree_cren_wf_n... }
Qed.

Lemma dyn_strengthen Θ m A :
  _: Θ ; nil ; nil ⊢ term_cren m (+1) : term_cren A (+1) ->
  Θ ; nil ; nil ⊢ m : A.
Proof with eauto using dyn_empty, dyn_type, dyn_agree_cren.
  move=>ty.
  have e:((+1) >>> subn_rec^~ 1) = id.
  { f_ext. move=>x. asimpl. fold subn. lia. }
  replace m with (term_cren (term_cren m (+1)) (subn^~ 1 >>> id)).
  replace A with (term_cren (term_cren A (+1)) (subn^~ 1 >>> id)).
  apply: dyn_crename.
  apply: ty.
  constructor.
  constructor.
  constructor.
  rewrite<-term_cren_comp. asimpl.
  rewrite e. apply: term_cren_id.
  rewrite<-term_cren_comp. asimpl.
  rewrite e. apply: term_cren_id.
Qed.

Lemma dyn_weaken Θ m A :
  Θ ; nil ; nil ⊢ m : A ->
  _: Θ ; nil ; nil ⊢ term_cren m (+1) : term_cren A (+1).
Proof with eauto using dyn_empty, dyn_type, dyn_agree_cren.
  move=>ty. apply: dyn_crename...
  constructor.
  constructor.
  constructor.
Qed.

