From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Import AutosubstSsr ARS tll_ast tll_cren.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition elem T := option (T * sort).
Definition dyn_ctx := seq (elem term).

Notation "m :U Γ" := (Some (m, U) :: Γ)
  (at level 30, right associativity).
Notation "m :L Γ" := (Some (m, L) :: Γ)
  (at level 30, right associativity).
Notation "m .{ s } Γ" := (Some (m, s) :: Γ)
  (at level 30, right associativity, format "m  .{ s }  Γ").
Notation "_: Γ" := (None :: Γ)
  (at level 30, right associativity).

Reserved Notation "Δ1 ∘ Δ2 => Δ" (at level 40).
Inductive merge : dyn_ctx -> dyn_ctx -> dyn_ctx -> Prop :=
| merge_nil :
  nil ∘ nil => nil
| merge_left Δ1 Δ2 Δ m :
  Δ1 ∘ Δ2 => Δ ->
  m :U Δ1 ∘ m :U Δ2 => m :U Δ
| merge_right1 Δ1 Δ2 Δ m :
  Δ1 ∘ Δ2 => Δ ->
  m :L Δ1 ∘ _: Δ2 => m :L Δ
| merge_right2 Δ1 Δ2 Δ m :
  Δ1 ∘ Δ2 => Δ ->
  _: Δ1 ∘ m :L Δ2 => m :L Δ
| merge_null Δ1 Δ2 Δ :
  Δ1 ∘ Δ2 => Δ ->
  _: Δ1 ∘ _: Δ2 => _: Δ
where "Δ1 ∘ Δ2 => Δ" := (merge Δ1 Δ2 Δ).

Reserved Notation "Δ ▷ s" (at level 40).
Inductive key : dyn_ctx -> sort -> Prop :=
| key_nil s :
  nil ▷ s
| key_u Δ m :
  Δ ▷ U ->
  m :U Δ ▷ U
| key_l Δ m s :
  Δ ▷ L ->
  m .{s} Δ ▷ L
| key_n Δ s :
  Δ ▷ s ->
  _: Δ ▷ s
where "Δ ▷ s" := (key Δ s).

Inductive dyn_empty : dyn_ctx -> Prop :=
| dyn_empty_nil :
  dyn_empty nil
| dyn_empty_n Δ :
  dyn_empty Δ ->
  dyn_empty (_: Δ).

Inductive dyn_has : dyn_ctx -> var -> sort -> term -> Prop :=
| dyn_has_O Δ A s :
  Δ ▷ U ->
  dyn_has (A .{s} Δ) 0 s A.[ren (+1)]
| dyn_has_S Δ A B x s :
  dyn_has Δ x s A ->
  dyn_has (B :U Δ) x.+1 s A.[ren (+1)]
| dyn_has_N Δ A x s :
  dyn_has Δ x s A ->
  dyn_has (_: Δ) x.+1 s A.[ren (+1)].

Inductive dyn_just : dyn_ctx -> var -> term -> Prop :=
| dyn_just_O Δ A :
  dyn_empty Δ ->
  dyn_just (A :L Δ) 0 (cren (+1) A)
| dyn_just_N Δ A x :
  dyn_just Δ x A ->
  dyn_just (_: Δ) x.+1 (cren (+1) A).

Lemma key_impure Δ : Δ ▷ L.
Proof with eauto using key.
  elim: Δ... move=>[[A s]|] Δ k...
Qed.

Lemma key_empty Δ s : dyn_empty Δ -> Δ ▷ s.
Proof with eauto using key. elim... Qed.

Lemma empty_split Δ1 Δ2 Δ : Δ1 ∘ Δ2 => Δ -> dyn_empty Δ -> dyn_empty Δ1 /\ dyn_empty Δ2.
Proof with eauto using dyn_empty.
  elim=>{Δ1 Δ2 Δ}...
  { move=>Δ1 Δ2 Δ m mrg ih emp. inv emp. }
  { move=>Δ1 Δ2 Δ m mrg ih emp. inv emp. }
  { move=>Δ1 Δ2 Δ m mrg ih emp. inv emp. }
  { move=>Δ1 Δ2 Δ mrg ih emp. inv emp.
    have[emp1 emp2]:=ih H0... }
Qed.

Lemma merge_empty Δ1 Δ2 Δ : Δ1 ∘ Δ2 => Δ -> dyn_empty Δ1 -> dyn_empty Δ2 -> dyn_empty Δ.
Proof with eauto using dyn_empty.
  elim=>{Δ1 Δ2 Δ}...
  { move=>Δ1 Δ2 Δ m mrg ih emp1 emp2. inv emp1. }
  { move=>Δ1 Δ2 Δ m mrg ih emp1 emp2. inv emp1. }
  { move=>Δ1 Δ2 Δ m mrg ih emp1 emp2. inv emp2. }
  { move=>Δ1 Δ2 Δ mrg ih emp1 emp2. inv emp1. inv emp2... }
Qed.

Lemma merge_emptyL Δ1 Δ2 Δ : Δ1 ∘ Δ2 => Δ -> dyn_empty Δ1 -> Δ2 = Δ.
Proof with eauto.
  elim=>{Δ1 Δ2 Δ}...
  { move=>Δ1 Δ2 Δ m mrg ih emp. inv emp. }
  { move=>Δ1 Δ2 Δ m mrg ih emp. inv emp. }
  { move=>Δ1 Δ2 Δ m mrg ih emp. inv emp. rewrite ih... }
  { move=>Δ1 Δ2 Δ mrg ih emp. inv emp. rewrite ih... }
Qed.

Lemma merge_emptyR Δ1 Δ2 Δ : Δ1 ∘ Δ2 => Δ -> dyn_empty Δ2 -> Δ1 = Δ.
Proof with eauto.
  elim=>{Δ1 Δ2 Δ}...
  { move=>Δ1 Δ2 Δ m mrg ih emp. inv emp. }
  { move=>Δ1 Δ2 Δ m mrg ih emp. inv emp. rewrite ih... }
  { move=>Δ1 Δ2 Δ m mrg ih emp. inv emp. }
  { move=>Δ1 Δ2 Δ mrg ih emp. inv emp. rewrite ih... }
Qed.

Lemma empty_merge_self Δ : dyn_empty Δ -> Δ ∘ Δ => Δ.
Proof with eauto using merge. elim... Qed.

Lemma just_empty Δ x A : dyn_just Δ x A -> exists Δ0, dyn_empty Δ0 /\ Δ0 ∘ Δ => Δ.
Proof with eauto.
  elim=>{Δ x A}...
  { move=>Δ A emp. exists (_: Δ). split; constructor... apply: empty_merge_self... }
  { move=>Δ A x js[Δ0[emp mrg]]. exists (_: Δ0). split; constructor...  }
Qed.

Lemma empty_just Δ x A : dyn_empty Δ -> ~dyn_just Δ x A.
Proof with eauto.
  move=>emp. elim: emp x A=>{Δ}.
  { move=>x A js. inv js. }
  { move=>Δ emp ih x A js. inv js.
    apply: ih... }
Qed.

Lemma pure_just Δ x A : dyn_just Δ x A -> ~Δ ▷ U.
Proof with eauto using key.
  elim=>{Δ x A}.
  { move=>Δ A emp k. inv k. }
  { move=>Δ A x js ih k. inv k... }
Qed.

Lemma pure_merge_self Δ : Δ ▷ U -> Δ ∘ Δ => Δ.
Proof with eauto using merge.
  move e:(U)=>s k. elim: k e=>//{Δ s}...
Qed.

Lemma key_merge Δ1 Δ2 Δ s : Δ1 ∘ Δ2 => Δ -> Δ1 ▷ s -> Δ2 ▷ s -> Δ ▷ s.
Proof with eauto using key.
  move=>mrg. elim: mrg s=>{Δ1 Δ2 Δ}...
  { move=>Δ1 Δ2 Δ m mrg ih s k1 k2. inv k1; inv k2... }
  { move=>Δ1 Δ2 Δ m mrg ih s k1 k2. inv k1; inv k2... }
  { move=>Δ1 Δ2 Δ m mrg ih s k1 k2. inv k1; inv k2... }
  { move=>Δ1 Δ2 Δ m mrg ih k1 k2. inv k1; inv k2... }
Qed.

Lemma pure_split Δ1 Δ2 Δ : Δ1 ∘ Δ2 => Δ -> Δ ▷ U -> Δ1 ▷ U /\ Δ2 ▷ U.
Proof with eauto using key.
  elim=>{Δ1 Δ2 Δ}...
  { move=>Δ1 Δ2 Δ m mrg ih k. inv k. have[]:=ih H0... }
  { move=>Δ1 Δ2 Δ m mrg ih k. inv k. }
  { move=>Δ1 Δ2 Δ m mrg ih k. inv k. }
  { move=>Δ1 Δ2 Δ mrg ih k. inv k. have[]:=ih H0... }
Qed.

Lemma merge_sym Δ1 Δ2 Δ : Δ1 ∘ Δ2 => Δ -> Δ2 ∘ Δ1 => Δ.
Proof with eauto using merge. elim... Qed.

Lemma merge_inj Δ1 Δ2 Δx Δy : Δ1 ∘ Δ2 => Δx -> Δ1 ∘ Δ2 => Δy -> Δx = Δy.
Proof with eauto.
  move=>mrg. elim: mrg Δy=>{Δ1 Δ2 Δx}.
  { move=>Δy mrg. inv mrg... }
  { move=>Δ1 Δ2 Δ m mrg1 ih Δy mrg2. inv mrg2. rewrite (ih _ H3)... }
  { move=>Δ1 Δ2 Δ m mrg1 ih Δy mrg2. inv mrg2. rewrite (ih _ H3)... }
  { move=>Δ1 Δ2 Δ m mrg1 ih Δy mrg2. inv mrg2. rewrite (ih _ H3)... }
  { move=>Δ1 Δ2 Δ mrg1 ih Δy mrg2. inv mrg2. rewrite (ih _ H1)... }
Qed.

Lemma merge_pureL Δ1 Δ2 Δ : Δ1 ∘ Δ2 => Δ -> Δ1 ▷ U -> Δ = Δ2.
Proof.
  elim=>//={Δ1 Δ2 Δ}.
  { move=>Δ1 Δ2 Δ m mrg ih k. inv k. by rewrite ih. }
  { move=>Δ1 Δ2 Δ m mrg ih k. inv k. }
  { move=>Δ1 Δ2 Δ m mrg ih k. inv k. by rewrite ih. }
  { move=>Δ1 Δ2 Δ mrg ih k. inv k. by rewrite ih. }
Qed.

Lemma merge_pureR Δ1 Δ2 Δ : Δ1 ∘ Δ2 => Δ -> Δ2 ▷ U -> Δ = Δ1.
Proof.
  elim=>//={Δ1 Δ2 Δ}.
  { move=>Δ1 Δ2 Δ m mrg ih k. inv k. by rewrite ih. }
  { move=>Δ1 Δ2 Δ m mrg ih k. inv k. by rewrite ih. }
  { move=>Δ1 Δ2 Δ m mrg ih k. inv k. }
  { move=>Δ1 Δ2 Δ mrg ih k. inv k. by rewrite ih. }
Qed.

Lemma merge_splitL Δ1 Δ2 Δ Δa Δb :
  Δ1 ∘ Δ2 => Δ -> Δa ∘ Δb => Δ1 -> exists Δc, Δa ∘ Δ2 => Δc /\ Δc ∘ Δb => Δ.
Proof with eauto using merge.
  move=>mrg. elim: mrg Δa Δb=>{Δ1 Δ2 Δ}.
  { move=>Δa Δb mrg. inv mrg. exists nil... }
  { move=>Δ1 Δ2 Δ m mrg1 ih Δa Δb mrg2. inv mrg2.
    have[Δc[mrga mrgb]]:=ih _ _ H2.
    exists (m :U Δc)... }
  { move=>Δ1 Δ2 Δ m mrg1 ih Δa Δb mrg2. inv mrg2.
    have[Δc[mrga mrgb]]:=ih _ _ H2. exists (m :L Δc)...
    have[Δc[mrga mrgb]]:=ih _ _ H2. exists (_: Δc)... }
  { move=>Δ1 Δ2 Δ m mrg1 ih Δa Δb mrg2. inv mrg2.
    have[Δc[mrga mrgb]]:=ih _ _ H2. exists (m :L Δc)... }
  { move=>Δ1 Δ2 Δ mrg1 ih Δa Δb mrg2. inv mrg2.
    have[Δc[mrga mrgb]]:=ih _ _ H2. exists (_: Δc)... }
Qed.

Lemma merge_splitR Δ1 Δ2 Δ Δa Δb :
  Δ1 ∘ Δ2 => Δ -> Δa ∘ Δb => Δ1 -> exists Δc, Δb ∘ Δ2 => Δc /\ Δc ∘ Δa => Δ.
Proof with eauto using merge.
  move=>mrg. elim: mrg Δa Δb=>{Δ1 Δ2 Δ}.
  { move=>Δa Δb mrg. inv mrg. exists nil... }
  { move=>Δ1 Δ2 Δ m mrg1 ih Δa Δb mrg2. inv mrg2.
    have[Δc[mrga mrgb]]:=ih _ _ H2.
    exists (m :U Δc)... }
  { move=>Δ1 Δ2 Δ m mrg1 ih Δa Δb mrg2. inv mrg2.
    have[Δc[mrga mrgb]]:=ih _ _ H2. exists (_: Δc)...
    have[Δc[mrga mrgb]]:=ih _ _ H2. exists (m :L Δc)... }
  { move=>Δ1 Δ2 Δ m mrg1 ih Δa Δb mrg2. inv mrg2.
    have[Δc[mrga mrgb]]:=ih _ _ H2. exists (m :L Δc)... }
  { move=>Δ1 Δ2 Δ mrg1 ih Δa Δb mrg2. inv mrg2.
    have[Δc[mrga mrgb]]:=ih _ _ H2. exists (_: Δc)... }
Qed.

Lemma merge_distr Γ1 Γ2 Γ :
  Γ1 ∘ Γ2 => Γ ->
  forall Δ11 Δ12 Δ21 Δ22,
    Δ11 ∘ Δ12 => Γ1 ->
    Δ21 ∘ Δ22 => Γ2 ->
    exists Δ1 Δ2,
      Δ1 ∘ Δ2 => Γ /\
      Δ11 ∘ Δ21 => Δ1 /\
      Δ12 ∘ Δ22 => Δ2.
Proof with eauto using merge.
  elim=>{Γ1 Γ2 Γ}.
  { move=>D11 D12 D21 D22 mrg1 mrg2.
    inv mrg1. inv mrg2. exists nil. exists nil... }
  { move=>G1 G2 G m mrg ih D11 D12 D21 D22 mrg1 mrg2.
    inv mrg1. inv mrg2.
    have{ih}[D1[D2[mrg3[mrg4 mrg5]]]]:=ih _ _ _ _ H2 H3.
    exists (m :U D1). exists (m :U D2).
    repeat split... }
  { move=>G1 G2 G m mrg ih D11 D12 D21 D22 mrg1 mrg2.
    inv mrg1; inv mrg2.
    have{ih}[D1[D2[mrg3[mrg4 mrg5]]]]:=ih _ _ _ _ H2 H3.
    exists (m :L D1). exists (_: D2). repeat split...
    have{ih}[D1[D2[mrg3[mrg4 mrg5]]]]:=ih _ _ _ _ H2 H3.
    exists (_: D1). exists (m :L D2). repeat split... }
  { move=>G1 G2 G m mrg ih D11 D12 D21 D22 mrg1 mrg2.
    inv mrg1; inv mrg2.
    have{ih}[D1[D2[mrg3[mrg4 mrg5]]]]:=ih _ _ _ _ H2 H3.
    exists (m :L D1). exists (_: D2). repeat split...
    have{ih}[D1[D2[mrg3[mrg4 mrg5]]]]:=ih _ _ _ _ H2 H3.
    exists (_: D1). exists (m :L D2). repeat split... }
  { move=>G1 G2 G mrg ih D11 D12 D21 D22 mrg1 mrg2.
    inv mrg1; inv mrg2.
    have{ih}[D1[D2[mrg3[mrg4 mrg5]]]]:=ih _ _ _ _ H2 H3.
    exists (_: D1). exists (_: D2). repeat split... }
Qed.
