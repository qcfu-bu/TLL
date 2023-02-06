From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Import AutosubstSsr ARS tll_ast.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition elem T := option (T * sort).
Definition dyn_ctx := seq (elem term).

Notation "m :U Γ" := (Some (m, U) :: Γ)
  (at level 30, right associativity).
Notation "m :L Γ" := (Some (m, L) :: Γ)
  (at level 30, right associativity).
Notation "m :{ s } Γ" := (Some (m, s) :: Γ)
  (at level 30, right associativity, format "m  :{ s }  Γ").
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
  m :{s} Δ ▷ L
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
  dyn_has (A :{s} Δ) 0 s A.[ren (+1)]
| dyn_has_S Δ A B x s :
  dyn_has Δ x s A ->
  dyn_has (B :U Δ) x.+1 s A.[ren (+1)]
| dyn_has_N Δ A x s :
  dyn_has Δ x s A ->
  dyn_has (_: Δ) x.+1 s A.[ren (+1)].

Inductive dyn_just : dyn_ctx -> var -> term -> Prop :=
| dyn_just_O Δ A :
  dyn_empty Δ ->
  dyn_just (A :L Δ) 0 A.[ren (+1)]
| dyn_just_N Δ A x :
  dyn_just Δ x A ->
  dyn_just (_: Δ) x.+1 A.[ren (+1)].

Lemma key_impure Δ : Δ ▷ L.
Proof with eauto using key.
  elim: Δ... move=>[[A s]|] Δ k...
Qed.

Lemma key_merge Δ1 Δ2 Δ s : Δ1 ∘ Δ2 => Δ -> Δ1 ▷ s -> Δ2 ▷ s -> Δ ▷ s.
Proof with eauto using key.
  move=>mrg. elim: mrg s=>{Δ1 Δ2 Δ}...
  { move=>Δ1 Δ2 Δ m mrg ih s k1 k2. inv k1; inv k2... }
  { move=>Δ1 Δ2 Δ m mrg ih s k1 k2. inv k1; inv k2... }
  { move=>Δ1 Δ2 Δ m mrg ih s k1 k2. inv k1; inv k2... }
  { move=>Δ1 Δ2 Δ m mrg ih k1 k2. inv k1; inv k2... }
Qed.

Lemma merge_sym Δ1 Δ2 Δ : Δ1 ∘ Δ2 => Δ -> Δ2 ∘ Δ1 => Δ.
Proof with eauto using merge. elim... Qed.

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
