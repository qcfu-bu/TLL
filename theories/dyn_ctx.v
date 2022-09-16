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
| key_u Γ m :
  Γ ▷ U ->
  m :U Γ ▷ U
| key_l Γ m s :
  Γ ▷ L ->
  m :{s} Γ ▷ L
| key_n Γ s :
  Γ ▷ s ->
  _: Γ ▷ s
where "Γ ▷ s" := (key Γ s).

Inductive dyn_has : dyn_ctx -> var -> term -> Prop :=
| dyn_has_O Γ A s :
  Γ ▷ U ->
  dyn_has (A :{s} Γ) 0 A.[ren (+1)]
| dyn_has_S Γ A B x :
  dyn_has Γ x A ->
  dyn_has (B :U Γ) x.+1 A.[ren (+1)]
| dyn_has_N Γ A x :
  dyn_has Γ x A ->
  dyn_has (_: Γ) x.+1 A.[ren (+1)].

