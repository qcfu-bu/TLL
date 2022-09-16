From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.

From Coq Require Import ssrfun Classical Utf8.
Require Import AutosubstSsr ARS.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope sort_scope.
Delimit Scope sort_scope with srt.
Open Scope sort_scope.

Inductive sort : Type := U | L.
Bind Scope sort_scope with sort.

Definition elem T := option (T * sort).
Definition dyn_ctx T := seq (elem T).

Notation "m :U Γ" := (Some (m, U) :: Γ)
  (at level 30, right associativity).
Notation "m :L Γ" := (Some (m, L) :: Γ)
  (at level 30, right associativity).
Notation "m :{ s } Γ" := (Some (m, s) :: Γ)
  (at level 30, right associativity, format "m  :{ s }  Γ").
Notation "_: Γ" := (None :: Γ)
  (at level 30, right associativity).

Definition sort_plus (s t : sort) :=
  match s with
  | U => t
  | L => L
  end.
Infix "+" := sort_plus : sort_scope.

Inductive sort_leq : sort -> sort -> Prop :=
| sort_leqU s :
  sort_leq U s
| sort_leqL :
  sort_leq L L.
Infix "≤" := sort_leq : sort_scope.

Reserved Notation "Δ1 ∘ Δ2 => Δ" (at level 40).
Inductive merge T : dyn_ctx T -> dyn_ctx T -> dyn_ctx T -> Prop :=
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
Inductive key T : dyn_ctx T -> sort -> Prop :=
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

Inductive dyn_has {T} `{Ids T} `{Subst T} :
  dyn_ctx T -> var -> T -> Prop :=
| dyn_has_O Γ A s :
  Γ ▷ U ->
  dyn_has (A :{s} Γ) 0 A.[ren (+1)]
| dyn_has_S Γ A B x :
  dyn_has Γ x A ->
  dyn_has (B :U Γ) x.+1 A.[ren (+1)]
| dyn_has_N Γ A x :
  dyn_has Γ x A ->
  dyn_has (_: Γ) x.+1 A.[ren (+1)].

