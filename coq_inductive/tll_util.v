From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq zify.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive nth A : nat -> list A -> A -> Prop :=
| nth_O m ls :
  nth 0 (m :: ls) m
| nth_S n m m' ls :
  nth n ls m ->
  nth n.+1 (m' :: ls) m.

Inductive Forall1 A (P : A -> Prop) : list A -> Prop :=
| Forall1_nil : Forall1 P nil
| Forall1_cons m ls : P m -> Forall1 P ls -> Forall1 P (m :: ls).

Notation "'{' '∀' x '∈' xs ',' P }" :=
  (Forall1 (fun x => P) xs) (x name, at level 200).

Inductive Exists1 A (P : A -> Prop) : list A -> Prop :=
| Exists1_exist m ls : 
  P m ->
  Exists1 P (m :: ls)
| Exists1_extend m ls :
  Exists1 P ls ->
  Exists1 P (m :: ls).

Notation "'{' '∃' x '∈' xs ',' P }" :=
  (Exists1 (fun x => P) xs).

Inductive Forall2 A (R : A -> A -> Prop) : list A -> list A -> Prop :=
| Forall2_nil :
  Forall2 R nil nil
| Froall2_cons m m' ls ls' :
  R m m' ->
  Forall2 R ls ls' ->
  Forall2 R (m :: ls) (m' :: ls').

Notation "'{' '∀' x y '∈' xs & ys ',' R }" :=
  (Forall2 (fun x y => R) xs ys) (x name, y name, at level 200).

Inductive Exists2 A (R : A -> A -> Prop) : list A -> list A -> Prop :=
| Exists2_exist m m' ls :
  R m m' ->
  Exists2 R (m :: ls) (m' :: ls)
| Exists2_extend m ls ls' :
  Exists2 R ls ls' ->
  Exists2 R (m :: ls) (m :: ls').

Notation "'{' '∃' x y '∈' xs & ys ',' R }" :=
  (Exists2 (fun x y => R) xs ys) (x name, y name, at level 200).

Inductive Forall2i' A (R : nat -> A -> A -> Prop) : nat -> list A -> list A -> Prop :=
| Forall2i'_nil i :
  Forall2i' R i nil nil
| Forall2i'_cons i m m' ls ls' :
  R i m m' ->
  Forall2i' R i.+1 ls ls' ->
  Forall2i' R i (m :: ls) (m' :: ls').

Notation "'{' '∀' '(' n \≤ i ')' x y '∈' xs & ys ',' R }" :=
  (Forall2i' (fun i x y => R) n xs ys) (i name, x name, y name, at level 200).

Definition Forall2i A R ls ls' :=
  @Forall2i' A R 0 ls ls'.

Notation "'{' '∀' i x y '∈' xs & ys ',' R }" :=
  (Forall2i (fun i x y => R) xs ys) (i name, x name, y name, at level 200).

Lemma nth_Forall2 A (R : A -> A -> Prop) xs ys x n :
 { ∀ x y ∈ xs & ys, R x y } -> nth n xs x -> exists y, nth n ys y /\ R x y.
Proof with eauto using nth.
  move=>h. elim: h x n=>{xs ys}.
  move=>x n h. inv h.
  move=>m m' ls ls' r h ih x n h0. inv h0.
  exists m'...
  have[y[h1 h2]]:=ih _ _ H3. exists y...
Qed.

Lemma nth_Forall2i' A (R : nat -> A -> A -> Prop) xs ys x i n :
  { ∀ (i \≤ j) x y ∈ xs & ys, R j x y } -> nth n xs x -> exists y, nth n ys y /\ R (i + n) x y.
Proof with eauto using nth.
  move=>h. elim: h x n=>{xs ys i}.
  move=>i x n h. inv h.
  move=>i m m' ls ls' h1 h2 ih x n h3. inv h3.
  exists m'. split... replace (i + 0) with i by lia...
  have[y[h4 h5]]:=ih _ _ H3.
  exists y. split... replace (i + n0.+1) with (i.+1 + n0) by lia...
Qed.

Lemma nth_Forall2i A (R : nat -> A -> A -> Prop) xs ys x n :
  {∀ i x y ∈ xs & ys, R i x y} -> nth n xs x -> exists y, nth n ys y /\ R n x y.
Proof with eauto using nth.
  move=>h1 h2. unfold Forall2i in h1.
  have[y[h3 h4]]:=nth_Forall2i' h1 h2.
  exists y=>//.
Qed.
