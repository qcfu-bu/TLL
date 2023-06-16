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

Inductive All1 A (P : A -> Prop) : list A -> Prop :=
| All1_nil : All1 P nil
| All1_cons m ls : P m -> All1 P ls -> All1 P (m :: ls).

Inductive One2 A R : list A -> list A -> Prop :=
| One2_hd m m' ls :
  R m m' ->
  One2 R (m :: ls) (m' :: ls)
| One2_tl m ls ls' :
  One2 R ls ls' ->
  One2 R (m :: ls) (m :: ls').

Inductive All2 A (R : A -> A -> Prop) : list A -> list A -> Prop :=
| All2_nil : All2 R nil nil
| All2_cons m m' ls ls' :
  R m m' ->
  All2 R ls ls' ->
  All2 R (m :: ls) (m' :: ls').

Inductive All2i A R : nat -> list A -> list A -> Prop :=
| All2i_nil i : All2i R i nil nil
| All2i_cons i m m' ls ls' :
  R i m m' ->
  All2i R i.+1 ls ls' ->
  All2i R i (m :: ls) (m' :: ls').

Lemma nth_All2 A (R : A -> A -> Prop) xs ys x n :
  All2 R xs ys -> nth n xs x -> exists y, nth n ys y /\ R x y.
Proof with eauto using nth.
  move=>h. elim: h x n=>{xs ys}.
  move=>x n h. inv h.
  move=>m m' ls ls' r h ih x n h0. inv h0.
  exists m'...
  have[y[h1 h2]]:=ih _ _ H3. exists y...
Qed.

Lemma nth_All2i A (R : nat -> A -> A -> Prop) xs ys x i n :
  All2i R i xs ys -> nth n xs x -> exists y, nth n ys y /\ R (i + n) x y.
Proof with eauto using nth.
  move=>h. elim: h x n=>{xs ys i}.
  move=>i x n h. inv h.
  move=>i m m' ls ls' h1 h2 ih x n h3. inv h3.
  exists m'. split... replace (i + 0) with i by lia...
  have[y[h4 h5]]:=ih _ _ H3.
  exists y. split... replace (i + n0.+1) with (i.+1 + n0) by lia...
Qed.
