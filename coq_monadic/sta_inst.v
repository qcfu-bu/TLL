From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_conf.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive inst : term -> term -> Prop :=
| inst_var x :
  inst (Var x) (Var x)
| inst_sort s :
  inst (Sort s) (Sort s)
| inst_pi0 A A' B B' s :
  inst A A' ->
  inst B B' ->
  inst (Pi0 A B s) (Pi0 A' B' s)
| inst_pi1 A A' B B' s :
  inst A A' ->
  inst B B' ->
  inst (Pi1 A B s) (Pi1 A' B' s)
| inst_lam0 A A' m m' s :
  inst A A' ->
  inst m m' ->
  inst (Lam0 A m s) (Lam0 A' m' s)
| inst_lam1 A A' m m' s :
  inst A A' ->
  inst m m' ->
  inst (Lam1 A m s) (Lam1 A' m' s)
| inst_app m m' n n' :
  inst m m' ->
  inst n n' ->
  inst (App m n) (App m' n')
| inst_unit :
  inst Unit Unit
| inst_it :
  inst It It
| inst_nat :
  inst Nat Nat
| inst_num n :
  inst (Num n) (Num n)
| inst_rand0 :
  inst Rand Rand
| inst_rand1 n :
  inst (Lam1 Unit (Num n) U) Rand
| inst_box :
  inst Box Box.
Infix "<:" := inst (at level 50, no associativity).

Lemma inst_refl A : inst A A.
Proof with eauto using inst. elim: A... Qed.

Lemma inst_trans A B C : A <: B -> B <: C -> A <: C.
Proof with eauto using inst, inst_refl.
  move=>ist. elim: ist C=>{A B}...
  { move=>A A' B B' s istA ihA istB ihB C ist. inv ist... }
  { move=>A A' B B' s istA ihA istB ihB C ist. inv ist... }
  { move=>A A' m m' s istA ihA istm ihm C ist. inv ist... }
  { move=>A A' m m' s istA ihA istm ihm C ist.
    inv ist... inv istA. inv istm... }
  { move=>m m' n n' istm ihm istn ihn C ist. inv ist... }
  { move=>n C ist. inv ist... }
Qed.

Lemma inst_subst A B σ : A <: B -> A.[σ] <: B.[σ].
Proof with eauto using inst, inst_refl.
  move=>ist. elim: ist σ=>{A B}...
Qed.
