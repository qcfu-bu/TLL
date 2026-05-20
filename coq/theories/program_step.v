(** * Program small-step reduction

    Call-by-value-style reduction [program_step] / [~>>] for TLL terms.
    Compared with [logical_step]: β1 fires only on values
    ([program_step_beta1]), [Pair1] reduces in both components but
    [Pair0] only in its first, [Ifte] reduces only its scrutinee, and
    [Rw] always strips to its [H]-witness. The set of values
    [program_val] includes pointers [Ptr l] (used by [heap_*]). *)

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Stdlib Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS tll_ast.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive program_val : term -> Prop :=
| program_val_var x :
  program_val (Var x)
| program_val_lam0 A B s :
  program_val (Lam0 A B s)
| program_val_lam1 A B s :
  program_val (Lam1 A B s)
| program_val_pair0 m1 m2 s :
  program_val m1 ->
  program_val (Pair0 m1 m2 s)
| program_val_pair1 m1 m2 s :
  program_val m1 ->
  program_val m2 ->
  program_val (Pair1 m1 m2 s)
| program_val_tt : program_val TT
| program_val_ff : program_val FF
| program_val_heap l :
  program_val (Ptr l).

Reserved Notation "m ~>> n" (at level 50).
Inductive program_step : term -> term -> Prop :=
| program_step_appL m m' n :
  m ~>> m' ->
  App m n ~>> App m' n
| program_step_appR m n n' :
  n ~>> n' ->
  App m n ~>> App m n'
| program_step_beta0 A m n s :
  App (Lam0 A m s) n ~>> m.[n/]
| program_step_beta1 A m v s :
  program_val v ->
  App (Lam1 A m s) v ~>> m.[v/]
| program_step_pair0L m m' n s :
  m ~>> m' ->
  Pair0 m n s ~>> Pair0 m' n s
| program_step_pair1L m m' n s :
  m ~>> m' ->
  Pair1 m n s ~>> Pair1 m' n s
| program_step_pair1R m n n' s :
  n ~>> n' ->
  Pair1 m n s ~>> Pair1 m n' s
| program_step_letinL A m m' n :
  m ~>> m' ->
  LetIn A m n ~>> LetIn A m' n
| program_step_iota0 A m1 m2 n s :
  program_val (Pair0 m1 m2 s) ->
  LetIn A (Pair0 m1 m2 s) n ~>> n.[m2,m1/]
| program_step_iota1 A m1 m2 n s :
  program_val (Pair1 m1 m2 s) ->
  LetIn A (Pair1 m1 m2 s) n ~>> n.[m2,m1/]
| program_step_ifteM A m m' n1 n2 :
  m ~>> m' ->
  Ifte A m n1 n2 ~>> Ifte A m' n1 n2
| program_step_ifteT A n1 n2 :
  Ifte A TT n1 n2 ~>> n1
| program_step_ifteF A n1 n2 :
  Ifte A FF n1 n2 ~>> n2
| program_step_rwE A H P :
  Rw A H P ~>> H
where "m ~>> n" := (program_step m n).

Notation program_red := (star program_step).
Notation "m ~>>* n" := (program_red m n) (at level 50).
