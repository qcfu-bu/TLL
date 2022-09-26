From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope sort_scope.
Delimit Scope sort_scope with srt.
Open Scope sort_scope.

Inductive sort : Type := U | L.
Bind Scope sort_scope with sort.

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

Inductive term : Type :=
| Var (x : var)
| Sort (s : sort)
| Pi0 (A : term) (B : {bind term}) (s : sort)
| Pi1 (A : term) (B : {bind term}) (s : sort)
| Lam0 (A : term) (m : {bind term}) (s : sort)
| Lam1 (A : term) (m : {bind term}) (s : sort)
| App (m n : term)
| Box.

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance substLemmas_term : SubstLemmas term. derive. Qed.
