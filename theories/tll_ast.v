From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS dyn_ctx.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive term : Type :=
| Var (x : var)
| Sort (s : sort)
| Pi0 (A : term) (B : {bind term}) (s t : sort)
| Pi1 (A : term) (B : {bind term}) (s t : sort)
| Lam0 (A : term) (m : {bind term}) (s t : sort)
| Lam1 (A : term) (m : {bind term}) (s t : sort)
| App (m n : term).

Notation "@ s" := (Sort s) (at level 20).

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance substLemmas_term : SubstLemmas term. derive. Qed.
