From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive term : Type :=
| Var (x : var)
| Ty
| Pi (A : term) (B : {bind term}) (* Π {x : A}.B *)
| Lam (A : term) (m : {bind term}) (* λ {x : A}.m *)
| App (m n : term)
| Id (A m n : term)
| Refl (m : term)
| Rw (A : {bind 2 of term}) (H P : term) (* R≡([x,p]A,H,P) *).

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance substLemmas_term : SubstLemmas term. derive. Qed.
