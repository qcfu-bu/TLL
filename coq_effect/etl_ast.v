From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope sort_scope.
Delimit Scope sort_scope with srt.
Open Scope sort_scope.

Inductive term : Type :=
| Var (x : var)
| Ty
| Forall0 (A : term) (B : {bind term}) (* ∀{x : A}.B *)
| Forall1 (A : term) (B : {bind term}) (* ∀(x : A).B *)
| Arrow   (A : term) (B : term)        (* A → B      *)
| Lam0 (A : term) (m : {bind term})    (* Λ{x : A}.m *)
| Lam1 (A : term) (m : {bind term})    (* Λ(x : A).m *)
| Fun (A : term) (m : {bind term})     (* λ(x : A).m *)
| App (m n : term)                     (* m n *).

#[global] Instance Ids_term : Ids term. derive. Defined.
#[global] Instance Rename_term : Rename term. derive. Defined.
#[global] Instance Subst_term : Subst term. derive. Defined.
#[global] Instance substLemmas_term : SubstLemmas term. derive. Qed.
