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
Notation "s ⊑ t" := (sort_leq s t) (at level 30) : sort_scope.

Inductive term : Type :=
(* core *)
| Var (x : var)
| Sort (s : sort)
| Pi0 (A : term) (B : {bind term}) (s : sort) (* Πs {x : A}.B *)
| Pi1 (A : term) (B : {bind term}) (s : sort) (* Πs (x : A).B *)
| Lam0 (A : term) (m : {bind term}) (s : sort) (* λs {x : A}.B *)
| Lam1 (A : term) (m : {bind term}) (s : sort) (* λs (x : A).B *)
| App (m n : term)
| Sig0 (A : term) (B : {bind term}) (s : sort) (* Σs {x : A}.B *)
| Sig1 (A : term) (B : {bind term}) (s : sort) (* Σs (x : A).B *)
| Pair0 (m n : term) (s : sort) (* {m, n}s *)
| Pair1 (m n : term) (s : sort) (* ⟨m, n}s *)
| LetIn (A : {bind term}) (m : term) (n : {bind 2 of term}) (* RΣ([z]A, m, [x,y]n) *)
| Fix (A : term) (m : {bind term})
(* data *)
| Unit | II
| Bool | TT | FF
| Ifte (A : {bind term}) (m n1 n2 : term) (* RB([z]A, m, n1, n2) *)
(* monadic *)
| IO (A : term)
| Return (m : term)
| Bind (m : term) (n : {bind term})
(* session *)
| Proto
| Stop (r : bool)
| Act0 (r : bool) (A : term) (B : {bind term}) (* ρ{x : A}.B *)
| Act1 (r : bool) (A : term) (B : {bind term}) (* ρ(x : A).B *)
| Ch (r : bool) (A : term)
| CVar (x : nat)
| Fork (m : {bind term})
| Recv (m : term)
| Send (m : term)
| Close (m : term)
| Wait (m : term).

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance substLemmas_term : SubstLemmas term. derive. Qed.
