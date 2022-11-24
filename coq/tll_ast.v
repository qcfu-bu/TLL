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

Inductive sort_leq : sort -> sort -> Prop :=
| sort_leqU s :
  sort_leq U s
| sort_leqL :
  sort_leq L L.
Notation "s ⊑ t" := (sort_leq s t) (at level 30) : sort_scope.

Inductive term : Type :=
| Var (x : var)
| Sort (s : sort)
| Pi0 (A : term) (B : {bind term}) (s : sort)  (* Πs {x : A}.B *)
| Pi1 (A : term) (B : {bind term}) (s : sort)  (* Πs (x : A).B *)
| Lam0 (A : term) (m : {bind term}) (s : sort) (* λs {x : A}.m *)
| Lam1 (A : term) (m : {bind term}) (s : sort) (* λs (x : A).m *)
| App (m n : term)
| Sig0 (A : term) (B : {bind term}) (s : sort) (* Σs {x : A}.B *)
| Sig1 (A : term) (B : {bind term}) (s : sort) (* Σs (x : A).B *)
| Pair0 (m n : term) (s : sort) (* {m, n}s *)
| Pair1 (m n : term) (s : sort) (* ⟨m, n}s *)
| LetIn (A : {bind term}) (m : term) (n : {bind 2 of term}) (* RΣ([z]A, m, [x,y]n) *)
| With (A B : term) (s : sort)  (* A &s B *)
| APair (m n : term) (s : sort) (* (m, n)s *)
| Fst (m : term) (* π1 m *)
| Snd (m : term) (* π2 m *)
| Id (A m n : term)
| Refl (m : term)
| J (A : {bind 3 of term}) (H : {bind term}) (P : term) (* R≡([x,y,p]A,[z]H,P) *)
| Box
| Ptr (l : nat).

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance substLemmas_term : SubstLemmas term. derive. Qed.
