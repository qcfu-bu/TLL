(* This file defines the abstract syntax of MLTT. *)

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Abstract syntax tree of MLTT.
   Variables are represented using DeBrujin indices. *)
Inductive term : Type :=
| Var (x : var)
| Ty
| Pi (A : term) (B : {bind term})  (* Π {x : A}.B *)
| Lam (A : term) (m : {bind term}) (* λ {x : A}.m *)
| App (m n : term)
| Sig (A : term) (B : {bind term}) (* Σ (x : A.B) *)
| DPair (m n : term) (* (m, n) *)
| LetIn (A : {bind term}) (m : term) (n : {bind 2 of term}) (* RΣ([z]A, m, [x,y]n) *)
| Tuple (A B : term) (* A×B *)
| Pair (m n : term) (* (m, n) *)
| Fst (m : term) (* π1 m *)
| Snd (m : term) (* π2 m *)
| Id (A m n : term) (* m =A n *)
| Refl (m : term)
| Rw (A : {bind 2 of term}) (H P : term) (* R=([x,p]A,H,P) *).

(* Derive basic syntactic lemmas using autosubst. *)
Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance substLemmas_term : SubstLemmas term. derive. Qed.
