From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS tll_ast tll_cren.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive proc :=
| Exp (m : term)
| Par (p q : proc)
| Nu (p : proc).

Notation "⟨ m ⟩" := (Exp m).
Notation "p ∣ q" := (Par p q) (at level 20).
Notation "'ν.' p" := (Nu p) (at level 20).
