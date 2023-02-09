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

Fixpoint proc_cren (p : proc) (ξ : cvar -> cvar) : proc :=
  match p with
  | ⟨ m ⟩ => ⟨ term_cren m ξ ⟩
  | p ∣ q => (proc_cren p ξ) ∣ (proc_cren q ξ)
  | ν.p => ν.(proc_cren p (upren (upren ξ)))
  end.

Inductive proc_congr0 : proc -> proc -> Prop :=
| proc_congr0_par_sym p q :
  proc_congr0 (p ∣ q) (q ∣ p)
| proc_congr0_assoc o p q :
  proc_congr0 (o ∣ (p ∣ q)) ((o ∣ p) ∣ q)
| proc_congr0_associ o p q :
  proc_congr0 ((o ∣ p) ∣ q) (o ∣ (p ∣ q)) 
| proc_congr0_scope p (q : proc) :
  proc_congr0 ((ν.p) ∣ q) (ν.(p ∣ proc_cren q (+2)))
| proc_congr0_scopei p (q : proc) :
  proc_congr0 (ν.(p ∣ proc_cren q (+2))) ((ν.p) ∣ q) 
| proc_congr0_par p p' q q' :
  proc_congr0 p p' ->
  proc_congr0 q q' ->
  proc_congr0 (p ∣ q) (p' ∣ q')
| proc_congr0_pari p p' q q' :
  proc_congr0 p p' ->
  proc_congr0 q q' ->
  proc_congr0 (p' ∣ q') (p ∣ q) 
| proc_congr0_nu p p' :
  proc_congr0 p p' ->
  proc_congr0 (ν.p) (ν.p')
| proc_congr0_nui p p' :
  proc_congr0 p p' ->
  proc_congr0 (ν.p') (ν.p).
Notation "p ≡ q" := (conv proc_congr0 p q) (at level 50).
