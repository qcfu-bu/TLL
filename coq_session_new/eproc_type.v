From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq zify.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS era_valid proc_type.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "Θ ⊢ p ~ p'" (at level 50, p, p' at next level).

Inductive eproc_type : dyn_ctx -> proc -> proc -> Prop :=
| eproc_exp Θ m m' :
  Θ ; nil ; nil ⊢ m ~ m' : IO Unit ->
  Θ ⊢ ⟨ m ⟩ ~ ⟨ m' ⟩
| eproc_par Θ1 Θ2 Θ p p' q q' :
  Θ1 ∘ Θ2 => Θ ->
  Θ1 ⊢ p ~ p' ->
  Θ2 ⊢ q ~ q' ->
  Θ ⊢ p ∣ q ~ p' ∣ q'
| eproc_scope Θ p p' r1 r2 A :
  r1 = ~~r2 ->
  Ch r1 (term_cren A (+1)) :L Ch r2 A :L Θ ⊢ p ~ p' ->
  Θ ⊢ ν.p ~ ν.p'
where "Θ ⊢ p ~ p'" := (eproc_type Θ p p').

Lemma eproc_proc_type Θ p p' : Θ ⊢ p ~ p' -> Θ ⊢ p.
Proof with eauto using era_dyn_type, proc_type. elim... Qed.

Lemma era_type_proc_wf Θ Γ Δ m m' A :
  Θ ; Γ ; Δ ⊢ m ~ m' : A -> proc_wf Θ.
Proof with eauto.
  move=>er. apply: dyn_type_proc_wf. apply: era_dyn_type...
Qed.

Lemma eproc_type_wf Θ p p' : Θ ⊢ p ~ p' -> proc_wf Θ.
Proof with eauto.
  move=>er. apply: proc_type_wf. apply: eproc_proc_type...
Qed.

Lemma proc_eproc_type Θ p : Θ ⊢ p -> exists p', Θ ⊢ p ~ p'. 
Proof with eauto using eproc_type.
  elim=>{Θ p}.
  { move=>Θ m tym.
    have[m' erm]:=dyn_era_type tym. exists ⟨ m' ⟩... }
  { move=>Θ1 Θ2 Θ p q mrg typ[p' erp]tyq[q' erq]. exists (p' ∣ q')... }
  { move=>Θ p r1 r2 A e typ[p' erp]. exists (ν.p')... }
Qed.

