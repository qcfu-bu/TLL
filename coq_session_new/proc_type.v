From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq zify.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS tllc_ast dyn_cren.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "Θ ⊢ p" (at level 50, p at next level).

Inductive proc_type : dyn_ctx -> proc -> Prop :=
| proc_exp Θ m :
  Θ ; nil ; nil ⊢ m : IO Unit ->
  Θ ⊢ ⟨ m ⟩
| proc_par Θ1 Θ2 Θ p q :
  Θ1 ∘ Θ2 => Θ ->
  Θ1 ⊢ p ->
  Θ2 ⊢ q ->
  Θ ⊢ p ∣ q
| proc_scope Θ p r1 r2 A :
  r1 = ~~r2 ->
  Ch r1 (cren (+1) A) :L Ch r2 A :L Θ ⊢ p ->
  Θ ⊢ ν.p
where "Θ ⊢ p" := (proc_type Θ p).

Inductive proc_wf : dyn_ctx -> Prop :=
| proc_wf_nil : proc_wf nil
| proc_wf_ty Θ r A :
  proc_wf Θ ->
  nil ⊢ A : Proto ->
  proc_wf (Ch r A :L Θ)
| proc_wf_n Θ :
  proc_wf Θ ->
  proc_wf (_: Θ).

Lemma dyn_empty_proc_wf Θ : dyn_empty Θ -> proc_wf Θ.
Proof with eauto using proc_wf. elim... Qed.

Lemma dyn_just_proc_wf Θ x r A :
  dyn_just Θ x (Ch r A) -> nil ⊢ A : Proto -> proc_wf Θ.
Proof with eauto.
  move e:(Ch r A)=>B js. elim: js r A e=>{Θ x B}.
  { move=>Θ A emp r A0 e tyA0. destruct A; inv e.
    have/={}tyA0:=sta_crename_inv tyA0.
    constructor...
    apply: dyn_empty_proc_wf... }
  { move=>Θ A x js ih r A0 e tyA0. destruct A; inv e.
    have/={}tyA0:=sta_crename_inv tyA0.
    constructor... }
Qed.

Lemma proc_wf_merge Θ1 Θ2 Θ :
  Θ1 ∘ Θ2 => Θ -> proc_wf Θ1 -> proc_wf Θ2 -> proc_wf Θ.
Proof with eauto using proc_wf.
  elim=>{Θ1 Θ2 Θ}...
  { move=>Θ1 Θ2 Θ m mrg ih wf1 wf2. inv wf1. }
  { move=>Θ1 Θ2 Θ m mrg ih wf1 wf2. inv wf1. inv wf2... }
  { move=>Θ1 Θ2 Θ m mrg ih wf1 wf2. inv wf1. inv wf2... }
  { move=>Θ1 Θ2 Θ mrg ih wf1 wf2. inv wf1. inv wf2... }
Qed.

Lemma dyn_type_proc_wf Θ Γ Δ m A : Θ ; Γ ; Δ ⊢ m : A -> proc_wf Θ.
Proof with eauto using proc_wf.
  elim=>{Θ Γ Δ m A}...
  { move=>Θ Γ Δ x s A emp wf shs dhs. apply: dyn_empty_proc_wf... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n s mrg1 mrg2 tym ihm tyn ihn.
    apply: proc_wf_merge mrg1 ihm ihn. }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n t mrg1 mrg2 tyS tym ihm tyn ihn.
    apply: proc_wf_merge mrg1 ihm ihn. }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r t mrg1 mrg2 tyC tym ihm tyn ihn.
    apply: proc_wf_merge mrg1 ihm ihn. }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r1 r2 t mrg1 mrg2 tyC tym ihm tyn ihn.
    apply: proc_wf_merge mrg1 ihm ihn. }
  { move=>Θ Γ Δ emp wf k. apply: dyn_empty_proc_wf... }
  { move=>Θ Γ Δ emp wf k. apply: dyn_empty_proc_wf... }
  { move=>Θ Γ Δ emp wf k. apply: dyn_empty_proc_wf... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m n1 n2 s mrg1 mrg2
           tyA tym ihm tyn1 ihn1 tyn2 ihn2.
    apply: proc_wf_merge mrg1 ihm ihn1. }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m n A B s t mrg1 mrg2 tyB tym ihm tyn ihn.
    apply: proc_wf_merge mrg1 ihm ihn. }
  { move=>Θ Γ Δ r x A js wf k tyA.
    apply: dyn_just_proc_wf... }
Qed.

Lemma proc_type_wf Θ p : Θ ⊢ p -> proc_wf Θ.
Proof with eauto using proc_wf.
  elim=>{Θ p}.
  { move=>Θ m tym. apply: dyn_type_proc_wf... }
  { move=>Θ1 Θ2 Θ p q mrg typ ihp tyq ihq. apply: proc_wf_merge... }
  { move=>Θ p r1 r2 A e typ wf. inv wf. inv H1... }
Qed.

Lemma proc_wf_empty Θ : proc_wf Θ -> exists Θ', dyn_empty Θ' /\ Θ' ∘ Θ => Θ.
Proof with eauto using merge, dyn_empty.
  elim=>{Θ}.
  exists nil...
  move=>Θ r A wf[Θ'[emp mrg]]tyA. exists (_: Θ')...
  move=>Θ wf[Θ'[emp mrg]]. exists (_: Θ')...
Qed.
