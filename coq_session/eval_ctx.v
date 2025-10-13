From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS dyn_inv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Inductive eval_ctx :=
| EHole
| EBind (M : eval_ctx) (n : term).

Fixpoint eval (M : eval_ctx) (m : term) : term :=
  match M with
  | EHole => m
  | EBind M n =>
    Bind (eval M m) n
  end.

Lemma dyn_eval_ctx_inv Θ M m B :
  Θ ; nil ; nil ⊢ eval M m : IO B ->
  exists Θ1 Θ2 A,
    Θ1 ∘ Θ2 => Θ ∧
    Θ1 ; nil ; nil ⊢ m : IO A ∧
    (forall Θ3 Θ' n,
        Θ2 ∘ Θ3 => Θ' ->
        Θ3 ; nil ; nil ⊢ n : IO A ->
        Θ' ; nil ; nil ⊢ eval M n : IO B).
Proof.
  elim: M Θ m B=>//=.
  { intros.
    have[Θ0[emp mrg]] := dyn_type_empty H.
    exists Θ, Θ0, B. repeat split; eauto.
    apply: merge_sym; eauto.
    intros.
    by have<-:=merge_emptyL H0 emp. }
  { intros.
    have[s tyIO]:=dyn_valid H0.
    have[r[tyB _]]:=sta_io_inv tyIO.
    have[Θ1[Θ2[Δ1[Δ2[A[t[mrg1[mrg2[tyM tyn]]]]]]]]]:=dyn_bind_inv H0.
    inv mrg2.
    have[Θ11[Θ12[A0[mrg3[tym h]]]]]:=H _ _ _ tyM.
    have[Θa[mrga mrgb]]:=merge_splitR mrg1 mrg3.
    exists Θ11, Θa, A0. repeat split; eauto.
    apply: merge_sym; eauto.
    intros.
    have[Θc[mrgc mrgd]]:=merge_splitL H1 mrga.
    have tyM0:=h _ _ _ mrgc H2.
    econstructor; eauto.
    constructor. }
Qed.
