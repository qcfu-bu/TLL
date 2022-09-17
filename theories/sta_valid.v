From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_inv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem sta_valid Γ m A : sta_wf Γ -> Γ ⊢ m : A -> exists s, Γ ⊢ A : @s.
Proof with eauto using sta_type.
  move=>wf ty. elim: ty wf=>{Γ m A}...
  { move=>Γ x A hs wf.
    apply: sta_wf_ok... }
  { move=>Γ A B m n s t tym ihm tyn ihn wf.
    have[_/sta_pi0_inv[r[tyA[tyB _]]]]:=ihm wf.
    exists r. have//:=sta_subst tyB tyn. }
  { move=>Γ A B m n s t tym ihm tyn ihn wf.
    have[_/sta_pi1_inv[r[tyA[tyB _]]]]:=ihm wf.
    exists r. have//:=sta_subst tyB tyn. }
Qed.
