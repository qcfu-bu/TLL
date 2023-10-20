From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS dyn_sr.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Ltac inv_dyn_val :=
  match goal with
  | [ H : dyn_val _ |- _ ] => inv H
  end.

Lemma dyn_forall_canonical m A B C :
  nil ⊢ m : C -> C === Forall A B -> dyn_val m ->
  exists A n, m = Lam A n.
Proof with eauto.
  move e:(nil)=>Γ ty. elim: ty e A B=>{Γ m C}.
  all: try solve[intros; exfalso; (solve_conv||inv_dyn_val)].
  { move=>Γ A B m tyA ihA tym ihm e A0 B0 eq v. subst.
    exists A. exists m... }
  { move=>Γ A B m eq1 tym ihm tyB ihB e A0 B0 eq2 vl. subst.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma dyn_arrow_canonical m A B C :
  nil ⊢ m : C -> C === Arrow A B -> dyn_val m ->
  exists A n, m = Fun A n.
Proof with eauto.
  move e:(nil)=>Γ ty. elim: ty e A B=>{Γ m C}.
  all: try solve[intros; exfalso; (solve_conv||inv_dyn_val)].
  { move=>Γ A B m tyA ihA tym ihm e1 A0 B0 eq v. subst.
    exists A. exists m... }
  { move=>Γ A B m eq1 tym ihm tyB ihB e A0 B0 eq2 vl.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma dyn_unit_canonical m C :
  nil ⊢ m : C -> C === UnitT -> dyn_val m -> m = Unit.
Proof with eauto.
  move e:(nil)=>Γ ty. elim: ty e=>{Γ m C}.
  all: try solve[intros; exfalso; (solve_conv||inv_dyn_val)]...
  { move=>Γ A B m eq1 tym ihm tyB ihB e eq2 vl. subst.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma dyn_prog m A : nil ⊢ m : A -> (exists n, m ~>> n) \/ dyn_val m.
Proof with eauto using sta_step, dyn_step, dyn_val.
  move e:(nil)=>Γ ty. elim: ty e=>{Γ m A}.
  { move=>Γ wf e. right... }
  { move=>Γ x A wf shs e. subst. inv shs. }
  { move=>*. right... }
  { move=>*. right... }
  { move=>*. right... }
  { move=>*. right... }
  { move=>Γ A B m n tym ihm tyn ihn e. subst.
    have[[m0 st]|v]:=ihm erefl.
    { left. exists (Inst m0 n)... }
    { have[A0[n0 e]]:=dyn_forall_canonical tym (convR _ _) v. subst.
      left. exists (n0.[n/])... } }
  { move=>Γ A B m n tym ihm tyn ihn e. subst.
    have[[m0 st]|v]:=ihm erefl.
    { left. exists (Call m0 n)... }
    { have[A0[m0 e]]:=dyn_arrow_canonical tym (convR _ _) v. subst.
      have[[n0 st]|v0]:=ihn erefl.
      left. exists (Call (Fun A0 m0) n0)...
      left. exists (m0.[n/])... } }
  { move=>Γ wf e. right... }
  { move=>Γ wf e. right... }
  { move=>Γ wf e. right... }
  { move=>Γ wf e. right... }
  { move=>Γ m tym ihm e. subst.
    have[[n st]|v]:=ihm erefl.
    left. exists (Rand n)...
    have e:=dyn_unit_canonical tym (convR _ _) v. subst.
    left. exists (Nat 0). constructor. }
  { move=>Γ A B m eq tym ihm tyB ihB e. subst... }
Qed.
