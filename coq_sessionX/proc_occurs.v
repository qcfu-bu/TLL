From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq zify.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS dyn_occurs proc_cren.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Fixpoint proc_occurs (i : cvar) (p : proc) : nat :=
  match p with
  | ⟨ m ⟩ => dyn_occurs i m
  | p ∣ q => proc_occurs i p + proc_occurs i q
  | ν.p => proc_occurs i.+2 p
  end.

Lemma proc_type_occurs0 Θ p i :
  Θ ⊢ p -> cvar_pos Θ i false -> proc_occurs i p = 0.
Proof with eauto using cvar_pos.
  move=>ty. elim: ty i=>//={Θ p}.
  { move=>Θ m tym i pos.
    apply: dyn_type_occurs0... }
  { move=>Θ1 Θ2 Θ p q mrg typ ihp tyq ihq i pos.
    have[pos1 pos2]:=cvar_pos_split_false mrg pos.
    rewrite ihp... }
  { move=>Θ p r1 r2 A xor typ ihp i pos.
    rewrite ihp... }
Qed.

Lemma proc_type_occurs1 Θ p i :
  Θ ⊢ p -> cvar_pos Θ i true -> proc_occurs i p = 1.
Proof with eauto using cvar_pos, proc_occurs, proc_type_occurs0.
  move=>ty. elim: ty i=>//={Θ p}.
  { move=>Θ m tym i pos.
    apply: dyn_type_occurs1... }
  { move=>Θ1 Θ2 Θ p q mrg typ ihp tyq ihq i pos.
    have[[pos1 pos2]|[pos1 pos2]]:=cvar_pos_split_true mrg pos.
    { erewrite ihq...
      erewrite proc_type_occurs0... }
    { erewrite ihp... } }
  { move=>Θ p r1 r2 A xor typ ihp i pos.
    rewrite ihp... }
Qed.

Lemma proc_occurs_iren Θ p i ξ :
  Θ ⊢ proc_cren p ξ -> iren i ξ -> proc_occurs i (proc_cren p ξ) = 0.
Proof with eauto using proc_occurs.
  move e:(proc_cren p ξ)=>x ty.
  elim: ty p ξ e i=>//={Θ x}.
  { move=>Θ m tym p ξ e i h.
    destruct p; inv e.
    apply: dyn_occurs_iren... }
  { move=>Θ1 Θ2 Θ p q mrg typ ihp tyq ihq x ξ e i h.
    destruct x; inv e.
    erewrite ihp... }
  { move=>Θ p r1 r2 A e1 typ ihp x ξ e i h.
    destruct x; inv e.
    apply: ihp...
    apply: iren_upren.
    by apply: iren_upren. }
Qed.

Lemma cren_id_up2 i j ξ :
  (forall x, (x == i) = false → (x == j) = false → ξ x = x) ->
  (forall x, (x == i.+2) = false → (x == j.+2) = false → upren (upren ξ) x = x).
Proof.
  move=>h [|[|x]]//=.
  move=>e1 e2.
  f_equal.
  f_equal.
  apply: h; lia.
Qed.

Lemma proc_occurs_cren_id Θ p i j ξ :
  Θ ⊢ proc_cren p ξ ->
  proc_occurs i p = 0 ->
  proc_occurs j p = 0 ->
  (forall x, x == i = false -> x == j = false -> ξ x = x) ->
  Θ ⊢ p.
Proof with eauto using proc_type.
  move e:(proc_cren p ξ)=>p' ty.
  elim: ty p ξ e i j=>{Θ p'}.
  { move=>Θ m tym p ξ e i j oc1 oc2 h.
    destruct p; inv e. simpl in oc1. simpl in oc2.
    constructor.
    apply: dyn_occurs_cren_id.
    eauto.
    apply: oc1.
    apply: oc2.
    eauto. }
  { move=>Θ1 Θ2 Θ p q mrg typ ihp tyq ihq p0 ξ e i j oc1 oc2 h.
    destruct p0; inv e. simpl in oc1. simpl in oc2.
    move: oc1. case_eq (proc_occurs i p0_1); case_eq (proc_occurs i p0_2)=>//=e1 e2 _.
    move: oc2. case_eq (proc_occurs j p0_1); case_eq (proc_occurs j p0_2)=>//=e3 e4 _.
    have{}ihp:=ihp _ _ erefl _ _ e2 e4 h.
    have{}ihq:=ihq _ _ erefl _ _ e1 e3 h.
    econstructor... }
  { move=>Θ p r1 r2 A e0 typ ihp p0 ξ e i j oc1 oc2 h.
    destruct p0; inv e. simpl in oc1. simpl in oc2.
    have{}ihp:=ihp _ _ erefl _ _ oc1 oc2 (cren_id_up2 h).
    econstructor... }
Qed.
