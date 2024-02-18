From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq zify.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS era_occurs proc_occurs eproc_cren.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma eproc_proc_occurs Θ p p' i x :
  Θ ⊢ p ~ p' -> proc_occurs i p = x -> proc_occurs i p' = x.
Proof with eauto using era_dyn_occurs.
  move=>er. elim: er i x=>//={Θ p p'}...
  move=>Θ1 Θ2 Θ p p' q q' mrg erp ihp erq ihq i x.
  move e1:(proc_occurs i p)=>v1.
  move e2:(proc_occurs i q)=>v2 e0.
  have->:=ihp _ _ e1.
  have->:=ihq _ _ e2.
  by [].
Qed.

Lemma eproc_type_occurs0 Θ p p' i :
  Θ ⊢ p ~ p' -> cvar_pos Θ i false ->
  proc_occurs i p = 0 /\ proc_occurs i p' = 0.
Proof with eauto using cvar_pos.
  move=>ty. elim: ty i=>//={Θ p p'}.
  { move=>Θ m m' tym i pos.
    apply: era_type_occurs0... }
  { move=>Θ1 Θ2 Θ p p' q q' mrg typ ihp tyq ihq i pos.
    have[pos1 pos2]:=cvar_pos_split_false mrg pos.
    have[->->]:=ihp _ pos1.
    have[->->]:=ihq _ pos2... }
  { move=>Θ p p' r1 r2 A xor typ ihp i pos.
    apply: ihp... }
Qed.

Lemma eproc_type_occurs1 Θ p p' i :
  Θ ⊢ p ~ p' -> cvar_pos Θ i true ->
  proc_occurs i p = 1 /\ proc_occurs i p' = 1.
Proof with eauto using cvar_pos, proc_occurs, eproc_type_occurs0.
  move=>ty. elim: ty i=>//={Θ p p'}.
  { move=>Θ m m' tym i pos.
    apply: era_type_occurs1... }
  { move=>Θ1 Θ2 Θ p p' q q' mrg typ ihp tyq ihq i pos.
    have[[pos1 pos2]|[pos1 pos2]]:=cvar_pos_split_true mrg pos.
    { have[->->]:=ihq _ pos2.
      have[->->]:=eproc_type_occurs0 typ pos1... }
    { have[->->]:=ihp _ pos1.
      have[->->]:=eproc_type_occurs0 tyq pos2... } }
  { move=>Θ p p' r1 r2 A xor typ ihp i pos.
    apply: ihp... }
Qed.

Lemma eproc_occurs_iren Θ p p' i ξ :
  Θ ⊢ proc_cren p ξ ~ proc_cren p' ξ -> iren i ξ ->
  proc_occurs i (proc_cren p ξ) = 0 /\
  proc_occurs i (proc_cren p' ξ) = 0.
Proof with eauto using proc_occurs.
  move e1:(proc_cren p ξ)=>x.
  move e2:(proc_cren p' ξ)=>y ty.
  elim: ty p p' ξ e1 e2 i=>//={Θ x y}.
  { move=>Θ m m' tym p p' ξ e1 e2 i h.
    destruct p; inv e1.
    destruct p'; inv e2.
    apply: era_occurs_iren... }
  { move=>Θ1 Θ2 Θ p p' q q' mrg typ ihp tyq ihq x y ξ e1 e2 i h.
    destruct x; inv e1.
    destruct y; inv e2.
    have[->->]:=ihp _ _ _ erefl erefl _ h.
    have[->->]:=ihq _ _ _ erefl erefl _ h... }
  { move=>Θ p p' r1 r2 A e typ ihp x y ξ e1 e2 i h.
    destruct x; inv e1.
    destruct y; inv e2.
    apply: ihp...
    apply: iren_upren.
    by apply: iren_upren. }
Qed.

(* Lemma eproc_occurs_cren_id Θ p p' i j ξ : *)
(*   Θ ⊢ proc_cren p ξ ~ proc_cren p' ξ -> *)
(*   proc_occurs i p = 0 -> *)
(*   proc_occurs j p = 0 -> *)
(*   (forall x, x == i = false -> x == j = false -> ξ x = x) -> *)
(*   Θ ⊢ p. *)
(* Proof with eauto using proc_type. *)
(*   move e:(proc_cren p ξ)=>p' ty. *)
(*   elim: ty p ξ e i j=>{Θ p'}. *)
(*   { move=>Θ m tym p ξ e i j oc1 oc2 h. *)
(*     destruct p; inv e. simpl in oc1. simpl in oc2. *)
(*     constructor. *)
(*     apply: dyn_occurs_cren_id. *)
(*     eauto. *)
(*     apply: oc1. *)
(*     apply: oc2. *)
(*     eauto. } *)
(*   { move=>Θ1 Θ2 Θ p q mrg typ ihp tyq ihq p0 ξ e i j oc1 oc2 h. *)
(*     destruct p0; inv e. simpl in oc1. simpl in oc2. *)
(*     move: oc1. case_eq (proc_occurs i p0_1); case_eq (proc_occurs i p0_2)=>//=e1 e2 _. *)
(*     move: oc2. case_eq (proc_occurs j p0_1); case_eq (proc_occurs j p0_2)=>//=e3 e4 _. *)
(*     have{}ihp:=ihp _ _ erefl _ _ e2 e4 h. *)
(*     have{}ihq:=ihq _ _ erefl _ _ e1 e3 h. *)
(*     econstructor... } *)
(*   { move=>Θ p r1 r2 A e0 typ ihp p0 ξ e i j oc1 oc2 h. *)
(*     destruct p0; inv e. simpl in oc1. simpl in oc2. *)
(*     have{}ihp:=ihp _ _ erefl _ _ oc1 oc2 (cren_id_up2 h). *)
(*     econstructor... } *)
(* Qed. *)
