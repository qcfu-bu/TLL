From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq zify.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS dyn_occurs proc_cren.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive proc_occurs : dyn_ctx -> proc -> cvar -> nat -> Prop :=
| proc_occurs_exp Θ m i j :
  dyn_occurs Θ nil nil m (IO Unit) i j ->
  proc_occurs Θ ⟨ m ⟩ i j
| proc_occurs_par Θ1 Θ2 Θ p q i j1 j2 :
  Θ1 ∘ Θ2 => Θ ->
  proc_occurs Θ1 p i j1 ->
  proc_occurs Θ2 q i j2 ->
  proc_occurs Θ (p ∣ q) i (j1 + j2)
| proc_occurs_scope Θ p r1 r2 A i j :
  r1 = ~~r2 ->
  proc_occurs (Ch r1 (term_cren A (+1)) :L Ch r2 A :L Θ) p i.+2 j ->
  proc_occurs Θ (ν.p) i j
where "Θ ⊢ p" := (proc_type Θ p).

Lemma proc_type_occurs0 Θ p i :
  Θ ⊢ p -> cvar_pos Θ i false -> proc_occurs Θ p i 0.
Proof with eauto using cvar_pos.
  move=>ty. elim: ty i=>{Θ p}.
  { move=>Θ m tym i pos.
    constructor. apply: dyn_type_occurs0... }
  { move=>Θ1 Θ2 Θ p q mrg typ ihp tyq ihq i pos.
    have[pos1 pos2]:=cvar_pos_split_false mrg pos.
    replace 0 with (0 + 0) by eauto.
    econstructor... }
  { move=>Θ p r1 r2 A xor typ ihp i pos.
    econstructor... }
Qed.

Lemma proc_type_occurs1 Θ p i :
  Θ ⊢ p -> cvar_pos Θ i true -> proc_occurs Θ p i 1.
Proof with eauto using cvar_pos, proc_occurs, proc_type_occurs0.
  move=>ty. elim: ty i=>{Θ p}.
  { move=>Θ m tym i pos.
    constructor. apply: dyn_type_occurs1... }
  { move=>Θ1 Θ2 Θ p q mrg typ ihp tyq ihq i pos.
    have[[pos1 pos2]|[pos1 pos2]]:=cvar_pos_split_true mrg pos.
    { replace 1 with (0 + 1) by eauto... }
    { replace 1 with (1 + 0) by eauto... } }
  { move=>Θ p r1 r2 A xor typ ihp i pos.
    econstructor... }
Qed.

Lemma proc_occurs_pos0 Θ p i :
  proc_occurs Θ p i 0 -> cvar_pos Θ i false.
Proof with eauto using cvar_pos.
  move e:(0)=>j ty. elim: ty e=>{Θ p i j}.
  { move=>Θ m i j ty e. subst.
    apply: dyn_occurs_pos0... }
  { move=>Θ1 Θ2 Θ p q i j1 j2 mrg typ ihp tyq ihq e.
    destruct j1; destruct j2; inv e.
    apply: cvar_pos_merge_false... }
  { move=>Θ p r1 r2 A i j e1 typ ihp e2. subst.
    have{}ihp:=ihp erefl.
    inv ihp. inv H3... }
Qed.

Lemma proc_occurs_iren Θ p i ξ :
  Θ ⊢ proc_cren p ξ -> iren i ξ -> proc_occurs Θ (proc_cren p ξ) i 0.
Proof with eauto using proc_occurs.
  move e:(proc_cren p ξ)=>x ty.
  elim: ty p ξ e i=>{Θ x}.
  { move=>Θ m tym p ξ e i h.
    destruct p; inv e.
    constructor.
    apply: dyn_occurs_iren... }
  { move=>Θ1 Θ2 Θ p q mrg typ ihp tyq ihq x ξ e i h.
    destruct x; inv e.
    replace 0 with (0 + 0) by eauto... }
  { move=>Θ p r1 r2 A e1 typ ihp x ξ e i h.
    destruct x; inv e.
    econstructor...
    apply: ihp...
    apply: iren_upren.
    by apply: iren_upren. }
Qed.
