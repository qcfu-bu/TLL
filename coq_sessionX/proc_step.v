From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS proc_cren proc_occurs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive proc_congr0 : proc -> proc -> Prop :=
| proc_congr0_par_sym p q :
  proc_congr0 (p ∣ q) (q ∣ p)
| proc_congr0_assoc o p q :
  proc_congr0 (o ∣ (p ∣ q)) ((o ∣ p) ∣ q)
| proc_congr0_extrude p (q : proc) :
  proc_congr0 ((ν.p) ∣ q) (ν.(p ∣ proc_cren q (+2)))
| proc_congr0_contract p (q : proc) :
  proc_occurs 0 q = 0 ->
  proc_occurs 1 q = 0 ->
  proc_congr0 (ν.(p ∣ q)) ((ν.p) ∣ proc_cren q (-2)) 
| proc_congr0_par p p' q q' :
  proc_congr0 p p' ->
  proc_congr0 q q' ->
  proc_congr0 (p ∣ q) (p' ∣ q')
| proc_congr0_nu p p' :
  proc_congr0 p p' ->
  proc_congr0 (ν.p) (ν.p')
| proc_congr0_end p :
  proc_congr0 (p ∣ ⟨ Return II ⟩) p.
Notation "p ≡ q" := (conv proc_congr0 p q) (at level 50).

Reserved Notation "p ≈>> q" (at level 50).
Inductive proc_step : proc -> proc -> Prop :=
(* monadic *)
| proc_step_exp m m' :
  m ~>> m' ->
  ⟨ m ⟩ ≈>> ⟨ m' ⟩
| proc_step_bind v n :
  dyn_val v ->
  ⟨ Bind (Return v) n ⟩ ≈>> ⟨ n.[v/] ⟩
(* session *)
| proc_step_fork A m m' n n' :
  m' = term_cren m (+2) ->
  n' = term_cren n (+2) ->
  ⟨ Bind (Fork A m) n ⟩ ≈>> ν.(⟨ n'.[CVar 0/] ⟩ ∣ ⟨ m'.[CVar 1/] ⟩)
| proc_step_com0 m n1 n2 :
  ν.(⟨ Bind (App0 (Send0 (CVar 0)) m) n1 ⟩ ∣ ⟨ Bind (Recv0 (CVar 1)) n2 ⟩) ≈>>
  ν.(⟨ Bind (Return (CVar 0)) n1 ⟩ ∣ ⟨ Bind (Return (Pair0 m (CVar 1) L)) n2 ⟩)
| proc_step_com0i m n1 n2 :
  ν.(⟨ Bind (App0 (Send0 (CVar 1)) m) n1 ⟩ ∣ ⟨ Bind (Recv0 (CVar 0)) n2 ⟩) ≈>>
  ν.(⟨ Bind (Return (CVar 1)) n1 ⟩ ∣ ⟨ Bind (Return (Pair0 m (CVar 0) L)) n2 ⟩)
| proc_step_com1 v n1 n2 :
  dyn_val v ->
  ν.(⟨ Bind (App1 (Send1 (CVar 0)) v) n1 ⟩ ∣ ⟨ Bind (Recv1 (CVar 1)) n2 ⟩) ≈>>
  ν.(⟨ Bind (Return (CVar 0)) n1 ⟩ ∣ ⟨ Bind (Return (Pair1 v (CVar 1) L)) n2 ⟩)
| proc_step_com1i v n1 n2 :
  dyn_val v ->
  ν.(⟨ Bind (App1 (Send1 (CVar 1)) v) n1 ⟩ ∣ ⟨ Bind (Recv1 (CVar 0)) n2 ⟩) ≈>>
  ν.(⟨ Bind (Return (CVar 1)) n1 ⟩ ∣ ⟨ Bind (Return (Pair1 v (CVar 0) L)) n2 ⟩)
| proc_step_end m m' n n' :
  m' = term_cren m (-2) ->
  n' = term_cren n (-2) ->
  ν.(⟨ Bind (Close (CVar 0)) m ⟩ ∣ ⟨ Bind (Wait (CVar 1)) n ⟩) ≈>>
  ⟨ Bind (Return II) m' ⟩ ∣ ⟨ Bind (Return II) n' ⟩
| proc_step_endi m m' n n' :
  m' = term_cren m (-2) ->
  n' = term_cren n (-2) ->
  ν.(⟨ Bind (Close (CVar 1)) m ⟩ ∣ ⟨ Bind (Wait (CVar 0)) n ⟩) ≈>>
  ⟨ Bind (Return II) m' ⟩ ∣ ⟨ Bind (Return II) n' ⟩
(* congruence *)
| proc_par o p q :
  p ≈>> q ->
  o ∣ p ≈>> o ∣ q
| proc_nu p q :
  p ≈>> q ->
  ν.p ≈>> ν.q
| proc_congr p p' q q' :
  p ≡ p' ->
  p' ≈>> q' ->
  q' ≡ q ->
  p ≈>> q
where "p ≈>> q" := (proc_step p q).
