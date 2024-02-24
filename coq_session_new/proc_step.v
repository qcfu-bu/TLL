From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS tllc_csubst proc_occurs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition exch :=
  CVar 2 .: CVar 3 .: CVar 0 .: CVar 1 .: (fun x => CVar x.+4).
Example ex0 : (exch 0 = CVar 2). by eauto. Qed.
Example ex1 : (exch 1 = CVar 3). by eauto. Qed.
Example ex2 : (exch 2 = CVar 0). by eauto. Qed.
Example ex3 : (exch 3 = CVar 1). by eauto. Qed.
Example ex4 : (exch 4 = CVar 4). by eauto. Qed.
Example ex5 : (exch 5 = CVar 5). by eauto. Qed.

Inductive proc_congr0 : proc -> proc -> Prop :=
| proc_congr0_par_sym p q :
  proc_congr0 (p ∣ q) (q ∣ p)
| proc_congr0_assoc o p q :
  proc_congr0 (o ∣ (p ∣ q)) ((o ∣ p) ∣ q)
| proc_congr0_scope p (q : proc) :
  proc_congr0 ((ν.p) ∣ q) (ν.(p ∣ cren (+2) q))
| proc_conrg0_exch p :
  proc_congr0 (ν.ν.p) (ν.ν.(csubst exch p))
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
(* session *)
| proc_step_fork A m m' n n' :
  m' = cren (+2) m ->
  n' = cren (+2) n ->
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
  m' = cren (-2) m ->
  n' = cren (-2) n ->
  ν.(⟨ Bind (Close (CVar 0)) m ⟩ ∣ ⟨ Bind (Wait (CVar 1)) n ⟩) ≈>>
  ⟨ Bind (Return II) m' ⟩ ∣ ⟨ Bind (Return II) n' ⟩
| proc_step_endi m m' n n' :
  m' = cren (-2) m ->
  n' = cren (-2) n ->
  ν.(⟨ Bind (Close (CVar 1)) m ⟩ ∣ ⟨ Bind (Wait (CVar 0)) n ⟩) ≈>>
  ⟨ Bind (Return II) m' ⟩ ∣ ⟨ Bind (Return II) n' ⟩
(* congruence *)
| proc_step_par o p q :
  p ≈>> q ->
  o ∣ p ≈>> o ∣ q
| proc_step_nu p q :
  p ≈>> q ->
  ν.p ≈>> ν.q
| proc_step_congr p p' q q' :
  p ≡ p' ->
  p' ≈>> q' ->
  q' ≡ q ->
  p ≈>> q
where "p ≈>> q" := (proc_step p q).

Lemma exch_invo : (exch >>> csubst exch) = cids.
Proof with eauto. f_ext. move=>[|[|[|[|]]]]//=. Qed.
