import TLLC.Dynamic.CRename
import TLLC.Static.Unique
import TLLC.Static.SR

/-!
# Dynamic inversion

Port of `coq_session/dyn_inv.v`: the typing-inversion lemmas for the linear (dynamic) judgment
`Θ ⨾ Γ ⨾ Δ ⊢ m : A`. As in the static layer (`TLLC/Static/Inversion.lean`), each lemma comes in a
strengthened form (`*_invX`, carrying an explicit conversion/equality hypothesis threaded through the
`conv` rule via the static injectivity lemmas of `Confluence`) and a clean corollary (`*_inv`,
discharging that conversion via `Typed.validity` and the relevant static inversion).

Coq → Lean naming (drop the `dyn_` prefix, `0`/`1` → `Im`/`Ex` tag):
`dyn_lam0_*`/`dyn_lam1_*` → `lamIm_*`/`lamEx_*`; `dyn_pair0_*`/`dyn_pair1_*` → `pairIm_*`/`pairEx_*`;
`dyn_app0_inv`/`dyn_app1_inv` → `appIm_inv`/`appEx_inv`; `dyn_ii_inv` → `one_inv`;
`dyn_tt_inv`/`dyn_ff_inv` → `tt_inv`/`ff_inv`; `dyn_return_*` → `pure_*`; `dyn_bind_*` → `mlet_*`;
`dyn_cvar_inv` → `chan_inv`; `dyn_fork_inv` → `fork_inv`; `dyn_recv0_inv`/`dyn_recv1_inv` →
`recvIm_inv`/`recvEx_inv`; `dyn_send0_inv`/`dyn_send1_inv` → `sendIm_inv`/`sendEx_inv`;
`dyn_wait_inv`/`dyn_close_inv` → `wait_inv`/`close_inv`.

The recv/send/close inversions are kept split (matching the split Coq lemmas) even though the typing
rules `recv`/`send`/`close` are merged on the `.im/.ex` resp. `Bool` tag, so as to retain a literal
one-to-one correspondence with Coq's lemmas; each just instantiates the merged rule at the relevant
tag.

Proofs follow the generalize-then-induct idiom: `generalize e : <subject> = z; rw [e] at ty;
induction ty generalizing …`. Unlike the static template, `Typed` is not mutual with `Wf` here, so
plain `induction` is used (no `Wf` motive); accordingly the per-case context binders differ. The real
constructor case and the `conv` case are handled explicitly first (fields/IHs grabbed by `rename_i`
from the tail of the local context, which is stable across constructors), the `conv` case threading
the conversion with `conv_trans`/`conv_sym`; then `all_goals (exact absurd e (by simp))` refutes every
remaining head-mismatch case via the impossible subject equation `e`.
-/

namespace TLLC.Dynamic
open Autosubst Autosubst.Notation
open scoped TLLC.Static
open TLLC.Static.Tactic

/-- Strengthened inversion for `lam .im` (Coq `dyn_lam0_invX`). -/
lemma lamIm_invX {Θ Γ Δ A1 A2 B C m s1 s2 t}
    (tyL : Θ ⨾ Γ ⨾ Δ ⊢ .lam A1 m .im s1 : C)
    (c : C ≃ .pi A2 B .im s2)
    (tyB : A2 :: Γ ⊢ B : .srt t) :
    Θ ⨾ (A2 :: Γ) ⨾ (none :: Δ) ⊢ m : B := by
  generalize e : Term.lam A1 m .im s1 = n
  rw [e] at tyL
  induction tyL generalizing A1 A2 B m s1 s2 t
  case lamIm =>
    rename_i _ _ tym _
    cases e
    obtain ⟨eqA, eqB, _, _⟩ := Static.pi_inj c
    cases tym.wf with
    | null wf' tyA =>
      cases tyB.wf with
      | cons _ tyA2 =>
        apply Typed.ctx_conv0 (ARS.conv_sym eqA) tyA2
        apply Typed.conv eqB tym
        exact Static.Typed.ctx_conv eqA tyA tyB
  case conv =>
    rename_i eq1 _ _ ih
    exact ih (ARS.conv_trans eq1 c) tyB e
  all_goals (exact absurd e (by simp))

/-- Strengthened inversion for `lam .ex` (Coq `dyn_lam1_invX`). -/
lemma lamEx_invX {Θ Γ Δ A1 A2 B C m s1 s2 t}
    (tyL : Θ ⨾ Γ ⨾ Δ ⊢ .lam A1 m .ex s1 : C)
    (c : C ≃ .pi A2 B .ex s2)
    (tyB : A2 :: Γ ⊢ B : .srt t) :
    ∃ r, Θ ⨾ (A2 :: Γ) ⨾ (A2 :⟨r⟩ Δ) ⊢ m : B := by
  generalize e : Term.lam A1 m .ex s1 = n
  rw [e] at tyL
  induction tyL generalizing A1 A2 B m s1 s2 t
  case lamEx =>
    rename_i r _ _ tym _
    cases e
    obtain ⟨eqA, eqB, _, _⟩ := Static.pi_inj c
    cases tym.wf with
    | cons wf' tyA =>
      cases tyB.wf with
      | cons _ tyA2 =>
        obtain ⟨A0, rd1, rd2⟩ := Static.church_rosser _ _ eqA
        have tyA0t := Static.Typed.prd tyA rd1
        have tyA0s := Static.Typed.prd tyA2 rd2
        have e := Static.Typed.unicity tyA0t tyA0s
        subst e
        refine ⟨r, ?_⟩
        apply Typed.ctx_conv1 (ARS.conv_sym eqA) tyA2
        apply Typed.conv eqB tym
        exact Static.Typed.ctx_conv eqA tyA tyB
  case conv =>
    rename_i eq1 _ _ ih
    exact ih (ARS.conv_trans eq1 c) tyB e
  all_goals (exact absurd e (by simp))

/-- Inversion for `lam .im` (Coq `dyn_lam0_inv`). -/
lemma lamIm_inv {Θ Γ Δ m A1 A2 B s1 s2}
    (ty : Θ ⨾ Γ ⨾ Δ ⊢ .lam A2 m .im s2 : .pi A1 B .im s1) :
    Θ ⨾ (A1 :: Γ) ⨾ (none :: Δ) ⊢ m : B := by
  obtain ⟨t, tyPi⟩ := ty.validity
  obtain ⟨r, tyB, _⟩ := Static.pi_inv tyPi
  exact lamIm_invX ty .refl tyB

/-- Inversion for `lam .ex` (Coq `dyn_lam1_inv`). -/
lemma lamEx_inv {Θ Γ Δ m A1 A2 B s1 s2}
    (ty : Θ ⨾ Γ ⨾ Δ ⊢ .lam A2 m .ex s2 : .pi A1 B .ex s1) :
    ∃ r, Θ ⨾ (A1 :: Γ) ⨾ (A1 :⟨r⟩ Δ) ⊢ m : B := by
  obtain ⟨t, tyPi⟩ := ty.validity
  obtain ⟨r, tyB, _⟩ := Static.pi_inv tyPi
  exact lamEx_invX ty .refl tyB

/-- Strengthened inversion for `pair .im` (Coq `dyn_pair0_invX`). -/
lemma pairIm_invX {Θ Γ Δ A B m n s r t C}
    (ty : Θ ⨾ Γ ⨾ Δ ⊢ .pair m n .im s : C)
    (c : C ≃ .sig A B .im r)
    (tyS : Γ ⊢ .sig A B .im r : .srt t) :
    s = r ∧ Γ ⊢ m : A ∧ Θ ⨾ Γ ⨾ Δ ⊢ n : B[Chan.var_Chan; m..] := by
  generalize e : Term.pair m n .im s = x
  rw [e] at ty
  induction ty generalizing A B m n s r t
  case pairIm =>
    rename_i _ tym tyn _
    cases e
    obtain ⟨eqA, eqB, _, esort⟩ := Static.sig_inj c
    obtain ⟨s0, r0, _, _, tyA0, tyB0, _⟩ := Static.sig_inv tyS
    refine ⟨esort, ?_, ?_⟩
    · exact Static.Typed.conv eqA tym tyA0
    · apply Typed.conv (Static.conv_subst _ eqB) tyn
      apply Static.Typed.esubst rfl rfl tyB0
      exact Static.Typed.conv eqA tym tyA0
  case conv =>
    rename_i eq1 _ _ ih
    exact ih (ARS.conv_trans eq1 c) tyS e
  all_goals (exact absurd e (by simp))

/-- Strengthened inversion for `pair .ex` (Coq `dyn_pair1_invX`). -/
lemma pairEx_invX {Θ Γ Δ A B m n s r t C}
    (ty : Θ ⨾ Γ ⨾ Δ ⊢ .pair m n .ex s : C)
    (c : C ≃ .sig A B .ex r)
    (tyS : Γ ⊢ .sig A B .ex r : .srt t) :
    ∃ Θ1 Θ2 Δ1 Δ2,
      s = r ∧
      Merge Θ1 Θ2 Θ ∧
      Merge Δ1 Δ2 Δ ∧
      Θ1 ⨾ Γ ⨾ Δ1 ⊢ m : A ∧
      Θ2 ⨾ Γ ⨾ Δ2 ⊢ n : B[Chan.var_Chan; m..] := by
  generalize e : Term.pair m n .ex s = x
  rw [e] at ty
  induction ty generalizing A B m n s r t
  case pairEx =>
    rename_i mrgΘ mrgΔ _ tym tyn _ _
    cases e
    obtain ⟨eqA, eqB, _, esort⟩ := Static.sig_inj c
    obtain ⟨s0, r0, _, _, tyA0, tyB0, _⟩ := Static.sig_inv tyS
    refine ⟨_, _, _, _, esort, mrgΘ, mrgΔ, ?_, ?_⟩
    · exact Typed.conv eqA tym tyA0
    · apply Typed.conv (Static.conv_subst _ eqB) tyn
      apply Static.Typed.esubst rfl rfl tyB0
      exact (Typed.conv eqA tym tyA0).toStatic
  case conv =>
    rename_i eq1 _ _ ih
    exact ih (ARS.conv_trans eq1 c) tyS e
  all_goals (exact absurd e (by simp))

/-- Inversion for `pair .im` (Coq `dyn_pair0_inv`). -/
lemma pairIm_inv {Θ Γ Δ A B m n s r}
    (ty : Θ ⨾ Γ ⨾ Δ ⊢ .pair m n .im s : .sig A B .im r) :
    s = r ∧ Γ ⊢ m : A ∧ Θ ⨾ Γ ⨾ Δ ⊢ n : B[Chan.var_Chan; m..] := by
  obtain ⟨t, tyS⟩ := ty.validity
  exact pairIm_invX ty .refl tyS

/-- Inversion for `pair .ex` (Coq `dyn_pair1_inv`). -/
lemma pairEx_inv {Θ Γ Δ A B m n s r}
    (ty : Θ ⨾ Γ ⨾ Δ ⊢ .pair m n .ex s : .sig A B .ex r) :
    ∃ Θ1 Θ2 Δ1 Δ2,
      s = r ∧
      Merge Θ1 Θ2 Θ ∧
      Merge Δ1 Δ2 Δ ∧
      Θ1 ⨾ Γ ⨾ Δ1 ⊢ m : A ∧
      Θ2 ⨾ Γ ⨾ Δ2 ⊢ n : B[Chan.var_Chan; m..] := by
  obtain ⟨t, tyS⟩ := ty.validity
  exact pairEx_invX ty .refl tyS

/-- Inversion for `app .im` (Coq `dyn_app0_inv`). -/
lemma appIm_inv {Θ Γ Δ m n C}
    (ty : Θ ⨾ Γ ⨾ Δ ⊢ .app m n .im : C) :
    ∃ A B s,
      Θ ⨾ Γ ⨾ Δ ⊢ m : .pi A B .im s ∧ Γ ⊢ n : A ∧ (C ≃ B[Chan.var_Chan; n..]) := by
  generalize e : Term.app m n .im = x
  rw [e] at ty
  induction ty generalizing m n
  case appIm =>
    rename_i tym tyn _
    cases e; exact ⟨_, _, _, tym, tyn, .refl⟩
  case conv =>
    rename_i eq1 _ _ ih
    obtain ⟨A0, B0, s0, tym0, tyn0, eq2⟩ := ih e
    exact ⟨A0, B0, s0, tym0, tyn0, ARS.conv_trans (ARS.conv_sym eq1) eq2⟩
  all_goals (exact absurd e (by simp))

/-- Inversion for `app .ex` (Coq `dyn_app1_inv`). -/
lemma appEx_inv {Θ Γ Δ m n C}
    (ty : Θ ⨾ Γ ⨾ Δ ⊢ .app m n .ex : C) :
    ∃ A B s Θ1 Θ2 Δ1 Δ2,
      Merge Θ1 Θ2 Θ ∧
      Merge Δ1 Δ2 Δ ∧
      Θ1 ⨾ Γ ⨾ Δ1 ⊢ m : .pi A B .ex s ∧
      Θ2 ⨾ Γ ⨾ Δ2 ⊢ n : A ∧
      (C ≃ B[Chan.var_Chan; n..]) := by
  generalize e : Term.app m n .ex = x
  rw [e] at ty
  induction ty generalizing m n
  case appEx =>
    rename_i mrgΘ mrgΔ tym tyn _ _
    cases e; exact ⟨_, _, _, _, _, _, _, mrgΘ, mrgΔ, tym, tyn, .refl⟩
  case conv =>
    rename_i eq1 _ _ ih
    obtain ⟨A0, B0, s0, Θ1, Θ2, Δ1, Δ2, mrgΘ, mrgΔ, tym0, tyn0, eq2⟩ := ih e
    exact ⟨A0, B0, s0, Θ1, Θ2, Δ1, Δ2, mrgΘ, mrgΔ, tym0, tyn0,
      ARS.conv_trans (ARS.conv_sym eq1) eq2⟩
  all_goals (exact absurd e (by simp))

/-- Inversion for `one` (Coq `dyn_ii_inv`). -/
lemma one_inv {Θ Γ Δ A} (ty : Θ ⨾ Γ ⨾ Δ ⊢ .one : A) : Empty Θ := by
  generalize e : Term.one = m
  rw [e] at ty
  induction ty
  case one => rename_i emp _ _; exact emp
  case conv => rename_i _ _ _ ih; exact ih e
  all_goals (exact absurd e (by simp))

/-- Inversion for `tt` (Coq `dyn_tt_inv`). -/
lemma tt_inv {Θ Γ Δ A} (ty : Θ ⨾ Γ ⨾ Δ ⊢ .tt : A) : Empty Θ := by
  generalize e : Term.tt = m
  rw [e] at ty
  induction ty
  case tt => rename_i emp _ _; exact emp
  case conv => rename_i _ _ _ ih; exact ih e
  all_goals (exact absurd e (by simp))

/-- Inversion for `ff` (Coq `dyn_ff_inv`). -/
lemma ff_inv {Θ Γ Δ A} (ty : Θ ⨾ Γ ⨾ Δ ⊢ .ff : A) : Empty Θ := by
  generalize e : Term.ff = m
  rw [e] at ty
  induction ty
  case ff => rename_i emp _ _; exact emp
  case conv => rename_i _ _ _ ih; exact ih e
  all_goals (exact absurd e (by simp))

/-- Strengthened inversion for `pure` (Coq `dyn_return_invX`). -/
lemma pure_invX {Θ Γ Δ m B}
    (ty : Θ ⨾ Γ ⨾ Δ ⊢ .pure m : B) :
    ∃ A, Θ ⨾ Γ ⨾ Δ ⊢ m : A ∧ (B ≃ .M A) := by
  generalize e : Term.pure m = x
  rw [e] at ty
  induction ty generalizing m
  case pure =>
    rename_i tym _
    cases e; exact ⟨_, tym, .refl⟩
  case conv =>
    rename_i eq1 _ _ ih
    obtain ⟨A0, tym0, eq2⟩ := ih e
    exact ⟨A0, tym0, ARS.conv_trans (ARS.conv_sym eq1) eq2⟩
  all_goals (exact absurd e (by simp))

/-- Inversion for `pure` (Coq `dyn_return_inv`). -/
lemma pure_inv {Θ Γ Δ m A}
    (ty : Θ ⨾ Γ ⨾ Δ ⊢ .pure m : .M A) :
    Θ ⨾ Γ ⨾ Δ ⊢ m : A := by
  obtain ⟨B, tym, eq⟩ := pure_invX ty
  have eq := Static.M_inj eq
  obtain ⟨s, tyM⟩ := ty.validity
  obtain ⟨r, tyA, _⟩ := Static.M_inv tyM
  exact Typed.conv (ARS.conv_sym eq) tym tyA

/-- Strengthened inversion for `mlet` (Coq `dyn_bind_invX`). -/
lemma mlet_invX {Θ Γ Δ m n C}
    (ty : Θ ⨾ Γ ⨾ Δ ⊢ .mlet m n : C) :
    ∃ Θ1 Θ2 Δ1 Δ2 A B s t,
      Merge Θ1 Θ2 Θ ∧
      Merge Δ1 Δ2 Δ ∧
      Γ ⊢ B : .srt t ∧
      Θ1 ⨾ Γ ⨾ Δ1 ⊢ m : .M A ∧
      Θ2 ⨾ (A :: Γ) ⨾ (A :⟨s⟩ Δ2) ⊢ n : .M (B⟨(id : Nat → Nat); ↑⟩) ∧
      (C ≃ .M B) := by
  generalize e : Term.mlet m n = x
  rw [e] at ty
  induction ty generalizing m n
  case mlet =>
    rename_i mrgΘ mrgΔ tyB tym tyn _ _
    cases e
    exact ⟨_, _, _, _, _, _, _, _, mrgΘ, mrgΔ, tyB, tym, tyn, .refl⟩
  case conv =>
    rename_i eq1 _ _ ih
    obtain ⟨Θ1, Θ2, Δ1, Δ2, A0, B1, s0, t, mrgΘ, mrgΔ, tyB1, tym0, tyn, eq2⟩ := ih e
    exact ⟨Θ1, Θ2, Δ1, Δ2, A0, B1, s0, t, mrgΘ, mrgΔ, tyB1, tym0, tyn,
      ARS.conv_trans (ARS.conv_sym eq1) eq2⟩
  all_goals (exact absurd e (by simp))

/-- Inversion for `mlet` (Coq `dyn_bind_inv`). -/
lemma mlet_inv {Θ Γ Δ m n B}
    (ty : Θ ⨾ Γ ⨾ Δ ⊢ .mlet m n : .M B) :
    ∃ Θ1 Θ2 Δ1 Δ2 A s,
      Merge Θ1 Θ2 Θ ∧
      Merge Δ1 Δ2 Δ ∧
      Θ1 ⨾ Γ ⨾ Δ1 ⊢ m : .M A ∧
      Θ2 ⨾ (A :: Γ) ⨾ (A :⟨s⟩ Δ2) ⊢ n : .M (B⟨(id : Nat → Nat); ↑⟩) := by
  obtain ⟨Θ1, Θ2, Δ1, Δ2, A0, B0, s, t, mrgΘ, mrgΔ, tyB0, tym, tyn, eq⟩ := mlet_invX ty
  have eq := Static.M_inj eq
  obtain ⟨sM, tyMB⟩ := ty.validity
  obtain ⟨rB, tyB, _⟩ := Static.M_inv tyMB
  cases tyn.wf with
  | cons _ tyA =>
    refine ⟨Θ1, Θ2, Δ1, Δ2, A0, s, mrgΘ, mrgΔ, tym, ?_⟩
    have ce : B0⟨(id : Nat → Nat); ↑⟩ ≃ B⟨(id : Nat → Nat); ↑⟩ := by
      have h := Static.conv_subst (funcomp Term.var_Term Nat.succ) (ARS.conv_sym eq)
      have e1 : B0⟨(id : Nat → Nat); ↑⟩ = B0[Chan.var_Chan; funcomp Term.var_Term Nat.succ] := by
        substify
      have e2 : B⟨(id : Nat → Nat); ↑⟩ = B[Chan.var_Chan; funcomp Term.var_Term Nat.succ] := by
        substify
      rw [e1, e2]; exact h
    exact Typed.conv (Static.conv_M ce) tyn (tyB.weaken tyA).M

/-- Inversion for `chan` (Coq `dyn_cvar_inv`). -/
lemma chan_inv {Θ Γ Δ x B}
    (ty : Θ ⨾ Γ ⨾ Δ ⊢ .chan (Chan.var_Chan x) : B) :
    ∃ r A,
      Just Θ x (.ch r A) ∧
      [] ⊢ A : .proto ∧
      (B ≃ .ch r (A⟨(id : Nat → Nat); (· + Γ.length)⟩)) := by
  generalize e : Term.chan (Chan.var_Chan x) = m
  rw [e] at ty
  induction ty generalizing x
  case chan =>
    rename_i js _ _ tyA
    cases e; exact ⟨_, _, js, tyA, .refl⟩
  case conv =>
    rename_i eq1 _ _ ih
    obtain ⟨r, A0, js, tyA0, eq2⟩ := ih e
    exact ⟨r, A0, js, tyA0, ARS.conv_trans (ARS.conv_sym eq1) eq2⟩
  all_goals (exact absurd e (by simp))

/-- Inversion for `fork` (Coq `dyn_fork_inv`). -/
lemma fork_inv {Θ Γ Δ A m B}
    (ty : Θ ⨾ Γ ⨾ Δ ⊢ .fork A m : B) :
    Θ ⨾ (.ch true A :: Γ) ⨾ (.ch true A :L Δ) ⊢ m : .M .unit ∧
    (B ≃ .M (.ch false A)) := by
  generalize e : Term.fork A m = x
  rw [e] at ty
  induction ty generalizing A m
  case fork =>
    rename_i tym _
    cases e; exact ⟨tym, .refl⟩
  case conv =>
    rename_i eq1 _ _ ih
    obtain ⟨tym0, eq2⟩ := ih e
    exact ⟨tym0, ARS.conv_trans (ARS.conv_sym eq1) eq2⟩
  all_goals (exact absurd e (by simp))

/-- Inversion for `recv .im` (Coq `dyn_recv0_inv`). -/
lemma recvIm_inv {Θ Γ Δ m C}
    (ty : Θ ⨾ Γ ⨾ Δ ⊢ .recv m .im : C) :
    ∃ r1 r2 A B,
      xor r1 r2 = false ∧
      (C ≃ .M (.sig A (.ch r1 B) .im .L)) ∧
      Θ ⨾ Γ ⨾ Δ ⊢ m : .ch r1 (.act r2 A B .im) := by
  generalize e : Term.recv m .im = n
  rw [e] at ty
  induction ty generalizing m
  case recv =>
    rename_i xor tym _
    cases e; exact ⟨_, _, _, _, xor, .refl, tym⟩
  case conv =>
    rename_i eq1 _ _ ih
    obtain ⟨r1, r2, A1, B1, xor, eq2, tym0⟩ := ih e
    exact ⟨r1, r2, A1, B1, xor, ARS.conv_trans (ARS.conv_sym eq1) eq2, tym0⟩
  all_goals (exact absurd e (by simp))

/-- Inversion for `recv .ex` (Coq `dyn_recv1_inv`). -/
lemma recvEx_inv {Θ Γ Δ m C}
    (ty : Θ ⨾ Γ ⨾ Δ ⊢ .recv m .ex : C) :
    ∃ r1 r2 A B,
      xor r1 r2 = false ∧
      (C ≃ .M (.sig A (.ch r1 B) .ex .L)) ∧
      Θ ⨾ Γ ⨾ Δ ⊢ m : .ch r1 (.act r2 A B .ex) := by
  generalize e : Term.recv m .ex = n
  rw [e] at ty
  induction ty generalizing m
  case recv =>
    rename_i xor tym _
    cases e; exact ⟨_, _, _, _, xor, .refl, tym⟩
  case conv =>
    rename_i eq1 _ _ ih
    obtain ⟨r1, r2, A1, B1, xor, eq2, tym0⟩ := ih e
    exact ⟨r1, r2, A1, B1, xor, ARS.conv_trans (ARS.conv_sym eq1) eq2, tym0⟩
  all_goals (exact absurd e (by simp))

/-- Inversion for `send .im` (Coq `dyn_send0_inv`). -/
lemma sendIm_inv {Θ Γ Δ m C}
    (ty : Θ ⨾ Γ ⨾ Δ ⊢ .send m .im : C) :
    ∃ r1 r2 A B,
      xor r1 r2 = true ∧
      (C ≃ .pi A (.M (.ch r1 B)) .im .L) ∧
      Θ ⨾ Γ ⨾ Δ ⊢ m : .ch r1 (.act r2 A B .im) := by
  generalize e : Term.send m .im = n
  rw [e] at ty
  induction ty generalizing m
  case send =>
    rename_i xor tym _
    cases e; exact ⟨_, _, _, _, xor, .refl, tym⟩
  case conv =>
    rename_i eq1 _ _ ih
    obtain ⟨r1, r2, A1, B1, xor, eq2, tym0⟩ := ih e
    exact ⟨r1, r2, A1, B1, xor, ARS.conv_trans (ARS.conv_sym eq1) eq2, tym0⟩
  all_goals (exact absurd e (by simp))

/-- Inversion for `send .ex` (Coq `dyn_send1_inv`). -/
lemma sendEx_inv {Θ Γ Δ m C}
    (ty : Θ ⨾ Γ ⨾ Δ ⊢ .send m .ex : C) :
    ∃ r1 r2 A B,
      xor r1 r2 = true ∧
      (C ≃ .pi A (.M (.ch r1 B)) .ex .L) ∧
      Θ ⨾ Γ ⨾ Δ ⊢ m : .ch r1 (.act r2 A B .ex) := by
  generalize e : Term.send m .ex = n
  rw [e] at ty
  induction ty generalizing m
  case send =>
    rename_i xor tym _
    cases e; exact ⟨_, _, _, _, xor, .refl, tym⟩
  case conv =>
    rename_i eq1 _ _ ih
    obtain ⟨r1, r2, A1, B1, xor, eq2, tym0⟩ := ih e
    exact ⟨r1, r2, A1, B1, xor, ARS.conv_trans (ARS.conv_sym eq1) eq2, tym0⟩
  all_goals (exact absurd e (by simp))

/-- Inversion for `close false` (Wait, Coq `dyn_wait_inv`). -/
lemma wait_inv {Θ Γ Δ m C}
    (ty : Θ ⨾ Γ ⨾ Δ ⊢ .close false m : C) :
    (C ≃ .M .unit) ∧
    Θ ⨾ Γ ⨾ Δ ⊢ m : .ch false .stop := by
  generalize e : Term.close false m = x
  rw [e] at ty
  induction ty generalizing m
  case close =>
    rename_i tym _
    cases e; exact ⟨.refl, tym⟩
  case conv =>
    rename_i eq1 _ _ ih
    obtain ⟨eq2, tym0⟩ := ih e
    exact ⟨ARS.conv_trans (ARS.conv_sym eq1) eq2, tym0⟩
  all_goals (exact absurd e (by simp))

/-- Inversion for `close true` (Close, Coq `dyn_close_inv`). -/
lemma close_inv {Θ Γ Δ m C}
    (ty : Θ ⨾ Γ ⨾ Δ ⊢ .close true m : C) :
    (C ≃ .M .unit) ∧
    Θ ⨾ Γ ⨾ Δ ⊢ m : .ch true .stop := by
  generalize e : Term.close true m = x
  rw [e] at ty
  induction ty generalizing m
  case close =>
    rename_i tym _
    cases e; exact ⟨.refl, tym⟩
  case conv =>
    rename_i eq1 _ _ ih
    obtain ⟨eq2, tym0⟩ := ih e
    exact ⟨ARS.conv_trans (ARS.conv_sym eq1) eq2, tym0⟩
  all_goals (exact absurd e (by simp))

end TLLC.Dynamic
