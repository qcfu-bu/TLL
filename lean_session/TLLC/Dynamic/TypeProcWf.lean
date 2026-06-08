import TLLC.Dynamic.CSubst

/-!
# Process-context well-formedness from typing

Port of the `proc_wf` metatheory from `coq_session/proc_type.v` that was deferred when the `ProcWf`
*inductive* was lifted into `Dynamic.ProcWf` (to break the `dyn_csubst` dependency cycle). This file
supplies the combining/derivation lemmas:

* `Empty.procWf` (Coq `dyn_empty_proc_wf`): an empty context is well-formed.
* `ProcWf.merge` (Coq `proc_wf_merge`): well-formedness is closed under merge.
* `Just.procWf` (Coq `dyn_just_proc_wf`): a context with a channel slot of closed protocol is
  well-formed — the case deferred earlier, now dischargeable via `Static.Typed.crename_inv`.
* `Typed.procWf` (Coq `dyn_type_proc_wf`): the process context of any dynamic typing is well-formed.
* `ProcWf.empty_merge` (Coq `proc_wf_empty`): a well-formed context is the right-merge of an empty
  one (used to seed channel substitutions).
-/

namespace TLLC.Dynamic
open Autosubst Autosubst.Notation
open scoped TLLC.Static

/-- An empty process context is well-formed (Coq `dyn_empty_proc_wf`). -/
lemma Empty.procWf {Θ} (emp : Empty Θ) : ProcWf Θ := by
  induction emp with
  | nil => exact .nil
  | null _ ih => exact .null ih

/-- Well-formedness is closed under merge (Coq `proc_wf_merge`). -/
lemma ProcWf.merge {Θ1 Θ2 Θ} (mrg : Merge Θ1 Θ2 Θ) (wf1 : ProcWf Θ1) (wf2 : ProcWf Θ2) :
    ProcWf Θ := by
  induction mrg with
  | nil => exact .nil
  | left _ _ => cases wf1
  | right1 _ _ ih => cases wf1 with | ty wf1' tyA => exact .ty (ih wf1' (by cases wf2; assumption)) tyA
  | right2 _ _ ih => cases wf2 with | ty wf2' tyA => exact .ty (ih (by cases wf1; assumption) wf2') tyA
  | null _ ih => cases wf1 with | null wf1' => cases wf2 with | null wf2' => exact .null (ih wf1' wf2')

/-- A context with a closed-protocol channel slot is well-formed (Coq `dyn_just_proc_wf`). -/
lemma Just.procWf {Θ x C r A} (js : Just Θ x C) (hC : C = .ch r A) (tyA : [] ⊢ A : .proto) :
    ProcWf Θ := by
  induction js generalizing r A with
  | @zero Δ A1 emp =>
    cases A1
    case ch r' A0 =>
      rw [show (Term.ch r' A0)⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩
            = Term.ch r' (A0⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) from by asimp] at hC
      cases hC
      exact .ty emp.procWf (proto_pred tyA)
    all_goals (asimp at hC; exact absurd hC (by simp))
  | @null Δ A1 y js' ih =>
    cases A1
    case ch r' A0 =>
      rw [show (Term.ch r' A0)⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩
            = Term.ch r' (A0⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) from by asimp] at hC
      cases hC
      exact .null (ih rfl (proto_pred tyA))
    all_goals (asimp at hC; exact absurd hC (by simp))

/-- The process context of a dynamic typing is well-formed (Coq `dyn_type_proc_wf`). -/
lemma Typed.procWf {Θ Γ Δ m A} (ty : Θ ⨾ Γ ⨾ Δ ⊢ m : A) : ProcWf Θ := by
  induction ty with
  | var emp _ _ _ => exact emp.procWf
  | lamIm _ _ _ ih => exact ih
  | lamEx _ _ _ ih => exact ih
  | appIm _ _ ihm => exact ihm
  | appEx mrg _ _ _ ihm ihn => exact ProcWf.merge mrg ihm ihn
  | pairIm _ _ _ ihn => exact ihn
  | pairEx mrg _ _ _ _ ihm ihn => exact ProcWf.merge mrg ihm ihn
  | projIm mrg _ _ _ _ ihm ihn => exact ProcWf.merge mrg ihm ihn
  | projEx mrg _ _ _ _ ihm ihn => exact ProcWf.merge mrg ihm ihn
  | one emp _ _ => exact emp.procWf
  | tt emp _ _ => exact emp.procWf
  | ff emp _ _ => exact emp.procWf
  | ite mrg _ _ _ _ _ ihm ihn1 _ => exact ProcWf.merge mrg ihm ihn1
  | pure _ ihm => exact ihm
  | mlet mrg _ _ _ _ ihm ihn => exact ProcWf.merge mrg ihm ihn
  | chan js _ _ tyA => exact js.procWf rfl tyA
  | fork _ ihm => exact ihm
  | recv _ _ ihm => exact ihm
  | send _ _ ihm => exact ihm
  | close _ ihm => exact ihm
  | conv _ _ _ ihm => exact ihm

/-- A well-formed context is the right component of a merge with an empty context (Coq
    `proc_wf_empty`). -/
lemma ProcWf.empty_merge {Θ} (wf : ProcWf Θ) : ∃ Θ', Empty Θ' ∧ Merge Θ' Θ Θ := by
  induction wf with
  | nil => exact ⟨[], .nil, .nil⟩
  | @ty Θ r A _ _ ih =>
    obtain ⟨Θ', emp, mrg⟩ := ih
    exact ⟨none :: Θ', .null emp, .right2 _ mrg⟩
  | @null Θ _ ih =>
    obtain ⟨Θ', emp, mrg⟩ := ih
    exact ⟨none :: Θ', .null emp, .null mrg⟩

end TLLC.Dynamic
