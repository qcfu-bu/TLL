import TLLC.Dynamic.CSubst

/-!
# Process-context well-formedness from typing

Port of the `proc_wf` metatheory from `coq_session/proc_type.v` that was deferred when the `ProcWf`
*inductive* was lifted into `Dynamic.ProcWf` (to break the `dyn_csubst` dependency cycle). This file
supplies the combining/derivation lemmas:

* `PEmpty.procWf` (Coq `dyn_empty_proc_wf`): an empty context is well-formed.
* `ProcWf.merge` (Coq `proc_wf_merge`): well-formedness is closed under merge.
* `PJust.procWf` (Coq `dyn_just_proc_wf`): a context with a channel slot of closed protocol is
  well-formed — the case deferred earlier, now dischargeable via `Static.Typed.crename_inv`.
* `Typed.procWf` (Coq `dyn_type_proc_wf`): the process context of any dynamic typing is well-formed.
* `ProcWf.empty_merge` (Coq `proc_wf_empty`): a well-formed context is the right-merge of an empty
  one (used to seed channel substitutions).
-/

namespace TLLC.Dynamic
open Autosubst Autosubst.Notation
open scoped TLLC.Static

/-- An empty process context is well-formed (Coq `dyn_empty_proc_wf`). -/
lemma PEmpty.procWf {Θ} (emp : PEmpty Θ) : ProcWf Θ := by
  induction emp with
  | nil => exact .nil
  | none _ ih => exact .none ih

/-- Well-formedness is closed under merge (Coq `proc_wf_merge`). -/
lemma ProcWf.merge {Θ1 Θ2 Θ} (mrg : PMerge Θ1 Θ2 Θ) (wf1 : ProcWf Θ1) (wf2 : ProcWf Θ2) :
    ProcWf Θ := by
  induction mrg with
  | nil => exact .nil
  | none _ ih =>
    cases wf1 with | none wf1' =>
    cases wf2 with | none wf2' =>
    exact .none (ih wf1' wf2')
  | oneL _ ih =>
    cases wf1 with | one wf1' tyA =>
    cases wf2 with | none wf2' =>
    exact .one (ih wf1' wf2') tyA
  | oneR _ ih =>
    cases wf1 with | none wf1' =>
    cases wf2 with | one wf2' tyA =>
    exact .one (ih wf1' wf2') tyA
  | bothL _ ih =>
    cases wf1 with | both wf1' tyA =>
    cases wf2 with | none wf2' =>
    exact .both (ih wf1' wf2') tyA
  | bothR _ ih =>
    cases wf1 with | none wf1' =>
    cases wf2 with | both wf2' tyA =>
    exact .both (ih wf1' wf2') tyA
  | split _ ih =>
    cases wf1 with | one wf1' tyA =>
    cases wf2 with | one wf2' _ =>
    exact .both (ih wf1' wf2') tyA

/-- A context with a closed-protocol channel slot is well-formed (Coq `dyn_just_proc_wf`). -/
lemma PJust.procWf {Θ x r A} (js : PJust Θ x r A) (tyA : [] ⊢ A : .proto) :
    ProcWf Θ := by
  induction js with
  | zero emp => exact .one emp.procWf (proto_pred tyA)
  | none _ ih => exact .none (ih (proto_pred tyA))

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
  | chan js _ _ tyA => exact js.procWf tyA
  | fork _ ihm => exact ihm
  | recv _ _ ihm => exact ihm
  | send _ _ ihm => exact ihm
  | close _ ihm => exact ihm
  | conv _ _ _ ihm => exact ihm

/-- A well-formed context is the right component of a merge with an empty context (Coq
    `proc_wf_empty`). -/
lemma ProcWf.empty_merge {Θ} (wf : ProcWf Θ) : ∃ Θ', PEmpty Θ' ∧ PMerge Θ' Θ Θ := by
  induction wf with
  | nil => exact ⟨[], .nil, .nil⟩
  | @one Θ r A _ _ ih =>
    obtain ⟨Θ', emp, mrg⟩ := ih
    exact ⟨.none :: Θ', .none emp, .oneR mrg⟩
  | @both Θ A _ _ ih =>
    obtain ⟨Θ', emp, mrg⟩ := ih
    exact ⟨.none :: Θ', .none emp, .bothR mrg⟩
  | @none Θ _ ih =>
    obtain ⟨Θ', emp, mrg⟩ := ih
    exact ⟨.none :: Θ', .none emp, .none mrg⟩

end TLLC.Dynamic
