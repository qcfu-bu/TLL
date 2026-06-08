import TLLC.Process.CRename
import TLLC.Process.Step
import TLLC.Dynamic.TypeProcWf
import TLLC.Static.CSubst

/-!
# Process channel substitution — the `exch` exchange (self-dual single-channel encoding)

Port of `coq_session/proc_csubst.v`'s only consumer, the scope-exchange congruence
`proc_exch_type` (`Θ ⊢ ν.ν.p → Θ ⊢ ν.ν.(csubst exch p)`). Process-level channel substitution is used
*only* for the transposition `exch` of the two innermost channels (in `proc_sr`'s `≡`-congruence
preservation). Because `Chan` is variable-only, `csubst exch = cren exch_ren` is a channel *renaming*
(`exch_ren = (1 .: 0 .: (·+2))`), per the user's chosen approach.

The transposition does not commute with the linear de-Bruijn `+1` shifts of `PJust`, so it cannot be a
`CtxCRen` constructor (the renamed lookup type only matches up to `cren_conv0` conversion). Instead
we reuse the already-proven dynamic channel *substitution* `Dynamic.Typed.csubstitution` at each leaf:
the process exchange relation `PCExch` (`swap` two front slots + `lift` under a binder) bridges to a
dynamic `AgreeCSubst Θ' exch Θ` over `PCtx` (`PCExch.agree`). `PCExch.merge` splits the exchange
across `par`, and `Typed.cexch` runs the process induction.
-/

namespace TLLC.Process
open Autosubst Autosubst.Notation
open TLLC.Dynamic
open scoped TLLC.Static TLLC.Dynamic

/-- The `Nat → Nat` channel renaming underlying `exch` (Coq `exch`'s index map): `1 .: 0 .: (·+2)`. -/
abbrev exch_ren : Nat → Nat := Static.csubst_ren exch

/-- Process channel substitution by `exch` is the channel renaming by `exch_ren` (Coq's
    `csubst exch = cren exch_ren`, unconditional since `Chan` is variable-only). -/
lemma csubst_exch (p : Proc) : p[exch; Term.var_Term] = p⟨exch_ren; (id : Nat → Nat)⟩ := by
  rw [show p⟨exch_ren; (id : Nat → Nat)⟩ = p[exch; Term.var_Term] from by
        substify; rw [Static.csubst_ren_eq]]

/-! ## Channel-typing and empty-merge helpers. -/

/-- An empty right component of a self-merge from well-formedness (`proc_wf_empty` + `merge_sym`). -/
lemma procWf_emptyR {Θ : PCtx} (wf : ProcWf Θ) : ∃ Θe, PEmpty Θe ∧ PMerge Θ Θe Θ := by
  obtain ⟨Θe, emp, mrg⟩ := wf.empty_merge
  exact ⟨Θe, emp, mrg.sym⟩

/-- Type a channel variable at a `PJust` slot whose protocol is conversion-equal to a closed `A`
    (the `Typed.chan` + `cren_conv0` reconciliation, Coq's `dyn_conv` + `sta_cren_conv0`). -/
lemma chanTyped {Θ : PCtx} {x r} {A0 A : Term} (js : PJust Θ x r A0)
    (tyA0 : [] ⊢ A0 : .proto) (h : A0 ≃ A) (tyA : [] ⊢ A : .proto) :
    Θ ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ .chan (Chan.var_Chan x) : .ch r A := by
  have hh := Typed.chan js Wf.nil Key.nil tyA0
  apply Typed.conv ?_ hh (Static.Typed.ch tyA)
  apply Static.conv_ch
  rw [show A0⟨(id : Nat → Nat); (· + ([] : Static.Ctx).length)⟩ = A0 from by
        simp only [List.length_nil, Nat.add_zero]
        rw [show ((fun x => x) : Nat → Nat) = (id : Nat → Nat) from rfl]; asimp]
  exact h

/-- The `PJust` lookup of a front channel slot, with the de Bruijn `+1` shift exposed. -/
lemma justShift1 {Θe : PCtx} {r} {A : Term} (emp : PEmpty Θe) :
    PJust (.one r A :: Θe) 0 r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) :=
  PJust.zero emp

/-- A channel variable at index `0` of a singleton channel context. -/
lemma chanAt0 {Θe : PCtx} {r} {A : Term} (emp : PEmpty Θe) (tyA : [] ⊢ A : .proto) :
    (.one r A :: Θe) ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ .chan (Chan.var_Chan 0) : .ch r A :=
  chanTyped (justShift1 emp) (Static.Typed.crename tyA _) (Static.cren_conv0 .refl _) tyA

/-- A channel variable at index `1` of a null-padded singleton channel context. -/
lemma chanAt1 {Θe : PCtx} {r} {A : Term} (emp : PEmpty Θe) (tyA : [] ⊢ A : .proto) :
    (.none :: .one r A :: Θe) ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ .chan (Chan.var_Chan 1) : .ch r A := by
  have js : PJust (.none :: .one r A :: Θe) 1 r
      ((A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)⟨((· + 1) : Nat → Nat);
        (id : Nat → Nat)⟩) :=
    PJust.none (justShift1 (Θe := Θe) (r := r) (A := A) emp)
  exact chanTyped js (Static.Typed.crename (Static.Typed.crename tyA _) _)
    (ARS.conv_trans (Static.cren_conv0 .refl _) (Static.cren_conv0 .refl _)) tyA

/-! ## The process exchange relation and its preservation. -/

/-- Process channel-exchange agreement: `swap` the two front slots (renaming by `exch`), `lift`
    under a binder (the index shift absorbed by `up_Chan_Chan`). -/
inductive PCExch : (Nat → Chan) → PCtx → PCtx → Prop where
  | swap {s0 s1 Θ} :
    PCExch exch (s0 :: s1 :: Θ) (s1 :: s0 :: Θ)
  | lift {σ s Θ Θ'} :
    PCExch σ Θ Θ' →
    PCExch (up_Chan_Chan σ) (s :: Θ) (s :: Θ')

/-- Process exchange bridges directly to dynamic channel-substitution agreement. -/
lemma PCExch.agree {σ Θ Θ'} (ex : PCExch σ Θ Θ') :
    ProcWf Θ → AgreeCSubst Θ' σ Θ := by
  induction ex with
  | @swap s0 s1 Θ =>
    intro wf
    exact .swap wf
  | @lift σ s Θ Θ' _ ih =>
    intro wf
    cases s with
    | none =>
      cases wf with | none wf0 => exact .n (ih wf0)
    | one r A =>
      cases wf with | one wf0 tyA => exact .ty (ih wf0) tyA
    | both A =>
      cases wf with | both wf0 tyA => exact .both (ih wf0) tyA

/-- The exchange splits across a process merge. -/
lemma PCExch.merge {σ Θ Θ'} (ex : PCExch σ Θ Θ') :
    ∀ {Θ1 Θ2}, PMerge Θ1 Θ2 Θ →
    ∃ Θ1' Θ2', PMerge Θ1' Θ2' Θ' ∧ PCExch σ Θ1 Θ1' ∧ PCExch σ Θ2 Θ2' := by
  induction ex with
  | @swap s0 s1 Θ =>
    intro Θ1 Θ2 mrg
    -- peel the two front slots, swap them in the merge, swap each side
    cases mrg <;> rename_i h1 <;> cases h1 <;> rename_i mrg0 <;>
      exact ⟨_, _, by constructor; constructor; exact mrg0, .swap, .swap⟩
  | @lift σ s Θ Θ' _ ih =>
    intro Θ1 Θ2 mrg
    cases mrg with
    | none mrg0 =>
      obtain ⟨A, B, mrg', e1, e2⟩ := ih mrg0; exact ⟨_ :: A, _ :: B, .none mrg', .lift e1, .lift e2⟩
    | oneL mrg0 =>
      obtain ⟨A, B, mrg', e1, e2⟩ := ih mrg0; exact ⟨_ :: A, _ :: B, .oneL mrg', .lift e1, .lift e2⟩
    | oneR mrg0 =>
      obtain ⟨A, B, mrg', e1, e2⟩ := ih mrg0; exact ⟨_ :: A, _ :: B, .oneR mrg', .lift e1, .lift e2⟩
    | bothL mrg0 =>
      obtain ⟨A, B, mrg', e1, e2⟩ := ih mrg0; exact ⟨_ :: A, _ :: B, .bothL mrg', .lift e1, .lift e2⟩
    | bothR mrg0 =>
      obtain ⟨A, B, mrg', e1, e2⟩ := ih mrg0; exact ⟨_ :: A, _ :: B, .bothR mrg', .lift e1, .lift e2⟩
    | split mrg0 =>
      obtain ⟨A, B, mrg', e1, e2⟩ := ih mrg0; exact ⟨_ :: A, _ :: B, .split mrg', .lift e1, .lift e2⟩

/-- Channel exchange preserves process typing (the core of Coq `proc_exch_type`). -/
lemma Typed.cexch {Θ p} (ty : Θ ⊩ p) :
    ∀ {σ Θ'}, PCExch σ Θ Θ' → Θ' ⊩ p[σ; Term.var_Term] := by
  induction ty with
  | @exp Θ m tym =>
    intro σ Θ' ex
    obtain agr := ex.agree tym.procWf
    asimp
    exact .exp (tym.csubstitution agr)
  | @par Θ1 Θ2 Θ p q mrg _ _ ihp ihq =>
    intro σ Θ' ex
    obtain ⟨Θ1', Θ2', mrg', ex1, ex2⟩ := ex.merge mrg
    asimp
    exact .par mrg' (ihp ex1) (ihq ex2)
  | @res Θ p A tyA _ ih =>
    intro σ Θ' ex
    asimp
    exact .res tyA (ih (.lift ex))

/-- The scope-exchange congruence preserves typing (Coq `proc_exch_type`). -/
lemma Typed.exch {Θ p} (ty : Θ ⊩ Proc.nu (Proc.nu p)) :
    Θ ⊩ Proc.nu (Proc.nu (p⟨exch_ren; (id : Nat → Nat)⟩)) := by
  cases ty with
  | res tyA1 ty1 =>
    cases ty1 with
    | res tyA0 ty0 =>
      have key := ty0.cexch (PCExch.swap (s0 := Slot.both _) (s1 := Slot.both _) (Θ := Θ))
      rw [csubst_exch] at key
      exact .res tyA0 (.res tyA1 key)

end TLLC.Process
