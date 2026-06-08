import TLLC.Dynamic.Context

/-!
# Process channel contexts (self-dual single-channel encoding)

The process channel context `PCtx` and its merge algebra, for the Lean **self-dual single-channel**
scope restriction (`Proc.nu : bind Chan in Proc`, one bound channel) rather than the Coq `Nu`'s two
endpoints / the report's two-channel `vcd.P`. See [[tllc-process-channel-encoding]].

## The self-dual design
A session channel has two dual endpoints. The Coq introduces both as two `:L` slots and routes each
to its thread with the ordinary merge. Here `res p` introduces ONE channel, tracked by a **trinary
slot** `Slot` recording how many of its two endpoints are still present:

* `Slot.both A` — both dual endpoints of protocol `A` (fresh from `res`),
* `Slot.one r A` — a single endpoint of polarity `r`,
* `Slot.none` — consumed/absent.

The process-context merge `PMerge` is **count-conserving**: its `split` rule divides a `both` (count 2)
into `one r` + `one (¬r)` (the two dual endpoints, 1 + 1). Crucially `split` PRODUCES a `both`, which
can never re-enter as a `one`, so a single endpoint cannot be split-merged against several duals (the
unsoundness of a naive `ch r`-shaped result). A single endpoint reaches exactly one leaf via the
ordinary `one`/`none` routing. Leaf (thread) typing converts a `both`-free process context to a
`Dynamic` channel context via `Realize` (`one r A ↦ ch r A :L`), so a `both` channel must be `split`
by a `par` before any thread can use it.
-/

namespace TLLC.Process
open Autosubst Autosubst.Notation
open TLLC.Dynamic

/-- A channel slot tracking how many of a channel's two dual endpoints are present. -/
inductive Slot where
  | none
  | one (r : Bool) (A : Term)
  | both (A : Term)

/-- Process channel context: a list of trinary channel slots. -/
abbrev PCtx := List Slot

/-- Count-conserving process-context merge with channel dual-`split`. -/
inductive PMerge : PCtx → PCtx → PCtx → Prop where
  | nil :
    PMerge [] [] []
  | none {Δ1 Δ2 Δ} :
    PMerge Δ1 Δ2 Δ →
    PMerge (.none :: Δ1) (.none :: Δ2) (.none :: Δ)
  | oneL {Δ1 Δ2 Δ r A} :
    PMerge Δ1 Δ2 Δ →
    PMerge (.one r A :: Δ1) (.none :: Δ2) (.one r A :: Δ)
  | oneR {Δ1 Δ2 Δ r A} :
    PMerge Δ1 Δ2 Δ →
    PMerge (.none :: Δ1) (.one r A :: Δ2) (.one r A :: Δ)
  | bothL {Δ1 Δ2 Δ A} :
    PMerge Δ1 Δ2 Δ →
    PMerge (.both A :: Δ1) (.none :: Δ2) (.both A :: Δ)
  | bothR {Δ1 Δ2 Δ A} :
    PMerge Δ1 Δ2 Δ →
    PMerge (.none :: Δ1) (.both A :: Δ2) (.both A :: Δ)
  | split {Δ1 Δ2 Δ r A} :
    PMerge Δ1 Δ2 Δ →
    PMerge (.one r A :: Δ1) (.one (!r) A :: Δ2) (.both A :: Δ)

/-- The process merge is symmetric (Coq `merge_sym`). -/
lemma PMerge.sym {Θ1 Θ2 Θ} (mrg : PMerge Θ1 Θ2 Θ) : PMerge Θ2 Θ1 Θ := by
  induction mrg with
  | nil => exact .nil
  | none _ ih => exact .none ih
  | oneL _ ih => exact .oneR ih
  | oneR _ ih => exact .oneL ih
  | bothL _ ih => exact .bothR ih
  | bothR _ ih => exact .bothL ih
  | @split Δ1 Δ2 Δ r A _ ih =>
    have h := PMerge.split (r := !r) (A := A) ih
    rwa [Bool.not_not] at h

/-- Left split-rotation of a nested process merge (Coq `merge_splitL`). -/
lemma PMerge.splitL {Θ1 Θ2 Θ} (mrg : PMerge Θ1 Θ2 Θ) :
    ∀ {Θa Θb}, PMerge Θa Θb Θ1 → ∃ Θc, PMerge Θa Θ2 Θc ∧ PMerge Θc Θb Θ := by
  induction mrg with
  | nil => intro _ _ m2; cases m2; exact ⟨[], .nil, .nil⟩
  | none _ ih => intro _ _ m2; cases m2 with
    | none m2' => obtain ⟨Θc, ha, hb⟩ := ih m2'; exact ⟨_, .none ha, .none hb⟩
  | @oneL Δ1 Δ2 Δ r A _ ih => intro _ _ m2; cases m2 with
    | oneL m2' => obtain ⟨Θc, ha, hb⟩ := ih m2'; exact ⟨_, .oneL ha, .oneL hb⟩
    | oneR m2' => obtain ⟨Θc, ha, hb⟩ := ih m2'; exact ⟨_, .none ha, .oneR hb⟩
  | oneR _ ih => intro _ _ m2; cases m2 with
    | none m2' => obtain ⟨Θc, ha, hb⟩ := ih m2'; exact ⟨_, .oneR ha, .oneL hb⟩
  | @bothL Δ1 Δ2 Δ A _ ih => intro _ _ m2; cases m2 with
    | bothL m2' => obtain ⟨Θc, ha, hb⟩ := ih m2'; exact ⟨_, .bothL ha, .bothL hb⟩
    | bothR m2' => obtain ⟨Θc, ha, hb⟩ := ih m2'; exact ⟨_, .none ha, .bothR hb⟩
    | split m2' => obtain ⟨Θc, ha, hb⟩ := ih m2'; exact ⟨_, .oneL ha, .split hb⟩
  | bothR _ ih => intro _ _ m2; cases m2 with
    | none m2' => obtain ⟨Θc, ha, hb⟩ := ih m2'; exact ⟨_, .bothR ha, .bothL hb⟩
  | @split Δ1 Δ2 Δ r A _ ih => intro _ _ m2; cases m2 with
    | oneL m2' => obtain ⟨Θc, ha, hb⟩ := ih m2'; exact ⟨_, .split ha, .bothL hb⟩
    | oneR m2' =>
      obtain ⟨Θc, ha, hb⟩ := ih m2'
      have hb' := PMerge.split (r := !r) (A := A) hb
      rw [Bool.not_not] at hb'
      exact ⟨_, .oneR ha, hb'⟩

/-- Right split-rotation of a nested process merge (Coq `merge_splitR`). -/
lemma PMerge.splitR {Θ1 Θ2 Θ} (mrg : PMerge Θ1 Θ2 Θ) :
    ∀ {Θa Θb}, PMerge Θa Θb Θ1 → ∃ Θc, PMerge Θb Θ2 Θc ∧ PMerge Θc Θa Θ := by
  induction mrg with
  | nil => intro _ _ m2; cases m2; exact ⟨[], .nil, .nil⟩
  | none _ ih => intro _ _ m2; cases m2 with
    | none m2' => obtain ⟨Θc, ha, hb⟩ := ih m2'; exact ⟨_, .none ha, .none hb⟩
  | @oneL Δ1 Δ2 Δ r A _ ih => intro _ _ m2; cases m2 with
    | oneL m2' => obtain ⟨Θc, ha, hb⟩ := ih m2'; exact ⟨_, .none ha, .oneR hb⟩
    | oneR m2' => obtain ⟨Θc, ha, hb⟩ := ih m2'; exact ⟨_, .oneL ha, .oneL hb⟩
  | oneR _ ih => intro _ _ m2; cases m2 with
    | none m2' => obtain ⟨Θc, ha, hb⟩ := ih m2'; exact ⟨_, .oneR ha, .oneL hb⟩
  | @bothL Δ1 Δ2 Δ A _ ih => intro _ _ m2; cases m2 with
    | bothL m2' => obtain ⟨Θc, ha, hb⟩ := ih m2'; exact ⟨_, .none ha, .bothR hb⟩
    | bothR m2' => obtain ⟨Θc, ha, hb⟩ := ih m2'; exact ⟨_, .bothL ha, .bothL hb⟩
    | @split Δa Δb _ r A m2' =>
      obtain ⟨Θc, ha, hb⟩ := ih m2'
      have hb' := PMerge.split (r := !r) (A := A) hb
      rw [Bool.not_not] at hb'
      exact ⟨_, .oneL ha, hb'⟩
  | bothR _ ih => intro _ _ m2; cases m2 with
    | none m2' => obtain ⟨Θc, ha, hb⟩ := ih m2'; exact ⟨_, .bothR ha, .bothL hb⟩
  | @split Δ1 Δ2 Δ r A _ ih => intro _ _ m2; cases m2 with
    | oneL m2' =>
      obtain ⟨Θc, ha, hb⟩ := ih m2'
      have hb' := PMerge.split (r := !r) (A := A) hb
      rw [Bool.not_not] at hb'
      exact ⟨_, .oneR ha, hb'⟩
    | oneR m2' => obtain ⟨Θc, ha, hb⟩ := ih m2'; exact ⟨_, .split ha, .bothL hb⟩

/-- Lower a `both`-free process context to a dynamic channel context for leaf (thread) typing. -/
inductive Realize : PCtx → Ctx → Prop where
  | nil :
    Realize [] []
  | none {Θ Θ'} :
    Realize Θ Θ' →
    Realize (.none :: Θ) (Option.none :: Θ')
  | one {Θ Θ' r A} :
    Realize Θ Θ' →
    Realize (.one r A :: Θ) (.ch r A :L Θ')

/-- A dynamic merge of a realized context lifts to a process merge of compatible realized halves
    (each `one`/`none` slot routes entirely to one side — no duplication). -/
lemma Realize.split {Θ Θd Θ1d Θ2d} (rea : Realize Θ Θd) (mrg : Merge Θ1d Θ2d Θd) :
    ∃ Θ1 Θ2, PMerge Θ1 Θ2 Θ ∧ Realize Θ1 Θ1d ∧ Realize Θ2 Θ2d := by
  induction rea generalizing Θ1d Θ2d with
  | nil => cases mrg; exact ⟨[], [], .nil, .nil, .nil⟩
  | none _ ih =>
    cases mrg with
    | null mrg' =>
      obtain ⟨Θ1, Θ2, m, r1, r2⟩ := ih mrg'
      exact ⟨.none :: Θ1, .none :: Θ2, .none m, .none r1, .none r2⟩
  | one _ ih =>
    cases mrg with
    | right1 _ mrg' =>
      obtain ⟨Θ1, Θ2, m, r1, r2⟩ := ih mrg'
      exact ⟨.one _ _ :: Θ1, .none :: Θ2, .oneL m, .one r1, .none r2⟩
    | right2 _ mrg' =>
      obtain ⟨Θ1, Θ2, m, r1, r2⟩ := ih mrg'
      exact ⟨.none :: Θ1, .one _ _ :: Θ2, .oneR m, .none r1, .one r2⟩

/-! ## Empty process contexts. -/

/-- A process context with every slot `none` (the all-`none` analogue of `Empty`). -/
inductive PEmpty : PCtx → Prop where
  | nil : PEmpty []
  | none {Θ} : PEmpty Θ → PEmpty (.none :: Θ)

/-- A leaf lowering of an empty dynamic context comes from an all-`none` process context. -/
lemma Realize.pempty {Θ Θd} (rea : Realize Θ Θd) (emp : Empty Θd) : PEmpty Θ := by
  induction rea with
  | nil => exact .nil
  | none _ ih => cases emp with | null e => exact .none (ih e)
  | one _ _ => cases emp

/-- An all-`none` process context lowers to an empty dynamic context. -/
lemma PEmpty.realize {Θ} (emp : PEmpty Θ) : ∃ Θd, Realize Θ Θd ∧ Empty Θd := by
  induction emp with
  | nil => exact ⟨[], .nil, .nil⟩
  | none _ ih => obtain ⟨Θd, rea, e⟩ := ih; exact ⟨Option.none :: Θd, .none rea, .null e⟩

/-- An all-`none` right component makes a process merge an identity on the left. -/
lemma PMerge.emptyR {Θ1 Θ2 Θ} (mrg : PMerge Θ1 Θ2 Θ) (emp : PEmpty Θ2) : Θ1 = Θ := by
  induction mrg with
  | nil => rfl
  | none _ ih => cases emp with | none e => rw [ih e]
  | oneL _ ih => cases emp with | none e => rw [ih e]
  | oneR _ _ => cases emp
  | bothL _ ih => cases emp with | none e => rw [ih e]
  | bothR _ _ => cases emp
  | split _ _ => cases emp

/-- Every process context has an all-`none` right identity for merge. -/
lemma PMerge.refl_emptyR (Θ : PCtx) : ∃ Θe, PEmpty Θe ∧ PMerge Θ Θe Θ := by
  induction Θ with
  | nil => exact ⟨[], .nil, .nil⟩
  | cons s Θ ih =>
    obtain ⟨Θe, emp, mrg⟩ := ih
    cases s with
    | none => exact ⟨_, .none emp, .none mrg⟩
    | one r A => exact ⟨_, .none emp, .oneL mrg⟩
    | both A => exact ⟨_, .none emp, .bothL mrg⟩

end TLLC.Process
