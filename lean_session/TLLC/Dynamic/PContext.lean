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
ordinary `one`/`none` routing. Dynamic leaf typing is channel-aware over the full `PCtx`; the
`PCtxSingle` predicate remains only as an auxiliary way to talk about contexts with no `both` slots.
-/

namespace TLLC.Dynamic
open Autosubst Autosubst.Notation

/-- A channel slot tracking how many of a channel's two dual endpoints are present. -/
inductive Slot where
  | none
  | one (r : Bool) (A : Term)
  | both (A : Term)

/-- Process channel context: a list of trinary channel slots. -/
abbrev PCtx := List Slot

/-- Channel substitution swapping the two innermost channels `0 ↔ 1`. -/
abbrev cexch : Nat → Chan :=
  Chan.var_Chan 1 .: Chan.var_Chan 0 .: (fun x => Chan.var_Chan (x + 2))

/-! ## Key and endpoint lookup. -/

/-- All live channel endpoints in a process context are admissible at sort `s`. Since channel
endpoints are linear resources, non-empty live slots are admissible only at sort `L`. -/
inductive PKey : PCtx → Srt → Prop where
  | nil {s} :
    PKey [] s
  | none {Θ s} :
    PKey Θ s →
    PKey (.none :: Θ) s
  | one {Θ r A} :
    PKey Θ Srt.L →
    PKey (.one r A :: Θ) Srt.L
  | both {Θ A} :
    PKey Θ Srt.L →
    PKey (.both A :: Θ) Srt.L

@[inherit_doc] scoped notation:40 Θ:41 " ▷ₚ " s:41 => PKey Θ s

/-- A process context with every slot `none` (the all-`none` analogue of `Empty`). -/
inductive PEmpty : PCtx → Prop where
  | nil : PEmpty []
  | none {Θ} : PEmpty Θ → PEmpty (.none :: Θ)

/-- An empty process context has every key. -/
lemma PEmpty.key {Θ s} (emp : PEmpty Θ) : Θ ▷ₚ s := by
  induction emp with
  | nil => exact .nil
  | none _ ih => exact .none ih

/-- Every process context has key `L`. -/
lemma PKey.impure : ∀ {Θ : PCtx}, Θ ▷ₚ Srt.L
  | [] => .nil
  | .none :: _ => .none PKey.impure
  | .one _ _ :: _ => .one PKey.impure
  | .both _ :: _ => .both PKey.impure

/-- Single-endpoint lookup used by channel variables. A bare channel occurrence consumes exactly one
endpoint; terms that use both endpoints of a self-dual channel obtain a `both` context by merging two
subterms, each typed from a `one` endpoint. -/
inductive PJust : PCtx → Nat → Bool → Term → Prop where
  | zero {Θ r A} :
    PEmpty Θ →
    PJust (.one r A :: Θ) 0 r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)
  | none {Θ x r A} :
    PJust Θ x r A →
    PJust (.none :: Θ) (x + 1) r (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)

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

/-! ## Derived process-merge lemmas. -/

/-- An empty process context self-merges. -/
lemma PEmpty.merge_self {Θ} (emp : PEmpty Θ) : PMerge Θ Θ Θ := by
  induction emp with
  | nil => exact .nil
  | none _ ih => exact .none ih

/-- Merging empty process contexts yields an empty process context. -/
lemma PMerge.empty_image {Θ1 Θ2 Θ} (mrg : PMerge Θ1 Θ2 Θ) : PEmpty Θ1 → PEmpty Θ2 → PEmpty Θ := by
  induction mrg with
  | nil => intro _ _; exact .nil
  | none _ ih => intro emp1 emp2; cases emp1 with | none e1 => cases emp2 with | none e2 => exact .none (ih e1 e2)
  | oneL _ _ => intro emp1 _; cases emp1
  | oneR _ _ => intro _ emp2; cases emp2
  | bothL _ _ => intro emp1 _; cases emp1
  | bothR _ _ => intro _ emp2; cases emp2
  | split _ _ => intro emp1 _; cases emp1

/-- Process-context merge is functional in its result. -/
lemma PMerge.inj {Θ1 Θ2 Θx Θy} (mrg1 : PMerge Θ1 Θ2 Θx) (mrg2 : PMerge Θ1 Θ2 Θy) : Θx = Θy := by
  induction mrg1 generalizing Θy with
  | nil => cases mrg2; rfl
  | none _ ih => cases mrg2 with | none m2 => rw [ih m2]
  | oneL _ ih => cases mrg2 with | oneL m2 => rw [ih m2]
  | oneR _ ih => cases mrg2 with | oneR m2 => rw [ih m2]
  | bothL _ ih => cases mrg2 with | bothL m2 => rw [ih m2]
  | bothR _ ih => cases mrg2 with | bothR m2 => rw [ih m2]
  | split _ ih => cases mrg2 with | split m2 => rw [ih m2]

/-- Merge preserves process-context keys. -/
lemma PMerge.key_image {Θ1 Θ2 Θ s} (mrg : PMerge Θ1 Θ2 Θ) (k1 : Θ1 ▷ₚ s) (k2 : Θ2 ▷ₚ s) : Θ ▷ₚ s := by
  induction mrg generalizing s with
  | nil => exact k1
  | none _ ih => cases k1 with | none k1' => cases k2 with | none k2' => exact .none (ih k1' k2')
  | oneL _ ih => cases k1 with | one k1' => cases k2 with | none k2' => exact .one (ih k1' k2')
  | oneR _ ih => cases k1 with | none k1' => cases k2 with | one k2' => exact .one (ih k1' k2')
  | bothL _ ih => cases k1 with | both k1' => cases k2 with | none k2' => exact .both (ih k1' k2')
  | bothR _ ih => cases k1 with | none k1' => cases k2 with | both k2' => exact .both (ih k1' k2')
  | split _ ih => cases k1 with | one k1' => cases k2 with | one k2' => exact .both (ih k1' k2')

/-- A pure left component makes the merge an identity on the right. -/
lemma PMerge.pureL {Θ1 Θ2 Θ} (mrg : PMerge Θ1 Θ2 Θ) : Θ1 ▷ₚ Srt.U → Θ = Θ2 := by
  induction mrg with
  | nil => intro _; rfl
  | none _ ih => intro k; cases k with | none k' => rw [ih k']
  | oneL _ _ => intro k; cases k
  | oneR _ ih => intro k; cases k with | none k' => rw [ih k']
  | bothL _ _ => intro k; cases k
  | bothR _ ih => intro k; cases k with | none k' => rw [ih k']
  | split _ _ => intro k; cases k

/-- A pure right component makes the merge an identity on the left. -/
lemma PMerge.pureR {Θ1 Θ2 Θ} (mrg : PMerge Θ1 Θ2 Θ) : Θ2 ▷ₚ Srt.U → Θ = Θ1 := by
  induction mrg with
  | nil => intro _; rfl
  | none _ ih => intro k; cases k with | none k' => rw [ih k']
  | oneL _ ih => intro k; cases k with | none k' => rw [ih k']
  | oneR _ _ => intro k; cases k
  | bothL _ ih => intro k; cases k with | none k' => rw [ih k']
  | bothR _ _ => intro k; cases k
  | split _ _ => intro k; cases k

/-- A pure merge result splits into pure components. -/
lemma PMerge.pure_split {Θ1 Θ2 Θ} (mrg : PMerge Θ1 Θ2 Θ) : Θ ▷ₚ Srt.U → Θ1 ▷ₚ Srt.U ∧ Θ2 ▷ₚ Srt.U := by
  induction mrg with
  | nil => intro _; exact ⟨.nil, .nil⟩
  | none _ ih =>
    intro k
    cases k with
    | none k' =>
      obtain ⟨k1, k2⟩ := ih k'
      exact ⟨.none k1, .none k2⟩
  | oneL _ _ => intro k; cases k
  | oneR _ _ => intro k; cases k
  | bothL _ _ => intro k; cases k
  | bothR _ _ => intro k; cases k
  | split _ _ => intro k; cases k

/-- Distributivity of process-context merge over two nested merges. -/
lemma PMerge.distr {Γ1 Γ2 Γ Δ11 Δ12 Δ21 Δ22}
    (mrg0 : PMerge Γ1 Γ2 Γ) (mrg1 : PMerge Δ11 Δ12 Γ1) (mrg2 : PMerge Δ21 Δ22 Γ2) :
    ∃ Δ1 Δ2, PMerge Δ1 Δ2 Γ ∧ PMerge Δ11 Δ21 Δ1 ∧ PMerge Δ12 Δ22 Δ2 := by
  obtain ⟨Δ4, mrg3, mrg4⟩ := mrg0.splitL mrg1
  obtain ⟨Δ5, mrg5, mrg6⟩ := mrg3.sym.splitL mrg2
  obtain ⟨Δ6, mrg7, mrg8⟩ := mrg4.splitL mrg6.sym
  exact ⟨Δ5, Δ6, mrg8.sym, mrg5.sym, mrg7.sym⟩

/-- A single endpoint lookup exposes an empty splitter. -/
lemma PJust.empty {Θ x r A} (js : PJust Θ x r A) : ∃ Θ0, PEmpty Θ0 ∧ PMerge Θ0 Θ Θ := by
  induction js with
  | zero emp =>
    exact ⟨.none :: _, .none emp, .oneR (emp.merge_self)⟩
  | none _ ih =>
    obtain ⟨Θ0, e, mrg⟩ := ih
    exact ⟨.none :: Θ0, .none e, .none mrg⟩

/-- A single endpoint lookup forbids key `U`. -/
lemma PJust.not_pure {Θ x r A} (js : PJust Θ x r A) : ¬ Θ ▷ₚ Srt.U := by
  induction js with
  | zero _ => intro k; cases k
  | none _ ih => intro k; cases k with | none k' => exact ih k'

/-- A leaf-safe process context: every slot is `none` or `one`, never `both`. -/
inductive PCtxSingle : PCtx → Prop where
  | nil :
    PCtxSingle []
  | none {Θ} :
    PCtxSingle Θ →
    PCtxSingle (.none :: Θ)
  | one {Θ r A} :
    PCtxSingle Θ →
    PCtxSingle (.one r A :: Θ)

/-- Splitting a leaf-safe context produces leaf-safe subcontexts. -/
lemma PCtxSingle.split {Θ1 Θ2 Θ} (rea : PCtxSingle Θ) (mrg : PMerge Θ1 Θ2 Θ) :
    PCtxSingle Θ1 ∧ PCtxSingle Θ2 := by
  induction mrg with
  | nil => exact ⟨.nil, .nil⟩
  | none _ ih =>
    cases rea with | none rea' =>
    obtain ⟨r1, r2⟩ := ih rea'
    exact ⟨.none r1, .none r2⟩
  | oneL _ ih =>
    cases rea with | one rea' =>
    obtain ⟨r1, r2⟩ := ih rea'
    exact ⟨.one r1, .none r2⟩
  | oneR _ ih =>
    cases rea with | one rea' =>
    obtain ⟨r1, r2⟩ := ih rea'
    exact ⟨.none r1, .one r2⟩
  | bothL _ _ => cases rea
  | bothR _ _ => cases rea
  | split _ _ => cases rea

/-- An all-`none` process context is leaf-safe. -/
lemma PEmpty.pctxSingle {Θ} (emp : PEmpty Θ) : PCtxSingle Θ := by
  induction emp with
  | nil => exact .nil
  | none _ ih => exact .none ih

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

/-- An all-`none` left component makes a process merge an identity on the right. -/
lemma PMerge.emptyL {Θ1 Θ2 Θ} (mrg : PMerge Θ1 Θ2 Θ) (emp : PEmpty Θ1) : Θ2 = Θ :=
  mrg.sym.emptyR emp

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

end TLLC.Dynamic
