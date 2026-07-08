import TLLC.Dynamic.SR
import TLLC.Process.CSubst
import TLLC.Spawning.Inversion

/-!
# Spawning-tree fidelity (Lemma 5.87)

Tree-level subject reduction: a valid spawning tree that takes a spawning-tree step reduces to a
valid spawning tree, literally. The report states the children of a node as a *set*; the Lean
`ChildrenTyped` judgment fixes the canonical increasing-label order, and the `Step` rules preserve
it (in-place updates and label-ordered insertion), so no quotient is needed: the constructed
canonical children lists coincide with the step results by `child_sorted_eq`.

The `Distinct` hypothesis is required by the explicit-payload cases: a payload's channel edges move
between a parent and a child endpoint context at their raw de Bruijn indices, which is only sound
when the indices used by distinct nodes do not collide.
-/

namespace TLLC.Spawning
open Autosubst Autosubst.Notation
open TLLC.Dynamic
open scoped TLLC.Static TLLC.Dynamic


/-! ## Process-context utilities -/

lemma PEmpty.replicate (k : Nat) : PEmpty (List.replicate k Slot.none) := by
  induction k with
  | zero => exact .nil
  | succ k ih => simpa [List.replicate_succ] using PEmpty.none ih

/-- Merge two merges component-wise along an append. -/
lemma PMerge.append {Θ1 Θ2 Θ Ξ1 Ξ2 Ξ : PCtx}
    (h1 : PMerge Θ1 Θ2 Θ) (h2 : PMerge Ξ1 Ξ2 Ξ) :
    PMerge (Θ1 ++ Ξ1) (Θ2 ++ Ξ2) (Θ ++ Ξ) := by
  induction h1 with
  | nil => simpa using h2
  | none _ ih => simpa using PMerge.none ih
  | oneL _ ih => simpa using PMerge.oneL ih
  | oneR _ ih => simpa using PMerge.oneR ih
  | bothL _ ih => simpa using PMerge.bothL ih
  | bothR _ ih => simpa using PMerge.bothR ih
  | split _ ih => simpa using PMerge.split ih

lemma PMerge.replicate_none (k : Nat) :
    PMerge (List.replicate k Slot.none) (List.replicate k Slot.none)
      (List.replicate k Slot.none) :=
  (PEmpty.replicate k).merge_self

/-- Pad all three components of a merge with trailing empty slots. -/
lemma PMerge.padR {Θ1 Θ2 Θ : PCtx} (k : Nat) (h : PMerge Θ1 Θ2 Θ) :
    PMerge (Θ1 ++ List.replicate k Slot.none) (Θ2 ++ List.replicate k Slot.none)
      (Θ ++ List.replicate k Slot.none) :=
  PMerge.append h (PMerge.replicate_none k)

lemma PMerge.length_left {Θ1 Θ2 Θ : PCtx} (h : PMerge Θ1 Θ2 Θ) : Θ1.length = Θ.length := by
  induction h <;> simp [*]

lemma PMerge.length_right {Θ1 Θ2 Θ : PCtx} (h : PMerge Θ1 Θ2 Θ) : Θ2.length = Θ.length := by
  induction h <;> simp [*]

lemma PCtxSingle.replicate (k : Nat) : PCtxSingle (List.replicate k Slot.none) :=
  (PEmpty.replicate k).pctxSingle

/-- Trailing empty padding of a `PJust` lookup. -/
lemma PJust.padR {Θ : PCtx} {x r A} (k : Nat) (h : PJust Θ x r A) :
    PJust (Θ ++ List.replicate k Slot.none) x r A := by
  induction h with
  | zero emp =>
      exact PJust.zero (by
        induction emp with
        | nil => simpa using PEmpty.replicate k
        | none _ ih => simpa using PEmpty.none ih)
  | none _ ih => simpa using PJust.none ih

/-- Trailing empty padding of a context is `PCtxEmptyRel`-related to the original. -/
lemma PCtxEmptyRel_padR (Θ : PCtx) (k : Nat) :
    TLLC.Process.PCtxEmptyRel Θ (Θ ++ List.replicate k Slot.none) := by
  induction Θ with
  | nil => exact .empty .nil (PEmpty.replicate k)
  | cons s Θ ih =>
      cases s with
      | none => exact .none ih
      | one r A => exact .one ih
      | both A => exact .both ih

/-- Trailing empty padding preserves term typing. -/
lemma Typed.padR {Θ : PCtx} {m A} (k : Nat)
    (ty : Θ ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ m : A) :
    (Θ ++ List.replicate k Slot.none) ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ m : A :=
  TLLC.Process.Dynamic.Typed.pctxEmptyRel ty (PCtxEmptyRel_padR Θ k)

lemma CvarPos.append_false {Θ Ξ : PCtx} {i} (h : CvarPos Θ i false) (emp : PEmpty Ξ) :
    CvarPos (Θ ++ Ξ) i false := by
  induction Θ generalizing i with
  | nil => exact emp.pos_false
  | cons s Θ ih =>
      cases h with
      | none => exact .none
      | cons h' => exact .cons (ih h')

/-- A live channel of a padded context is live in the unpadded context. -/
lemma CvarPos.of_append_true {Θ Ξ : PCtx} {i} (emp : PEmpty Ξ)
    (h : CvarPos (Θ ++ Ξ) i true) : CvarPos Θ i true := by
  induction Θ generalizing i with
  | nil => exact absurd h emp.pos_true
  | cons s Θ ih =>
      cases h with
      | one => exact .one
      | cons h' => exact .cons (ih h')

lemma CvarPos.append_true {Θ Ξ : PCtx} {i} (h : CvarPos Θ i true) :
    CvarPos (Θ ++ Ξ) i true := by
  induction Θ generalizing i with
  | nil => cases h
  | cons s Θ ih =>
      cases h with
      | one => exact .one
      | cons h' => exact .cons (ih h')

/-- Liveness propagates from the left component of a leaf-safe merge to the result. -/
lemma CvarPos.merge_true_left {Θ1 Θ2 Θ : PCtx} {i} (single : PCtxSingle Θ)
    (mrg : PMerge Θ1 Θ2 Θ) (h : CvarPos Θ1 i true) : CvarPos Θ i true := by
  induction mrg generalizing i with
  | nil => cases h
  | none _ ih =>
      cases single with
      | none single' => cases h with | cons h' => exact .cons (ih single' h')
  | oneL _ ih =>
      cases single with
      | one single' =>
          cases h with
          | one => exact .one
          | cons h' => exact .cons (ih single' h')
  | oneR _ ih =>
      cases single with
      | one single' => cases h with | cons h' => exact .cons (ih single' h')
  | bothL _ _ => cases single
  | bothR _ _ => cases single
  | split _ _ => cases single

lemma CvarPos.merge_true_right {Θ1 Θ2 Θ : PCtx} {i} (single : PCtxSingle Θ)
    (mrg : PMerge Θ1 Θ2 Θ) (h : CvarPos Θ2 i true) : CvarPos Θ i true :=
  CvarPos.merge_true_left single mrg.sym h

/-- In a leaf-safe merge, the two components cannot both hold the endpoint at `i`. -/
lemma PCtxSingle.merge_true_excl {Θ1 Θ2 Θ : PCtx} {i} (single : PCtxSingle Θ)
    (mrg : PMerge Θ1 Θ2 Θ) (h1 : CvarPos Θ1 i true) (h2 : CvarPos Θ2 i true) : False := by
  induction mrg generalizing i with
  | nil => cases h1
  | none _ ih =>
      cases single with
      | none single' =>
          cases h1 with | cons h1' =>
          cases h2 with | cons h2' =>
          exact ih single' h1' h2'
  | oneL _ ih =>
      cases single with
      | one single' =>
          cases h2 with | cons h2' =>
          cases h1 with | cons h1' =>
          exact ih single' h1' h2'
  | oneR _ ih =>
      cases single with
      | one single' =>
          cases h1 with | cons h1' =>
          cases h2 with | cons h2' =>
          exact ih single' h1' h2'
  | bothL _ _ => cases single
  | bothR _ _ => cases single
  | split _ _ => cases single

/-- Two disjoint leaf-safe contexts of equal length merge. -/
lemma pmerge_single_disjoint : ∀ {Θ1 Θ2 : PCtx},
    Θ1.length = Θ2.length → PCtxSingle Θ1 → PCtxSingle Θ2 →
    (∀ i, CvarPos Θ1 i true → CvarPos Θ2 i true → False) →
    ∃ Θ, PMerge Θ1 Θ2 Θ ∧ PCtxSingle Θ := by
  intro Θ1
  induction Θ1 with
  | nil =>
      intro Θ2 len _ _ _
      cases Θ2 with
      | nil => exact ⟨[], .nil, .nil⟩
      | cons _ _ => simp at len
  | cons s1 Θ1 ih =>
      intro Θ2 len s1s s2s disj
      cases Θ2 with
      | nil => simp at len
      | cons s2 Θ2 =>
          have lenT : Θ1.length = Θ2.length := by simpa using len
          have disjT : ∀ i, CvarPos Θ1 i true → CvarPos Θ2 i true → False := by
            intro i h1 h2
            exact disj (i + 1) (.cons h1) (.cons h2)
          cases s1s with
          | none s1s' =>
              cases s2s with
              | none s2s' =>
                  obtain ⟨Θ, mrg, single⟩ := ih lenT s1s' s2s' disjT
                  exact ⟨_, .none mrg, .none single⟩
              | one s2s' =>
                  obtain ⟨Θ, mrg, single⟩ := ih lenT s1s' s2s' disjT
                  exact ⟨_, .oneR mrg, .one single⟩
          | one s1s' =>
              cases s2s with
              | none s2s' =>
                  obtain ⟨Θ, mrg, single⟩ := ih lenT s1s' s2s' disjT
                  exact ⟨_, .oneL mrg, .one single⟩
              | one s2s' =>
                  exact absurd (disj 0 .one .one) not_false

/-! ## Shift-list utilities -/

@[simp] lemma shiftChildren_nil : shiftChildren [] = [] := rfl

@[simp] lemma shiftChildren_cons (x : Nat) (child : Tree) (children : List (Chan × Tree)) :
    shiftChildren ((Chan.var_Chan x, child) :: children) =
      (Chan.var_Chan (x + 1), child) :: shiftChildren children := rfl

lemma shiftChildren_append (l r : List (Chan × Tree)) :
    shiftChildren (l ++ r) = shiftChildren l ++ shiftChildren r := by
  induction l with
  | nil => rfl
  | cons e l ih =>
      rcases e with ⟨c, t⟩
      cases c with
      | var_Chan x => simp [ih]

lemma shiftChildren_perm {l l' : List (Chan × Tree)} (h : List.Perm l l') :
    List.Perm (shiftChildren l) (shiftChildren l') := by
  induction h with
  | nil => exact .refl _
  | cons e _ ih =>
      rcases e with ⟨c, t⟩
      cases c with
      | var_Chan x =>
          simp only [shiftChildren_cons]
          exact List.Perm.cons _ ih
  | swap e1 e2 l =>
      rcases e1 with ⟨c1, t1⟩
      rcases e2 with ⟨c2, t2⟩
      cases c1 with
      | var_Chan x1 =>
          cases c2 with
          | var_Chan x2 =>
              simp only [shiftChildren_cons]
              exact List.Perm.swap _ _ _
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- Un-shift a decomposition of a shifted children list. -/
lemma shiftChildren_eq_append_cons {ch l r : List (Chan × Tree)} {c : Chan} {t : Tree}
    (h : shiftChildren ch = l ++ (c, t) :: r) :
    ∃ x l₀ r₀, c = Chan.var_Chan (x + 1) ∧ ch = l₀ ++ (Chan.var_Chan x, t) :: r₀ ∧
      l = shiftChildren l₀ ∧ r = shiftChildren r₀ := by
  induction ch generalizing l with
  | nil =>
      rw [shiftChildren_nil] at h
      exact absurd h (List.ne_nil_of_length_pos (by simp)).symm
  | cons e ch ih =>
      rcases e with ⟨ec, et⟩
      cases ec with
      | var_Chan ex =>
          rw [shiftChildren_cons] at h
          cases l with
          | nil =>
              simp only [List.nil_append, List.cons.injEq] at h
              obtain ⟨he, hr⟩ := h
              obtain ⟨hc, ht⟩ := Prod.mk.injEq .. ▸ he
              exact ⟨ex, [], ch, hc.symm, by rw [ht]; rfl, rfl, hr.symm⟩
          | cons e' l₀ =>
              simp only [List.cons_append, List.cons.injEq] at h
              obtain ⟨he, hrest⟩ := h
              obtain ⟨x, l₀', r₀', hc, hch, hl, hr⟩ := ih hrest
              exact ⟨x, (Chan.var_Chan ex, et) :: l₀', r₀', hc, by rw [hch]; rfl,
                by rw [shiftChildren_cons, hl, he], hr⟩

/-! ## Children-judgment surgery -/

/-- An all-`none` context types the empty children list. -/
lemma ChildrenTyped.of_empty {Θ : PCtx} (emp : PEmpty Θ) : ChildrenTyped Θ [] := by
  induction emp with
  | nil => exact .nil
  | none _ ih => exact ChildrenTyped.none (children := []) ih

/-- Remove the child edge selected by a `PJust` endpoint from a children typing. The child is
typed at a protocol convertible to the `PJust`-exposed one. -/
lemma ChildrenTyped.remove {Θ1 : PCtx} {x : Nat} {r' : Bool} {B : Term}
    (just : PJust Θ1 x r' B) :
    ∀ {Θ2 Θ : PCtx} {ms l r : List (Chan × Tree)} {c : Chan} {child : Tree},
      PMerge Θ1 Θ2 Θ →
      ChildrenTyped Θ ms →
      ms = l ++ (c, child) :: r →
      chanIndex c = x →
      ∃ C, TypedAt (!r') C child ∧ (C ≃ B) ∧ ChildrenTyped Θ2 (l ++ r) := by
  induction just with
  | @zero Θe r' A emp =>
      intro Θ2 Θ ms l r c child mrg ty hms hc
      cases c with
      | var_Chan cx =>
      simp only [chanIndex] at hc
      subst hc
      cases mrg with
      | @oneL _ Θ2t _ _ _ mrg' =>
          cases ty with
          | @one Θt _ _ hd chT tyChild tyTail =>
              cases l with
              | nil =>
                  simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at hms
                  obtain ⟨⟨_, ht⟩, hr⟩ := hms
                  subst ht
                  rw [← mrg'.emptyL emp] at tyTail
                  refine ⟨_, tyChild, ARS.Conv.refl, ?_⟩
                  rw [List.nil_append, ← hr]
                  exact ChildrenTyped.none tyTail
              | cons e l₀ =>
                  exfalso
                  simp only [List.cons_append, List.cons.injEq] at hms
                  obtain ⟨_, hrest⟩ := hms
                  have hmem : (Chan.var_Chan 0, child) ∈ shiftChildren chT := by
                    rw [hrest]; simp
                  exact zero_pair_notin_shift child hmem
      | split _ => cases ty
  | @none Θ1t y r' B' just' ih =>
      intro Θ2 Θ ms l r c child mrg ty hms hc
      cases c with
      | var_Chan cx =>
      simp only [chanIndex] at hc
      subst hc
      cases mrg with
      | @none _ Θ2t _ mrg' =>
          cases ty with
          | @none Θt chT tyTail =>
              obtain ⟨x0, l₀, r₀, hcEq, hch, hl, hr⟩ := shiftChildren_eq_append_cons hms
              have hx0 : y = x0 := by injection hcEq with h; omega
              subst hx0
              obtain ⟨C, tyC, convC, tyRest⟩ := ih mrg' tyTail hch rfl
              refine ⟨C, tyC, ?_, ?_⟩
              · exact ARS.conv_trans convC
                  (ARS.conv_sym (Static.cren_conv0 .refl ((· + 1) : Nat → Nat)))
              · rw [hl, hr, ← shiftChildren_append]
                exact ChildrenTyped.none tyRest
      | @oneR _ Θ2t _ _ _ mrg' =>
          cases ty with
          | @one Θt _ _ hd chT tyChild tyTail =>
              cases l with
              | nil =>
                  exfalso
                  simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at hms
                  obtain ⟨⟨hcx, _⟩, _⟩ := hms
                  exact absurd hcx (by intro h; injection h with h'; omega)
              | cons e l₀ =>
                  simp only [List.cons_append, List.cons.injEq] at hms
                  obtain ⟨he, hrest⟩ := hms
                  obtain ⟨x0, l₀', r₀', hcEq, hch, hl, hr⟩ := shiftChildren_eq_append_cons hrest
                  have hx0 : y = x0 := by injection hcEq with h; omega
                  subst hx0
                  obtain ⟨C, tyC, convC, tyRest⟩ := ih mrg' tyTail hch rfl
                  refine ⟨C, tyC, ?_, ?_⟩
                  · exact ARS.conv_trans convC
                      (ARS.conv_sym (Static.cren_conv0 .refl ((· + 1) : Nat → Nat)))
                  · rw [← he, hl, hr]
                    simp only [List.cons_append]
                    rw [← shiftChildren_append]
                    exact ChildrenTyped.one tyChild tyRest
      | bothR _ => cases ty

lemma shiftChildren_perm_append {ms ms1 ms2 : List (Chan × Tree)}
    (h : List.Perm ms (ms1 ++ ms2)) :
    List.Perm (shiftChildren ms) (shiftChildren ms1 ++ shiftChildren ms2) := by
  have h' := shiftChildren_perm h
  rwa [shiftChildren_append] at h'

/-- `ChildrenTyped.remove` for a node's children judgment: the reserved parent endpoint is kept. -/
lemma ChildrenTypedAt.remove {Θ1 : PCtx} {x : Nat} {r' : Bool} {B : Term}
    (just : PJust Θ1 x r' B) :
    ∀ {Θ2 Θ : PCtx} {y : Nat} {ry : Bool} {Ay : Term}
      {ms l r : List (Chan × Tree)} {c : Chan} {child : Tree},
      PMerge Θ1 Θ2 Θ →
      ChildrenTypedAt Θ y ry Ay ms →
      ms = l ++ (c, child) :: r →
      chanIndex c = x →
      ∃ C, TypedAt (!r') C child ∧ (C ≃ B) ∧ ChildrenTypedAt Θ2 y ry Ay (l ++ r) := by
  induction just with
  | @zero Θe r'0 A emp =>
      intro Θ2 Θ y ry Ay ms l r c child mrg ty hms hc
      cases c with
      | var_Chan cx =>
      simp only [chanIndex] at hc
      subst hc
      cases mrg with
      | @oneL _ Θ2t _ _ _ mrg' =>
          cases ty with
          | @parent Θt _ _ chT tyPlain =>
              exfalso
              have hmem : (Chan.var_Chan 0, child) ∈ shiftChildren chT := by
                rw [hms]; simp
              exact zero_pair_notin_shift child hmem
          | @one Θt y' ry' Ay' _ _ hd chT tyChild tyTail =>
              cases l with
              | nil =>
                  simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at hms
                  obtain ⟨⟨_, ht⟩, hr⟩ := hms
                  subst ht
                  rw [← mrg'.emptyL emp] at tyTail
                  refine ⟨_, tyChild, ARS.Conv.refl, ?_⟩
                  rw [List.nil_append, ← hr]
                  exact ChildrenTypedAt.none tyTail
              | cons e l₀ =>
                  exfalso
                  simp only [List.cons_append, List.cons.injEq] at hms
                  obtain ⟨_, hrest⟩ := hms
                  have hmem : (Chan.var_Chan 0, child) ∈ shiftChildren chT := by
                    rw [hrest]; simp
                  exact zero_pair_notin_shift child hmem
      | split _ => cases ty
  | @none Θ1t y0 r'0 B' just' ih =>
      intro Θ2 Θ y ry Ay ms l r c child mrg ty hms hc
      cases c with
      | var_Chan cx =>
      simp only [chanIndex] at hc
      subst hc
      cases mrg with
      | @none _ Θ2t _ mrg' =>
          cases ty with
          | @none Θt y' ry' Ay' chT tyTail =>
              obtain ⟨x0, l₀, r₀, hcEq, hch, hl, hr⟩ := shiftChildren_eq_append_cons hms
              have hx0 : y0 = x0 := by injection hcEq with h; omega
              subst hx0
              obtain ⟨C, tyC, convC, tyRest⟩ := ih mrg' tyTail hch rfl
              refine ⟨C, tyC, ?_, ?_⟩
              · exact ARS.conv_trans convC
                  (ARS.conv_sym (Static.cren_conv0 .refl ((· + 1) : Nat → Nat)))
              · rw [hl, hr, ← shiftChildren_append]
                exact ChildrenTypedAt.none tyRest
      | @oneR _ Θ2t _ _ _ mrg' =>
          cases ty with
          | @parent Θt _ _ chT tyPlain =>
              obtain ⟨x0, l₀, r₀, hcEq, hch, hl, hr⟩ := shiftChildren_eq_append_cons hms
              have hx0 : y0 = x0 := by injection hcEq with h; omega
              subst hx0
              obtain ⟨C, tyC, convC, tyRest⟩ :=
                ChildrenTyped.remove just' mrg' tyPlain hch rfl
              refine ⟨C, tyC, ?_, ?_⟩
              · exact ARS.conv_trans convC
                  (ARS.conv_sym (Static.cren_conv0 .refl ((· + 1) : Nat → Nat)))
              · rw [hl, hr, ← shiftChildren_append]
                exact ChildrenTypedAt.parent tyRest
          | @one Θt y' ry' Ay' _ _ hd chT tyChild tyTail =>
              cases l with
              | nil =>
                  exfalso
                  simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at hms
                  obtain ⟨⟨hcx, _⟩, _⟩ := hms
                  exact absurd hcx (by intro h; injection h with h'; omega)
              | cons e l₀ =>
                  simp only [List.cons_append, List.cons.injEq] at hms
                  obtain ⟨he, hrest⟩ := hms
                  obtain ⟨x0, l₀', r₀', hcEq, hch, hl, hr⟩ :=
                    shiftChildren_eq_append_cons hrest
                  have hx0 : y0 = x0 := by injection hcEq with h; omega
                  subst hx0
                  obtain ⟨C, tyC, convC, tyRest⟩ := ih mrg' tyTail hch rfl
                  refine ⟨C, tyC, ?_, ?_⟩
                  · exact ARS.conv_trans convC
                      (ARS.conv_sym (Static.cren_conv0 .refl ((· + 1) : Nat → Nat)))
                  · rw [← he, hl, hr]
                    simp only [List.cons_append]
                    rw [← shiftChildren_append]
                    exact ChildrenTypedAt.one tyChild tyRest
      | bothR _ => cases ty

/-- Split a children typing along a leaf-safe merge of its endpoint context. -/
lemma ChildrenTyped.split {Θ1 Θ2 Θ : PCtx} (mrg : PMerge Θ1 Θ2 Θ) :
    ∀ (_ : PCtxSingle Θ) {ms}, ChildrenTyped Θ ms →
    ∃ ms1 ms2, ChildrenTyped Θ1 ms1 ∧ ChildrenTyped Θ2 ms2 ∧
      List.Perm ms (ms1 ++ ms2) := by
  induction mrg with
  | nil =>
      intro _ ms ty
      cases ty
      exact ⟨[], [], .nil, .nil, .refl _⟩
  | none _ ih =>
      intro single ms ty
      cases single with
      | none single' =>
          cases ty with
          | @none Θt chT tyTail =>
              obtain ⟨ms1, ms2, ty1, ty2, hperm⟩ := ih single' tyTail
              exact ⟨shiftChildren ms1, shiftChildren ms2, .none ty1, .none ty2,
                shiftChildren_perm_append hperm⟩
  | oneL _ ih =>
      intro single ms ty
      cases single with
      | one single' =>
          cases ty with
          | @one Θt _ _ hd chT tyChild tyTail =>
              obtain ⟨ms1, ms2, ty1, ty2, hperm⟩ := ih single' tyTail
              refine ⟨(Chan.var_Chan 0, hd) :: shiftChildren ms1, shiftChildren ms2,
                .one tyChild ty1, .none ty2, ?_⟩
              simp only [List.cons_append]
              exact List.Perm.cons _ (shiftChildren_perm_append hperm)
  | oneR _ ih =>
      intro single ms ty
      cases single with
      | one single' =>
          cases ty with
          | @one Θt _ _ hd chT tyChild tyTail =>
              obtain ⟨ms1, ms2, ty1, ty2, hperm⟩ := ih single' tyTail
              refine ⟨shiftChildren ms1, (Chan.var_Chan 0, hd) :: shiftChildren ms2,
                .none ty1, .one tyChild ty2, ?_⟩
              exact List.Perm.trans
                (List.Perm.cons _ (shiftChildren_perm_append hperm))
                List.perm_middle.symm
  | bothL _ _ => intro single; cases single
  | bothR _ _ => intro single; cases single
  | split _ _ => intro single; cases single

/-- Split a node's children typing along a leaf-safe merge, keeping the reserved parent endpoint
on the right component. -/
lemma ChildrenTypedAt.split_right {Θ1 Θ2 Θ : PCtx} (mrg : PMerge Θ1 Θ2 Θ) :
    ∀ (_ : PCtxSingle Θ) {y ry Ay ms},
      ChildrenTypedAt Θ y ry Ay ms →
      CvarPos Θ1 y false →
      ∃ ms1 ms2, ChildrenTyped Θ1 ms1 ∧ ChildrenTypedAt Θ2 y ry Ay ms2 ∧
        List.Perm ms (ms1 ++ ms2) := by
  induction mrg with
  | nil =>
      intro _ y ry Ay ms ty _
      cases ty
  | none _ ih =>
      intro single y ry Ay ms ty pos
      cases single with
      | none single' =>
          cases ty with
          | @none Θt y' ry' Ay' chT tyTail =>
              cases pos with
              | cons pos' =>
                  obtain ⟨ms1, ms2, ty1, ty2, hperm⟩ := ih single' tyTail pos'
                  exact ⟨shiftChildren ms1, shiftChildren ms2, .none ty1, .none ty2,
                    shiftChildren_perm_append hperm⟩
  | oneL _ ih =>
      intro single y ry Ay ms ty pos
      cases single with
      | one single' =>
          cases ty with
          | parent _ => cases pos
          | @one Θt y' ry' Ay' _ _ hd chT tyChild tyTail =>
              cases pos with
              | cons pos' =>
                  obtain ⟨ms1, ms2, ty1, ty2, hperm⟩ := ih single' tyTail pos'
                  refine ⟨(Chan.var_Chan 0, hd) :: shiftChildren ms1, shiftChildren ms2,
                    .one tyChild ty1, .none ty2, ?_⟩
                  simp only [List.cons_append]
                  exact List.Perm.cons _ (shiftChildren_perm_append hperm)
  | @oneR _ _ _ r0 A0 mrg' ih =>
      intro single y ry Ay ms ty pos
      cases single with
      | one single' =>
          cases ty with
          | @parent Θt _ _ chT tyPlain =>
              obtain ⟨ms1, ms2, ty1, ty2, hperm⟩ :=
                ChildrenTyped.split mrg' single' tyPlain
              exact ⟨shiftChildren ms1, shiftChildren ms2, .none ty1, .parent ty2,
                shiftChildren_perm_append hperm⟩
          | @one Θt y' ry' Ay' _ _ hd chT tyChild tyTail =>
              cases pos with
              | cons pos' =>
                  obtain ⟨ms1, ms2, ty1, ty2, hperm⟩ := ih single' tyTail pos'
                  refine ⟨shiftChildren ms1, (Chan.var_Chan 0, hd) :: shiftChildren ms2,
                    .none ty1, .one tyChild ty2, ?_⟩
                  exact List.Perm.trans
                    (List.Perm.cons _ (shiftChildren_perm_append hperm))
                    List.perm_middle.symm
  | bothL _ _ => intro single; cases single
  | bothR _ _ => intro single; cases single
  | split _ _ => intro single; cases single

/-- Recombine two children typings along a leaf-safe merge. -/
lemma ChildrenTyped.merge {Θ1 Θ2 Θ : PCtx} (mrg : PMerge Θ1 Θ2 Θ) :
    ∀ (_ : PCtxSingle Θ) {ms1 ms2},
      ChildrenTyped Θ1 ms1 → ChildrenTyped Θ2 ms2 →
      ∃ ms, ChildrenTyped Θ ms ∧ List.Perm ms (ms1 ++ ms2) := by
  induction mrg with
  | nil =>
      intro _ ms1 ms2 ty1 ty2
      cases ty1
      cases ty2
      exact ⟨[], .nil, .refl _⟩
  | none _ ih =>
      intro single ms1 ms2 ty1 ty2
      cases single with
      | none single' =>
          cases ty1 with
          | none ty1' =>
              cases ty2 with
              | none ty2' =>
                  obtain ⟨ms, ty, hperm⟩ := ih single' ty1' ty2'
                  exact ⟨shiftChildren ms, .none ty, shiftChildren_perm_append hperm⟩
  | oneL _ ih =>
      intro single ms1 ms2 ty1 ty2
      cases single with
      | one single' =>
          cases ty1 with
          | one tyChild ty1' =>
              cases ty2 with
              | none ty2' =>
                  obtain ⟨ms, ty, hperm⟩ := ih single' ty1' ty2'
                  refine ⟨(Chan.var_Chan 0, _) :: shiftChildren ms, .one tyChild ty, ?_⟩
                  simp only [List.cons_append]
                  exact List.Perm.cons _ (shiftChildren_perm_append hperm)
  | oneR _ ih =>
      intro single ms1 ms2 ty1 ty2
      cases single with
      | one single' =>
          cases ty1 with
          | none ty1' =>
              cases ty2 with
              | one tyChild ty2' =>
                  obtain ⟨ms, ty, hperm⟩ := ih single' ty1' ty2'
                  refine ⟨(Chan.var_Chan 0, _) :: shiftChildren ms, .one tyChild ty, ?_⟩
                  exact List.Perm.trans
                    (List.Perm.cons _ (shiftChildren_perm_append hperm))
                    List.perm_middle.symm
  | bothL _ _ => intro single; cases single
  | bothR _ _ => intro single; cases single
  | split _ _ => intro single; cases single

/-- Recombine a node's children typing with a plain children typing along a leaf-safe merge. -/
lemma ChildrenTypedAt.merge {Θ1 Θ2 Θ : PCtx} (mrg : PMerge Θ1 Θ2 Θ) :
    ∀ (_ : PCtxSingle Θ) {y ry Ay ms1 ms2},
      ChildrenTypedAt Θ1 y ry Ay ms1 → ChildrenTyped Θ2 ms2 →
      ∃ ms, ChildrenTypedAt Θ y ry Ay ms ∧ List.Perm ms (ms1 ++ ms2) := by
  induction mrg with
  | nil =>
      intro _ y ry Ay ms1 ms2 ty1 _
      cases ty1
  | none _ ih =>
      intro single y ry Ay ms1 ms2 ty1 ty2
      cases single with
      | none single' =>
          cases ty1 with
          | none ty1' =>
              cases ty2 with
              | none ty2' =>
                  obtain ⟨ms, ty, hperm⟩ := ih single' ty1' ty2'
                  exact ⟨shiftChildren ms, .none ty, shiftChildren_perm_append hperm⟩
  | oneL _ ih =>
      intro single y ry Ay ms1 ms2 ty1 ty2
      cases single with
      | one single' =>
          cases ty1 with
          | parent ty1' =>
              cases ty2 with
              | none ty2' =>
                  obtain ⟨ms, ty, hperm⟩ := ChildrenTyped.merge ‹_› single' ty1' ty2'
                  exact ⟨shiftChildren ms, .parent ty, shiftChildren_perm_append hperm⟩
          | one tyChild ty1' =>
              cases ty2 with
              | none ty2' =>
                  obtain ⟨ms, ty, hperm⟩ := ih single' ty1' ty2'
                  refine ⟨(Chan.var_Chan 0, _) :: shiftChildren ms, .one tyChild ty, ?_⟩
                  simp only [List.cons_append]
                  exact List.Perm.cons _ (shiftChildren_perm_append hperm)
  | oneR _ ih =>
      intro single y ry Ay ms1 ms2 ty1 ty2
      cases single with
      | one single' =>
          cases ty1 with
          | none ty1' =>
              cases ty2 with
              | one tyChild ty2' =>
                  obtain ⟨ms, ty, hperm⟩ := ih single' ty1' ty2'
                  refine ⟨(Chan.var_Chan 0, _) :: shiftChildren ms, .one tyChild ty, ?_⟩
                  exact List.Perm.trans
                    (List.Perm.cons _ (shiftChildren_perm_append hperm))
                    List.perm_middle.symm
  | bothL _ _ => intro single; cases single
  | bothR _ _ => intro single; cases single
  | split _ _ => intro single; cases single

/-- Reserve a fresh endpoint as the parent slot of a plain children typing. -/
lemma ChildrenTypedAt.intro {Θ1 : PCtx} {x : Nat} {r : Bool} {B : Term}
    (just : PJust Θ1 x r B) :
    ∀ {Θ2 Θ : PCtx} {ms}, PMerge Θ1 Θ2 Θ → PCtxSingle Θ → ChildrenTyped Θ2 ms →
      ChildrenTypedAt Θ x r B ms := by
  induction just with
  | @zero Θe r0 A emp =>
      intro Θ2 Θ ms mrg single ty
      cases mrg with
      | @oneL _ Θ2t _ _ _ mrg' =>
          cases ty with
          | @none Θt chT tyTail =>
              rw [mrg'.emptyL emp] at tyTail
              exact ChildrenTypedAt.parent tyTail
      | split _ => cases single
  | @none Θ1t y r0 B' just' ih =>
      intro Θ2 Θ ms mrg single ty
      cases mrg with
      | @none _ Θ2t _ mrg' =>
          cases single with
          | none single' =>
              cases ty with
              | none tyTail => exact ChildrenTypedAt.none (ih mrg' single' tyTail)
      | @oneR _ Θ2t _ _ _ mrg' =>
          cases single with
          | one single' =>
              cases ty with
              | one tyChild tyTail =>
                  exact ChildrenTypedAt.one tyChild (ih mrg' single' tyTail)
      | bothR _ => cases single

/-- Replace the child at a fixed position by any tree typed at the same endpoint protocol,
threading an abstract relation `F` through the replacement. -/
lemma ChildrenTyped.replace_via {F : Tree → Tree → Prop} :
    ∀ {Θ : PCtx} {ms l r : List (Chan × Tree)} {c : Chan} {child : Tree},
      ChildrenTyped Θ ms →
      ms = l ++ (c, child) :: r →
      (∀ rc C, TypedAt rc C child → ∃ child', F child child' ∧ TypedAt rc C child') →
      ∃ child', F child child' ∧ ChildrenTyped Θ (l ++ (c, child') :: r) := by
  intro Θ
  induction Θ with
  | nil =>
      intro ms l r c child ty hms h
      cases ty
      exact absurd hms (List.ne_nil_of_length_pos (by simp)).symm
  | cons s Θt ih =>
      intro ms l r c child ty hms h
      cases ty with
      | @none _ chT tyTail =>
          obtain ⟨x0, l₀, r₀, hcEq, hch, hl, hr⟩ := shiftChildren_eq_append_cons hms
          obtain ⟨child', hF, tyNew⟩ := ih tyTail hch h
          refine ⟨child', hF, ?_⟩
          rw [hcEq, hl, hr]
          have := ChildrenTyped.none (Θ := Θt) tyNew
          rwa [shiftChildren_append, shiftChildren_cons] at this
      | @one _ _ _ hd chT tyChild tyTail =>
          cases l with
          | nil =>
              simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at hms
              obtain ⟨⟨hc0, ht⟩, hr⟩ := hms
              subst ht
              obtain ⟨child', hF, tyChild'⟩ := h _ _ tyChild
              refine ⟨child', hF, ?_⟩
              rw [List.nil_append, ← hc0, ← hr]
              exact ChildrenTyped.one tyChild' tyTail
          | cons e l₀ =>
              simp only [List.cons_append, List.cons.injEq] at hms
              obtain ⟨he, hrest⟩ := hms
              obtain ⟨x0, l₀', r₀', hcEq, hch, hl, hr⟩ := shiftChildren_eq_append_cons hrest
              obtain ⟨child', hF, tyNew⟩ := ih tyTail hch h
              refine ⟨child', hF, ?_⟩
              rw [← he, hcEq, hl, hr]
              simp only [List.cons_append]
              have := ChildrenTyped.one (r := ‹Bool›) tyChild tyNew
              rwa [shiftChildren_append, shiftChildren_cons] at this

/-- `ChildrenTyped.replace_via` for a node's children judgment. -/
lemma ChildrenTypedAt.replace_via {F : Tree → Tree → Prop} :
    ∀ {Θ : PCtx} {y : Nat} {ry : Bool} {Ay : Term}
      {ms l r : List (Chan × Tree)} {c : Chan} {child : Tree},
      ChildrenTypedAt Θ y ry Ay ms →
      ms = l ++ (c, child) :: r →
      (∀ rc C, TypedAt rc C child → ∃ child', F child child' ∧ TypedAt rc C child') →
      ∃ child', F child child' ∧ ChildrenTypedAt Θ y ry Ay (l ++ (c, child') :: r) := by
  intro Θ
  induction Θ with
  | nil =>
      intro y ry Ay ms l r c child ty hms h
      cases ty
  | cons s Θt ih =>
      intro y ry Ay ms l r c child ty hms h
      cases ty with
      | @parent _ ryP AP chT tyPlain =>
          obtain ⟨x0, l₀, r₀, hcEq, hch, hl, hr⟩ := shiftChildren_eq_append_cons hms
          obtain ⟨child', hF, tyNew⟩ := ChildrenTyped.replace_via tyPlain hch h
          refine ⟨child', hF, ?_⟩
          rw [hcEq, hl, hr]
          have := ChildrenTypedAt.parent (r := ry) (A := AP) tyNew
          rwa [shiftChildren_append, shiftChildren_cons] at this
      | @none _ _ _ _ chT tyTail =>
          obtain ⟨x0, l₀, r₀, hcEq, hch, hl, hr⟩ := shiftChildren_eq_append_cons hms
          obtain ⟨child', hF, tyNew⟩ := ih tyTail hch h
          refine ⟨child', hF, ?_⟩
          rw [hcEq, hl, hr]
          have := ChildrenTypedAt.none tyNew
          rwa [shiftChildren_append, shiftChildren_cons] at this
      | @one _ _ _ _ _ _ hd chT tyChild tyTail =>
          cases l with
          | nil =>
              simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at hms
              obtain ⟨⟨hc0, ht⟩, hr⟩ := hms
              subst ht
              obtain ⟨child', hF, tyChild'⟩ := h _ _ tyChild
              refine ⟨child', hF, ?_⟩
              rw [List.nil_append, ← hc0, ← hr]
              exact ChildrenTypedAt.one tyChild' tyTail
          | cons e l₀ =>
              simp only [List.cons_append, List.cons.injEq] at hms
              obtain ⟨he, hrest⟩ := hms
              obtain ⟨x0, l₀', r₀', hcEq, hch, hl, hr⟩ := shiftChildren_eq_append_cons hrest
              obtain ⟨child', hF, tyNew⟩ := ih tyTail hch h
              refine ⟨child', hF, ?_⟩
              rw [← he, hcEq, hl, hr]
              simp only [List.cons_append]
              have := ChildrenTypedAt.one tyChild tyNew
              rwa [shiftChildren_append, shiftChildren_cons] at this

/-! ## Subtree-list helpers -/

lemma SubtreesTyped.of_forall {qs : List Tree} (h : ∀ q, q ∈ qs → Typed q) :
    SubtreesTyped qs := by
  induction qs with
  | nil => exact .nil
  | cons q qs ih =>
      exact .cons (h q (by simp)) (ih (fun q' hq' => h q' (by simp [hq'])))

lemma SubtreesTyped.append : ∀ {qs qs' : List Tree},
    SubtreesTyped qs → SubtreesTyped qs' → SubtreesTyped (qs ++ qs') := by
  intro qs
  induction qs with
  | nil => intro qs' _ h2; simpa using h2
  | cons q qs ih =>
      intro qs' h1 h2
      cases h1 with
      | cons ty tyRest => exact .cons ty (ih tyRest h2)

lemma SubtreesTyped.replace_via {F : Tree → Tree → Prop} {l r : List Tree} {sub : Tree}
    (ty : SubtreesTyped (l ++ sub :: r))
    (h : Typed sub → ∃ sub', F sub sub' ∧ Typed sub') :
    ∃ sub', F sub sub' ∧ SubtreesTyped (l ++ sub' :: r) := by
  induction l with
  | nil =>
      cases ty with
      | cons tySub tyRest =>
          obtain ⟨sub', hF, tySub'⟩ := h tySub
          exact ⟨sub', hF, .cons tySub' tyRest⟩
  | cons q l ih =>
      cases ty with
      | cons tyQ tyRest =>
          obtain ⟨sub', hF, tyRest'⟩ := ih tyRest
          exact ⟨sub', hF, .cons tyQ tyRest'⟩

/-! ## Endpoint-slot transport -/

/-- Transport a `PHas` lookup to the merge component that does not hold `x`. -/
lemma PHas.merge_inv_right {Θ1 Θ2 Θ : PCtx} (mrg : PMerge Θ1 Θ2 Θ) :
    ∀ {x r A}, PHas Θ x r A → CvarPos Θ1 x false → PHas Θ2 x r A := by
  induction mrg with
  | nil => intro x r A has; cases has
  | none _ ih =>
      intro x r A has pos
      cases has with
      | succ has' => cases pos with | cons pos' => exact .succ (ih has' pos')
  | oneL _ ih =>
      intro x r A has pos
      cases has with
      | zero => cases pos
      | succ has' => cases pos with | cons pos' => exact .succ (ih has' pos')
  | oneR _ ih =>
      intro x r A has pos
      cases has with
      | zero => exact .zero
      | succ has' => cases pos with | cons pos' => exact .succ (ih has' pos')
  | bothL _ ih =>
      intro x r A has pos
      cases has with
      | succ has' => cases pos with | cons pos' => exact .succ (ih has' pos')
  | bothR _ ih =>
      intro x r A has pos
      cases has with
      | succ has' => cases pos with | cons pos' => exact .succ (ih has' pos')
  | split _ ih =>
      intro x r A has pos
      cases has with
      | succ has' => cases pos with | cons pos' => exact .succ (ih has' pos')

/-- A child-edge label of a node's children judgment never equals the reserved parent slot. -/
lemma ChildrenTypedAt.label_ne_parent : ∀ {Θ : PCtx} {y : Nat} {ry : Bool} {Ay : Term}
    {ms : List (Chan × Tree)} {c : Chan},
    ChildrenTypedAt Θ y ry Ay ms → c ∈ childLabels ms → chanIndex c ≠ y := by
  intro Θ
  induction Θ with
  | nil =>
      intro y ry Ay ms c ty _
      cases ty
  | cons s Θt ih =>
      intro y ry Ay ms c ty mem
      cases ty with
      | parent tyPlain =>
          cases c with
          | var_Chan x =>
              cases x with
              | zero => exact absurd mem zero_notin_shiftLabels
              | succ x => simp [chanIndex]
      | none tyTail =>
          cases c with
          | var_Chan x =>
              cases x with
              | zero => simp [chanIndex]
              | succ x =>
                  have memT := childLabels_shift_mem_inv mem
                  have hne := ih tyTail memT
                  simp only [chanIndex] at hne ⊢
                  omega
      | one tyChild tyTail =>
          cases c with
          | var_Chan x =>
              cases x with
              | zero => simp [chanIndex]
              | succ x =>
                  have memT : Chan.var_Chan (x + 1) ∈
                      childLabels (shiftChildren ‹List (Chan × Tree)›) := by
                    simp only [childLabels, List.map_cons, List.mem_cons] at mem
                    rcases mem with h | h
                    · exact absurd h (by intro hc; injection hc with hc'; omega)
                    · exact h
                  have hne := ih tyTail (childLabels_shift_mem_inv memT)
                  simp only [chanIndex] at hne ⊢
                  omega

/-- The parent half of an END step: consuming the closing endpoint leaves the continuation
typed over the merge complement, and exposes the endpoint's `PJust` lookup. -/
lemma close_parent_typed {Θ : PCtx} {M : EvalCtx} {b : Bool} {cx : Nat}
    (tym : Θ ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢
      M.eval (.close b (Term.chan (Chan.var_Chan cx))) : .M .unit) :
    ∃ Θ1 Θ2 r1 A1, PJust Θ1 cx r1 A1 ∧ PMerge Θ1 Θ2 Θ ∧
      (Θ2 ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ M.eval (.pure .one) : .M .unit) := by
  obtain ⟨Θ1, Θ2, A0, mrg, tyClose, cont⟩ := evalCtx_inv tym
  have hinv : (Term.M A0 ≃ Term.M .unit) ∧
      (Θ1 ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢
        .chan (Chan.var_Chan cx) : .ch b .stop) := by
    cases b
    · exact wait_inv tyClose
    · exact close_inv tyClose
  obtain ⟨eqA0, tyChan⟩ := hinv
  obtain ⟨r1, A1, just, _, _⟩ := chan_inv tyChan
  obtain ⟨s, tyMA0⟩ := tyClose.validity
  have tyPure : erasePCtx Θ2 ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢
      Term.pure .one : .M A0 :=
    Typed.conv (ARS.conv_sym eqA0)
      (Typed.pure (Typed.one (erasePCtx_empty Θ2) Wf.nil Key.nil)) tyMA0
  exact ⟨Θ1, Θ2, r1, A1, just, mrg,
    cont (erasePCtx Θ2) Θ2 _ (PMerge.erasePCtx_right Θ2) tyPure⟩

/-! ## Iterated endpoint shifts and singleton endpoint contexts -/

/-- `A` shifted by `k` channel binders, as iterated one-step shifts. The iteration matches the
shift accumulation of `PJust`/`PHas`/`ChildrenTyped` definitionally. -/
def shiftK : Nat → Term → Term
  | 0, A => A
  | k + 1, A => (shiftK k A)⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩

lemma shiftK_proto {A : Term} (tyA : ([] : Static.Ctx) ⊢ A : .proto) :
    ∀ k, ([] : Static.Ctx) ⊢ shiftK k A : .proto
  | 0 => tyA
  | k + 1 => Static.Typed.crename (shiftK_proto tyA k) _

lemma shiftK_conv (A : Term) : ∀ k, shiftK k A ≃ A
  | 0 => ARS.Conv.refl
  | k + 1 => Static.cren_conv0 (shiftK_conv A k) _

/-- The `PJust` lookup of the singleton endpoint context `x ↦ one r A`. -/
lemma PJust_single {x : Nat} {r : Bool} {A : Term} {Θe : PCtx} (emp : PEmpty Θe) :
    PJust (List.replicate x Slot.none ++ .one r A :: Θe) x r (shiftK (x + 1) A) := by
  induction x with
  | zero => exact PJust.zero emp
  | succ x ih => exact PJust.none ih

/-- The singleton endpoint context types the singleton child list. -/
lemma childrenTyped_single {x : Nat} {r : Bool} {A : Term} {child : Tree} {Θe : PCtx}
    (emp : PEmpty Θe)
    (tyChild : TypedAt (!r) (shiftK 1 A) child) :
    ChildrenTyped (List.replicate x Slot.none ++ .one r A :: Θe)
      [(Chan.var_Chan x, child)] := by
  induction x with
  | zero => exact ChildrenTyped.one tyChild (ChildrenTyped.of_empty emp)
  | succ x ih => exact ChildrenTyped.none (children := [(Chan.var_Chan x, child)]) ih

lemma PJust.toPHas {Θ : PCtx} {x r A} (just : PJust Θ x r A) : PHas Θ x r A := by
  induction just with
  | zero _ => exact .zero
  | none _ ih => exact .succ ih

/-- Transport a `PHas` from the right component of a leaf-safe merge to the result. -/
lemma PHas.merge_right {Θ1 Θ2 Θ : PCtx} (single : PCtxSingle Θ) (mrg : PMerge Θ1 Θ2 Θ) :
    ∀ {x r A}, PHas Θ2 x r A → PHas Θ x r A := by
  induction mrg with
  | nil => intro x r A has; cases has
  | none _ ih =>
      intro x r A has
      cases single with
      | none single' => cases has with | succ has' => exact .succ (ih single' has')
  | oneL _ ih =>
      intro x r A has
      cases single with
      | one single' => cases has with | succ has' => exact .succ (ih single' has')
  | oneR _ ih =>
      intro x r A has
      cases single with
      | one single' =>
          cases has with
          | zero => exact .zero
          | succ has' => exact .succ (ih single' has')
  | bothL _ _ => cases single
  | bothR _ _ => cases single
  | split _ _ => cases single

lemma PHas.merge_left {Θ1 Θ2 Θ : PCtx} (single : PCtxSingle Θ) (mrg : PMerge Θ1 Θ2 Θ)
    {x r A} (has : PHas Θ1 x r A) : PHas Θ x r A :=
  PHas.merge_right single mrg.sym has

/-- Endpoint liveness is decided in a leaf-safe context. -/
lemma PCtxSingle.pos_total {Θ : PCtx} (single : PCtxSingle Θ) :
    ∀ i, CvarPos Θ i true ∨ CvarPos Θ i false := by
  induction single with
  | nil => intro i; exact Or.inr .nil
  | none _ ih =>
      intro i
      cases i with
      | zero => exact Or.inr .none
      | succ i => exact (ih i).imp .cons .cons
  | one _ ih =>
      intro i
      cases i with
      | zero => exact Or.inl .one
      | succ i => exact (ih i).imp .cons .cons

/-! ## Trailing padding of the children judgments -/

lemma PHas.padR {Θ : PCtx} {x r A} (k : Nat) (has : PHas Θ x r A) :
    PHas (Θ ++ List.replicate k Slot.none) x r A := by
  induction has with
  | zero => exact .zero
  | succ _ ih => exact .succ ih

lemma ChildrenTyped.padR (k : Nat) : ∀ {Θ : PCtx} {ms},
    ChildrenTyped Θ ms → ChildrenTyped (Θ ++ List.replicate k Slot.none) ms := by
  intro Θ
  induction Θ with
  | nil =>
      intro ms ty
      cases ty
      exact ChildrenTyped.of_empty (PEmpty.replicate k)
  | cons s Θt ih =>
      intro ms ty
      cases ty with
      | none ty' => exact .none (ih ty')
      | one tyChild ty' => exact .one tyChild (ih ty')

lemma ChildrenTypedAt.padR (k : Nat) : ∀ {Θ : PCtx} {y ry Ay ms},
    ChildrenTypedAt Θ y ry Ay ms →
    ChildrenTypedAt (Θ ++ List.replicate k Slot.none) y ry Ay ms := by
  intro Θ
  induction Θ with
  | nil =>
      intro y ry Ay ms ty
      cases ty
  | cons s Θt ih =>
      intro y ry Ay ms ty
      cases ty with
      | parent ty' => exact .parent (ChildrenTyped.padR k ty')
      | none ty' => exact .none (ih ty')
      | one tyChild ty' => exact .one tyChild (ih ty')

/-- Merge a fresh singleton endpoint context into a leaf-safe context that does not hold the
endpoint. -/
lemma merge_fresh_single {Θ : PCtx} {x : Nat} {r : Bool} {X : Term}
    (single : PCtxSingle Θ) (hlen : x < Θ.length)
    (fresh : CvarPos Θ x true → False) :
    ∃ Θ', PMerge (List.replicate x Slot.none ++
        .one r X :: List.replicate (Θ.length - x - 1) Slot.none) Θ Θ' ∧
      PCtxSingle Θ' := by
  refine pmerge_single_disjoint ?_ ?_ single ?_
  · simp only [List.length_append, List.length_replicate, List.length_cons]
    omega
  · exact PCtxSingle.append (PCtxSingle.replicate x)
      (PCtxSingle.one (PCtxSingle.replicate _))
  · intro i h1 h2
    have hx : x = i := ((PJust_single (PEmpty.replicate _)).pos_true (i := i)).mp h1
    subst hx
    exact fresh h2

/-! ## Splitting children by payload occurrence -/

/-- A context-driven children split coincides (up to permutation) with the term-driven
`splitChildrenByTerm` partition whenever the context liveness matches term occurrence. -/
lemma split_children_perm {Θ1 Θ2 Θ : PCtx} {ms ms1 ms2 : List (Chan × Tree)} {w : Term}
    (single : PCtxSingle Θ) (mrg : PMerge Θ1 Θ2 Θ)
    (pos2 : ∀ p : Chan × Tree, p ∈ ms2 → CvarPos Θ2 (chanIndex p.1) true)
    (nodupMs1 : ms1.Nodup) (nodupMs2 : ms2.Nodup)
    (hperm : List.Perm ms (ms1 ++ ms2))
    (nodup : (childLabels ms).Nodup)
    (hocc1 : ∀ p : Chan × Tree, p ∈ ms1 → occurs (chanIndex p.1) w = 1)
    (hocc0 : ∀ i, CvarPos Θ1 i false → occurs i w = 0) :
    List.Perm (splitChildrenByTerm w ms).1 ms1 ∧
      List.Perm (splitChildrenByTerm w ms).2 ms2 := by
  have single1 := (PCtxSingle.split single mrg).1
  have pairsNodup : ms.Nodup := List.Nodup.of_map _ nodup
  have splitPerm := splitChildrenByTerm_perm w ms
  have nodup21 : ((splitChildrenByTerm w ms).2 ++ (splitChildrenByTerm w ms).1).Nodup :=
    splitPerm.symm.nodup pairsNodup
  have nodup1 : (splitChildrenByTerm w ms).1.Nodup := (List.nodup_append.mp nodup21).2.1
  have nodup2 : (splitChildrenByTerm w ms).2.Nodup := (List.nodup_append.mp nodup21).1
  -- an `ms2` member is dead on the redex side, so its occurrence count in `w` is zero
  have occMs2 : ∀ p : Chan × Tree, p ∈ ms2 → occurs (chanIndex p.1) w = 0 := by
    intro p hp
    have posP := pos2 p hp
    rcases PCtxSingle.pos_total single1 (chanIndex p.1) with hpos | hneg
    · exact absurd posP (fun h => PCtxSingle.merge_true_excl single mrg hpos h)
    · exact hocc0 _ hneg
  have mem1 : ∀ p, p ∈ ms1 → p ∈ (splitChildrenByTerm w ms).1 := by
    intro p hp
    have hocc : occurs (chanIndex p.1) w = 1 := hocc1 p hp
    have hmemMs : p ∈ ms := hperm.symm.subset (by simp [hp])
    rcases List.mem_append.mp (splitPerm.symm.subset hmemMs) with h2 | h1
    · exact absurd (splitChildrenByTerm_mem₂ h2).2 (by omega)
    · exact h1
  have mem2 : ∀ p, p ∈ ms2 → p ∈ (splitChildrenByTerm w ms).2 := by
    intro p hp
    have hmemMs : p ∈ ms := hperm.symm.subset (by simp [hp])
    rcases List.mem_append.mp (splitPerm.symm.subset hmemMs) with h2 | h1
    · exact h2
    · exact absurd (splitChildrenByTerm_mem₁ h1).2 (by simp [occMs2 p hp])
  have sub1 : ∀ p, p ∈ (splitChildrenByTerm w ms).1 → p ∈ ms1 := by
    intro p hp
    obtain ⟨hmemMs, hocc⟩ := splitChildrenByTerm_mem₁ hp
    rcases List.mem_append.mp (hperm.subset hmemMs) with h | h
    · exact h
    · exact absurd (occMs2 p h) hocc
  have sub2 : ∀ p, p ∈ (splitChildrenByTerm w ms).2 → p ∈ ms2 := by
    intro p hp
    obtain ⟨hmemMs, hocc⟩ := splitChildrenByTerm_mem₂ hp
    rcases List.mem_append.mp (hperm.subset hmemMs) with h | h
    · exfalso
      have := hocc1 p h
      omega
    · exact h
  exact ⟨List.Subperm.antisymm (nodup1.subperm sub1) (nodupMs1.subperm mem1),
    List.Subperm.antisymm (nodup2.subperm sub2) (nodupMs2.subperm mem2)⟩

/-! ## Communication-case helpers -/

/-- A `PJust` lookup of a merge component agrees with a `PHas` lookup of the leaf-safe result. -/
lemma PJust_PHas_agree {Θ1 Θ2 Θ : PCtx} (single : PCtxSingle Θ) (mrg : PMerge Θ1 Θ2 Θ) :
    ∀ {x r1 A1 r2 A2}, PJust Θ1 x r1 A1 → PHas Θ x r2 A2 → r1 = r2 ∧ A1 = A2 := by
  induction mrg with
  | nil =>
      intro x r1 A1 r2 A2 just _
      cases just
  | none _ ih =>
      intro x r1 A1 r2 A2 just has
      cases single with
      | none single' =>
          cases just with
          | none just' =>
              cases has with
              | succ has' =>
                  obtain ⟨hr, hA⟩ := ih single' just' has'
                  exact ⟨hr, by rw [hA]⟩
  | oneL _ ih =>
      intro x r1 A1 r2 A2 just has
      cases single with
      | one single' =>
          cases just with
          | zero _ =>
              cases has with
              | zero => exact ⟨rfl, rfl⟩
  | oneR _ ih =>
      intro x r1 A1 r2 A2 just has
      cases single with
      | one single' =>
          cases just with
          | none just' =>
              cases has with
              | succ has' =>
                  obtain ⟨hr, hA⟩ := ih single' just' has'
                  exact ⟨hr, by rw [hA]⟩
  | bothL _ _ => cases single
  | bothR _ _ => cases single
  | split _ _ => cases single

lemma CvarPos.lt_length : ∀ {Θ : PCtx} {i}, CvarPos Θ i true → i < Θ.length := by
  intro Θ
  induction Θ with
  | nil => intro i h; cases h
  | cons s Θt ih =>
      intro i h
      cases h with
      | one => simp
      | cons h' =>
          have := ih h'
          simp
          omega

/-- The vacuous term-variable shift of a closed lookup type. -/
lemma cren_len_nil (A : Term) :
    A⟨(id : Nat → Nat); (· + ([] : Static.Ctx).length)⟩ = A := by
  simp only [List.length_nil]
  rw [show ((· + 0) : Nat → Nat) = (id : Nat → Nat) from by funext x; simp]
  asimp

/-- The endpoint context holding exactly `x ↦ one r W`, padded to length `L`. -/
def oneCtx (x : Nat) (r : Bool) (W : Term) (L : Nat) : PCtx :=
  List.replicate x Slot.none ++ .one r W :: List.replicate (L - x - 1) Slot.none

lemma oneCtx_just {x : Nat} {r : Bool} {W : Term} (L : Nat) :
    PJust (oneCtx x r W L) x r (shiftK (x + 1) W) :=
  PJust_single (PEmpty.replicate _)

lemma oneCtx_single {x : Nat} {r : Bool} {W : Term} (L : Nat) :
    PCtxSingle (oneCtx x r W L) :=
  PCtxSingle.append (PCtxSingle.replicate _) (PCtxSingle.one (PCtxSingle.replicate _))

/-- The channel variable of a `oneCtx`, typed at any protocol its slot converts to. -/
lemma oneCtx_chan {x : Nat} {r : Bool} {W B : Term} (L : Nat)
    (tyW : ([] : Static.Ctx) ⊢ W : .proto) (hWB : W ≃ B)
    (tyB : ([] : Static.Ctx) ⊢ B : .proto) :
    (oneCtx x r W L) ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢
      .chan (Chan.var_Chan x) : .ch r B :=
  TLLC.Process.chanTyped (oneCtx_just L) (shiftK_proto tyW _)
    (ARS.conv_trans (shiftK_conv W _) hWB) tyB

/-- Merge a fresh `oneCtx` endpoint into a leaf-safe context that does not hold it. -/
lemma oneCtx_merge {Θ : PCtx} {x : Nat} {r : Bool} {W : Term}
    (single : PCtxSingle Θ) (hlen : x < Θ.length)
    (fresh : CvarPos Θ x true → False) :
    ∃ Θ', PMerge (oneCtx x r W Θ.length) Θ Θ' ∧ PCtxSingle Θ' :=
  merge_fresh_single single hlen fresh

/-- The singleton child list of a `oneCtx`. -/
lemma oneCtx_children {x : Nat} {r : Bool} {W : Term} {child : Tree} (L : Nat)
    (tyChild : TypedAt (!r) (shiftK 1 W) child) :
    ChildrenTyped (oneCtx x r W L) [(Chan.var_Chan x, child)] :=
  childrenTyped_single (PEmpty.replicate _) tyChild

/-- An endpoint is not both live and dead. -/
lemma CvarPos.not_both : ∀ {Θ : PCtx} {i}, CvarPos Θ i true → CvarPos Θ i false → False := by
  intro Θ
  induction Θ with
  | nil => intro i h _; cases h
  | cons s Θt ih =>
      intro i ht hf
      cases ht with
      | one => cases hf
      | cons ht' => cases hf with | cons hf' => exact ih ht' hf'

/-- A live endpoint of a children context is a child-edge label. -/
lemma ChildrenTyped.label_of_pos {Θ : PCtx} {ms i} (ty : ChildrenTyped Θ ms)
    (h : CvarPos Θ i true) : Chan.var_Chan i ∈ childLabels ms := by
  by_contra hmem
  exact CvarPos.not_both h (ty.notLabel_false (c := Chan.var_Chan i) hmem)

/-- A live endpoint of a node's children context is a child-edge label or the parent slot. -/
lemma ChildrenTypedAt.label_of_pos {Θ : PCtx} {y ry Ay ms i}
    (ty : ChildrenTypedAt Θ y ry Ay ms) (h : CvarPos Θ i true) :
    Chan.var_Chan i ∈ childLabels ms ∨ i = y := by
  by_cases hy : i = y
  · exact Or.inr hy
  · left
    by_contra hmem
    exact CvarPos.not_both h (ty.notLabel_false (c := Chan.var_Chan i) hmem hy)

/-! ## Position-based endpoint extraction -/

/-- Turn slot liveness into an endpoint lookup. -/
lemma CvarPos.toPHas : ∀ {Θ : PCtx} {i}, CvarPos Θ i true → ∃ r A, PHas Θ i r A := by
  intro Θ
  induction Θ with
  | nil => intro i h; cases h
  | cons s Θt ih =>
      intro i h
      cases h with
      | one => exact ⟨_, _, .zero⟩
      | cons h' =>
          obtain ⟨r, A, has⟩ := ih h'
          exact ⟨r, _, .succ has⟩

/-- Erase the slot at index `x` (the merge complement of `eraseExcept`). -/
def eraseAt : PCtx → Nat → PCtx
  | [], _ => []
  | _ :: Θ, 0 => .none :: Θ
  | s :: Θ, x + 1 => s :: eraseAt Θ x

@[simp] lemma eraseAt_nil (x : Nat) : eraseAt [] x = [] := rfl

@[simp] lemma eraseAt_zero (s : Slot) (Θ : PCtx) : eraseAt (s :: Θ) 0 = .none :: Θ := rfl

@[simp] lemma eraseAt_succ (s : Slot) (Θ : PCtx) (x : Nat) :
    eraseAt (s :: Θ) (x + 1) = s :: eraseAt Θ x := rfl

/-- `eraseExcept` and `eraseAt` merge back to the original context. -/
lemma pmerge_eraseExcept : ∀ (Θ : PCtx) (x : Nat), PMerge (eraseExcept Θ x) (eraseAt Θ x) Θ := by
  intro Θ
  induction Θ with
  | nil => intro x; exact .nil
  | cons s Θt ih =>
      intro x
      cases x with
      | zero =>
          cases s with
          | none => exact .none (PMerge.erasePCtx_right Θt).sym
          | one r A => exact .oneL (PMerge.erasePCtx_right Θt).sym
          | both A => exact .bothL (PMerge.erasePCtx_right Θt).sym
      | succ x =>
          cases s with
          | none => exact .none (ih x)
          | one r A => exact .oneR (ih x)
          | both A => exact .bothR (ih x)

/-- In a leaf-safe context, the merge complement of an endpoint lookup is `eraseAt`. -/
lemma PJust_merge_eq : ∀ {Θ1 Θ2 Θ : PCtx} {x r A}, PCtxSingle Θ →
    PJust Θ1 x r A → PMerge Θ1 Θ2 Θ → Θ2 = eraseAt Θ x := by
  intro Θ1 Θ2 Θ x r A single just mrg
  induction just generalizing Θ2 Θ with
  | zero emp =>
      cases mrg with
      | oneL mrg' => rw [eraseAt_zero, mrg'.emptyL emp]
      | split _ => cases single
  | none _ ih =>
      cases mrg with
      | none mrg' =>
          cases single with
          | none single' => rw [eraseAt_succ, ih single' mrg']
      | oneR mrg' =>
          cases single with
          | one single' => rw [eraseAt_succ, ih single' mrg']
      | bothR _ => cases single

lemma eraseAt_append (Ξ : PCtx) : ∀ (Θ : PCtx) (x : Nat), x < Θ.length →
    eraseAt (Θ ++ Ξ) x = eraseAt Θ x ++ Ξ := by
  intro Θ
  induction Θ with
  | nil => intro x h; simp at h
  | cons s Θt ih =>
      intro x h
      cases x with
      | zero => simp
      | succ x =>
          simp only [List.cons_append, eraseAt_succ]
          rw [ih x (by simpa using h)]

/-! ## Canonical label order -/

/-- Strict label order on child edges (the tree component is irrelevant). -/
def childLT (p q : Chan × Tree) : Prop := chanIndex p.1 < chanIndex q.1

instance : Std.Antisymm childLT where
  antisymm _ _ h1 h2 := absurd h2 (by unfold childLT at h1 ⊢; omega)

/-- Label-sorted child lists agreeing up to permutation are equal. -/
lemma child_sorted_eq {ms1 ms2 : List (Chan × Tree)} (perm : List.Perm ms1 ms2)
    (h1 : List.Pairwise childLT ms1) (h2 : List.Pairwise childLT ms2) : ms1 = ms2 :=
  List.Perm.eq_of_pairwise' h1 h2 perm

lemma shiftChildren_mem_shape {ms : List (Chan × Tree)} {b : Chan × Tree}
    (hb : b ∈ shiftChildren ms) :
    ∃ y s, b = (Chan.var_Chan (y + 1), s) ∧ (Chan.var_Chan y, s) ∈ ms := by
  rcases b with ⟨bc, bs⟩
  cases bc with
  | var_Chan yb =>
      cases yb with
      | zero => exact absurd hb (zero_pair_notin_shift bs)
      | succ y => exact ⟨y, bs, rfl, shiftChildren_mem_inv hb⟩

lemma sorted_shiftChildren : ∀ {ms : List (Chan × Tree)},
    List.Pairwise childLT ms → List.Pairwise childLT (shiftChildren ms) := by
  intro ms
  induction ms with
  | nil => intro _; simp
  | cons p ms ih =>
      intro h
      rcases p with ⟨pc, pt⟩
      cases pc with
      | var_Chan x =>
          rw [List.pairwise_cons] at h
          rw [shiftChildren_cons, List.pairwise_cons]
          refine ⟨?_, ih h.2⟩
          intro b hb
          obtain ⟨y, s, rfl, hmem⟩ := shiftChildren_mem_shape hb
          have := h.1 _ hmem
          unfold childLT at this ⊢
          simp only [chanIndex] at this ⊢
          omega

/-- The canonical children list of the validity judgment is label-sorted. -/
lemma ChildrenTyped.sorted : ∀ {Θ : PCtx} {ms},
    ChildrenTyped Θ ms → List.Pairwise childLT ms := by
  intro Θ
  induction Θ with
  | nil =>
      intro ms ty
      cases ty
      simp
  | cons s Θt ih =>
      intro ms ty
      cases ty with
      | none ty' => exact sorted_shiftChildren (ih ty')
      | one tyChild ty' =>
          rw [List.pairwise_cons]
          refine ⟨?_, sorted_shiftChildren (ih ty')⟩
          intro b hb
          obtain ⟨y, s, rfl, _⟩ := shiftChildren_mem_shape hb
          unfold childLT
          simp [chanIndex]

lemma ChildrenTypedAt.sorted : ∀ {Θ : PCtx} {y ry Ay ms},
    ChildrenTypedAt Θ y ry Ay ms → List.Pairwise childLT ms := by
  intro Θ
  induction Θ with
  | nil =>
      intro y ry Ay ms ty
      cases ty
  | cons s Θt ih =>
      intro y ry Ay ms ty
      cases ty with
      | parent ty' => exact sorted_shiftChildren (ChildrenTyped.sorted ty')
      | none ty' => exact sorted_shiftChildren (ih ty')
      | one tyChild ty' =>
          rw [List.pairwise_cons]
          refine ⟨?_, sorted_shiftChildren (ih ty')⟩
          intro b hb
          obtain ⟨y', s', rfl, _⟩ := shiftChildren_mem_shape hb
          unfold childLT
          simp [chanIndex]

/-- Sortedness only depends on the labels, so a same-label replacement preserves it. -/
lemma sorted_replace {c : Chan} {t t' : Tree} :
    ∀ {l r : List (Chan × Tree)},
    List.Pairwise childLT (l ++ (c, t) :: r) →
    List.Pairwise childLT (l ++ (c, t') :: r) := by
  intro l
  induction l with
  | nil =>
      intro r h
      rw [List.nil_append, List.pairwise_cons] at h ⊢
      exact ⟨fun b hb => h.1 b hb, h.2⟩
  | cons q l ih =>
      intro r h
      rw [List.cons_append, List.pairwise_cons] at h ⊢
      refine ⟨?_, ih h.2⟩
      intro b hb
      rw [List.mem_append, List.mem_cons] at hb
      rcases hb with hb | hb | hb
      · exact h.1 b (by simp [hb])
      · subst hb
        exact h.1 (c, t) (by simp)
      · exact h.1 b (by simp [hb])

lemma insertChild_perm (c : Chan) (t : Tree) (ms : List (Chan × Tree)) :
    List.Perm (insertChild c t ms) ((c, t) :: ms) :=
  List.perm_orderedInsert _ _ _

lemma mergeChildren_perm : ∀ (extra base : List (Chan × Tree)),
    List.Perm (mergeChildren extra base) (extra ++ base) := by
  intro extra
  induction extra with
  | nil => intro base; exact .refl _
  | cons p extra ih =>
      intro base
      simp only [mergeChildren, List.foldr_cons]
      exact (List.perm_orderedInsert _ _ _).trans (List.Perm.cons p (ih base))

lemma sorted_insertChild {c : Chan} {t : Tree} :
    ∀ {ms : List (Chan × Tree)},
    List.Pairwise childLT ms →
    (∀ p : Chan × Tree, p ∈ ms → chanIndex c ≠ chanIndex p.1) →
    List.Pairwise childLT (insertChild c t ms) := by
  intro ms
  induction ms with
  | nil =>
      intro _ _
      simp [insertChild, List.orderedInsert]
  | cons q ms ih =>
      intro h fresh
      rw [List.pairwise_cons] at h
      unfold insertChild List.orderedInsert
      have hct : chanIndex ((c, t) : Chan × Tree).1 = chanIndex c := rfl
      by_cases hle : childLE (c, t) q
      · rw [if_pos hle]
        rw [List.pairwise_cons]
        refine ⟨?_, by rw [List.pairwise_cons]; exact h⟩
        intro b hb
        have hcq := fresh q (by simp)
        unfold childLE at hle
        rcases List.mem_cons.mp hb with rfl | hb
        · unfold childLT
          omega
        · have hq := h.1 b hb
          unfold childLT at hq ⊢
          omega
      · rw [if_neg hle]
        rw [List.pairwise_cons]
        refine ⟨?_, ih h.2 (fun p hp => fresh p (by simp [hp]))⟩
        intro b hb
        unfold childLE at hle
        rcases (List.mem_orderedInsert _).mp hb with rfl | hb
        · unfold childLT
          omega
        · exact h.1 b hb

lemma sorted_mergeChildren : ∀ {extra base : List (Chan × Tree)},
    List.Pairwise childLT base →
    (childLabels (extra ++ base)).Nodup →
    List.Pairwise childLT (mergeChildren extra base) := by
  intro extra
  induction extra with
  | nil =>
      intro base h _
      exact h
  | cons p extra ih =>
      intro base hbase nodup
      simp only [mergeChildren, List.foldr_cons]
      have nodupT : (childLabels (extra ++ base)).Nodup := by
        simp only [childLabels, List.cons_append, List.map_cons, List.nodup_cons] at nodup
        exact nodup.2
      have hrec := ih hbase nodupT
      refine sorted_insertChild hrec ?_
      intro q hq
      have hqmem : q ∈ extra ++ base := (mergeChildren_perm extra base).subset hq
      have hne : p.1 ≠ q.1 := by
        intro h
        simp only [childLabels, List.cons_append, List.map_cons, List.nodup_cons] at nodup
        exact nodup.1 (by
          rw [h]
          exact List.mem_map.mpr ⟨q, hqmem, rfl⟩)
      cases hp1 : p.1 with
      | var_Chan a =>
          cases hq1 : q.1 with
          | var_Chan b =>
              simp only [chanIndex]
              intro hab
              exact hne (by rw [hp1, hq1, hab])

/-- The second split component is a sublist of the original list. -/
lemma splitChildrenByTerm_sublist₂ (m : Term) :
    ∀ ms : List (Chan × Tree), List.Sublist (splitChildrenByTerm m ms).2 ms := by
  intro ms
  induction ms with
  | nil => simp [splitChildrenByTerm]
  | cons q rest ih =>
      rcases q with ⟨e, sib⟩
      cases e with
      | var_Chan ex =>
          by_cases hocc : occurs ex m = 0
          · rw [splitChildrenByTerm_cons_pos hocc]
            exact List.Sublist.cons_cons _ ih
          · rw [splitChildrenByTerm_cons_neg hocc]
            exact List.Sublist.cons _ ih

/-! ## Fidelity (Lemma 5.87) -/

theorem fidelity_mutual : ∀ {t t' : Tree}, Step t t' →
    (Typed t → Distinct t → Typed t') ∧
    (∀ ry Ay, TypedAt ry Ay t → Distinct t → TypedAt ry Ay t') := by
  intro t t' st
  induction st with
  | @rootFork M A m c d ms qs freshC freshD _treeFresh =>
      refine ⟨fun ty dist => ?_, fun ry Ay ty _ => (by cases ty)⟩
      cases ty with
      | @root Θ0 _ _ _ single0 tym0 tyms0 tyqs =>
      cases c with
      | var_Chan cx =>
      cases d with
      | var_Chan dx =>
      have freshC' : occurs cx (M.eval (.fork A m)) = 0 := freshC
      have freshD' : occurs dx (M.eval (.fork A m)) = 0 := freshD
      -- pad the endpoint context so both fresh indices fit
      have single : PCtxSingle (Θ0 ++ List.replicate (cx + dx + 1) Slot.none) :=
        PCtxSingle.append single0 (PCtxSingle.replicate _)
      have tym := Typed.padR (cx + dx + 1) tym0
      have tyms := ChildrenTyped.padR (cx + dx + 1) tyms0
      have hLen : (Θ0 ++ List.replicate (cx + dx + 1) Slot.none).length
          = Θ0.length + (cx + dx + 1) := by simp
      -- invert the term typing at the fork redex
      obtain ⟨Θ1, Θ2, A0, mrg, tyFork, cont⟩ := evalCtx_inv tym
      obtain ⟨tyBody, eqA0⟩ := fork_inv tyFork
      have tyA : ([] : Static.Ctx) ⊢ A : .proto := by
        cases tyBody.wf with
        | cons _ tyCh => exact (Static.ch_inv tyCh).1
      have hL1 : Θ1.length = Θ0.length + (cx + dx + 1) := by
        rw [PMerge.length_left mrg, hLen]
      have hL2 : Θ2.length = Θ0.length + (cx + dx + 1) := by
        rw [PMerge.length_right mrg, hLen]
      have single1 := (PCtxSingle.split single mrg).1
      have single2 := (PCtxSingle.split single mrg).2
      -- freshness transfers to context liveness
      have hD1 : CvarPos Θ1 dx true → False := by
        intro h
        have h1 := tyFork.occurs1 h
        have h2 : occurs dx (Term.fork A m) = occurs dx m := rfl
        have h3 := evalctx_occurs_plug M (.fork A m) dx
        omega
      have hC2 : CvarPos Θ2 cx true → False := by
        intro h
        have h1 := tym.occurs1 (CvarPos.merge_true_right single mrg h)
        omega
      -- the spawned child: fire the body at the fresh endpoint `d`
      obtain ⟨Θchild, mrgD, singleChild⟩ :=
        merge_fresh_single (Θ := Θ1) (x := dx) (r := true) (X := A) single1
          (by omega) hD1
      have justD : PJust (List.replicate dx Slot.none ++
          .one true A :: List.replicate (Θ1.length - dx - 1) Slot.none) dx true
          (shiftK (dx + 1) A) := PJust_single (PEmpty.replicate _)
      have tyChanD := TLLC.Process.chanTyped justD (shiftK_proto tyA _)
        (shiftK_conv A _) tyA
      have tyChildTerm : Θchild ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢
          m[Chan.var_Chan; (Term.chan (Chan.var_Chan dx))..] : .M .unit :=
        Typed.esubst1 rfl (by asimp) PKey.impure mrgD.sym Key.nil Merge.nil
          tyBody tyChanD
      -- children bookkeeping
      obtain ⟨ms1, ms2, ty1, ty2, hperm⟩ := ChildrenTyped.split mrg single tyms
      obtain ⟨permSplit1, permSplit2⟩ :=
        split_children_perm (w := m) single mrg
          (fun p hp => ChildrenTyped.pos_of_label ty2 (List.mem_map.mpr ⟨p, hp, rfl⟩))
          (List.Nodup.of_map _ (ChildrenTyped.labels_nodup ty1))
          (List.Nodup.of_map _ (ChildrenTyped.labels_nodup ty2))
          hperm (ChildrenTyped.labels_nodup tyms)
          (fun p hp => tyFork.occurs1
            (ChildrenTyped.pos_of_label ty1 (List.mem_map.mpr ⟨p, hp, rfl⟩)))
          (fun i h => tyFork.occurs0 h)
      -- the new child node
      have hasD : PHas Θchild dx true (shiftK (dx + 1) A) :=
        PHas.merge_left singleChild mrgD (PJust.toPHas justD)
      have tymsAt : ChildrenTypedAt Θchild dx true (shiftK (dx + 1) A) ms1 :=
        ChildrenTypedAt.intro justD mrgD singleChild ty1
      have tyNode : TypedAt true (shiftK (dx + 1) A)
          (.node (Chan.var_Chan dx) (m[Chan.var_Chan; (Term.chan (Chan.var_Chan dx))..])
            ms1 []) :=
        TypedAt.node singleChild hasD tyChildTerm tymsAt .nil
      -- the parent: return the fresh endpoint `c`
      obtain ⟨Θ', mrgC, singleΘ'⟩ :=
        merge_fresh_single (Θ := Θ2) (x := cx) (r := false) (X := shiftK dx A) single2
          (by omega) hC2
      have justC : PJust (List.replicate cx Slot.none ++
          .one false (shiftK dx A) :: List.replicate (Θ2.length - cx - 1) Slot.none)
          cx false (shiftK (cx + 1) (shiftK dx A)) := PJust_single (PEmpty.replicate _)
      have tyChanC := TLLC.Process.chanTyped justC
        (shiftK_proto (shiftK_proto tyA dx) _)
        (ARS.conv_trans (shiftK_conv (shiftK dx A) _) (shiftK_conv A dx)) tyA
      obtain ⟨s0, tyMA0⟩ := tyFork.validity
      have tyPure := Typed.conv (ARS.conv_sym eqA0) (Typed.pure tyChanC) tyMA0
      have tyTerm' := cont _ Θ' _ mrgC.sym tyPure
      have tySingleton : ChildrenTyped (List.replicate cx Slot.none ++
          .one false (shiftK dx A) :: List.replicate (Θ2.length - cx - 1) Slot.none)
          [(Chan.var_Chan cx, .node (Chan.var_Chan dx)
            (m[Chan.var_Chan; (Term.chan (Chan.var_Chan dx))..]) ms1 [])] :=
        childrenTyped_single (PEmpty.replicate _) tyNode
      obtain ⟨msNew, tyMsNew, hpermNew⟩ :=
        ChildrenTyped.merge mrgC.sym singleΘ' ty2 tySingleton
      -- canonical equalities
      have sortedSrc := ChildrenTyped.sorted tyms
      have e1 : (splitChildrenByTerm m ms).1 = ms1 :=
        child_sorted_eq permSplit1
          (List.Pairwise.sublist (splitChildrenByTerm_sublist₁ m ms) sortedSrc)
          (ChildrenTyped.sorted ty1)
      have e2 : (splitChildrenByTerm m ms).2 = ms2 :=
        child_sorted_eq permSplit2
          (List.Pairwise.sublist (splitChildrenByTerm_sublist₂ m ms) sortedSrc)
          (ChildrenTyped.sorted ty2)
      have freshC2 : ∀ p : Chan × Tree, p ∈ ms2 →
          chanIndex (Chan.var_Chan cx) ≠ chanIndex p.1 := by
        intro p hp he
        apply hC2
        have hpos := ChildrenTyped.pos_of_label ty2 (List.mem_map.mpr ⟨p, hp, rfl⟩)
        have he' : cx = chanIndex p.1 := he
        rw [← he'] at hpos
        exact hpos
      have eNew : insertChild (Chan.var_Chan cx)
          (.node (Chan.var_Chan dx)
            (m[Chan.var_Chan; (Term.chan (Chan.var_Chan dx))..]) ms1 [])
          ms2 = msNew :=
        child_sorted_eq
          ((insertChild_perm _ _ _).trans
            ((List.perm_append_singleton _ _).symm.trans hpermNew.symm))
          (sorted_insertChild (ChildrenTyped.sorted ty2) freshC2)
          (ChildrenTyped.sorted tyMsNew)
      have hfork : forkChildren m (Chan.var_Chan cx) (Chan.var_Chan dx) ms =
          insertChild (Chan.var_Chan cx)
            (.node (Chan.var_Chan dx)
              (m[Chan.var_Chan; (Term.chan (Chan.var_Chan dx))..])
              (splitChildrenByTerm m ms).1 [])
            (splitChildrenByTerm m ms).2 := by
        simp [forkChildren]
      rw [hfork, e1, e2, eNew]
      exact Typed.root singleΘ' tyTerm' tyMsNew tyqs
  | @nodeFork M p A m c d ms qs freshC freshD freshP _treeFresh =>
      refine ⟨fun ty _ => (by cases ty), fun ry Ay ty dist => ?_⟩
      cases ty with
      | @node Θ0 y _ _ _ _ _ single0 has0 tym0 tyms0 tyqs =>
      cases c with
      | var_Chan cx =>
      cases d with
      | var_Chan dx =>
      have freshC' : occurs cx (M.eval (.fork A m)) = 0 := freshC
      have freshD' : occurs dx (M.eval (.fork A m)) = 0 := freshD
      have freshP' : occurs y m = 0 := freshP
      -- pad the endpoint context so both fresh indices fit
      have single : PCtxSingle (Θ0 ++ List.replicate (cx + dx + 1) Slot.none) :=
        PCtxSingle.append single0 (PCtxSingle.replicate _)
      have tym := Typed.padR (cx + dx + 1) tym0
      have tyms := ChildrenTypedAt.padR (cx + dx + 1) tyms0
      have has := PHas.padR (cx + dx + 1) has0
      have hLen : (Θ0 ++ List.replicate (cx + dx + 1) Slot.none).length
          = Θ0.length + (cx + dx + 1) := by simp
      -- invert the term typing at the fork redex
      obtain ⟨Θ1, Θ2, A0, mrg, tyFork, cont⟩ := evalCtx_inv tym
      obtain ⟨tyBody, eqA0⟩ := fork_inv tyFork
      have tyA : ([] : Static.Ctx) ⊢ A : .proto := by
        cases tyBody.wf with
        | cons _ tyCh => exact (Static.ch_inv tyCh).1
      have hL1 : Θ1.length = Θ0.length + (cx + dx + 1) := by
        rw [PMerge.length_left mrg, hLen]
      have hL2 : Θ2.length = Θ0.length + (cx + dx + 1) := by
        rw [PMerge.length_right mrg, hLen]
      have single1 := (PCtxSingle.split single mrg).1
      have single2 := (PCtxSingle.split single mrg).2
      -- freshness transfers to context liveness
      have hD1 : CvarPos Θ1 dx true → False := by
        intro h
        have h1 := tyFork.occurs1 h
        have h2 : occurs dx (Term.fork A m) = occurs dx m := rfl
        have h3 := evalctx_occurs_plug M (.fork A m) dx
        omega
      have hC2 : CvarPos Θ2 cx true → False := by
        intro h
        have h1 := tym.occurs1 (CvarPos.merge_true_right single mrg h)
        omega
      -- the parent endpoint stays with the continuation
      have posY1 : CvarPos Θ1 y false := by
        rcases PCtxSingle.pos_total single1 y with hpos | hneg
        · exfalso
          have h1 := tyFork.occurs1 hpos
          have h2 : occurs y (Term.fork A m) = occurs y m := rfl
          omega
        · exact hneg
      -- the spawned child: fire the body at the fresh endpoint `d`
      obtain ⟨Θchild, mrgD, singleChild⟩ :=
        merge_fresh_single (Θ := Θ1) (x := dx) (r := true) (X := A) single1
          (by omega) hD1
      have justD : PJust (List.replicate dx Slot.none ++
          .one true A :: List.replicate (Θ1.length - dx - 1) Slot.none) dx true
          (shiftK (dx + 1) A) := PJust_single (PEmpty.replicate _)
      have tyChanD := TLLC.Process.chanTyped justD (shiftK_proto tyA _)
        (shiftK_conv A _) tyA
      have tyChildTerm : Θchild ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢
          m[Chan.var_Chan; (Term.chan (Chan.var_Chan dx))..] : .M .unit :=
        Typed.esubst1 rfl (by asimp) PKey.impure mrgD.sym Key.nil Merge.nil
          tyBody tyChanD
      -- children bookkeeping (the reserved parent endpoint stays on the right)
      obtain ⟨ms1, ms2, ty1, ty2, hperm⟩ :=
        ChildrenTypedAt.split_right mrg single tyms posY1
      obtain ⟨permSplit1, permSplit2⟩ :=
        split_children_perm (w := m) single mrg
          (fun p hp => ChildrenTypedAt.pos_of_label ty2 (List.mem_map.mpr ⟨p, hp, rfl⟩))
          (List.Nodup.of_map _ (ChildrenTyped.labels_nodup ty1))
          (List.Nodup.of_map _ (ChildrenTypedAt.labels_nodup ty2))
          hperm (ChildrenTypedAt.labels_nodup tyms)
          (fun p hp => tyFork.occurs1
            (ChildrenTyped.pos_of_label ty1 (List.mem_map.mpr ⟨p, hp, rfl⟩)))
          (fun i h => tyFork.occurs0 h)
      -- the new child node
      have hasD : PHas Θchild dx true (shiftK (dx + 1) A) :=
        PHas.merge_left singleChild mrgD (PJust.toPHas justD)
      have tymsAt : ChildrenTypedAt Θchild dx true (shiftK (dx + 1) A) ms1 :=
        ChildrenTypedAt.intro justD mrgD singleChild ty1
      have tyNode : TypedAt true (shiftK (dx + 1) A)
          (.node (Chan.var_Chan dx) (m[Chan.var_Chan; (Term.chan (Chan.var_Chan dx))..])
            ms1 []) :=
        TypedAt.node singleChild hasD tyChildTerm tymsAt .nil
      -- the parent: return the fresh endpoint `c`
      obtain ⟨Θ', mrgC, singleΘ'⟩ :=
        merge_fresh_single (Θ := Θ2) (x := cx) (r := false) (X := shiftK dx A) single2
          (by omega) hC2
      have justC : PJust (List.replicate cx Slot.none ++
          .one false (shiftK dx A) :: List.replicate (Θ2.length - cx - 1) Slot.none)
          cx false (shiftK (cx + 1) (shiftK dx A)) := PJust_single (PEmpty.replicate _)
      have tyChanC := TLLC.Process.chanTyped justC
        (shiftK_proto (shiftK_proto tyA dx) _)
        (ARS.conv_trans (shiftK_conv (shiftK dx A) _) (shiftK_conv A dx)) tyA
      obtain ⟨s0, tyMA0⟩ := tyFork.validity
      have tyPure := Typed.conv (ARS.conv_sym eqA0) (Typed.pure tyChanC) tyMA0
      have tyTerm' := cont _ Θ' _ mrgC.sym tyPure
      have tySingleton : ChildrenTyped (List.replicate cx Slot.none ++
          .one false (shiftK dx A) :: List.replicate (Θ2.length - cx - 1) Slot.none)
          [(Chan.var_Chan cx, .node (Chan.var_Chan dx)
            (m[Chan.var_Chan; (Term.chan (Chan.var_Chan dx))..]) ms1 [])] :=
        childrenTyped_single (PEmpty.replicate _) tyNode
      obtain ⟨msNew, tyMsNew, hpermNew⟩ :=
        ChildrenTypedAt.merge mrgC.sym singleΘ' ty2 tySingleton
      -- the parent endpoint survives into the final context
      have hasY : PHas Θ' y ry Ay :=
        PHas.merge_right singleΘ' mrgC (PHas.merge_inv_right mrg has posY1)
      -- canonical equalities
      have sortedSrc := ChildrenTypedAt.sorted tyms
      have e1 : (splitChildrenByTerm m ms).1 = ms1 :=
        child_sorted_eq permSplit1
          (List.Pairwise.sublist (splitChildrenByTerm_sublist₁ m ms) sortedSrc)
          (ChildrenTyped.sorted ty1)
      have e2 : (splitChildrenByTerm m ms).2 = ms2 :=
        child_sorted_eq permSplit2
          (List.Pairwise.sublist (splitChildrenByTerm_sublist₂ m ms) sortedSrc)
          (ChildrenTypedAt.sorted ty2)
      have freshC2 : ∀ p : Chan × Tree, p ∈ ms2 →
          chanIndex (Chan.var_Chan cx) ≠ chanIndex p.1 := by
        intro p hp he
        apply hC2
        have hpos := ChildrenTypedAt.pos_of_label ty2 (List.mem_map.mpr ⟨p, hp, rfl⟩)
        have he' : cx = chanIndex p.1 := he
        rw [← he'] at hpos
        exact hpos
      have eNew : insertChild (Chan.var_Chan cx)
          (.node (Chan.var_Chan dx)
            (m[Chan.var_Chan; (Term.chan (Chan.var_Chan dx))..]) ms1 [])
          ms2 = msNew :=
        child_sorted_eq
          ((insertChild_perm _ _ _).trans
            ((List.perm_append_singleton _ _).symm.trans hpermNew.symm))
          (sorted_insertChild (ChildrenTypedAt.sorted ty2) freshC2)
          (ChildrenTypedAt.sorted tyMsNew)
      have hfork : forkChildren m (Chan.var_Chan cx) (Chan.var_Chan dx) ms =
          insertChild (Chan.var_Chan cx)
            (.node (Chan.var_Chan dx)
              (m[Chan.var_Chan; (Term.chan (Chan.var_Chan dx))..])
              (splitChildrenByTerm m ms).1 [])
            (splitChildrenByTerm m ms).2 := by
        simp [forkChildren]
      rw [hfork, e1, e2, eNew]
      exact TypedAt.node singleΘ' hasY tyTerm' tyMsNew tyqs
  | @rootWait M N c d l r ms' qs qs' =>
      refine ⟨fun ty dist => ?_, fun ry Ay ty _ => (by cases ty)⟩
      cases ty with
      | root single tym tyms tyqs =>
          cases c with
          | var_Chan cx =>
              obtain ⟨Θ1, Θ2, r1, A1, just, mrg, tyTerm2⟩ := close_parent_typed tym
              obtain ⟨C, tyChild, _, tyRest⟩ := ChildrenTyped.remove just mrg tyms rfl rfl
              exact Typed.root (PCtxSingle.split single mrg).2 tyTerm2 tyRest
                (SubtreesTyped.append tyqs
                  (.cons (TypedAt.close_detached_typed tyChild) .nil))
  | @nodeWait M N p c d l r ms' qs qs' =>
      refine ⟨fun ty _ => (by cases ty), fun ry Ay ty dist => ?_⟩
      cases ty with
      | @node _ x _ _ _ _ _ single has tym tyms tyqs =>
          cases c with
          | var_Chan cx =>
              obtain ⟨Θ1, Θ2, r1, A1, just, mrg, tyTerm2⟩ := close_parent_typed tym
              obtain ⟨C, tyChild, _, tyRest⟩ := ChildrenTypedAt.remove just mrg tyms rfl rfl
              have hne : cx ≠ x :=
                ChildrenTypedAt.label_ne_parent (c := Chan.var_Chan cx) tyms (by simp [childLabels])
              have has2 : PHas Θ2 x _ _ :=
                PHas.merge_inv_right mrg has ((just.pos_false).mpr hne)
              exact TypedAt.node (PCtxSingle.split single mrg).2 has2 tyTerm2 tyRest
                (SubtreesTyped.append tyqs
                  (.cons (TypedAt.close_detached_typed tyChild) .nil))
  | @rootClose M N c d l r ms' qs qs' =>
      refine ⟨fun ty dist => ?_, fun ry Ay ty _ => (by cases ty)⟩
      cases ty with
      | root single tym tyms tyqs =>
          cases c with
          | var_Chan cx =>
              obtain ⟨Θ1, Θ2, r1, A1, just, mrg, tyTerm2⟩ := close_parent_typed tym
              obtain ⟨C, tyChild, _, tyRest⟩ := ChildrenTyped.remove just mrg tyms rfl rfl
              exact Typed.root (PCtxSingle.split single mrg).2 tyTerm2 tyRest
                (SubtreesTyped.append tyqs
                  (.cons (TypedAt.close_detached_typed tyChild) .nil))
  | @nodeClose M N p c d l r ms' qs qs' =>
      refine ⟨fun ty _ => (by cases ty), fun ry Ay ty dist => ?_⟩
      cases ty with
      | @node _ x _ _ _ _ _ single has tym tyms tyqs =>
          cases c with
          | var_Chan cx =>
              obtain ⟨Θ1, Θ2, r1, A1, just, mrg, tyTerm2⟩ := close_parent_typed tym
              obtain ⟨C, tyChild, _, tyRest⟩ := ChildrenTypedAt.remove just mrg tyms rfl rfl
              have hne : cx ≠ x :=
                ChildrenTypedAt.label_ne_parent (c := Chan.var_Chan cx) tyms (by simp [childLabels])
              have has2 : PHas Θ2 x _ _ :=
                PHas.merge_inv_right mrg has ((just.pos_false).mpr hne)
              exact TypedAt.node (PCtxSingle.split single mrg).2 has2 tyTerm2 tyRest
                (SubtreesTyped.append tyqs
                  (.cons (TypedAt.close_detached_typed tyChild) .nil))
  | @rootSendEx M N v c d l r ms' qs qs' value =>
      refine ⟨fun ty dist => ?_, fun ry Ay ty _ => (by cases ty)⟩
      cases ty with
      | @root Θ0 _ _ _ single tym tyms tyqs =>
      cases c with
      | var_Chan cx =>
      cases d with
      | var_Chan dx =>
      -- parent term: peel the send redex and its payload
      obtain ⟨Θ1, Θ2, A0, mrg, tyApp, cont⟩ := evalCtx_inv tym
      obtain ⟨AS, BS, sS, ΘF, ΘV, ΔF, ΔV, mrgApp, mrgΔ, tySend, tyV, eqApp⟩ :=
        appEx_inv tyApp
      cases mrgΔ
      obtain ⟨rs1, rs2, AAs, BBs, xorS, eqPiS, tyvS⟩ := sendEx_inv tySend
      obtain ⟨rJS, AJS, jsF, tyAJS, eqChS⟩ := chan_inv tyvS
      rw [cren_len_nil] at eqChS
      obtain ⟨ers, eActS⟩ := Static.ch_inj eqChS
      subst ers
      have single1 := (PCtxSingle.split single mrg).1
      have single2 := (PCtxSingle.split single mrg).2
      have singleF := (PCtxSingle.split single1 mrgApp).1
      have singleV := (PCtxSingle.split single1 mrgApp).2
      -- select and invert the receiving child
      obtain ⟨ΘR, mrgV2, mrgFR⟩ := PMerge.splitR mrg mrgApp
      have singleR := (PCtxSingle.split single mrgFR.sym).2
      obtain ⟨C, tyChildAt, convC, tyRest⟩ :=
        ChildrenTyped.remove jsF mrgFR.sym tyms rfl rfl
      -- split the surviving children by the payload's endpoints
      obtain ⟨msV, ms2, tyMsV, tyMs2, hpermR⟩ := ChildrenTyped.split mrgV2 singleR tyRest
      obtain ⟨permSplit1, permSplit2⟩ :=
        split_children_perm (w := v) singleR mrgV2
          (fun p hp => ChildrenTyped.pos_of_label tyMs2 (List.mem_map.mpr ⟨p, hp, rfl⟩))
          (List.Nodup.of_map _ (ChildrenTyped.labels_nodup tyMsV))
          (List.Nodup.of_map _ (ChildrenTyped.labels_nodup tyMs2))
          hpermR (ChildrenTyped.labels_nodup tyRest)
          (fun p hp => tyV.occurs1
            (ChildrenTyped.pos_of_label tyMsV (List.mem_map.mpr ⟨p, hp, rfl⟩)))
          (fun i h => tyV.occurs0 h)
      cases tyChildAt with
      | @node Θc _ _ _ _ _ _ singleC hasD tyN tyms' tyqs' =>
      -- pad the child context and the payload context to a common length
      have tyNpad := Typed.padR Θ0.length tyN
      have tyms'pad := ChildrenTypedAt.padR Θ0.length tyms'
      have singleCpad : PCtxSingle (Θc ++ List.replicate Θ0.length Slot.none) :=
        PCtxSingle.append singleC (PCtxSingle.replicate _)
      have hasDpad := PHas.padR Θ0.length hasD
      have hLenCpad : (Θc ++ List.replicate Θ0.length Slot.none).length
          = Θc.length + Θ0.length := by simp
      obtain ⟨Θc1, Θc2, AR0, mrgR, tyRecv, contR⟩ := evalCtx_inv tyNpad
      obtain ⟨rr1, rr2, AAr, BBr, xorR, eqMR, tyvR⟩ := recvEx_inv tyRecv
      obtain ⟨rJR, AJR, jsR, tyAJR, eqChR⟩ := chan_inv tyvR
      rw [cren_len_nil] at eqChR
      obtain ⟨err, eActR⟩ := Static.ch_inj eqChR
      subst err
      obtain ⟨hrr, hAJR⟩ := PJust_PHas_agree singleCpad mrgR jsR hasDpad
      subst hrr
      -- session-protocol duality
      have eActR' : (Term.act rr2 AAr BBr .ex) ≃ C := by rw [← hAJR]; exact eActR
      have eSR := ARS.conv_trans eActS
        (ARS.conv_sym (ARS.conv_trans eActR' convC))
      obtain ⟨eAAsr, eBBsr, _, _⟩ := Static.act_inj eSR
      -- protocol typings and the advanced protocol `W`
      obtain ⟨_, tyChS⟩ := tyvS.validity
      obtain ⟨tyActS, _⟩ := Static.ch_inv tyChS
      have tyBBs := Static.act_inv tyActS
      obtain ⟨_, tyAAs⟩ : ∃ s, ([] : Static.Ctx) ⊢ AAs : Term.srt s := by
        cases tyBBs.wf with | cons _ h => exact ⟨_, h⟩
      obtain ⟨eAS, eBS, _, _⟩ := Static.pi_inj eqPiS
      have tyVA : ΘV ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ v : AAs :=
        Typed.conv eAS tyV tyAAs
      have tyW : ([] : Static.Ctx) ⊢ BBs[Chan.var_Chan; v..] : .proto := by
        have h := tyBBs.subst tyVA.toStatic
        asimp at h
        exact h
      -- Distinct-derived freshness of the moved endpoints
      have hnodup : (((l ++ (Chan.var_Chan cx,
            Tree.node (Chan.var_Chan dx) (N.eval (.recv (Term.chan (Chan.var_Chan dx)) .ex))
              ms' qs') :: r).map (fun e => chanIndex e.1)) ++
          childInteriors (l ++ (Chan.var_Chan cx,
            Tree.node (Chan.var_Chan dx) (N.eval (.recv (Term.chan (Chan.var_Chan dx)) .ex))
              ms' qs') :: r)).Nodup :=
        labelsInteriors_sublist_root.nodup dist
      have memChild : (Chan.var_Chan cx,
          Tree.node (Chan.var_Chan dx) (N.eval (.recv (Term.chan (Chan.var_Chan dx)) .ex))
            ms' qs') ∈ l ++ (Chan.var_Chan cx,
          Tree.node (Chan.var_Chan dx) (N.eval (.recv (Term.chan (Chan.var_Chan dx)) .ex))
            ms' qs') :: r := by simp
      have hdxFresh := child_node_label_fresh hnodup memChild
      have vLabel : ∀ i, CvarPos ΘV i true →
          Chan.var_Chan i ∈ childLabels (l ++ (Chan.var_Chan cx,
            Tree.node (Chan.var_Chan dx) (N.eval (.recv (Term.chan (Chan.var_Chan dx)) .ex))
              ms' qs') :: r) := fun i h =>
        ChildrenTyped.label_of_pos tyms
          (CvarPos.merge_true_left single mrg (CvarPos.merge_true_right single1 mrgApp h))
      -- the advanced child endpoint is dead in the child's continuation
      have posDx1 : CvarPos Θc1 dx true := (jsR.pos_true).mpr rfl
      have hD2dead : CvarPos Θc2 dx true → False := fun h =>
        PCtxSingle.merge_true_excl singleCpad mrgR posDx1 h
      have hlenC2 : dx < Θc2.length := by
        have h := CvarPos.lt_length (CvarPos.merge_true_left singleCpad mrgR posDx1)
        rw [hLenCpad] at h
        rw [PMerge.length_right mrgR, hLenCpad]
        omega
      -- live endpoints of the child's continuation are grandchild labels
      have cLabel : ∀ i, CvarPos Θc2 i true → Chan.var_Chan i ∈ childLabels ms' := by
        intro i h
        rcases ChildrenTypedAt.label_of_pos tyms'pad
            (CvarPos.merge_true_right singleCpad mrgR h) with hmem | hy
        · exact hmem
        · subst hy
          exact absurd h hD2dead
      -- assemble the child's new endpoint context
      have hLenΘc2 : Θc2.length = Θc.length + Θ0.length := by
        rw [PMerge.length_right mrgR, hLenCpad]
      have tyMsVpad := ChildrenTyped.padR Θc.length tyMsV
      have tyVApad := Typed.padR Θc.length tyVA
      have singleVpad : PCtxSingle (ΘV ++ List.replicate Θc.length Slot.none) :=
        PCtxSingle.append singleV (PCtxSingle.replicate _)
      have hLenV : ΘV.length = Θ0.length := by
        rw [PMerge.length_right mrgApp, PMerge.length_left mrg]
      obtain ⟨Θ3R, mrgPair, single3R⟩ :=
        pmerge_single_disjoint
          (Θ1 := ΘV ++ List.replicate Θc.length Slot.none)
          (Θ2 := oneCtx dx (!rs1) (BBs[Chan.var_Chan; v..]) (Θc.length + Θ0.length))
          (by simp [oneCtx]; omega)
          singleVpad (oneCtx_single _)
          (by
            intro i h1 h2
            have hdx : dx = i :=
              ((oneCtx_just (x := dx) (r := !rs1) (W := BBs[Chan.var_Chan; v..])
                (Θc.length + Θ0.length)).pos_true).mp h2
            subst hdx
            have hV : CvarPos ΘV dx true :=
              CvarPos.of_append_true (PEmpty.replicate _) h1
            exact hdxFresh (vLabel dx hV))
      have hLen3R : Θ3R.length = Θc.length + Θ0.length := by
        rw [← PMerge.length_left mrgPair]
        simp
        omega
      obtain ⟨Θc', mrgFinalC, singleC'⟩ :=
        pmerge_single_disjoint (Θ1 := Θ3R) (Θ2 := Θc2)
          (by rw [hLen3R, PMerge.length_right mrgR, hLenCpad])
          single3R (PCtxSingle.split singleCpad mrgR).2
          (by
            intro i h1 h2
            rcases CvarPos.split_true mrgPair h1 with ⟨_, hone⟩ | ⟨hV, _⟩
            · have hdx : dx = i :=
                ((oneCtx_just (x := dx) (r := !rs1) (W := BBs[Chan.var_Chan; v..])
                  (Θc.length + Θ0.length)).pos_true).mp hone
              subst hdx
              exact hD2dead h2
            · have hVi : CvarPos ΘV i true :=
                CvarPos.of_append_true (PEmpty.replicate _) hV
              have hmemV := vLabel i hVi
              have hmemC := cLabel i h2
              obtain ⟨⟨e, gc⟩, memPair, heq⟩ := List.mem_map.mp hmemC
              have he : e = Chan.var_Chan i := heq
              subst he
              exact (grandchild_fresh hnodup memChild memPair).2 hmemV)
      -- the child's continuation term
      obtain ⟨_, tyChR⟩ := tyvR.validity
      obtain ⟨tyActR, _⟩ := Static.ch_inv tyChR
      have tyBBr := Static.act_inv tyActR
      obtain ⟨_, tyAAr⟩ : ∃ s, ([] : Static.Ctx) ⊢ AAr : Term.srt s := by
        cases tyBBr.wf with | cons _ h => exact ⟨_, h⟩
      have tyMsgR : (ΘV ++ List.replicate Θc.length Slot.none) ⨾
          ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ v : AAr :=
        Typed.conv eAAsr tyVApad tyAAr
      obtain ⟨_, tyMAR0⟩ := tyRecv.validity
      have tyPairR : Θ3R ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢
          .pure (.pair v (.chan (Chan.var_Chan dx)) .ex .L) : .M AR0 := by
        refine Typed.conv (ARS.conv_sym eqMR) (.pure ?_) tyMAR0
        refine Typed.pairEx mrgPair .nil
          (Static.Typed.sig (fun _ => Static.sort_leq_Lgt) Static.sort_leq_Lgt tyAAr
            (Static.Typed.ch tyBBr))
          tyMsgR ?_
        refine Typed.conv (s := .L)
          (Static.conv_ch (Static.conv_subst (v..) eBBsr))
          (oneCtx_chan _ tyW ARS.Conv.refl tyW) ?_
        have h := Static.Typed.ch (b := !rs1) (tyBBr.subst tyMsgR.toStatic)
        asimp at h ⊢
        exact h
      have tyTermC := contR _ Θc' _ mrgFinalC.sym tyPairR
      -- the child's new children: continuation children plus the moved payload children
      have tyRest' := ChildrenTypedAt.strengthen jsR mrgR tyms'pad
      obtain ⟨ΘVc2, mrgVc2, mrgOne⟩ := PMerge.splitL mrgFinalC mrgPair
      have singleVc2 : PCtxSingle ΘVc2 := (PCtxSingle.split singleC' mrgOne).1
      obtain ⟨msC, tyMsC, hpermC⟩ :=
        ChildrenTyped.merge mrgVc2.sym singleVc2 tyRest' tyMsVpad
      have tymsAtC : ChildrenTypedAt Θc' dx (!rs1)
          (shiftK (dx + 1) (BBs[Chan.var_Chan; v..])) msC :=
        ChildrenTypedAt.intro (oneCtx_just _) mrgOne.sym singleC' tyMsC
      have hasD' : PHas Θc' dx (!rs1) (shiftK (dx + 1) (BBs[Chan.var_Chan; v..])) :=
        PHas.merge_left singleC' mrgOne.sym (PJust.toPHas (oneCtx_just _))
      have tyNode' : TypedAt (!rs1) (shiftK (dx + 1) (BBs[Chan.var_Chan; v..]))
          (.node (Chan.var_Chan dx)
            (N.eval (.pure (.pair v (.chan (Chan.var_Chan dx)) .ex .L))) msC qs') :=
        TypedAt.node singleC' hasD' tyTermC tymsAtC tyqs'
      -- the parent continuation: the advanced endpoint at `cx`
      have posCx1 : CvarPos Θ1 cx true :=
        CvarPos.merge_true_left single1 mrgApp ((jsF.pos_true).mpr rfl)
      have hlen2 : cx < Θ2.length := by
        have h := CvarPos.lt_length (CvarPos.merge_true_left single mrg posCx1)
        rw [PMerge.length_right mrg]
        omega
      have hC2dead : CvarPos Θ2 cx true → False := fun h =>
        PCtxSingle.merge_true_excl single mrg posCx1 h
      obtain ⟨Θ', mrgC, singleΘ'⟩ :=
        oneCtx_merge (Θ := Θ2) (x := cx) (r := rs1)
          (W := shiftK dx (BBs[Chan.var_Chan; v..])) single2 hlen2 hC2dead
      have tyChanC := oneCtx_chan (x := cx) (r := rs1)
        (W := shiftK dx (BBs[Chan.var_Chan; v..])) (B := BBs[Chan.var_Chan; v..])
        Θ2.length (shiftK_proto tyW dx) (shiftK_conv _ dx) tyW
      obtain ⟨_, tyMAS0⟩ := tyApp.validity
      have tyPureC : (oneCtx cx rs1 (shiftK dx (BBs[Chan.var_Chan; v..])) Θ2.length) ⨾
          ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢
          .pure (.chan (Chan.var_Chan cx)) : .M A0 := by
        refine Typed.conv ?_ (Typed.pure tyChanC) tyMAS0
        refine ARS.conv_sym (ARS.conv_trans eqApp ?_)
        exact Static.conv_subst (v..) eBS
      have tyTermP := cont _ Θ' _ mrgC.sym tyPureC
      -- reassemble the parent
      obtain ⟨msNew, tyMsNew, hpermNew⟩ :=
        ChildrenTyped.merge mrgC.sym singleΘ' tyMs2 (oneCtx_children _ tyNode')
      have hsim : sendExChildren v (Chan.var_Chan cx) (Chan.var_Chan dx) N ms' qs'
          (l ++ r) = insertChild (Chan.var_Chan cx)
            (.node (Chan.var_Chan dx)
              (N.eval (.pure (.pair v (.chan (Chan.var_Chan dx)) .ex .L)))
              (mergeChildren (splitChildrenByTerm v (l ++ r)).1 ms') qs')
            (splitChildrenByTerm v (l ++ r)).2 := by
        simp [sendExChildren]
      have sortedRest := ChildrenTyped.sorted tyRest
      have e1 : (splitChildrenByTerm v (l ++ r)).1 = msV :=
        child_sorted_eq permSplit1
          (List.Pairwise.sublist (splitChildrenByTerm_sublist₁ v (l ++ r)) sortedRest)
          (ChildrenTyped.sorted tyMsV)
      have e2 : (splitChildrenByTerm v (l ++ r)).2 = ms2 :=
        child_sorted_eq permSplit2
          (List.Pairwise.sublist (splitChildrenByTerm_sublist₂ v (l ++ r)) sortedRest)
          (ChildrenTyped.sorted tyMs2)
      have nodupVms' : (childLabels (msV ++ ms')).Nodup := by
        have h := (List.Perm.map Prod.fst hpermC).nodup
          (ChildrenTyped.labels_nodup tyMsC)
        exact ((List.perm_append_comm (l₁ := ms') (l₂ := msV)).map Prod.fst).nodup h
      have eC : mergeChildren msV ms' = msC :=
        child_sorted_eq
          ((mergeChildren_perm msV ms').trans
            (List.perm_append_comm.trans hpermC.symm))
          (sorted_mergeChildren (ChildrenTyped.sorted tyRest') nodupVms')
          (ChildrenTyped.sorted tyMsC)
      have freshC2 : ∀ p : Chan × Tree, p ∈ ms2 →
          chanIndex (Chan.var_Chan cx) ≠ chanIndex p.1 := by
        intro p hp he
        apply hC2dead
        have hpos := ChildrenTyped.pos_of_label tyMs2 (List.mem_map.mpr ⟨p, hp, rfl⟩)
        have he' : cx = chanIndex p.1 := he
        rw [← he'] at hpos
        exact hpos
      have eTop : insertChild (Chan.var_Chan cx)
          (.node (Chan.var_Chan dx)
            (N.eval (.pure (.pair v (.chan (Chan.var_Chan dx)) .ex .L))) msC qs')
          ms2 = msNew :=
        child_sorted_eq
          ((insertChild_perm _ _ _).trans
            ((List.perm_append_singleton _ _).symm.trans hpermNew.symm))
          (sorted_insertChild (ChildrenTyped.sorted tyMs2) freshC2)
          (ChildrenTyped.sorted tyMsNew)
      rw [hsim, e1, e2, eC, eTop]
      exact Typed.root singleΘ' tyTermP tyMsNew tyqs
  | @nodeSendEx M N p v c d l r ms' qs qs' value freshP =>
      refine ⟨fun ty _ => (by cases ty), fun ry Ay ty dist => ?_⟩
      cases ty with
      | @node Θ0 y _ _ _ _ _ single has tym tyms tyqs =>
      cases c with
      | var_Chan cx =>
      cases d with
      | var_Chan dx =>
      have freshP' : occurs y v = 0 := freshP
      -- parent term: peel the send redex and its payload
      obtain ⟨Θ1, Θ2, A0, mrg, tyApp, cont⟩ := evalCtx_inv tym
      obtain ⟨AS, BS, sS, ΘF, ΘV, ΔF, ΔV, mrgApp, mrgΔ, tySend, tyV, eqApp⟩ :=
        appEx_inv tyApp
      cases mrgΔ
      obtain ⟨rs1, rs2, AAs, BBs, xorS, eqPiS, tyvS⟩ := sendEx_inv tySend
      obtain ⟨rJS, AJS, jsF, tyAJS, eqChS⟩ := chan_inv tyvS
      rw [cren_len_nil] at eqChS
      obtain ⟨ers, eActS⟩ := Static.ch_inj eqChS
      subst ers
      have single1 := (PCtxSingle.split single mrg).1
      have single2 := (PCtxSingle.split single mrg).2
      have singleF := (PCtxSingle.split single1 mrgApp).1
      have singleV := (PCtxSingle.split single1 mrgApp).2
      -- select and invert the receiving child
      obtain ⟨ΘR, mrgV2, mrgFR⟩ := PMerge.splitR mrg mrgApp
      have singleR := (PCtxSingle.split single mrgFR.sym).2
      obtain ⟨C, tyChildAt, convC, tyRest⟩ :=
        ChildrenTypedAt.remove jsF mrgFR.sym tyms rfl rfl
      -- the reserved parent endpoint is fresh for the payload
      have posYV : CvarPos ΘV y false := by
        rcases PCtxSingle.pos_total singleV y with h | h
        · exact absurd (tyV.occurs1 h) (by omega)
        · exact h
      -- split the surviving children by the payload's endpoints
      obtain ⟨msV, ms2, tyMsV, tyMs2, hpermR⟩ :=
        ChildrenTypedAt.split_right mrgV2 singleR tyRest posYV
      obtain ⟨permSplit1, permSplit2⟩ :=
        split_children_perm (w := v) singleR mrgV2
          (fun p hp => ChildrenTypedAt.pos_of_label tyMs2 (List.mem_map.mpr ⟨p, hp, rfl⟩))
          (List.Nodup.of_map _ (ChildrenTyped.labels_nodup tyMsV))
          (List.Nodup.of_map _ (ChildrenTypedAt.labels_nodup tyMs2))
          hpermR (ChildrenTypedAt.labels_nodup tyRest)
          (fun p hp => tyV.occurs1
            (ChildrenTyped.pos_of_label tyMsV (List.mem_map.mpr ⟨p, hp, rfl⟩)))
          (fun i h => tyV.occurs0 h)
      cases tyChildAt with
      | @node Θc _ _ _ _ _ _ singleC hasD tyN tyms' tyqs' =>
      -- pad the child context and the payload context to a common length
      have tyNpad := Typed.padR Θ0.length tyN
      have tyms'pad := ChildrenTypedAt.padR Θ0.length tyms'
      have singleCpad : PCtxSingle (Θc ++ List.replicate Θ0.length Slot.none) :=
        PCtxSingle.append singleC (PCtxSingle.replicate _)
      have hasDpad := PHas.padR Θ0.length hasD
      have hLenCpad : (Θc ++ List.replicate Θ0.length Slot.none).length
          = Θc.length + Θ0.length := by simp
      obtain ⟨Θc1, Θc2, AR0, mrgR, tyRecv, contR⟩ := evalCtx_inv tyNpad
      obtain ⟨rr1, rr2, AAr, BBr, xorR, eqMR, tyvR⟩ := recvEx_inv tyRecv
      obtain ⟨rJR, AJR, jsR, tyAJR, eqChR⟩ := chan_inv tyvR
      rw [cren_len_nil] at eqChR
      obtain ⟨err, eActR⟩ := Static.ch_inj eqChR
      subst err
      obtain ⟨hrr, hAJR⟩ := PJust_PHas_agree singleCpad mrgR jsR hasDpad
      subst hrr
      -- session-protocol duality
      have eActR' : (Term.act rr2 AAr BBr .ex) ≃ C := by rw [← hAJR]; exact eActR
      have eSR := ARS.conv_trans eActS
        (ARS.conv_sym (ARS.conv_trans eActR' convC))
      obtain ⟨eAAsr, eBBsr, _, _⟩ := Static.act_inj eSR
      -- protocol typings and the advanced protocol `W`
      obtain ⟨_, tyChS⟩ := tyvS.validity
      obtain ⟨tyActS, _⟩ := Static.ch_inv tyChS
      have tyBBs := Static.act_inv tyActS
      obtain ⟨_, tyAAs⟩ : ∃ s, ([] : Static.Ctx) ⊢ AAs : Term.srt s := by
        cases tyBBs.wf with | cons _ h => exact ⟨_, h⟩
      obtain ⟨eAS, eBS, _, _⟩ := Static.pi_inj eqPiS
      have tyVA : ΘV ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ v : AAs :=
        Typed.conv eAS tyV tyAAs
      have tyW : ([] : Static.Ctx) ⊢ BBs[Chan.var_Chan; v..] : .proto := by
        have h := tyBBs.subst tyVA.toStatic
        asimp at h
        exact h
      -- Distinct-derived freshness of the moved endpoints
      have hnodup : (((l ++ (Chan.var_Chan cx,
            Tree.node (Chan.var_Chan dx) (N.eval (.recv (Term.chan (Chan.var_Chan dx)) .ex))
              ms' qs') :: r).map (fun e => chanIndex e.1)) ++
          childInteriors (l ++ (Chan.var_Chan cx,
            Tree.node (Chan.var_Chan dx) (N.eval (.recv (Term.chan (Chan.var_Chan dx)) .ex))
              ms' qs') :: r)).Nodup :=
        labelsInteriors_sublist_node.nodup dist
      have memChild : (Chan.var_Chan cx,
          Tree.node (Chan.var_Chan dx) (N.eval (.recv (Term.chan (Chan.var_Chan dx)) .ex))
            ms' qs') ∈ l ++ (Chan.var_Chan cx,
          Tree.node (Chan.var_Chan dx) (N.eval (.recv (Term.chan (Chan.var_Chan dx)) .ex))
            ms' qs') :: r := by simp
      have hdxFresh := child_node_label_fresh hnodup memChild
      have vLabel : ∀ i, CvarPos ΘV i true →
          Chan.var_Chan i ∈ childLabels (l ++ (Chan.var_Chan cx,
            Tree.node (Chan.var_Chan dx) (N.eval (.recv (Term.chan (Chan.var_Chan dx)) .ex))
              ms' qs') :: r) := by
        intro i h
        rcases ChildrenTypedAt.label_of_pos tyms
            (CvarPos.merge_true_left single mrg (CvarPos.merge_true_right single1 mrgApp h))
          with hmem | hy
        · exact hmem
        · subst hy
          exact absurd (tyV.occurs1 h) (by omega)
      -- the advanced child endpoint is dead in the child's continuation
      have posDx1 : CvarPos Θc1 dx true := (jsR.pos_true).mpr rfl
      have hD2dead : CvarPos Θc2 dx true → False := fun h =>
        PCtxSingle.merge_true_excl singleCpad mrgR posDx1 h
      have hlenC2 : dx < Θc2.length := by
        have h := CvarPos.lt_length (CvarPos.merge_true_left singleCpad mrgR posDx1)
        rw [hLenCpad] at h
        rw [PMerge.length_right mrgR, hLenCpad]
        omega
      -- live endpoints of the child's continuation are grandchild labels
      have cLabel : ∀ i, CvarPos Θc2 i true → Chan.var_Chan i ∈ childLabels ms' := by
        intro i h
        rcases ChildrenTypedAt.label_of_pos tyms'pad
            (CvarPos.merge_true_right singleCpad mrgR h) with hmem | hy
        · exact hmem
        · subst hy
          exact absurd h hD2dead
      -- assemble the child's new endpoint context
      have hLenΘc2 : Θc2.length = Θc.length + Θ0.length := by
        rw [PMerge.length_right mrgR, hLenCpad]
      have tyMsVpad := ChildrenTyped.padR Θc.length tyMsV
      have tyVApad := Typed.padR Θc.length tyVA
      have singleVpad : PCtxSingle (ΘV ++ List.replicate Θc.length Slot.none) :=
        PCtxSingle.append singleV (PCtxSingle.replicate _)
      have hLenV : ΘV.length = Θ0.length := by
        rw [PMerge.length_right mrgApp, PMerge.length_left mrg]
      obtain ⟨Θ3R, mrgPair, single3R⟩ :=
        pmerge_single_disjoint
          (Θ1 := ΘV ++ List.replicate Θc.length Slot.none)
          (Θ2 := oneCtx dx (!rs1) (BBs[Chan.var_Chan; v..]) (Θc.length + Θ0.length))
          (by simp [oneCtx]; omega)
          singleVpad (oneCtx_single _)
          (by
            intro i h1 h2
            have hdx : dx = i :=
              ((oneCtx_just (x := dx) (r := !rs1) (W := BBs[Chan.var_Chan; v..])
                (Θc.length + Θ0.length)).pos_true).mp h2
            subst hdx
            have hV : CvarPos ΘV dx true :=
              CvarPos.of_append_true (PEmpty.replicate _) h1
            exact hdxFresh (vLabel dx hV))
      have hLen3R : Θ3R.length = Θc.length + Θ0.length := by
        rw [← PMerge.length_left mrgPair]
        simp
        omega
      obtain ⟨Θc', mrgFinalC, singleC'⟩ :=
        pmerge_single_disjoint (Θ1 := Θ3R) (Θ2 := Θc2)
          (by rw [hLen3R, PMerge.length_right mrgR, hLenCpad])
          single3R (PCtxSingle.split singleCpad mrgR).2
          (by
            intro i h1 h2
            rcases CvarPos.split_true mrgPair h1 with ⟨_, hone⟩ | ⟨hV, _⟩
            · have hdx : dx = i :=
                ((oneCtx_just (x := dx) (r := !rs1) (W := BBs[Chan.var_Chan; v..])
                  (Θc.length + Θ0.length)).pos_true).mp hone
              subst hdx
              exact hD2dead h2
            · have hVi : CvarPos ΘV i true :=
                CvarPos.of_append_true (PEmpty.replicate _) hV
              have hmemV := vLabel i hVi
              have hmemC := cLabel i h2
              obtain ⟨⟨e, gc⟩, memPair, heq⟩ := List.mem_map.mp hmemC
              have he : e = Chan.var_Chan i := heq
              subst he
              exact (grandchild_fresh hnodup memChild memPair).2 hmemV)
      -- the child's continuation term
      obtain ⟨_, tyChR⟩ := tyvR.validity
      obtain ⟨tyActR, _⟩ := Static.ch_inv tyChR
      have tyBBr := Static.act_inv tyActR
      obtain ⟨_, tyAAr⟩ : ∃ s, ([] : Static.Ctx) ⊢ AAr : Term.srt s := by
        cases tyBBr.wf with | cons _ h => exact ⟨_, h⟩
      have tyMsgR : (ΘV ++ List.replicate Θc.length Slot.none) ⨾
          ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ v : AAr :=
        Typed.conv eAAsr tyVApad tyAAr
      obtain ⟨_, tyMAR0⟩ := tyRecv.validity
      have tyPairR : Θ3R ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢
          .pure (.pair v (.chan (Chan.var_Chan dx)) .ex .L) : .M AR0 := by
        refine Typed.conv (ARS.conv_sym eqMR) (.pure ?_) tyMAR0
        refine Typed.pairEx mrgPair .nil
          (Static.Typed.sig (fun _ => Static.sort_leq_Lgt) Static.sort_leq_Lgt tyAAr
            (Static.Typed.ch tyBBr))
          tyMsgR ?_
        refine Typed.conv (s := .L)
          (Static.conv_ch (Static.conv_subst (v..) eBBsr))
          (oneCtx_chan _ tyW ARS.Conv.refl tyW) ?_
        have h := Static.Typed.ch (b := !rs1) (tyBBr.subst tyMsgR.toStatic)
        asimp at h ⊢
        exact h
      have tyTermC := contR _ Θc' _ mrgFinalC.sym tyPairR
      -- the child's new children: continuation children plus the moved payload children
      have tyRest' := ChildrenTypedAt.strengthen jsR mrgR tyms'pad
      obtain ⟨ΘVc2, mrgVc2, mrgOne⟩ := PMerge.splitL mrgFinalC mrgPair
      have singleVc2 : PCtxSingle ΘVc2 := (PCtxSingle.split singleC' mrgOne).1
      obtain ⟨msC, tyMsC, hpermC⟩ :=
        ChildrenTyped.merge mrgVc2.sym singleVc2 tyRest' tyMsVpad
      have tymsAtC : ChildrenTypedAt Θc' dx (!rs1)
          (shiftK (dx + 1) (BBs[Chan.var_Chan; v..])) msC :=
        ChildrenTypedAt.intro (oneCtx_just _) mrgOne.sym singleC' tyMsC
      have hasD' : PHas Θc' dx (!rs1) (shiftK (dx + 1) (BBs[Chan.var_Chan; v..])) :=
        PHas.merge_left singleC' mrgOne.sym (PJust.toPHas (oneCtx_just _))
      have tyNode' : TypedAt (!rs1) (shiftK (dx + 1) (BBs[Chan.var_Chan; v..]))
          (.node (Chan.var_Chan dx)
            (N.eval (.pure (.pair v (.chan (Chan.var_Chan dx)) .ex .L))) msC qs') :=
        TypedAt.node singleC' hasD' tyTermC tymsAtC tyqs'
      -- the parent continuation: the advanced endpoint at `cx`
      have posCx1 : CvarPos Θ1 cx true :=
        CvarPos.merge_true_left single1 mrgApp ((jsF.pos_true).mpr rfl)
      have hlen2 : cx < Θ2.length := by
        have h := CvarPos.lt_length (CvarPos.merge_true_left single mrg posCx1)
        rw [PMerge.length_right mrg]
        omega
      have hC2dead : CvarPos Θ2 cx true → False := fun h =>
        PCtxSingle.merge_true_excl single mrg posCx1 h
      obtain ⟨Θ', mrgC, singleΘ'⟩ :=
        oneCtx_merge (Θ := Θ2) (x := cx) (r := rs1)
          (W := shiftK dx (BBs[Chan.var_Chan; v..])) single2 hlen2 hC2dead
      have tyChanC := oneCtx_chan (x := cx) (r := rs1)
        (W := shiftK dx (BBs[Chan.var_Chan; v..])) (B := BBs[Chan.var_Chan; v..])
        Θ2.length (shiftK_proto tyW dx) (shiftK_conv _ dx) tyW
      obtain ⟨_, tyMAS0⟩ := tyApp.validity
      have tyPureC : (oneCtx cx rs1 (shiftK dx (BBs[Chan.var_Chan; v..])) Θ2.length) ⨾
          ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢
          .pure (.chan (Chan.var_Chan cx)) : .M A0 := by
        refine Typed.conv ?_ (Typed.pure tyChanC) tyMAS0
        refine ARS.conv_sym (ARS.conv_trans eqApp ?_)
        exact Static.conv_subst (v..) eBS
      have tyTermP := cont _ Θ' _ mrgC.sym tyPureC
      -- the reserved parent endpoint survives into the final context
      have hcy : cx ≠ y :=
        ChildrenTypedAt.label_ne_parent (c := Chan.var_Chan cx) tyms
          (by simp [childLabels])
      have posYF : CvarPos ΘF y false := (jsF.pos_false).mpr hcy
      have posY1 : CvarPos Θ1 y false := CvarPos.merge_false mrgApp posYF posYV
      have hasY : PHas Θ' y ry Ay :=
        PHas.merge_right singleΘ' mrgC (PHas.merge_inv_right mrg has posY1)
      -- reassemble the parent
      obtain ⟨msNew, tyMsNew, hpermNew⟩ :=
        ChildrenTypedAt.merge mrgC.sym singleΘ' tyMs2 (oneCtx_children _ tyNode')
      have hsim : sendExChildren v (Chan.var_Chan cx) (Chan.var_Chan dx) N ms' qs'
          (l ++ r) = insertChild (Chan.var_Chan cx)
            (.node (Chan.var_Chan dx)
              (N.eval (.pure (.pair v (.chan (Chan.var_Chan dx)) .ex .L)))
              (mergeChildren (splitChildrenByTerm v (l ++ r)).1 ms') qs')
            (splitChildrenByTerm v (l ++ r)).2 := by
        simp [sendExChildren]
      have sortedRest := ChildrenTypedAt.sorted tyRest
      have e1 : (splitChildrenByTerm v (l ++ r)).1 = msV :=
        child_sorted_eq permSplit1
          (List.Pairwise.sublist (splitChildrenByTerm_sublist₁ v (l ++ r)) sortedRest)
          (ChildrenTyped.sorted tyMsV)
      have e2 : (splitChildrenByTerm v (l ++ r)).2 = ms2 :=
        child_sorted_eq permSplit2
          (List.Pairwise.sublist (splitChildrenByTerm_sublist₂ v (l ++ r)) sortedRest)
          (ChildrenTypedAt.sorted tyMs2)
      have nodupVms' : (childLabels (msV ++ ms')).Nodup := by
        have h := (List.Perm.map Prod.fst hpermC).nodup
          (ChildrenTyped.labels_nodup tyMsC)
        exact ((List.perm_append_comm (l₁ := ms') (l₂ := msV)).map Prod.fst).nodup h
      have eC : mergeChildren msV ms' = msC :=
        child_sorted_eq
          ((mergeChildren_perm msV ms').trans
            (List.perm_append_comm.trans hpermC.symm))
          (sorted_mergeChildren (ChildrenTyped.sorted tyRest') nodupVms')
          (ChildrenTyped.sorted tyMsC)
      have freshC2 : ∀ p : Chan × Tree, p ∈ ms2 →
          chanIndex (Chan.var_Chan cx) ≠ chanIndex p.1 := by
        intro p hp he
        apply hC2dead
        have hpos := ChildrenTypedAt.pos_of_label tyMs2 (List.mem_map.mpr ⟨p, hp, rfl⟩)
        have he' : cx = chanIndex p.1 := he
        rw [← he'] at hpos
        exact hpos
      have eTop : insertChild (Chan.var_Chan cx)
          (.node (Chan.var_Chan dx)
            (N.eval (.pure (.pair v (.chan (Chan.var_Chan dx)) .ex .L))) msC qs')
          ms2 = msNew :=
        child_sorted_eq
          ((insertChild_perm _ _ _).trans
            ((List.perm_append_singleton _ _).symm.trans hpermNew.symm))
          (sorted_insertChild (ChildrenTypedAt.sorted tyMs2) freshC2)
          (ChildrenTypedAt.sorted tyMsNew)
      rw [hsim, e1, e2, eC, eTop]
      exact TypedAt.node singleΘ' hasY tyTermP tyMsNew tyqs
  | @rootRecvEx M N v c d l r ms' qs qs' value =>
      refine ⟨fun ty dist => ?_, fun ry Ay ty _ => (by cases ty)⟩
      cases ty with
      | @root Θ0 _ _ _ single tym tyms tyqs =>
      cases c with
      | var_Chan cx =>
      cases d with
      | var_Chan dx =>
      -- select the sending child by its slot position (before fixing the padding)
      have posC : CvarPos Θ0 cx true :=
        ChildrenTyped.pos_of_label tyms (by simp [childLabels])
      obtain ⟨r0, A0', hasP0⟩ := CvarPos.toPHas posC
      obtain ⟨C, tyChildAt, convC, tyRest⟩ :=
        ChildrenTyped.remove (PHas.eraseExcept hasP0) (pmerge_eraseExcept Θ0 cx) tyms rfl rfl
      cases tyChildAt with
      | @node Θc _ _ _ _ _ _ singleC hasD tyN tyms' tyqs' =>
      -- parent term: peel the recv redex over the padded context
      have tympad := Typed.padR Θc.length tym
      have tymspad := ChildrenTyped.padR Θc.length tyms
      have singlepad : PCtxSingle (Θ0 ++ List.replicate Θc.length Slot.none) :=
        PCtxSingle.append single (PCtxSingle.replicate _)
      have hLenPad : (Θ0 ++ List.replicate Θc.length Slot.none).length
          = Θ0.length + Θc.length := by simp
      obtain ⟨Θ1, Θ2, A0, mrg, tyRecv, cont⟩ := evalCtx_inv tympad
      obtain ⟨rr1, rr2, AAr, BBr, xorR, eqMR, tyvR⟩ := recvEx_inv tyRecv
      obtain ⟨rJR, AJR, jsP, tyAJR, eqChR⟩ := chan_inv tyvR
      rw [cren_len_nil] at eqChR
      obtain ⟨err, eActR⟩ := Static.ch_inj eqChR
      subst err
      -- link the term-side lookup with the position-based extraction
      obtain ⟨hr0, hA0⟩ :=
        PJust_PHas_agree singlepad mrg jsP (PHas.padR Θc.length hasP0)
      subst hr0
      have hCA : C ≃ AJR := by rw [hA0]; exact convC
      -- the continuation context is the erased complement
      have hΘ2 : Θ2 = eraseAt Θ0 cx ++ List.replicate Θc.length Slot.none := by
        rw [PJust_merge_eq singlepad jsP mrg,
          eraseAt_append _ Θ0 cx (CvarPos.lt_length posC)]
      have tyRestPad : ChildrenTyped Θ2 (l ++ r) := by
        rw [hΘ2]
        exact ChildrenTyped.padR _ tyRest
      -- child term: peel the send redex and its payload over the padded context
      have tyNpad := Typed.padR Θ0.length tyN
      have tyms'pad := ChildrenTypedAt.padR Θ0.length tyms'
      have singleCpad : PCtxSingle (Θc ++ List.replicate Θ0.length Slot.none) :=
        PCtxSingle.append singleC (PCtxSingle.replicate _)
      have hasDpad := PHas.padR Θ0.length hasD
      have hLenCpad : (Θc ++ List.replicate Θ0.length Slot.none).length
          = Θc.length + Θ0.length := by simp
      obtain ⟨Θc1, Θc2, AR0, mrgR, tyAppC, contR⟩ := evalCtx_inv tyNpad
      obtain ⟨AS, BS, sS, ΘFc, ΘVc, ΔF, ΔV, mrgAppC, mrgΔ, tySend, tyV, eqApp⟩ :=
        appEx_inv tyAppC
      cases mrgΔ
      obtain ⟨rs1, rs2, AAs, BBs, xorS, eqPiS, tyvS⟩ := sendEx_inv tySend
      obtain ⟨rJS, AJS, jsC, tyAJS, eqChS⟩ := chan_inv tyvS
      rw [cren_len_nil] at eqChS
      obtain ⟨ers, eActS⟩ := Static.ch_inj eqChS
      subst ers
      have singleC1 := (PCtxSingle.split singleCpad mrgR).1
      have singleC2 := (PCtxSingle.split singleCpad mrgR).2
      have singleFc := (PCtxSingle.split singleC1 mrgAppC).1
      have singleVc := (PCtxSingle.split singleC1 mrgAppC).2
      obtain ⟨ΘRc, mrgVcC2, mrgFRc⟩ := PMerge.splitR mrgR mrgAppC
      obtain ⟨hrr2, hAJS⟩ := PJust_PHas_agree singleCpad mrgFRc.sym jsC hasDpad
      subst hrr2
      -- session-protocol duality
      have eActS' : (Term.act rs2 AAs BBs .ex) ≃ C := by rw [← hAJS]; exact eActS
      have eSR := ARS.conv_trans eActS' (ARS.conv_trans hCA (ARS.conv_sym eActR))
      obtain ⟨eAAsr, eBBsr, _, _⟩ := Static.act_inj eSR
      -- protocol typings and the advanced protocol `W`
      obtain ⟨_, tyChS⟩ := tyvS.validity
      obtain ⟨tyActS, _⟩ := Static.ch_inv tyChS
      have tyBBs := Static.act_inv tyActS
      obtain ⟨_, tyAAs⟩ : ∃ s, ([] : Static.Ctx) ⊢ AAs : Term.srt s := by
        cases tyBBs.wf with | cons _ h => exact ⟨_, h⟩
      obtain ⟨eAS, eBS, _, _⟩ := Static.pi_inj eqPiS
      have tyVA : ΘVc ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ v : AAs :=
        Typed.conv eAS tyV tyAAs
      have tyW : ([] : Static.Ctx) ⊢ BBs[Chan.var_Chan; v..] : .proto := by
        have h := tyBBs.subst tyVA.toStatic
        asimp at h
        exact h
      -- split the child's children by the payload's endpoints
      have posDxC1 : CvarPos Θc1 dx true :=
        CvarPos.merge_true_left singleC1 mrgAppC ((jsC.pos_true).mpr rfl)
      have hD2dead : CvarPos Θc2 dx true → False := fun h =>
        PCtxSingle.merge_true_excl singleCpad mrgR posDxC1 h
      have posDxC2 : CvarPos Θc2 dx false := by
        rcases PCtxSingle.pos_total singleC2 dx with h | h
        · exact absurd h hD2dead
        · exact h
      obtain ⟨msL, msR, tyMsL, tyMsRAt, hpermMs'⟩ :=
        ChildrenTypedAt.split_right mrgR.sym singleCpad tyms'pad posDxC2
      have tyMsR : ChildrenTyped ΘVc msR :=
        ChildrenTypedAt.strengthen jsC mrgAppC tyMsRAt
      obtain ⟨permSplit1, permSplit2⟩ :=
        split_children_perm (w := v) singleCpad mrgR
          (fun p hp => ChildrenTyped.pos_of_label tyMsL (List.mem_map.mpr ⟨p, hp, rfl⟩))
          (List.Nodup.of_map _ (ChildrenTypedAt.labels_nodup tyMsRAt))
          (List.Nodup.of_map _ (ChildrenTyped.labels_nodup tyMsL))
          (hpermMs'.trans List.perm_append_comm)
          (ChildrenTypedAt.labels_nodup tyms'pad)
          (fun p hp => by
            rcases p with ⟨pc, pt⟩
            cases pc with
            | var_Chan px =>
                have hpos := ChildrenTypedAt.pos_of_label tyMsRAt
                  (List.mem_map.mpr ⟨(Chan.var_Chan px, pt), hp, rfl⟩)
                have h1 := tyAppC.occurs1 hpos
                have hne := ChildrenTypedAt.label_ne_parent tyMsRAt
                  (List.mem_map.mpr ⟨(Chan.var_Chan px, pt), hp, rfl⟩)
                simp only [chanIndex] at h1 hne ⊢
                simp only [occurs] at h1 ⊢
                rw [if_neg (fun h => hne h.symm)] at h1
                omega)
          (fun i h => by
            have h0 := tyAppC.occurs0 h
            simp only [occurs] at h0 ⊢
            omega)
      -- Distinct-derived freshness of the moved endpoints
      have hnodup : (((l ++ (Chan.var_Chan cx,
            Tree.node (Chan.var_Chan dx)
              (N.eval (.app (.send (Term.chan (Chan.var_Chan dx)) .ex) v .ex))
              ms' qs') :: r).map (fun e => chanIndex e.1)) ++
          childInteriors (l ++ (Chan.var_Chan cx,
            Tree.node (Chan.var_Chan dx)
              (N.eval (.app (.send (Term.chan (Chan.var_Chan dx)) .ex) v .ex))
              ms' qs') :: r)).Nodup :=
        labelsInteriors_sublist_root.nodup dist
      have memChild : (Chan.var_Chan cx,
          Tree.node (Chan.var_Chan dx)
            (N.eval (.app (.send (Term.chan (Chan.var_Chan dx)) .ex) v .ex))
            ms' qs') ∈ l ++ (Chan.var_Chan cx,
          Tree.node (Chan.var_Chan dx)
            (N.eval (.app (.send (Term.chan (Chan.var_Chan dx)) .ex) v .ex))
            ms' qs') :: r := by simp
      -- live payload endpoints are grandchild labels
      have vcLabel : ∀ i, CvarPos ΘVc i true → Chan.var_Chan i ∈ childLabels ms' := by
        intro i h
        have hC1 : CvarPos Θc1 i true := CvarPos.merge_true_right singleC1 mrgAppC h
        rcases ChildrenTypedAt.label_of_pos tyms'pad
            (CvarPos.merge_true_left singleCpad mrgR hC1) with hmem | hy
        · exact hmem
        · subst hy
          exact (PCtxSingle.merge_true_excl singleC1 mrgAppC
            ((jsC.pos_true).mpr rfl) h).elim
      -- rebuild the child: return the advanced endpoint
      have hlenC2 : dx < Θc2.length := by
        have h := CvarPos.lt_length (CvarPos.merge_true_left singleCpad mrgR posDxC1)
        rw [hLenCpad] at h
        rw [PMerge.length_right mrgR, hLenCpad]
        omega
      obtain ⟨Θc', mrgD', singleC'⟩ :=
        oneCtx_merge (Θ := Θc2) (x := dx) (r := !rr1)
          (W := BBs[Chan.var_Chan; v..]) singleC2 hlenC2 hD2dead
      have tyChanD := oneCtx_chan (x := dx) (r := !rr1)
        (W := BBs[Chan.var_Chan; v..]) (B := BBs[Chan.var_Chan; v..])
        Θc2.length tyW ARS.Conv.refl tyW
      obtain ⟨_, tyMAS0⟩ := tyAppC.validity
      have tyPureD : (oneCtx dx (!rr1) (BBs[Chan.var_Chan; v..]) Θc2.length) ⨾
          ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢
          .pure (.chan (Chan.var_Chan dx)) : .M AR0 := by
        refine Typed.conv ?_ (Typed.pure tyChanD) tyMAS0
        refine ARS.conv_sym (ARS.conv_trans eqApp ?_)
        exact Static.conv_subst (v..) eBS
      have tyTermC := contR _ Θc' _ mrgD'.sym tyPureD
      have tymsAtC :=
        ChildrenTypedAt.intro (oneCtx_just Θc2.length) mrgD' singleC' tyMsL
      have hasD' : PHas Θc' dx (!rr1) (shiftK (dx + 1) (BBs[Chan.var_Chan; v..])) :=
        PHas.merge_left singleC' mrgD' (PJust.toPHas (oneCtx_just _))
      have tyNodeC : TypedAt (!rr1) (shiftK (dx + 1) (BBs[Chan.var_Chan; v..]))
          (.node (Chan.var_Chan dx)
            (N.eval (.pure (.chan (Chan.var_Chan dx)))) msL qs') :=
        TypedAt.node singleC' hasD' tyTermC tymsAtC tyqs'
      -- rebuild the parent: receive the pair with the moved payload resources
      have posCx1 : CvarPos Θ1 cx true := (jsP.pos_true).mpr rfl
      have hlen2 : cx < Θ2.length := by
        have h := CvarPos.lt_length (CvarPos.merge_true_left singlepad mrg posCx1)
        rw [hLenPad] at h
        rw [PMerge.length_right mrg, hLenPad]
        omega
      have hC2dead : CvarPos Θ2 cx true → False := fun h =>
        PCtxSingle.merge_true_excl singlepad mrg posCx1 h
      have hLenVc : ΘVc.length = Θc.length + Θ0.length := by
        rw [PMerge.length_right mrgAppC, PMerge.length_left mrgR, hLenCpad]
      have hLenΘ2 : Θ2.length = Θ0.length + Θc.length := by
        rw [PMerge.length_right mrg, hLenPad]
      obtain ⟨Θ3P, mrgPairP, single3P⟩ :=
        pmerge_single_disjoint (Θ1 := ΘVc)
          (Θ2 := oneCtx cx rr1 (shiftK dx (BBs[Chan.var_Chan; v..])) Θ2.length)
          (by simp [oneCtx]; omega)
          singleVc (oneCtx_single _)
          (by
            intro i h1 h2
            have hcx : cx = i :=
              ((oneCtx_just (x := cx) (r := rr1)
                (W := shiftK dx (BBs[Chan.var_Chan; v..])) Θ2.length).pos_true).mp h2
            subst hcx
            have hmemC := vcLabel cx h1
            obtain ⟨⟨e, gc⟩, memPair, heq⟩ := List.mem_map.mp hmemC
            have he : e = Chan.var_Chan cx := heq
            subst he
            exact (grandchild_fresh hnodup memChild memPair).2
              (by simp [childLabels]))
      have hLen3P : Θ3P.length = Θ2.length := by
        rw [← PMerge.length_left mrgPairP]
        omega
      obtain ⟨Θ', mrgFinalP, singleΘ'⟩ :=
        pmerge_single_disjoint (Θ1 := Θ3P) (Θ2 := Θ2) hLen3P single3P
          (PCtxSingle.split singlepad mrg).2
          (by
            intro i h1 h2
            rcases CvarPos.split_true mrgPairP h1 with ⟨_, hone⟩ | ⟨hV, _⟩
            · have hcx : cx = i :=
                ((oneCtx_just (x := cx) (r := rr1)
                  (W := shiftK dx (BBs[Chan.var_Chan; v..])) Θ2.length).pos_true).mp hone
              subst hcx
              exact hC2dead h2
            · have hmemC := vcLabel i hV
              obtain ⟨⟨e, gc⟩, memPair, heq⟩ := List.mem_map.mp hmemC
              have he : e = Chan.var_Chan i := heq
              subst he
              have hmemP : Chan.var_Chan i ∈ childLabels (l ++ (Chan.var_Chan cx,
                  Tree.node (Chan.var_Chan dx)
                    (N.eval (.app (.send (Term.chan (Chan.var_Chan dx)) .ex) v .ex))
                    ms' qs') :: r) :=
                ChildrenTyped.label_of_pos tymspad
                  (CvarPos.merge_true_right singlepad mrg h2)
              exact (grandchild_fresh hnodup memChild memPair).2 hmemP)
      -- the parent's received pair
      obtain ⟨_, tyChR⟩ := tyvR.validity
      obtain ⟨tyActR, _⟩ := Static.ch_inv tyChR
      have tyBBr := Static.act_inv tyActR
      obtain ⟨_, tyAAr⟩ : ∃ s, ([] : Static.Ctx) ⊢ AAr : Term.srt s := by
        cases tyBBr.wf with | cons _ h => exact ⟨_, h⟩
      have tyMsgR : ΘVc ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ v : AAr :=
        Typed.conv eAAsr tyVA tyAAr
      obtain ⟨_, tyMAR0⟩ := tyRecv.validity
      have tyPairP : Θ3P ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢
          .pure (.pair v (.chan (Chan.var_Chan cx)) .ex .L) : .M A0 := by
        refine Typed.conv (ARS.conv_sym eqMR) (.pure ?_) tyMAR0
        refine Typed.pairEx mrgPairP .nil
          (Static.Typed.sig (fun _ => Static.sort_leq_Lgt) Static.sort_leq_Lgt tyAAr
            (Static.Typed.ch tyBBr))
          tyMsgR ?_
        refine Typed.conv (s := .L)
          (Static.conv_ch (Static.conv_subst (v..) eBBsr))
          (oneCtx_chan _ (shiftK_proto tyW dx) (shiftK_conv _ dx) tyW) ?_
        have h := Static.Typed.ch (b := rr1) (tyBBr.subst tyMsgR.toStatic)
        asimp at h ⊢
        exact h
      have tyTermP := cont _ Θ' _ mrgFinalP.sym tyPairP
      -- the parent's new children
      obtain ⟨Θmid, mrgVc2P, mrgOneP⟩ := PMerge.splitL mrgFinalP mrgPairP
      have singleMid : PCtxSingle Θmid := (PCtxSingle.split singleΘ' mrgOneP).1
      obtain ⟨msMid, tyMsMid, hpermMid⟩ :=
        ChildrenTyped.merge mrgVc2P.sym singleMid tyRestPad tyMsR
      obtain ⟨msNew, tyMsNew, hpermNew⟩ :=
        ChildrenTyped.merge mrgOneP singleΘ' tyMsMid (oneCtx_children _ tyNodeC)
      have hsim : recvExChildren v (Chan.var_Chan cx) (Chan.var_Chan dx) N ms' qs'
          (l ++ r) = insertChild (Chan.var_Chan cx)
            (.node (Chan.var_Chan dx) (N.eval (.pure (.chan (Chan.var_Chan dx))))
              (splitChildrenByTerm v ms').2 qs')
            (mergeChildren (splitChildrenByTerm v ms').1 (l ++ r)) := by
        simp [recvExChildren]
      have sortedMs' := ChildrenTypedAt.sorted tyms'
      have e1 : (splitChildrenByTerm v ms').1 = msR :=
        child_sorted_eq permSplit1
          (List.Pairwise.sublist (splitChildrenByTerm_sublist₁ v ms') sortedMs')
          (ChildrenTyped.sorted tyMsR)
      have e2 : (splitChildrenByTerm v ms').2 = msL :=
        child_sorted_eq permSplit2
          (List.Pairwise.sublist (splitChildrenByTerm_sublist₂ v ms') sortedMs')
          (ChildrenTyped.sorted tyMsL)
      have nodupRLR : (childLabels (msR ++ (l ++ r))).Nodup := by
        have h := (List.Perm.map Prod.fst hpermMid).nodup
          (ChildrenTyped.labels_nodup tyMsMid)
        exact ((List.perm_append_comm (l₁ := l ++ r) (l₂ := msR)).map Prod.fst).nodup h
      have eMid : mergeChildren msR (l ++ r) = msMid :=
        child_sorted_eq
          ((mergeChildren_perm msR (l ++ r)).trans
            (List.perm_append_comm.trans hpermMid.symm))
          (sorted_mergeChildren (ChildrenTyped.sorted tyRestPad) nodupRLR)
          (ChildrenTyped.sorted tyMsMid)
      have freshMid : ∀ p : Chan × Tree, p ∈ msMid →
          chanIndex (Chan.var_Chan cx) ≠ chanIndex p.1 := by
        intro p hp he
        have hpos := ChildrenTyped.pos_of_label tyMsMid (List.mem_map.mpr ⟨p, hp, rfl⟩)
        have he' : cx = chanIndex p.1 := he
        rw [← he'] at hpos
        rcases CvarPos.split_true mrgVc2P hpos with ⟨_, h2⟩ | ⟨hV, _⟩
        · exact hC2dead h2
        · have hmemC := vcLabel cx hV
          obtain ⟨⟨e, gc⟩, memPair, heq⟩ := List.mem_map.mp hmemC
          have hee : e = Chan.var_Chan cx := heq
          subst hee
          exact (grandchild_fresh hnodup memChild memPair).2 (by simp [childLabels])
      have eTop : insertChild (Chan.var_Chan cx)
          (.node (Chan.var_Chan dx) (N.eval (.pure (.chan (Chan.var_Chan dx))))
            msL qs') msMid = msNew :=
        child_sorted_eq
          ((insertChild_perm _ _ _).trans
            ((List.perm_append_singleton _ _).symm.trans hpermNew.symm))
          (sorted_insertChild (ChildrenTyped.sorted tyMsMid) freshMid)
          (ChildrenTyped.sorted tyMsNew)
      rw [hsim, e1, e2, eMid, eTop]
      exact Typed.root singleΘ' tyTermP tyMsNew tyqs
  | @nodeRecvEx M N p v c d l r ms' qs qs' value =>
      refine ⟨fun ty _ => (by cases ty), fun ry Ay ty dist => ?_⟩
      cases ty with
      | @node Θ0 y _ _ _ _ _ single has tym tyms tyqs =>
      cases c with
      | var_Chan cx =>
      cases d with
      | var_Chan dx =>
      -- select the sending child by its slot position (before fixing the padding)
      have posC : CvarPos Θ0 cx true :=
        ChildrenTypedAt.pos_of_label tyms (by simp [childLabels])
      obtain ⟨r0, A0', hasP0⟩ := CvarPos.toPHas posC
      obtain ⟨C, tyChildAt, convC, tyRest⟩ :=
        ChildrenTypedAt.remove (PHas.eraseExcept hasP0) (pmerge_eraseExcept Θ0 cx) tyms rfl rfl
      cases tyChildAt with
      | @node Θc _ _ _ _ _ _ singleC hasD tyN tyms' tyqs' =>
      -- parent term: peel the recv redex over the padded context
      have tympad := Typed.padR Θc.length tym
      have tymspad := ChildrenTypedAt.padR Θc.length tyms
      have singlepad : PCtxSingle (Θ0 ++ List.replicate Θc.length Slot.none) :=
        PCtxSingle.append single (PCtxSingle.replicate _)
      have hLenPad : (Θ0 ++ List.replicate Θc.length Slot.none).length
          = Θ0.length + Θc.length := by simp
      obtain ⟨Θ1, Θ2, A0, mrg, tyRecv, cont⟩ := evalCtx_inv tympad
      obtain ⟨rr1, rr2, AAr, BBr, xorR, eqMR, tyvR⟩ := recvEx_inv tyRecv
      obtain ⟨rJR, AJR, jsP, tyAJR, eqChR⟩ := chan_inv tyvR
      rw [cren_len_nil] at eqChR
      obtain ⟨err, eActR⟩ := Static.ch_inj eqChR
      subst err
      -- link the term-side lookup with the position-based extraction
      obtain ⟨hr0, hA0⟩ :=
        PJust_PHas_agree singlepad mrg jsP (PHas.padR Θc.length hasP0)
      subst hr0
      have hCA : C ≃ AJR := by rw [hA0]; exact convC
      -- the continuation context is the erased complement
      have hΘ2 : Θ2 = eraseAt Θ0 cx ++ List.replicate Θc.length Slot.none := by
        rw [PJust_merge_eq singlepad jsP mrg,
          eraseAt_append _ Θ0 cx (CvarPos.lt_length posC)]
      have tyRestPad : ChildrenTypedAt Θ2 y ry Ay (l ++ r) := by
        rw [hΘ2]
        exact ChildrenTypedAt.padR _ tyRest
      -- child term: peel the send redex and its payload over the padded context
      have tyNpad := Typed.padR Θ0.length tyN
      have tyms'pad := ChildrenTypedAt.padR Θ0.length tyms'
      have singleCpad : PCtxSingle (Θc ++ List.replicate Θ0.length Slot.none) :=
        PCtxSingle.append singleC (PCtxSingle.replicate _)
      have hasDpad := PHas.padR Θ0.length hasD
      have hLenCpad : (Θc ++ List.replicate Θ0.length Slot.none).length
          = Θc.length + Θ0.length := by simp
      obtain ⟨Θc1, Θc2, AR0, mrgR, tyAppC, contR⟩ := evalCtx_inv tyNpad
      obtain ⟨AS, BS, sS, ΘFc, ΘVc, ΔF, ΔV, mrgAppC, mrgΔ, tySend, tyV, eqApp⟩ :=
        appEx_inv tyAppC
      cases mrgΔ
      obtain ⟨rs1, rs2, AAs, BBs, xorS, eqPiS, tyvS⟩ := sendEx_inv tySend
      obtain ⟨rJS, AJS, jsC, tyAJS, eqChS⟩ := chan_inv tyvS
      rw [cren_len_nil] at eqChS
      obtain ⟨ers, eActS⟩ := Static.ch_inj eqChS
      subst ers
      have singleC1 := (PCtxSingle.split singleCpad mrgR).1
      have singleC2 := (PCtxSingle.split singleCpad mrgR).2
      have singleFc := (PCtxSingle.split singleC1 mrgAppC).1
      have singleVc := (PCtxSingle.split singleC1 mrgAppC).2
      obtain ⟨ΘRc, mrgVcC2, mrgFRc⟩ := PMerge.splitR mrgR mrgAppC
      obtain ⟨hrr2, hAJS⟩ := PJust_PHas_agree singleCpad mrgFRc.sym jsC hasDpad
      subst hrr2
      -- session-protocol duality
      have eActS' : (Term.act rs2 AAs BBs .ex) ≃ C := by rw [← hAJS]; exact eActS
      have eSR := ARS.conv_trans eActS' (ARS.conv_trans hCA (ARS.conv_sym eActR))
      obtain ⟨eAAsr, eBBsr, _, _⟩ := Static.act_inj eSR
      -- protocol typings and the advanced protocol `W`
      obtain ⟨_, tyChS⟩ := tyvS.validity
      obtain ⟨tyActS, _⟩ := Static.ch_inv tyChS
      have tyBBs := Static.act_inv tyActS
      obtain ⟨_, tyAAs⟩ : ∃ s, ([] : Static.Ctx) ⊢ AAs : Term.srt s := by
        cases tyBBs.wf with | cons _ h => exact ⟨_, h⟩
      obtain ⟨eAS, eBS, _, _⟩ := Static.pi_inj eqPiS
      have tyVA : ΘVc ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ v : AAs :=
        Typed.conv eAS tyV tyAAs
      have tyW : ([] : Static.Ctx) ⊢ BBs[Chan.var_Chan; v..] : .proto := by
        have h := tyBBs.subst tyVA.toStatic
        asimp at h
        exact h
      -- split the child's children by the payload's endpoints
      have posDxC1 : CvarPos Θc1 dx true :=
        CvarPos.merge_true_left singleC1 mrgAppC ((jsC.pos_true).mpr rfl)
      have hD2dead : CvarPos Θc2 dx true → False := fun h =>
        PCtxSingle.merge_true_excl singleCpad mrgR posDxC1 h
      have posDxC2 : CvarPos Θc2 dx false := by
        rcases PCtxSingle.pos_total singleC2 dx with h | h
        · exact absurd h hD2dead
        · exact h
      obtain ⟨msL, msR, tyMsL, tyMsRAt, hpermMs'⟩ :=
        ChildrenTypedAt.split_right mrgR.sym singleCpad tyms'pad posDxC2
      have tyMsR : ChildrenTyped ΘVc msR :=
        ChildrenTypedAt.strengthen jsC mrgAppC tyMsRAt
      obtain ⟨permSplit1, permSplit2⟩ :=
        split_children_perm (w := v) singleCpad mrgR
          (fun p hp => ChildrenTyped.pos_of_label tyMsL (List.mem_map.mpr ⟨p, hp, rfl⟩))
          (List.Nodup.of_map _ (ChildrenTypedAt.labels_nodup tyMsRAt))
          (List.Nodup.of_map _ (ChildrenTyped.labels_nodup tyMsL))
          (hpermMs'.trans List.perm_append_comm)
          (ChildrenTypedAt.labels_nodup tyms'pad)
          (fun p hp => by
            rcases p with ⟨pc, pt⟩
            cases pc with
            | var_Chan px =>
                have hpos := ChildrenTypedAt.pos_of_label tyMsRAt
                  (List.mem_map.mpr ⟨(Chan.var_Chan px, pt), hp, rfl⟩)
                have h1 := tyAppC.occurs1 hpos
                have hne := ChildrenTypedAt.label_ne_parent tyMsRAt
                  (List.mem_map.mpr ⟨(Chan.var_Chan px, pt), hp, rfl⟩)
                simp only [chanIndex] at h1 hne ⊢
                simp only [occurs] at h1 ⊢
                rw [if_neg (fun h => hne h.symm)] at h1
                omega)
          (fun i h => by
            have h0 := tyAppC.occurs0 h
            simp only [occurs] at h0 ⊢
            omega)
      -- Distinct-derived freshness of the moved endpoints
      have hnodup : (((l ++ (Chan.var_Chan cx,
            Tree.node (Chan.var_Chan dx)
              (N.eval (.app (.send (Term.chan (Chan.var_Chan dx)) .ex) v .ex))
              ms' qs') :: r).map (fun e => chanIndex e.1)) ++
          childInteriors (l ++ (Chan.var_Chan cx,
            Tree.node (Chan.var_Chan dx)
              (N.eval (.app (.send (Term.chan (Chan.var_Chan dx)) .ex) v .ex))
              ms' qs') :: r)).Nodup :=
        labelsInteriors_sublist_node.nodup dist
      have memChild : (Chan.var_Chan cx,
          Tree.node (Chan.var_Chan dx)
            (N.eval (.app (.send (Term.chan (Chan.var_Chan dx)) .ex) v .ex))
            ms' qs') ∈ l ++ (Chan.var_Chan cx,
          Tree.node (Chan.var_Chan dx)
            (N.eval (.app (.send (Term.chan (Chan.var_Chan dx)) .ex) v .ex))
            ms' qs') :: r := by simp
      -- live payload endpoints are grandchild labels
      have vcLabel : ∀ i, CvarPos ΘVc i true → Chan.var_Chan i ∈ childLabels ms' := by
        intro i h
        have hC1 : CvarPos Θc1 i true := CvarPos.merge_true_right singleC1 mrgAppC h
        rcases ChildrenTypedAt.label_of_pos tyms'pad
            (CvarPos.merge_true_left singleCpad mrgR hC1) with hmem | hy
        · exact hmem
        · subst hy
          exact (PCtxSingle.merge_true_excl singleC1 mrgAppC
            ((jsC.pos_true).mpr rfl) h).elim
      -- rebuild the child: return the advanced endpoint
      have hlenC2 : dx < Θc2.length := by
        have h := CvarPos.lt_length (CvarPos.merge_true_left singleCpad mrgR posDxC1)
        rw [hLenCpad] at h
        rw [PMerge.length_right mrgR, hLenCpad]
        omega
      obtain ⟨Θc', mrgD', singleC'⟩ :=
        oneCtx_merge (Θ := Θc2) (x := dx) (r := !rr1)
          (W := BBs[Chan.var_Chan; v..]) singleC2 hlenC2 hD2dead
      have tyChanD := oneCtx_chan (x := dx) (r := !rr1)
        (W := BBs[Chan.var_Chan; v..]) (B := BBs[Chan.var_Chan; v..])
        Θc2.length tyW ARS.Conv.refl tyW
      obtain ⟨_, tyMAS0⟩ := tyAppC.validity
      have tyPureD : (oneCtx dx (!rr1) (BBs[Chan.var_Chan; v..]) Θc2.length) ⨾
          ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢
          .pure (.chan (Chan.var_Chan dx)) : .M AR0 := by
        refine Typed.conv ?_ (Typed.pure tyChanD) tyMAS0
        refine ARS.conv_sym (ARS.conv_trans eqApp ?_)
        exact Static.conv_subst (v..) eBS
      have tyTermC := contR _ Θc' _ mrgD'.sym tyPureD
      have tymsAtC :=
        ChildrenTypedAt.intro (oneCtx_just Θc2.length) mrgD' singleC' tyMsL
      have hasD' : PHas Θc' dx (!rr1) (shiftK (dx + 1) (BBs[Chan.var_Chan; v..])) :=
        PHas.merge_left singleC' mrgD' (PJust.toPHas (oneCtx_just _))
      have tyNodeC : TypedAt (!rr1) (shiftK (dx + 1) (BBs[Chan.var_Chan; v..]))
          (.node (Chan.var_Chan dx)
            (N.eval (.pure (.chan (Chan.var_Chan dx)))) msL qs') :=
        TypedAt.node singleC' hasD' tyTermC tymsAtC tyqs'
      -- rebuild the parent: receive the pair with the moved payload resources
      have posCx1 : CvarPos Θ1 cx true := (jsP.pos_true).mpr rfl
      have hlen2 : cx < Θ2.length := by
        have h := CvarPos.lt_length (CvarPos.merge_true_left singlepad mrg posCx1)
        rw [hLenPad] at h
        rw [PMerge.length_right mrg, hLenPad]
        omega
      have hC2dead : CvarPos Θ2 cx true → False := fun h =>
        PCtxSingle.merge_true_excl singlepad mrg posCx1 h
      have hLenVc : ΘVc.length = Θc.length + Θ0.length := by
        rw [PMerge.length_right mrgAppC, PMerge.length_left mrgR, hLenCpad]
      have hLenΘ2 : Θ2.length = Θ0.length + Θc.length := by
        rw [PMerge.length_right mrg, hLenPad]
      obtain ⟨Θ3P, mrgPairP, single3P⟩ :=
        pmerge_single_disjoint (Θ1 := ΘVc)
          (Θ2 := oneCtx cx rr1 (shiftK dx (BBs[Chan.var_Chan; v..])) Θ2.length)
          (by simp [oneCtx]; omega)
          singleVc (oneCtx_single _)
          (by
            intro i h1 h2
            have hcx : cx = i :=
              ((oneCtx_just (x := cx) (r := rr1)
                (W := shiftK dx (BBs[Chan.var_Chan; v..])) Θ2.length).pos_true).mp h2
            subst hcx
            have hmemC := vcLabel cx h1
            obtain ⟨⟨e, gc⟩, memPair, heq⟩ := List.mem_map.mp hmemC
            have he : e = Chan.var_Chan cx := heq
            subst he
            exact (grandchild_fresh hnodup memChild memPair).2
              (by simp [childLabels]))
      have hLen3P : Θ3P.length = Θ2.length := by
        rw [← PMerge.length_left mrgPairP]
        omega
      obtain ⟨Θ', mrgFinalP, singleΘ'⟩ :=
        pmerge_single_disjoint (Θ1 := Θ3P) (Θ2 := Θ2) hLen3P single3P
          (PCtxSingle.split singlepad mrg).2
          (by
            intro i h1 h2
            rcases CvarPos.split_true mrgPairP h1 with ⟨_, hone⟩ | ⟨hV, _⟩
            · have hcx : cx = i :=
                ((oneCtx_just (x := cx) (r := rr1)
                  (W := shiftK dx (BBs[Chan.var_Chan; v..])) Θ2.length).pos_true).mp hone
              subst hcx
              exact hC2dead h2
            · have hmemC := vcLabel i hV
              obtain ⟨⟨e, gc⟩, memPair, heq⟩ := List.mem_map.mp hmemC
              have he : e = Chan.var_Chan i := heq
              subst he
              rcases ChildrenTypedAt.label_of_pos tymspad
                  (CvarPos.merge_true_right singlepad mrg h2) with hmemP | hyP
              · exact (grandchild_fresh hnodup memChild memPair).2 hmemP
              · subst hyP
                exact grandchild_ne_node_parent dist memChild memPair rfl)
      -- the parent's received pair
      obtain ⟨_, tyChR⟩ := tyvR.validity
      obtain ⟨tyActR, _⟩ := Static.ch_inv tyChR
      have tyBBr := Static.act_inv tyActR
      obtain ⟨_, tyAAr⟩ : ∃ s, ([] : Static.Ctx) ⊢ AAr : Term.srt s := by
        cases tyBBr.wf with | cons _ h => exact ⟨_, h⟩
      have tyMsgR : ΘVc ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ v : AAr :=
        Typed.conv eAAsr tyVA tyAAr
      obtain ⟨_, tyMAR0⟩ := tyRecv.validity
      have tyPairP : Θ3P ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢
          .pure (.pair v (.chan (Chan.var_Chan cx)) .ex .L) : .M A0 := by
        refine Typed.conv (ARS.conv_sym eqMR) (.pure ?_) tyMAR0
        refine Typed.pairEx mrgPairP .nil
          (Static.Typed.sig (fun _ => Static.sort_leq_Lgt) Static.sort_leq_Lgt tyAAr
            (Static.Typed.ch tyBBr))
          tyMsgR ?_
        refine Typed.conv (s := .L)
          (Static.conv_ch (Static.conv_subst (v..) eBBsr))
          (oneCtx_chan _ (shiftK_proto tyW dx) (shiftK_conv _ dx) tyW) ?_
        have h := Static.Typed.ch (b := rr1) (tyBBr.subst tyMsgR.toStatic)
        asimp at h ⊢
        exact h
      have tyTermP := cont _ Θ' _ mrgFinalP.sym tyPairP
      -- the reserved parent endpoint survives into the final context
      have hcy : cx ≠ y :=
        ChildrenTypedAt.label_ne_parent (c := Chan.var_Chan cx) tyms
          (by simp [childLabels])
      have posY1 : CvarPos Θ1 y false := (jsP.pos_false).mpr hcy
      have hasY : PHas Θ' y ry Ay :=
        PHas.merge_right singleΘ' mrgFinalP
          (PHas.merge_inv_right mrg (PHas.padR Θc.length has) posY1)
      -- the parent's new children
      obtain ⟨Θmid, mrgVc2P, mrgOneP⟩ := PMerge.splitL mrgFinalP mrgPairP
      have singleMid : PCtxSingle Θmid := (PCtxSingle.split singleΘ' mrgOneP).1
      obtain ⟨msMid, tyMsMid, hpermMid⟩ :=
        ChildrenTypedAt.merge mrgVc2P.sym singleMid tyRestPad tyMsR
      obtain ⟨msNew, tyMsNew, hpermNew⟩ :=
        ChildrenTypedAt.merge mrgOneP singleΘ' tyMsMid (oneCtx_children _ tyNodeC)
      have hsim : recvExChildren v (Chan.var_Chan cx) (Chan.var_Chan dx) N ms' qs'
          (l ++ r) = insertChild (Chan.var_Chan cx)
            (.node (Chan.var_Chan dx) (N.eval (.pure (.chan (Chan.var_Chan dx))))
              (splitChildrenByTerm v ms').2 qs')
            (mergeChildren (splitChildrenByTerm v ms').1 (l ++ r)) := by
        simp [recvExChildren]
      have sortedMs' := ChildrenTypedAt.sorted tyms'
      have e1 : (splitChildrenByTerm v ms').1 = msR :=
        child_sorted_eq permSplit1
          (List.Pairwise.sublist (splitChildrenByTerm_sublist₁ v ms') sortedMs')
          (ChildrenTyped.sorted tyMsR)
      have e2 : (splitChildrenByTerm v ms').2 = msL :=
        child_sorted_eq permSplit2
          (List.Pairwise.sublist (splitChildrenByTerm_sublist₂ v ms') sortedMs')
          (ChildrenTyped.sorted tyMsL)
      have nodupRLR : (childLabels (msR ++ (l ++ r))).Nodup := by
        have h := (List.Perm.map Prod.fst hpermMid).nodup
          (ChildrenTypedAt.labels_nodup tyMsMid)
        exact ((List.perm_append_comm (l₁ := l ++ r) (l₂ := msR)).map Prod.fst).nodup h
      have eMid : mergeChildren msR (l ++ r) = msMid :=
        child_sorted_eq
          ((mergeChildren_perm msR (l ++ r)).trans
            (List.perm_append_comm.trans hpermMid.symm))
          (sorted_mergeChildren (ChildrenTypedAt.sorted tyRestPad) nodupRLR)
          (ChildrenTypedAt.sorted tyMsMid)
      have freshMid : ∀ p : Chan × Tree, p ∈ msMid →
          chanIndex (Chan.var_Chan cx) ≠ chanIndex p.1 := by
        intro p hp he
        have hpos := ChildrenTypedAt.pos_of_label tyMsMid (List.mem_map.mpr ⟨p, hp, rfl⟩)
        have he' : cx = chanIndex p.1 := he
        rw [← he'] at hpos
        rcases CvarPos.split_true mrgVc2P hpos with ⟨_, h2⟩ | ⟨hV, _⟩
        · exact hC2dead h2
        · have hmemC := vcLabel cx hV
          obtain ⟨⟨e, gc⟩, memPair, heq⟩ := List.mem_map.mp hmemC
          have hee : e = Chan.var_Chan cx := heq
          subst hee
          exact (grandchild_fresh hnodup memChild memPair).2 (by simp [childLabels])
      have eTop : insertChild (Chan.var_Chan cx)
          (.node (Chan.var_Chan dx) (N.eval (.pure (.chan (Chan.var_Chan dx))))
            msL qs') msMid = msNew :=
        child_sorted_eq
          ((insertChild_perm _ _ _).trans
            ((List.perm_append_singleton _ _).symm.trans hpermNew.symm))
          (sorted_insertChild (ChildrenTypedAt.sorted tyMsMid) freshMid)
          (ChildrenTypedAt.sorted tyMsNew)
      rw [hsim, e1, e2, eMid, eTop]
      exact TypedAt.node singleΘ' hasY tyTermP tyMsNew tyqs
  | @rootSendIm M N o c d l r ms' qs qs' implicit =>
      refine ⟨fun ty dist => ?_, fun ry Ay ty _ => (by cases ty)⟩
      cases ty with
      | @root Θ0 _ _ _ single tym tyms tyqs =>
      cases c with
      | var_Chan cx =>
      cases d with
      | var_Chan dx =>
      -- parent term: peel the send redex
      obtain ⟨Θ1, Θ2, A0, mrg, tyApp, cont⟩ := evalCtx_inv tym
      obtain ⟨AS, BS, sS, tySend, tyMsg, eqApp⟩ := appIm_inv tyApp
      obtain ⟨rs1, rs2, AAs, BBs, xorS, eqPiS, tyvS⟩ := sendIm_inv tySend
      obtain ⟨rJS, AJS, jsS, tyAJS, eqChS⟩ := chan_inv tyvS
      rw [cren_len_nil] at eqChS
      obtain ⟨ers, eActS⟩ := Static.ch_inj eqChS
      subst ers
      -- select and invert the receiving child
      obtain ⟨C, tyChildAt, convC, tyRest⟩ := ChildrenTyped.remove jsS mrg tyms rfl rfl
      cases tyChildAt with
      | @node Θc _ _ _ _ _ _ singleC hasD tyN tyms' tyqs' =>
      obtain ⟨Θc1, Θc2, AR0, mrgR, tyRecv, contR⟩ := evalCtx_inv tyN
      obtain ⟨rr1, rr2, AAr, BBr, xorR, eqMR, tyvR⟩ := recvIm_inv tyRecv
      obtain ⟨rJR, AJR, jsR, tyAJR, eqChR⟩ := chan_inv tyvR
      rw [cren_len_nil] at eqChR
      obtain ⟨err, eActR⟩ := Static.ch_inj eqChR
      subst err
      obtain ⟨hrr, hAJR⟩ := PJust_PHas_agree singleC mrgR jsR hasD
      subst hrr
      -- session-protocol duality
      have eActR' : (Term.act rr2 AAr BBr .im) ≃ C := by rw [← hAJR]; exact eActR
      have eSR := ARS.conv_trans eActS
        (ARS.conv_sym (ARS.conv_trans eActR' convC))
      obtain ⟨eAAsr, eBBsr, _, _⟩ := Static.act_inj eSR
      -- protocol typings and the advanced protocol `W`
      obtain ⟨_, tyChS⟩ := tyvS.validity
      obtain ⟨tyActS, _⟩ := Static.ch_inv tyChS
      have tyBBs := Static.act_inv tyActS
      obtain ⟨_, tyAAs⟩ : ∃ s, ([] : Static.Ctx) ⊢ AAs : Term.srt s := by
        cases tyBBs.wf with | cons _ h => exact ⟨_, h⟩
      obtain ⟨eAS, eBS, _, _⟩ := Static.pi_inj eqPiS
      have tyMsgA : ([] : Static.Ctx) ⊢ o : AAs := Static.Typed.conv eAS tyMsg tyAAs
      have tyW : ([] : Static.Ctx) ⊢ BBs[Chan.var_Chan; o..] : .proto := by
        have h := tyBBs.subst tyMsgA
        asimp at h
        exact h
      have single2 := (PCtxSingle.split single mrg).2
      have singleC2 := (PCtxSingle.split singleC mrgR).2
      -- parent continuation: the advanced endpoint at `cx`
      have posCx1 : CvarPos Θ1 cx true := (jsS.pos_true).mpr rfl
      have hlen2 : cx < Θ2.length := by
        have h := CvarPos.lt_length (CvarPos.merge_true_left single mrg posCx1)
        rw [PMerge.length_right mrg]
        omega
      have hC2dead : CvarPos Θ2 cx true → False := fun h =>
        PCtxSingle.merge_true_excl single mrg posCx1 h
      obtain ⟨Θ', mrgC, singleΘ'⟩ :=
        oneCtx_merge (Θ := Θ2) (x := cx) (r := rs1)
          (W := shiftK dx (BBs[Chan.var_Chan; o..])) single2 hlen2 hC2dead
      have tyChanC := oneCtx_chan (x := cx) (r := rs1)
        (W := shiftK dx (BBs[Chan.var_Chan; o..])) (B := BBs[Chan.var_Chan; o..])
        Θ2.length (shiftK_proto tyW dx) (shiftK_conv _ dx) tyW
      obtain ⟨_, tyMAS0⟩ := tyApp.validity
      have tyPureC : (oneCtx cx rs1 (shiftK dx (BBs[Chan.var_Chan; o..])) Θ2.length) ⨾
          ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢
          .pure (.chan (Chan.var_Chan cx)) : .M A0 := by
        refine Typed.conv ?_ (Typed.pure tyChanC) tyMAS0
        refine ARS.conv_sym (ARS.conv_trans eqApp ?_)
        exact Static.conv_subst (o..) eBS
      have tyTermP := cont _ Θ' _ mrgC.sym tyPureC
      -- child continuation: receive the pair at the advanced endpoint `dx`
      have posDx1 : CvarPos Θc1 dx true := (jsR.pos_true).mpr rfl
      have hlenC2 : dx < Θc2.length := by
        have h := CvarPos.lt_length (CvarPos.merge_true_left singleC mrgR posDx1)
        rw [PMerge.length_right mrgR]
        omega
      have hD2dead : CvarPos Θc2 dx true → False := fun h =>
        PCtxSingle.merge_true_excl singleC mrgR posDx1 h
      obtain ⟨Θc', mrgD', singleC'⟩ :=
        oneCtx_merge (Θ := Θc2) (x := dx) (r := !rs1)
          (W := BBs[Chan.var_Chan; o..]) singleC2 hlenC2 hD2dead
      obtain ⟨_, tyChR⟩ := tyvR.validity
      obtain ⟨tyActR, _⟩ := Static.ch_inv tyChR
      have tyBBr := Static.act_inv tyActR
      obtain ⟨_, tyAAr⟩ : ∃ s, ([] : Static.Ctx) ⊢ AAr : Term.srt s := by
        cases tyBBr.wf with | cons _ h => exact ⟨_, h⟩
      have tyMsgR : ([] : Static.Ctx) ⊢ o : AAr :=
        Static.Typed.conv (ARS.conv_trans eAS eAAsr) tyMsg tyAAr
      obtain ⟨_, tyMAR0⟩ := tyRecv.validity
      have tyPairR : (oneCtx dx (!rs1) (BBs[Chan.var_Chan; o..]) Θc2.length) ⨾
          ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢
          .pure (.pair o (.chan (Chan.var_Chan dx)) .im .L) : .M AR0 := by
        refine Typed.conv (ARS.conv_sym eqMR) (.pure ?_) tyMAR0
        refine Typed.pairIm
          (Static.Typed.sig (by nofun) Static.sort_leq_Lgt tyAAr (Static.Typed.ch tyBBr))
          tyMsgR ?_
        refine Typed.conv (s := .L)
          (Static.conv_ch (Static.conv_subst (o..) eBBsr))
          (oneCtx_chan _ tyW ARS.Conv.refl tyW) ?_
        have h := Static.Typed.ch (b := !rs1) (tyBBr.subst tyMsgR)
        asimp at h ⊢
        exact h
      have tyTermC := contR _ Θc' _ mrgD'.sym tyPairR
      -- the updated child node
      have tyRest' := ChildrenTypedAt.strengthen jsR mrgR tyms'
      have tymsAt' := ChildrenTypedAt.intro (oneCtx_just Θc2.length) mrgD' singleC' tyRest'
      have hasD' : PHas Θc' dx (!rs1) (shiftK (dx + 1) (BBs[Chan.var_Chan; o..])) :=
        PHas.merge_left singleC' mrgD' (PJust.toPHas (oneCtx_just _))
      have tyNode' : TypedAt (!rs1) (shiftK (dx + 1) (BBs[Chan.var_Chan; o..]))
          (.node (Chan.var_Chan dx)
            (N.eval (.pure (.pair o (.chan (Chan.var_Chan dx)) .im .L))) ms' qs') :=
        TypedAt.node singleC' hasD' tyTermC tymsAt' tyqs'
      -- reassemble the parent
      obtain ⟨msNew, tyMsNew, hpermNew⟩ :=
        ChildrenTyped.merge mrgC.sym singleΘ' tyRest (oneCtx_children _ tyNode')
      have eNew : l ++ (Chan.var_Chan cx, .node (Chan.var_Chan dx)
          (N.eval (.pure (.pair o (.chan (Chan.var_Chan dx)) .im .L))) ms' qs') :: r
          = msNew :=
        child_sorted_eq
          (List.perm_middle.trans
            ((List.perm_append_singleton _ _).symm.trans hpermNew.symm))
          (sorted_replace (ChildrenTyped.sorted tyms))
          (ChildrenTyped.sorted tyMsNew)
      rw [eNew]
      exact Typed.root singleΘ' tyTermP tyMsNew tyqs
  | @nodeSendIm M N p o c d l r ms' qs qs' implicit =>
      refine ⟨fun ty _ => (by cases ty), fun ry Ay ty dist => ?_⟩
      cases ty with
      | @node Θ0 y _ _ _ _ _ single has tym tyms tyqs =>
      cases c with
      | var_Chan cx =>
      cases d with
      | var_Chan dx =>
      -- parent term: peel the send redex
      obtain ⟨Θ1, Θ2, A0, mrg, tyApp, cont⟩ := evalCtx_inv tym
      obtain ⟨AS, BS, sS, tySend, tyMsg, eqApp⟩ := appIm_inv tyApp
      obtain ⟨rs1, rs2, AAs, BBs, xorS, eqPiS, tyvS⟩ := sendIm_inv tySend
      obtain ⟨rJS, AJS, jsS, tyAJS, eqChS⟩ := chan_inv tyvS
      rw [cren_len_nil] at eqChS
      obtain ⟨ers, eActS⟩ := Static.ch_inj eqChS
      subst ers
      -- select and invert the receiving child
      obtain ⟨C, tyChildAt, convC, tyRest⟩ := ChildrenTypedAt.remove jsS mrg tyms rfl rfl
      cases tyChildAt with
      | @node Θc _ _ _ _ _ _ singleC hasD tyN tyms' tyqs' =>
      obtain ⟨Θc1, Θc2, AR0, mrgR, tyRecv, contR⟩ := evalCtx_inv tyN
      obtain ⟨rr1, rr2, AAr, BBr, xorR, eqMR, tyvR⟩ := recvIm_inv tyRecv
      obtain ⟨rJR, AJR, jsR, tyAJR, eqChR⟩ := chan_inv tyvR
      rw [cren_len_nil] at eqChR
      obtain ⟨err, eActR⟩ := Static.ch_inj eqChR
      subst err
      obtain ⟨hrr, hAJR⟩ := PJust_PHas_agree singleC mrgR jsR hasD
      subst hrr
      -- session-protocol duality
      have eActR' : (Term.act rr2 AAr BBr .im) ≃ C := by rw [← hAJR]; exact eActR
      have eSR := ARS.conv_trans eActS
        (ARS.conv_sym (ARS.conv_trans eActR' convC))
      obtain ⟨eAAsr, eBBsr, _, _⟩ := Static.act_inj eSR
      -- protocol typings and the advanced protocol `W`
      obtain ⟨_, tyChS⟩ := tyvS.validity
      obtain ⟨tyActS, _⟩ := Static.ch_inv tyChS
      have tyBBs := Static.act_inv tyActS
      obtain ⟨_, tyAAs⟩ : ∃ s, ([] : Static.Ctx) ⊢ AAs : Term.srt s := by
        cases tyBBs.wf with | cons _ h => exact ⟨_, h⟩
      obtain ⟨eAS, eBS, _, _⟩ := Static.pi_inj eqPiS
      have tyMsgA : ([] : Static.Ctx) ⊢ o : AAs := Static.Typed.conv eAS tyMsg tyAAs
      have tyW : ([] : Static.Ctx) ⊢ BBs[Chan.var_Chan; o..] : .proto := by
        have h := tyBBs.subst tyMsgA
        asimp at h
        exact h
      have single1 := (PCtxSingle.split single mrg).1
      have single2 := (PCtxSingle.split single mrg).2
      have singleC2 := (PCtxSingle.split singleC mrgR).2
      -- the reserved parent endpoint stays with the continuation
      have hcy : cx ≠ y :=
        ChildrenTypedAt.label_ne_parent (c := Chan.var_Chan cx) tyms
          (by simp [childLabels])
      have posY1 : CvarPos Θ1 y false := (jsS.pos_false).mpr hcy
      -- parent continuation: the advanced endpoint at `cx`
      have posCx1 : CvarPos Θ1 cx true := (jsS.pos_true).mpr rfl
      have hlen2 : cx < Θ2.length := by
        have h := CvarPos.lt_length (CvarPos.merge_true_left single mrg posCx1)
        rw [PMerge.length_right mrg]
        omega
      have hC2dead : CvarPos Θ2 cx true → False := fun h =>
        PCtxSingle.merge_true_excl single mrg posCx1 h
      obtain ⟨Θ', mrgC, singleΘ'⟩ :=
        oneCtx_merge (Θ := Θ2) (x := cx) (r := rs1)
          (W := shiftK dx (BBs[Chan.var_Chan; o..])) single2 hlen2 hC2dead
      have tyChanC := oneCtx_chan (x := cx) (r := rs1)
        (W := shiftK dx (BBs[Chan.var_Chan; o..])) (B := BBs[Chan.var_Chan; o..])
        Θ2.length (shiftK_proto tyW dx) (shiftK_conv _ dx) tyW
      obtain ⟨_, tyMAS0⟩ := tyApp.validity
      have tyPureC : (oneCtx cx rs1 (shiftK dx (BBs[Chan.var_Chan; o..])) Θ2.length) ⨾
          ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢
          .pure (.chan (Chan.var_Chan cx)) : .M A0 := by
        refine Typed.conv ?_ (Typed.pure tyChanC) tyMAS0
        refine ARS.conv_sym (ARS.conv_trans eqApp ?_)
        exact Static.conv_subst (o..) eBS
      have tyTermP := cont _ Θ' _ mrgC.sym tyPureC
      -- child continuation: receive the pair at the advanced endpoint `dx`
      have posDx1 : CvarPos Θc1 dx true := (jsR.pos_true).mpr rfl
      have hlenC2 : dx < Θc2.length := by
        have h := CvarPos.lt_length (CvarPos.merge_true_left singleC mrgR posDx1)
        rw [PMerge.length_right mrgR]
        omega
      have hD2dead : CvarPos Θc2 dx true → False := fun h =>
        PCtxSingle.merge_true_excl singleC mrgR posDx1 h
      obtain ⟨Θc', mrgD', singleC'⟩ :=
        oneCtx_merge (Θ := Θc2) (x := dx) (r := !rs1)
          (W := BBs[Chan.var_Chan; o..]) singleC2 hlenC2 hD2dead
      obtain ⟨_, tyChR⟩ := tyvR.validity
      obtain ⟨tyActR, _⟩ := Static.ch_inv tyChR
      have tyBBr := Static.act_inv tyActR
      obtain ⟨_, tyAAr⟩ : ∃ s, ([] : Static.Ctx) ⊢ AAr : Term.srt s := by
        cases tyBBr.wf with | cons _ h => exact ⟨_, h⟩
      have tyMsgR : ([] : Static.Ctx) ⊢ o : AAr :=
        Static.Typed.conv (ARS.conv_trans eAS eAAsr) tyMsg tyAAr
      obtain ⟨_, tyMAR0⟩ := tyRecv.validity
      have tyPairR : (oneCtx dx (!rs1) (BBs[Chan.var_Chan; o..]) Θc2.length) ⨾
          ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢
          .pure (.pair o (.chan (Chan.var_Chan dx)) .im .L) : .M AR0 := by
        refine Typed.conv (ARS.conv_sym eqMR) (.pure ?_) tyMAR0
        refine Typed.pairIm
          (Static.Typed.sig (by nofun) Static.sort_leq_Lgt tyAAr (Static.Typed.ch tyBBr))
          tyMsgR ?_
        refine Typed.conv (s := .L)
          (Static.conv_ch (Static.conv_subst (o..) eBBsr))
          (oneCtx_chan _ tyW ARS.Conv.refl tyW) ?_
        have h := Static.Typed.ch (b := !rs1) (tyBBr.subst tyMsgR)
        asimp at h ⊢
        exact h
      have tyTermC := contR _ Θc' _ mrgD'.sym tyPairR
      -- the updated child node
      have tyRest' := ChildrenTypedAt.strengthen jsR mrgR tyms'
      have tymsAt' := ChildrenTypedAt.intro (oneCtx_just Θc2.length) mrgD' singleC' tyRest'
      have hasD' : PHas Θc' dx (!rs1) (shiftK (dx + 1) (BBs[Chan.var_Chan; o..])) :=
        PHas.merge_left singleC' mrgD' (PJust.toPHas (oneCtx_just _))
      have tyNode' : TypedAt (!rs1) (shiftK (dx + 1) (BBs[Chan.var_Chan; o..]))
          (.node (Chan.var_Chan dx)
            (N.eval (.pure (.pair o (.chan (Chan.var_Chan dx)) .im .L))) ms' qs') :=
        TypedAt.node singleC' hasD' tyTermC tymsAt' tyqs'
      -- the reserved parent endpoint survives into the final context
      have hasY : PHas Θ' y ry Ay :=
        PHas.merge_right singleΘ' mrgC (PHas.merge_inv_right mrg has posY1)
      -- reassemble the parent
      obtain ⟨msNew, tyMsNew, hpermNew⟩ :=
        ChildrenTypedAt.merge mrgC.sym singleΘ' tyRest (oneCtx_children _ tyNode')
      have eNew : l ++ (Chan.var_Chan cx, .node (Chan.var_Chan dx)
          (N.eval (.pure (.pair o (.chan (Chan.var_Chan dx)) .im .L))) ms' qs') :: r
          = msNew :=
        child_sorted_eq
          (List.perm_middle.trans
            ((List.perm_append_singleton _ _).symm.trans hpermNew.symm))
          (sorted_replace (ChildrenTypedAt.sorted tyms))
          (ChildrenTypedAt.sorted tyMsNew)
      rw [eNew]
      exact TypedAt.node singleΘ' hasY tyTermP tyMsNew tyqs
  | @rootRecvIm M N o c d l r ms' qs qs' implicit =>
      refine ⟨fun ty dist => ?_, fun ry Ay ty _ => (by cases ty)⟩
      cases ty with
      | @root Θ0 _ _ _ single tym tyms tyqs =>
      cases c with
      | var_Chan cx =>
      cases d with
      | var_Chan dx =>
      -- parent term: peel the recv redex
      obtain ⟨Θ1, Θ2, A0, mrg, tyRecv, cont⟩ := evalCtx_inv tym
      obtain ⟨rr1, rr2, AAr, BBr, xorR, eqMR, tyvR⟩ := recvIm_inv tyRecv
      obtain ⟨rJR, AJR, jsP, tyAJR, eqChR⟩ := chan_inv tyvR
      rw [cren_len_nil] at eqChR
      obtain ⟨err, eActR⟩ := Static.ch_inj eqChR
      subst err
      -- select and invert the sending child
      obtain ⟨C, tyChildAt, convC, tyRest⟩ := ChildrenTyped.remove jsP mrg tyms rfl rfl
      cases tyChildAt with
      | @node Θc _ _ _ _ _ _ singleC hasD tyN tyms' tyqs' =>
      obtain ⟨Θc1, Θc2, AR0, mrgR, tyApp, contR⟩ := evalCtx_inv tyN
      obtain ⟨AS, BS, sS, tySend, tyMsg, eqApp⟩ := appIm_inv tyApp
      obtain ⟨rs1, rs2, AAs, BBs, xorS, eqPiS, tyvS⟩ := sendIm_inv tySend
      obtain ⟨rJS, AJS, jsC, tyAJS, eqChS⟩ := chan_inv tyvS
      rw [cren_len_nil] at eqChS
      obtain ⟨ers, eActS⟩ := Static.ch_inj eqChS
      subst ers
      obtain ⟨hrr, hAJS⟩ := PJust_PHas_agree singleC mrgR jsC hasD
      have hrr1 : rr1 = !rs1 := by rw [hrr, Bool.not_not]
      subst hrr1
      -- session-protocol duality
      have eActS' : (Term.act rs2 AAs BBs .im) ≃ C := by rw [← hAJS]; exact eActS
      have eSR := ARS.conv_trans eActS'
        (ARS.conv_trans convC (ARS.conv_sym eActR))
      obtain ⟨eAAsr, eBBsr, _, _⟩ := Static.act_inj eSR
      -- protocol typings and the advanced protocol `W` (from the sending child)
      obtain ⟨_, tyChS⟩ := tyvS.validity
      obtain ⟨tyActS, _⟩ := Static.ch_inv tyChS
      have tyBBs := Static.act_inv tyActS
      obtain ⟨_, tyAAs⟩ : ∃ s, ([] : Static.Ctx) ⊢ AAs : Term.srt s := by
        cases tyBBs.wf with | cons _ h => exact ⟨_, h⟩
      obtain ⟨eAS, eBS, _, _⟩ := Static.pi_inj eqPiS
      have tyMsgA : ([] : Static.Ctx) ⊢ o : AAs := Static.Typed.conv eAS tyMsg tyAAs
      have tyW : ([] : Static.Ctx) ⊢ BBs[Chan.var_Chan; o..] : .proto := by
        have h := tyBBs.subst tyMsgA
        asimp at h
        exact h
      have single1 := (PCtxSingle.split single mrg).1
      have single2 := (PCtxSingle.split single mrg).2
      have singleC2 := (PCtxSingle.split singleC mrgR).2
      -- parent continuation: receive the pair at the advanced endpoint `cx`
      have posCx1 : CvarPos Θ1 cx true := (jsP.pos_true).mpr rfl
      have hlen2 : cx < Θ2.length := by
        have h := CvarPos.lt_length (CvarPos.merge_true_left single mrg posCx1)
        rw [PMerge.length_right mrg]
        omega
      have hC2dead : CvarPos Θ2 cx true → False := fun h =>
        PCtxSingle.merge_true_excl single mrg posCx1 h
      obtain ⟨Θ', mrgC, singleΘ'⟩ :=
        oneCtx_merge (Θ := Θ2) (x := cx) (r := !rs1)
          (W := shiftK dx (BBs[Chan.var_Chan; o..])) single2 hlen2 hC2dead
      obtain ⟨_, tyChR⟩ := tyvR.validity
      obtain ⟨tyActR, _⟩ := Static.ch_inv tyChR
      have tyBBr := Static.act_inv tyActR
      obtain ⟨_, tyAAr⟩ : ∃ s, ([] : Static.Ctx) ⊢ AAr : Term.srt s := by
        cases tyBBr.wf with | cons _ h => exact ⟨_, h⟩
      have tyMsgR : ([] : Static.Ctx) ⊢ o : AAr :=
        Static.Typed.conv (ARS.conv_trans eAS eAAsr) tyMsg tyAAr
      obtain ⟨_, tyMAR0⟩ := tyRecv.validity
      have tyPairP : (oneCtx cx (!rs1) (shiftK dx (BBs[Chan.var_Chan; o..])) Θ2.length) ⨾
          ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢
          .pure (.pair o (.chan (Chan.var_Chan cx)) .im .L) : .M A0 := by
        refine Typed.conv (ARS.conv_sym eqMR) (.pure ?_) tyMAR0
        refine Typed.pairIm
          (Static.Typed.sig (by nofun) Static.sort_leq_Lgt tyAAr (Static.Typed.ch tyBBr))
          tyMsgR ?_
        refine Typed.conv (s := .L)
          (Static.conv_ch (Static.conv_subst (o..) eBBsr))
          (oneCtx_chan _ (shiftK_proto tyW dx) (shiftK_conv _ dx) tyW) ?_
        have h := Static.Typed.ch (b := !rs1) (tyBBr.subst tyMsgR)
        asimp at h ⊢
        exact h
      have tyTermP := cont _ Θ' _ mrgC.sym tyPairP
      -- child continuation: return the advanced endpoint `dx`
      have posDx1 : CvarPos Θc1 dx true := (jsC.pos_true).mpr rfl
      have hlenC2 : dx < Θc2.length := by
        have h := CvarPos.lt_length (CvarPos.merge_true_left singleC mrgR posDx1)
        rw [PMerge.length_right mrgR]
        omega
      have hD2dead : CvarPos Θc2 dx true → False := fun h =>
        PCtxSingle.merge_true_excl singleC mrgR posDx1 h
      obtain ⟨Θc', mrgD', singleC'⟩ :=
        oneCtx_merge (Θ := Θc2) (x := dx) (r := rs1)
          (W := BBs[Chan.var_Chan; o..]) singleC2 hlenC2 hD2dead
      have tyChanD := oneCtx_chan (x := dx) (r := rs1)
        (W := BBs[Chan.var_Chan; o..]) (B := BBs[Chan.var_Chan; o..])
        Θc2.length tyW ARS.Conv.refl tyW
      obtain ⟨_, tyMAS0⟩ := tyApp.validity
      have tyPureD : (oneCtx dx rs1 (BBs[Chan.var_Chan; o..]) Θc2.length) ⨾
          ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢
          .pure (.chan (Chan.var_Chan dx)) : .M AR0 := by
        refine Typed.conv ?_ (Typed.pure tyChanD) tyMAS0
        refine ARS.conv_sym (ARS.conv_trans eqApp ?_)
        exact Static.conv_subst (o..) eBS
      have tyTermC := contR _ Θc' _ mrgD'.sym tyPureD
      -- the updated child node
      have tyRest' := ChildrenTypedAt.strengthen jsC mrgR tyms'
      have tymsAt' := ChildrenTypedAt.intro (oneCtx_just Θc2.length) mrgD' singleC' tyRest'
      have hasD' : PHas Θc' dx rs1 (shiftK (dx + 1) (BBs[Chan.var_Chan; o..])) :=
        PHas.merge_left singleC' mrgD' (PJust.toPHas (oneCtx_just _))
      have tyNode' : TypedAt rs1 (shiftK (dx + 1) (BBs[Chan.var_Chan; o..]))
          (.node (Chan.var_Chan dx)
            (N.eval (.pure (.chan (Chan.var_Chan dx)))) ms' qs') :=
        TypedAt.node singleC' hasD' tyTermC tymsAt' tyqs'
      have tyNode'' : TypedAt (!(!rs1)) (shiftK 1 (shiftK dx (BBs[Chan.var_Chan; o..])))
          (.node (Chan.var_Chan dx)
            (N.eval (.pure (.chan (Chan.var_Chan dx)))) ms' qs') := by
        rw [Bool.not_not]
        exact tyNode'
      -- reassemble the parent
      obtain ⟨msNew, tyMsNew, hpermNew⟩ :=
        ChildrenTyped.merge mrgC.sym singleΘ' tyRest (oneCtx_children _ tyNode'')
      have eNew : l ++ (Chan.var_Chan cx, .node (Chan.var_Chan dx)
          (N.eval (.pure (.chan (Chan.var_Chan dx)))) ms' qs') :: r
          = msNew :=
        child_sorted_eq
          (List.perm_middle.trans
            ((List.perm_append_singleton _ _).symm.trans hpermNew.symm))
          (sorted_replace (ChildrenTyped.sorted tyms))
          (ChildrenTyped.sorted tyMsNew)
      rw [eNew]
      exact Typed.root singleΘ' tyTermP tyMsNew tyqs
  | @nodeRecvIm M N p o c d l r ms' qs qs' implicit =>
      refine ⟨fun ty _ => (by cases ty), fun ry Ay ty dist => ?_⟩
      cases ty with
      | @node Θ0 y _ _ _ _ _ single has tym tyms tyqs =>
      cases c with
      | var_Chan cx =>
      cases d with
      | var_Chan dx =>
      -- parent term: peel the recv redex
      obtain ⟨Θ1, Θ2, A0, mrg, tyRecv, cont⟩ := evalCtx_inv tym
      obtain ⟨rr1, rr2, AAr, BBr, xorR, eqMR, tyvR⟩ := recvIm_inv tyRecv
      obtain ⟨rJR, AJR, jsP, tyAJR, eqChR⟩ := chan_inv tyvR
      rw [cren_len_nil] at eqChR
      obtain ⟨err, eActR⟩ := Static.ch_inj eqChR
      subst err
      -- select and invert the sending child
      obtain ⟨C, tyChildAt, convC, tyRest⟩ := ChildrenTypedAt.remove jsP mrg tyms rfl rfl
      cases tyChildAt with
      | @node Θc _ _ _ _ _ _ singleC hasD tyN tyms' tyqs' =>
      obtain ⟨Θc1, Θc2, AR0, mrgR, tyApp, contR⟩ := evalCtx_inv tyN
      obtain ⟨AS, BS, sS, tySend, tyMsg, eqApp⟩ := appIm_inv tyApp
      obtain ⟨rs1, rs2, AAs, BBs, xorS, eqPiS, tyvS⟩ := sendIm_inv tySend
      obtain ⟨rJS, AJS, jsC, tyAJS, eqChS⟩ := chan_inv tyvS
      rw [cren_len_nil] at eqChS
      obtain ⟨ers, eActS⟩ := Static.ch_inj eqChS
      subst ers
      obtain ⟨hrr, hAJS⟩ := PJust_PHas_agree singleC mrgR jsC hasD
      have hrr1 : rr1 = !rs1 := by rw [hrr, Bool.not_not]
      subst hrr1
      -- session-protocol duality
      have eActS' : (Term.act rs2 AAs BBs .im) ≃ C := by rw [← hAJS]; exact eActS
      have eSR := ARS.conv_trans eActS'
        (ARS.conv_trans convC (ARS.conv_sym eActR))
      obtain ⟨eAAsr, eBBsr, _, _⟩ := Static.act_inj eSR
      -- protocol typings and the advanced protocol `W` (from the sending child)
      obtain ⟨_, tyChS⟩ := tyvS.validity
      obtain ⟨tyActS, _⟩ := Static.ch_inv tyChS
      have tyBBs := Static.act_inv tyActS
      obtain ⟨_, tyAAs⟩ : ∃ s, ([] : Static.Ctx) ⊢ AAs : Term.srt s := by
        cases tyBBs.wf with | cons _ h => exact ⟨_, h⟩
      obtain ⟨eAS, eBS, _, _⟩ := Static.pi_inj eqPiS
      have tyMsgA : ([] : Static.Ctx) ⊢ o : AAs := Static.Typed.conv eAS tyMsg tyAAs
      have tyW : ([] : Static.Ctx) ⊢ BBs[Chan.var_Chan; o..] : .proto := by
        have h := tyBBs.subst tyMsgA
        asimp at h
        exact h
      have single1 := (PCtxSingle.split single mrg).1
      have single2 := (PCtxSingle.split single mrg).2
      have singleC2 := (PCtxSingle.split singleC mrgR).2
      -- the reserved parent endpoint stays with the continuation
      have hcy : cx ≠ y :=
        ChildrenTypedAt.label_ne_parent (c := Chan.var_Chan cx) tyms
          (by simp [childLabels])
      have posY1 : CvarPos Θ1 y false := (jsP.pos_false).mpr hcy
      -- parent continuation: receive the pair at the advanced endpoint `cx`
      have posCx1 : CvarPos Θ1 cx true := (jsP.pos_true).mpr rfl
      have hlen2 : cx < Θ2.length := by
        have h := CvarPos.lt_length (CvarPos.merge_true_left single mrg posCx1)
        rw [PMerge.length_right mrg]
        omega
      have hC2dead : CvarPos Θ2 cx true → False := fun h =>
        PCtxSingle.merge_true_excl single mrg posCx1 h
      obtain ⟨Θ', mrgC, singleΘ'⟩ :=
        oneCtx_merge (Θ := Θ2) (x := cx) (r := !rs1)
          (W := shiftK dx (BBs[Chan.var_Chan; o..])) single2 hlen2 hC2dead
      obtain ⟨_, tyChR⟩ := tyvR.validity
      obtain ⟨tyActR, _⟩ := Static.ch_inv tyChR
      have tyBBr := Static.act_inv tyActR
      obtain ⟨_, tyAAr⟩ : ∃ s, ([] : Static.Ctx) ⊢ AAr : Term.srt s := by
        cases tyBBr.wf with | cons _ h => exact ⟨_, h⟩
      have tyMsgR : ([] : Static.Ctx) ⊢ o : AAr :=
        Static.Typed.conv (ARS.conv_trans eAS eAAsr) tyMsg tyAAr
      obtain ⟨_, tyMAR0⟩ := tyRecv.validity
      have tyPairP : (oneCtx cx (!rs1) (shiftK dx (BBs[Chan.var_Chan; o..])) Θ2.length) ⨾
          ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢
          .pure (.pair o (.chan (Chan.var_Chan cx)) .im .L) : .M A0 := by
        refine Typed.conv (ARS.conv_sym eqMR) (.pure ?_) tyMAR0
        refine Typed.pairIm
          (Static.Typed.sig (by nofun) Static.sort_leq_Lgt tyAAr (Static.Typed.ch tyBBr))
          tyMsgR ?_
        refine Typed.conv (s := .L)
          (Static.conv_ch (Static.conv_subst (o..) eBBsr))
          (oneCtx_chan _ (shiftK_proto tyW dx) (shiftK_conv _ dx) tyW) ?_
        have h := Static.Typed.ch (b := !rs1) (tyBBr.subst tyMsgR)
        asimp at h ⊢
        exact h
      have tyTermP := cont _ Θ' _ mrgC.sym tyPairP
      -- child continuation: return the advanced endpoint `dx`
      have posDx1 : CvarPos Θc1 dx true := (jsC.pos_true).mpr rfl
      have hlenC2 : dx < Θc2.length := by
        have h := CvarPos.lt_length (CvarPos.merge_true_left singleC mrgR posDx1)
        rw [PMerge.length_right mrgR]
        omega
      have hD2dead : CvarPos Θc2 dx true → False := fun h =>
        PCtxSingle.merge_true_excl singleC mrgR posDx1 h
      obtain ⟨Θc', mrgD', singleC'⟩ :=
        oneCtx_merge (Θ := Θc2) (x := dx) (r := rs1)
          (W := BBs[Chan.var_Chan; o..]) singleC2 hlenC2 hD2dead
      have tyChanD := oneCtx_chan (x := dx) (r := rs1)
        (W := BBs[Chan.var_Chan; o..]) (B := BBs[Chan.var_Chan; o..])
        Θc2.length tyW ARS.Conv.refl tyW
      obtain ⟨_, tyMAS0⟩ := tyApp.validity
      have tyPureD : (oneCtx dx rs1 (BBs[Chan.var_Chan; o..]) Θc2.length) ⨾
          ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢
          .pure (.chan (Chan.var_Chan dx)) : .M AR0 := by
        refine Typed.conv ?_ (Typed.pure tyChanD) tyMAS0
        refine ARS.conv_sym (ARS.conv_trans eqApp ?_)
        exact Static.conv_subst (o..) eBS
      have tyTermC := contR _ Θc' _ mrgD'.sym tyPureD
      -- the updated child node
      have tyRest' := ChildrenTypedAt.strengthen jsC mrgR tyms'
      have tymsAt' := ChildrenTypedAt.intro (oneCtx_just Θc2.length) mrgD' singleC' tyRest'
      have hasD' : PHas Θc' dx rs1 (shiftK (dx + 1) (BBs[Chan.var_Chan; o..])) :=
        PHas.merge_left singleC' mrgD' (PJust.toPHas (oneCtx_just _))
      have tyNode' : TypedAt rs1 (shiftK (dx + 1) (BBs[Chan.var_Chan; o..]))
          (.node (Chan.var_Chan dx)
            (N.eval (.pure (.chan (Chan.var_Chan dx)))) ms' qs') :=
        TypedAt.node singleC' hasD' tyTermC tymsAt' tyqs'
      have tyNode'' : TypedAt (!(!rs1)) (shiftK 1 (shiftK dx (BBs[Chan.var_Chan; o..])))
          (.node (Chan.var_Chan dx)
            (N.eval (.pure (.chan (Chan.var_Chan dx)))) ms' qs') := by
        rw [Bool.not_not]
        exact tyNode'
      -- the reserved parent endpoint survives into the final context
      have hasY : PHas Θ' y ry Ay :=
        PHas.merge_right singleΘ' mrgC (PHas.merge_inv_right mrg has posY1)
      -- reassemble the parent
      obtain ⟨msNew, tyMsNew, hpermNew⟩ :=
        ChildrenTypedAt.merge mrgC.sym singleΘ' tyRest (oneCtx_children _ tyNode'')
      have eNew : l ++ (Chan.var_Chan cx, .node (Chan.var_Chan dx)
          (N.eval (.pure (.chan (Chan.var_Chan dx)))) ms' qs') :: r
          = msNew :=
        child_sorted_eq
          (List.perm_middle.trans
            ((List.perm_append_singleton _ _).symm.trans hpermNew.symm))
          (sorted_replace (ChildrenTypedAt.sorted tyms))
          (ChildrenTypedAt.sorted tyMsNew)
      rw [eNew]
      exact TypedAt.node singleΘ' hasY tyTermP tyMsNew tyqs
  | @nodeForward M N p v c d l r ms' qs qs' value occursP =>
      refine ⟨fun ty _ => (by cases ty), fun ry Ay ty dist => ?_⟩
      cases ty with
      | @node Θ0 y _ _ _ _ _ single has tym tyms tyqs =>
      cases c with
      | var_Chan cx =>
      cases d with
      | var_Chan dx =>
      have occursP' : occurs y v ≠ 0 := occursP
      -- parent term: peel the send redex and its payload (which carries `y`)
      obtain ⟨Θ1, Θ2, A0, mrg, tyApp, cont⟩ := evalCtx_inv tym
      obtain ⟨AS, BS, sS, ΘF, ΘV, ΔF, ΔV, mrgApp, mrgΔ, tySend, tyV, eqApp⟩ :=
        appEx_inv tyApp
      cases mrgΔ
      obtain ⟨rs1, rs2, AAs, BBs, xorS, eqPiS, tyvS⟩ := sendEx_inv tySend
      obtain ⟨rJS, AJS, jsF, tyAJS, eqChS⟩ := chan_inv tyvS
      rw [cren_len_nil] at eqChS
      obtain ⟨ers, eActS⟩ := Static.ch_inj eqChS
      subst ers
      have single1 := (PCtxSingle.split single mrg).1
      have single2 := (PCtxSingle.split single mrg).2
      have singleF := (PCtxSingle.split single1 mrgApp).1
      have singleV := (PCtxSingle.split single1 mrgApp).2
      -- the parent endpoint `y` sits inside the payload context
      have posYV : CvarPos ΘV y true := by
        rcases PCtxSingle.pos_total singleV y with h | h
        · exact h
        · exact absurd (tyV.occurs0 h) occursP'
      have posY2 : CvarPos Θ2 y false := by
        rcases PCtxSingle.pos_total single2 y with h | h
        · exact absurd h (fun h2 => PCtxSingle.merge_true_excl single mrg
            (CvarPos.merge_true_right single1 mrgApp posYV) h2)
        · exact h
      have posYF : CvarPos ΘF y false := by
        have hcy : cx ≠ y :=
          ChildrenTypedAt.label_ne_parent (c := Chan.var_Chan cx) tyms
            (by simp [childLabels])
        exact (jsF.pos_false).mpr hcy
      -- select and invert the receiving child
      obtain ⟨ΘR, mrgV2, mrgFR⟩ := PMerge.splitR mrg mrgApp
      have singleR := (PCtxSingle.split single mrgFR.sym).2
      obtain ⟨C, tyChildAt, convC, tyRest⟩ :=
        ChildrenTypedAt.remove jsF mrgFR.sym tyms rfl rfl
      -- split the surviving children by the payload; the parent endpoint moves with it
      obtain ⟨ms2, msV, tyMs2, tyMsVAt, hpermR⟩ :=
        ChildrenTypedAt.split_right mrgV2.sym singleR tyRest posY2
      obtain ⟨permSplit1, permSplit2⟩ :=
        split_children_perm (w := v) singleR mrgV2
          (fun p hp => ChildrenTyped.pos_of_label tyMs2 (List.mem_map.mpr ⟨p, hp, rfl⟩))
          (List.Nodup.of_map _ (ChildrenTypedAt.labels_nodup tyMsVAt))
          (List.Nodup.of_map _ (ChildrenTyped.labels_nodup tyMs2))
          (hpermR.trans List.perm_append_comm)
          (ChildrenTypedAt.labels_nodup tyRest)
          (fun p hp => tyV.occurs1
            (ChildrenTypedAt.pos_of_label tyMsVAt (List.mem_map.mpr ⟨p, hp, rfl⟩)))
          (fun i h => tyV.occurs0 h)
      cases tyChildAt with
      | @node Θc _ _ _ _ _ _ singleC hasD tyN tyms' tyqs' =>
      -- pad the child context and the payload context to a common length
      have tyNpad := Typed.padR Θ0.length tyN
      have tyms'pad := ChildrenTypedAt.padR Θ0.length tyms'
      have singleCpad : PCtxSingle (Θc ++ List.replicate Θ0.length Slot.none) :=
        PCtxSingle.append singleC (PCtxSingle.replicate _)
      have hasDpad := PHas.padR Θ0.length hasD
      have hLenCpad : (Θc ++ List.replicate Θ0.length Slot.none).length
          = Θc.length + Θ0.length := by simp
      obtain ⟨Θc1, Θc2, AR0, mrgR, tyRecv, contR⟩ := evalCtx_inv tyNpad
      obtain ⟨rr1, rr2, AAr, BBr, xorR, eqMR, tyvR⟩ := recvEx_inv tyRecv
      obtain ⟨rJR, AJR, jsR, tyAJR, eqChR⟩ := chan_inv tyvR
      rw [cren_len_nil] at eqChR
      obtain ⟨err, eActR⟩ := Static.ch_inj eqChR
      subst err
      obtain ⟨hrr, hAJR⟩ := PJust_PHas_agree singleCpad mrgR jsR hasDpad
      subst hrr
      -- session-protocol duality
      have eActR' : (Term.act rr2 AAr BBr .ex) ≃ C := by rw [← hAJR]; exact eActR
      have eSR := ARS.conv_trans eActS
        (ARS.conv_sym (ARS.conv_trans eActR' convC))
      obtain ⟨eAAsr, eBBsr, _, _⟩ := Static.act_inj eSR
      -- protocol typings and the advanced protocol `W`
      obtain ⟨_, tyChS⟩ := tyvS.validity
      obtain ⟨tyActS, _⟩ := Static.ch_inv tyChS
      have tyBBs := Static.act_inv tyActS
      obtain ⟨_, tyAAs⟩ : ∃ s, ([] : Static.Ctx) ⊢ AAs : Term.srt s := by
        cases tyBBs.wf with | cons _ h => exact ⟨_, h⟩
      obtain ⟨eAS, eBS, _, _⟩ := Static.pi_inj eqPiS
      have tyVA : ΘV ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ v : AAs :=
        Typed.conv eAS tyV tyAAs
      have tyW : ([] : Static.Ctx) ⊢ BBs[Chan.var_Chan; v..] : .proto := by
        have h := tyBBs.subst tyVA.toStatic
        asimp at h
        exact h
      -- Distinct-derived freshness of the moved endpoints
      have hnodup : (((l ++ (Chan.var_Chan cx,
            Tree.node (Chan.var_Chan dx) (N.eval (.recv (Term.chan (Chan.var_Chan dx)) .ex))
              ms' qs') :: r).map (fun e => chanIndex e.1)) ++
          childInteriors (l ++ (Chan.var_Chan cx,
            Tree.node (Chan.var_Chan dx) (N.eval (.recv (Term.chan (Chan.var_Chan dx)) .ex))
              ms' qs') :: r)).Nodup :=
        labelsInteriors_sublist_node.nodup dist
      have memChild : (Chan.var_Chan cx,
          Tree.node (Chan.var_Chan dx) (N.eval (.recv (Term.chan (Chan.var_Chan dx)) .ex))
            ms' qs') ∈ l ++ (Chan.var_Chan cx,
          Tree.node (Chan.var_Chan dx) (N.eval (.recv (Term.chan (Chan.var_Chan dx)) .ex))
            ms' qs') :: r := by simp
      have hdxFresh := child_node_label_fresh hnodup memChild
      have hdxNeY : dx ≠ y := child_node_label_ne_parent dist memChild
      have vLabel : ∀ i, CvarPos ΘV i true →
          Chan.var_Chan i ∈ childLabels (l ++ (Chan.var_Chan cx,
            Tree.node (Chan.var_Chan dx) (N.eval (.recv (Term.chan (Chan.var_Chan dx)) .ex))
              ms' qs') :: r) ∨ i = y := fun i h =>
        ChildrenTypedAt.label_of_pos tyms
          (CvarPos.merge_true_left single mrg (CvarPos.merge_true_right single1 mrgApp h))
      -- the advanced child endpoint is dead in the child's continuation
      have posDx1 : CvarPos Θc1 dx true := (jsR.pos_true).mpr rfl
      have hD2dead : CvarPos Θc2 dx true → False := fun h =>
        PCtxSingle.merge_true_excl singleCpad mrgR posDx1 h
      have hlenC2 : dx < Θc2.length := by
        have h := CvarPos.lt_length (CvarPos.merge_true_left singleCpad mrgR posDx1)
        rw [hLenCpad] at h
        rw [PMerge.length_right mrgR, hLenCpad]
        omega
      -- live endpoints of the child's continuation are grandchild labels
      have cLabel : ∀ i, CvarPos Θc2 i true → Chan.var_Chan i ∈ childLabels ms' := by
        intro i h
        rcases ChildrenTypedAt.label_of_pos tyms'pad
            (CvarPos.merge_true_right singleCpad mrgR h) with hmem | hy
        · exact hmem
        · subst hy
          exact absurd h hD2dead
      -- assemble the new top node's endpoint context
      have hLenΘc2 : Θc2.length = Θc.length + Θ0.length := by
        rw [PMerge.length_right mrgR, hLenCpad]
      have tyMsVAtPad := ChildrenTypedAt.padR Θc.length tyMsVAt
      have tyVApad := Typed.padR Θc.length tyVA
      have singleVpad : PCtxSingle (ΘV ++ List.replicate Θc.length Slot.none) :=
        PCtxSingle.append singleV (PCtxSingle.replicate _)
      have hLenV : ΘV.length = Θ0.length := by
        rw [PMerge.length_right mrgApp, PMerge.length_left mrg]
      obtain ⟨Θ3R, mrgPair, single3R⟩ :=
        pmerge_single_disjoint
          (Θ1 := ΘV ++ List.replicate Θc.length Slot.none)
          (Θ2 := oneCtx dx (!rs1) (shiftK cx (BBs[Chan.var_Chan; v..]))
            (Θc.length + Θ0.length))
          (by simp [oneCtx]; omega)
          singleVpad (oneCtx_single _)
          (by
            intro i h1 h2
            have hdx : dx = i :=
              ((oneCtx_just (x := dx) (r := !rs1)
                (W := shiftK cx (BBs[Chan.var_Chan; v..]))
                (Θc.length + Θ0.length)).pos_true).mp h2
            subst hdx
            have hV : CvarPos ΘV dx true :=
              CvarPos.of_append_true (PEmpty.replicate _) h1
            rcases vLabel dx hV with hmem | hy
            · exact hdxFresh hmem
            · exact hdxNeY hy)
      have hLen3R : Θ3R.length = Θc.length + Θ0.length := by
        rw [← PMerge.length_left mrgPair]
        simp
        omega
      obtain ⟨Θtop, mrgFinalC, singleTop⟩ :=
        pmerge_single_disjoint (Θ1 := Θ3R) (Θ2 := Θc2)
          (by rw [hLen3R, PMerge.length_right mrgR, hLenCpad])
          single3R (PCtxSingle.split singleCpad mrgR).2
          (by
            intro i h1 h2
            rcases CvarPos.split_true mrgPair h1 with ⟨_, hone⟩ | ⟨hV, _⟩
            · have hdx : dx = i :=
                ((oneCtx_just (x := dx) (r := !rs1)
                  (W := shiftK cx (BBs[Chan.var_Chan; v..]))
                  (Θc.length + Θ0.length)).pos_true).mp hone
              subst hdx
              exact hD2dead h2
            · have hVi : CvarPos ΘV i true :=
                CvarPos.of_append_true (PEmpty.replicate _) hV
              have hmemC := cLabel i h2
              obtain ⟨⟨e, gc⟩, memPair, heq⟩ := List.mem_map.mp hmemC
              have he : e = Chan.var_Chan i := heq
              subst he
              rcases vLabel i hVi with hmemV | hy
              · exact (grandchild_fresh hnodup memChild memPair).2 hmemV
              · subst hy
                exact grandchild_ne_node_parent dist memChild memPair rfl)
      -- the new top node's term: receive the forwarded pair
      obtain ⟨_, tyChR⟩ := tyvR.validity
      obtain ⟨tyActR, _⟩ := Static.ch_inv tyChR
      have tyBBr := Static.act_inv tyActR
      obtain ⟨_, tyAAr⟩ : ∃ s, ([] : Static.Ctx) ⊢ AAr : Term.srt s := by
        cases tyBBr.wf with | cons _ h => exact ⟨_, h⟩
      have tyMsgR : (ΘV ++ List.replicate Θc.length Slot.none) ⨾
          ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ v : AAr :=
        Typed.conv eAAsr tyVApad tyAAr
      obtain ⟨_, tyMAR0⟩ := tyRecv.validity
      have tyPairR : Θ3R ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢
          .pure (.pair v (.chan (Chan.var_Chan dx)) .ex .L) : .M AR0 := by
        refine Typed.conv (ARS.conv_sym eqMR) (.pure ?_) tyMAR0
        refine Typed.pairEx mrgPair .nil
          (Static.Typed.sig (fun _ => Static.sort_leq_Lgt) Static.sort_leq_Lgt tyAAr
            (Static.Typed.ch tyBBr))
          tyMsgR ?_
        refine Typed.conv (s := .L)
          (Static.conv_ch (Static.conv_subst (v..) eBBsr))
          (oneCtx_chan _ (shiftK_proto tyW cx) (shiftK_conv _ cx) tyW) ?_
        have h := Static.Typed.ch (b := !rs1) (tyBBr.subst tyMsgR.toStatic)
        asimp at h ⊢
        exact h
      have tyTermTop := contR _ Θtop _ mrgFinalC.sym tyPairR
      -- the old node becomes a child: its continuation returns the advanced endpoint
      have posCx1 : CvarPos Θ1 cx true :=
        CvarPos.merge_true_left single1 mrgApp ((jsF.pos_true).mpr rfl)
      have hlen2 : cx < Θ2.length := by
        have h := CvarPos.lt_length (CvarPos.merge_true_left single mrg posCx1)
        rw [PMerge.length_right mrg]
        omega
      have hC2dead : CvarPos Θ2 cx true → False := fun h =>
        PCtxSingle.merge_true_excl single mrg posCx1 h
      obtain ⟨Θop, mrgCP, singleOP⟩ :=
        oneCtx_merge (Θ := Θ2) (x := cx) (r := rs1)
          (W := BBs[Chan.var_Chan; v..]) single2 hlen2 hC2dead
      have tyChanC := oneCtx_chan (x := cx) (r := rs1)
        (W := BBs[Chan.var_Chan; v..]) (B := BBs[Chan.var_Chan; v..])
        Θ2.length tyW ARS.Conv.refl tyW
      obtain ⟨_, tyMAS0⟩ := tyApp.validity
      have tyPureC : (oneCtx cx rs1 (BBs[Chan.var_Chan; v..]) Θ2.length) ⨾
          ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢
          .pure (.chan (Chan.var_Chan cx)) : .M A0 := by
        refine Typed.conv ?_ (Typed.pure tyChanC) tyMAS0
        refine ARS.conv_sym (ARS.conv_trans eqApp ?_)
        exact Static.conv_subst (v..) eBS
      have tyTermOP := cont _ Θop _ mrgCP.sym tyPureC
      have tymsAtOP : ChildrenTypedAt Θop cx rs1
          (shiftK (cx + 1) (BBs[Chan.var_Chan; v..])) ms2 :=
        ChildrenTypedAt.intro (oneCtx_just _) mrgCP singleOP tyMs2
      have hasCP : PHas Θop cx rs1 (shiftK (cx + 1) (BBs[Chan.var_Chan; v..])) :=
        PHas.merge_left singleOP mrgCP (PJust.toPHas (oneCtx_just _))
      have tyOldParent : TypedAt rs1 (shiftK (cx + 1) (BBs[Chan.var_Chan; v..]))
          (.node (Chan.var_Chan cx) (M.eval (.pure (Term.chan (Chan.var_Chan cx))))
            ms2 qs) :=
        TypedAt.node singleOP hasCP tyTermOP tymsAtOP tyqs
      have tyOldParent' : TypedAt (!(!rs1))
          (shiftK 1 (shiftK cx (BBs[Chan.var_Chan; v..])))
          (.node (Chan.var_Chan cx) (M.eval (.pure (Term.chan (Chan.var_Chan cx))))
            ms2 qs) := by
        rw [Bool.not_not]
        exact tyOldParent
      -- the new top node's children
      have tyRest' := ChildrenTypedAt.strengthen jsR mrgR tyms'pad
      obtain ⟨ΘVc2, mrgVc2, mrgOne⟩ := PMerge.splitL mrgFinalC mrgPair
      have singleVc2 : PCtxSingle ΘVc2 := (PCtxSingle.split singleTop mrgOne).1
      obtain ⟨msMid, tyMsMid, hpermMid⟩ :=
        ChildrenTypedAt.merge mrgVc2 singleVc2 tyMsVAtPad tyRest'
      obtain ⟨msTop, tyMsTop, hpermTop⟩ :=
        ChildrenTypedAt.merge mrgOne singleTop tyMsMid
          (oneCtx_children _ tyOldParent')
      -- the reserved parent endpoint survives into the new top context
      have hasY : PHas Θtop y ry Ay := by
        have h1 : PHas Θ1 y ry Ay := PHas.merge_inv_right mrg.sym has posY2
        have h2 : PHas ΘV y ry Ay := PHas.merge_inv_right mrgApp h1 posYF
        exact PHas.merge_left singleTop mrgOne
          (PHas.merge_left singleVc2 mrgVc2 (PHas.padR _ h2))
      -- assemble
      have hsim : forwardChildren v (Chan.var_Chan cx) (Chan.var_Chan dx) M ms'
          (l ++ r) qs
          = insertChild (Chan.var_Chan dx)
            (.node (Chan.var_Chan cx) (M.eval (.pure (Term.chan (Chan.var_Chan cx))))
              (splitChildrenByTerm v (l ++ r)).2 qs)
            (mergeChildren (splitChildrenByTerm v (l ++ r)).1 ms') := by
        simp [forwardChildren]
      have sortedRest := ChildrenTypedAt.sorted tyRest
      have e1 : (splitChildrenByTerm v (l ++ r)).1 = msV :=
        child_sorted_eq permSplit1
          (List.Pairwise.sublist (splitChildrenByTerm_sublist₁ v (l ++ r)) sortedRest)
          (ChildrenTypedAt.sorted tyMsVAt)
      have e2 : (splitChildrenByTerm v (l ++ r)).2 = ms2 :=
        child_sorted_eq permSplit2
          (List.Pairwise.sublist (splitChildrenByTerm_sublist₂ v (l ++ r)) sortedRest)
          (ChildrenTyped.sorted tyMs2)
      have nodupVms' : (childLabels (msV ++ ms')).Nodup :=
        (List.Perm.map Prod.fst hpermMid).nodup
          (ChildrenTypedAt.labels_nodup tyMsMid)
      have eMid : mergeChildren msV ms' = msMid :=
        child_sorted_eq
          ((mergeChildren_perm msV ms').trans hpermMid.symm)
          (sorted_mergeChildren (ChildrenTyped.sorted tyRest') nodupVms')
          (ChildrenTypedAt.sorted tyMsMid)
      have freshMid : ∀ p : Chan × Tree, p ∈ msMid →
          chanIndex (Chan.var_Chan dx) ≠ chanIndex p.1 := by
        intro p hp he
        have hpos := ChildrenTypedAt.pos_of_label tyMsMid (List.mem_map.mpr ⟨p, hp, rfl⟩)
        have he' : dx = chanIndex p.1 := he
        rw [← he'] at hpos
        rcases CvarPos.split_true mrgVc2 hpos with ⟨_, h2⟩ | ⟨hV, _⟩
        · exact hD2dead h2
        · have hVi : CvarPos ΘV dx true :=
            CvarPos.of_append_true (PEmpty.replicate _) hV
          rcases vLabel dx hVi with hmem | hy
          · exact hdxFresh hmem
          · exact hdxNeY hy
      have eTop : insertChild (Chan.var_Chan dx)
          (.node (Chan.var_Chan cx) (M.eval (.pure (Term.chan (Chan.var_Chan cx))))
            ms2 qs) msMid = msTop :=
        child_sorted_eq
          ((insertChild_perm _ _ _).trans
            ((List.perm_append_singleton _ _).symm.trans hpermTop.symm))
          (sorted_insertChild (ChildrenTypedAt.sorted tyMsMid) freshMid)
          (ChildrenTypedAt.sorted tyMsTop)
      rw [hsim, e1, e2, eMid, eTop]
      exact TypedAt.node singleTop hasY tyTermTop tyMsTop tyqs'
  | @rootChild m c child child' l r qs st' _avoids ih =>
      refine ⟨fun ty dist => ?_, fun ry Ay ty _ => (by cases ty)⟩
      cases ty with
      | root single tym tyms tyqs =>
          have distC : Distinct child := Distinct.child_root (c := c) dist (by simp)
          obtain ⟨u, rfl, tyms'⟩ :=
            ChildrenTyped.replace_via (F := fun _ u => u = child') tyms rfl
              (fun rc C tyc => ⟨child', rfl, ih.2 rc C tyc distC⟩)
          exact Typed.root single tym tyms' tyqs
  | @nodeChild p m c child child' l r qs st' _avoids ih =>
      refine ⟨fun ty _ => (by cases ty), fun ry Ay ty dist => ?_⟩
      cases ty with
      | node single has tym tyms tyqs =>
          have distC : Distinct child := Distinct.child_node (c := c) dist (by simp)
          obtain ⟨u, rfl, tyms'⟩ :=
            ChildrenTypedAt.replace_via (F := fun _ u => u = child') tyms rfl
              (fun rc C tyc => ⟨child', rfl, ih.2 rc C tyc distC⟩)
          exact TypedAt.node single has tym tyms' tyqs
  | @rootSubtree m ms sub sub' l r st' _avoids ih =>
      refine ⟨fun ty dist => ?_, fun ry Ay ty _ => (by cases ty)⟩
      cases ty with
      | root single tym tyms tyqs =>
          have distS : Distinct sub := Distinct.subtree_root dist (by simp)
          obtain ⟨u, rfl, tyqs'⟩ :=
            SubtreesTyped.replace_via (F := fun _ u => u = sub') tyqs
              (fun tys => ⟨sub', rfl, ih.1 tys distS⟩)
          exact Typed.root single tym tyms tyqs'
  | @nodeSubtree p m ms sub sub' l r st' _avoids ih =>
      refine ⟨fun ty _ => (by cases ty), fun ry Ay ty dist => ?_⟩
      cases ty with
      | node single has tym tyms tyqs =>
          have distS : Distinct sub := Distinct.subtree_node dist (by simp)
          obtain ⟨u, rfl, tyqs'⟩ :=
            SubtreesTyped.replace_via (F := fun _ u => u = sub') tyqs
              (fun tys => ⟨sub', rfl, ih.1 tys distS⟩)
          exact TypedAt.node single has tym tyms tyqs'
  | @rootExpr m m' ms qs dst =>
      refine ⟨fun ty dist => ?_, fun ry Ay ty _ => (by cases ty)⟩
      cases ty with
      | root single tym tyms tyqs =>
          exact Typed.root single (tym.sr dst) tyms tyqs
  | @nodeExpr p m m' ms qs dst =>
      refine ⟨fun ty _ => (by cases ty), fun ry Ay ty dist => ?_⟩
      cases ty with
      | node single has tym tyms tyqs =>
          exact TypedAt.node single has (tym.sr dst) tyms tyqs

/-! ## Distinctness preservation

Only the fork rules create channels; every other rule permutes or drops them. The fork side
conditions (`forkFresh`) and the congruence side conditions (`stepAvoids`) are exactly what keeps
the global channel multiset duplicate-free, so `Distinct` is an invariant of reduction and the
fidelity/simulation theorems can be iterated along `Red`. -/

lemma childChansM_insertChild (c : Chan) (t : Tree) (ms : List (Chan × Tree)) :
    childChansM (insertChild c t ms) = (chanIndex c ::ₘ treeChansM t) + childChansM ms := by
  rw [childChansM_perm (insertChild_perm c t ms), childChansM_cons]

lemma childChansM_mergeChildren (extra base : List (Chan × Tree)) :
    childChansM (mergeChildren extra base) = childChansM extra + childChansM base := by
  rw [childChansM_perm (mergeChildren_perm extra base), childChansM_append]

lemma childChansM_split (v : Term) (ms : List (Chan × Tree)) :
    childChansM (splitChildrenByTerm v ms).1 + childChansM (splitChildrenByTerm v ms).2
      = childChansM ms := by
  rw [← childChansM_perm (splitChildrenByTerm_perm v ms), childChansM_append]
  exact add_comm _ _

/-- Replacing a sub-multiset by a duplicate-free one whose new elements avoid the whole keeps the
whole duplicate-free. -/
lemma nodupM_replace {ctx s s' : Multiset Nat}
    (h : (ctx + s).Nodup) (hs' : s'.Nodup)
    (avoid : ∀ x ∈ s', x ∉ s → x ∉ ctx + s) : (ctx + s').Nodup := by
  rw [Multiset.nodup_add] at h ⊢
  refine ⟨h.1, hs', Multiset.disjoint_left.mpr ?_⟩
  intro x hxc hxs'
  by_cases hxs : x ∈ s
  · exact Multiset.disjoint_left.mp h.2.2 hxc hxs
  · exact avoid x hxs' hxs (Multiset.mem_add.mpr (Or.inl hxc))

/-- Channel distinctness is preserved by spawning-tree reduction. -/
theorem Step.distinct {t t' : Tree} (st : Step t t') : Distinct t → Distinct t' := by
  simp only [distinct_iff_nodupM]
  induction st with
  | @rootFork M A m c d ms qs _freshC _freshD treeFresh =>
      intro h
      obtain ⟨hc, hd, hcd⟩ := treeFresh
      have e : treeChansM (.root (M.eval (.pure (Term.chan c))) (forkChildren m c d ms) qs)
          = chanIndex c ::ₘ chanIndex d ::ₘ treeChansM (.root (M.eval (.fork A m)) ms qs) := by
        simp only [treeChansM_root, forkChildren, childChansM_insertChild, treeChansM_node,
          subChansM_nil, add_zero, ← Multiset.singleton_add]
        rw [← childChansM_split m ms]
        abel
      rw [e, Multiset.nodup_cons, Multiset.nodup_cons]
      refine ⟨?_, by simpa only [mem_treeChansM] using hd, h⟩
      simp only [Multiset.mem_cons, mem_treeChansM]
      exact fun h' => h'.elim hcd hc
  | @nodeFork M p A m c d ms qs _freshC _freshD _freshP treeFresh =>
      intro h
      obtain ⟨hc, hd, hcd⟩ := treeFresh
      have e : treeChansM (.node p (M.eval (.pure (Term.chan c))) (forkChildren m c d ms) qs)
          = chanIndex c ::ₘ chanIndex d ::ₘ treeChansM (.node p (M.eval (.fork A m)) ms qs) := by
        simp only [treeChansM_root, forkChildren, childChansM_insertChild, treeChansM_node,
          subChansM_nil, add_zero, ← Multiset.singleton_add]
        rw [← childChansM_split m ms]
        abel
      rw [e, Multiset.nodup_cons, Multiset.nodup_cons]
      refine ⟨?_, by simpa only [mem_treeChansM] using hd, h⟩
      simp only [Multiset.mem_cons, mem_treeChansM]
      exact fun h' => h'.elim hcd hc
  | @rootWait M N c d l r ms' qs qs' =>
      intro h
      have e : treeChansM (.root (M.eval (.close false (Term.chan c)))
            (l ++ (c, .node d (N.eval (.close true (Term.chan d))) ms' qs') :: r) qs)
          = chanIndex c ::ₘ chanIndex d ::ₘ
              treeChansM (.root (M.eval (.pure .one)) (l ++ r)
                (qs ++ [Tree.root (N.eval (.pure .one)) ms' qs'])) := by
        simp only [treeChansM_root, treeChansM_node, childChansM_append, childChansM_cons,
          childChansM_nil, subChansM_append, subChansM_cons, subChansM_nil, add_zero,
          ← Multiset.singleton_add]
        abel
      rw [e] at h
      exact (Multiset.nodup_cons.mp (Multiset.nodup_cons.mp h).2).2
  | @nodeWait M N p c d l r ms' qs qs' =>
      intro h
      have e : treeChansM (.node p (M.eval (.close false (Term.chan c)))
            (l ++ (c, .node d (N.eval (.close true (Term.chan d))) ms' qs') :: r) qs)
          = chanIndex c ::ₘ chanIndex d ::ₘ
              treeChansM (.node p (M.eval (.pure .one)) (l ++ r)
                (qs ++ [Tree.root (N.eval (.pure .one)) ms' qs'])) := by
        simp only [treeChansM_root, treeChansM_node, childChansM_append, childChansM_cons,
          childChansM_nil, subChansM_append, subChansM_cons, subChansM_nil, add_zero,
          ← Multiset.singleton_add]
        abel
      rw [e] at h
      exact (Multiset.nodup_cons.mp (Multiset.nodup_cons.mp h).2).2
  | @rootClose M N c d l r ms' qs qs' =>
      intro h
      have e : treeChansM (.root (M.eval (.close true (Term.chan c)))
            (l ++ (c, .node d (N.eval (.close false (Term.chan d))) ms' qs') :: r) qs)
          = chanIndex c ::ₘ chanIndex d ::ₘ
              treeChansM (.root (M.eval (.pure .one)) (l ++ r)
                (qs ++ [Tree.root (N.eval (.pure .one)) ms' qs'])) := by
        simp only [treeChansM_root, treeChansM_node, childChansM_append, childChansM_cons,
          childChansM_nil, subChansM_append, subChansM_cons, subChansM_nil, add_zero,
          ← Multiset.singleton_add]
        abel
      rw [e] at h
      exact (Multiset.nodup_cons.mp (Multiset.nodup_cons.mp h).2).2
  | @nodeClose M N p c d l r ms' qs qs' =>
      intro h
      have e : treeChansM (.node p (M.eval (.close true (Term.chan c)))
            (l ++ (c, .node d (N.eval (.close false (Term.chan d))) ms' qs') :: r) qs)
          = chanIndex c ::ₘ chanIndex d ::ₘ
              treeChansM (.node p (M.eval (.pure .one)) (l ++ r)
                (qs ++ [Tree.root (N.eval (.pure .one)) ms' qs'])) := by
        simp only [treeChansM_root, treeChansM_node, childChansM_append, childChansM_cons,
          childChansM_nil, subChansM_append, subChansM_cons, subChansM_nil, add_zero,
          ← Multiset.singleton_add]
        abel
      rw [e] at h
      exact (Multiset.nodup_cons.mp (Multiset.nodup_cons.mp h).2).2
  | @rootSendEx M N v c d l r ms' qs qs' _value =>
      intro h
      have e3 : childChansM (splitChildrenByTerm v (l ++ r)).1
            + childChansM (splitChildrenByTerm v (l ++ r)).2
          = childChansM l + childChansM r := by
        rw [childChansM_split, childChansM_append]
      have e1 : treeChansM (.root (M.eval (.pure (Term.chan c)))
            (sendExChildren v c d N ms' qs' (l ++ r)) qs)
          = (childChansM (splitChildrenByTerm v (l ++ r)).1
              + childChansM (splitChildrenByTerm v (l ++ r)).2)
            + ({chanIndex c} + {chanIndex d} + childChansM ms' + subChansM qs'
                + subChansM qs) := by
        simp only [sendExChildren, treeChansM_root, treeChansM_node, childChansM_insertChild,
          childChansM_mergeChildren, ← Multiset.singleton_add]
        abel
      have e2 : treeChansM (.root (M.eval (.app (.send (Term.chan c) .ex) v .ex))
            (l ++ (c, .node d (N.eval (.recv (Term.chan d) .ex)) ms' qs') :: r) qs)
          = (childChansM l + childChansM r)
            + ({chanIndex c} + {chanIndex d} + childChansM ms' + subChansM qs'
                + subChansM qs) := by
        simp only [treeChansM_root, treeChansM_node, childChansM_append, childChansM_cons,
          ← Multiset.singleton_add]
        abel
      rw [e1, e3, ← e2]
      exact h
  | @nodeSendEx M N p v c d l r ms' qs qs' _value _freshP =>
      intro h
      have e3 : childChansM (splitChildrenByTerm v (l ++ r)).1
            + childChansM (splitChildrenByTerm v (l ++ r)).2
          = childChansM l + childChansM r := by
        rw [childChansM_split, childChansM_append]
      have e1 : treeChansM (.node p (M.eval (.pure (Term.chan c)))
            (sendExChildren v c d N ms' qs' (l ++ r)) qs)
          = (childChansM (splitChildrenByTerm v (l ++ r)).1
              + childChansM (splitChildrenByTerm v (l ++ r)).2)
            + ({chanIndex p} + {chanIndex c} + {chanIndex d} + childChansM ms' + subChansM qs'
                + subChansM qs) := by
        simp only [sendExChildren, treeChansM_root, treeChansM_node, childChansM_insertChild,
          childChansM_mergeChildren, ← Multiset.singleton_add]
        abel
      have e2 : treeChansM (.node p (M.eval (.app (.send (Term.chan c) .ex) v .ex))
            (l ++ (c, .node d (N.eval (.recv (Term.chan d) .ex)) ms' qs') :: r) qs)
          = (childChansM l + childChansM r)
            + ({chanIndex p} + {chanIndex c} + {chanIndex d} + childChansM ms' + subChansM qs'
                + subChansM qs) := by
        simp only [treeChansM_root, treeChansM_node, childChansM_append, childChansM_cons,
          ← Multiset.singleton_add]
        abel
      rw [e1, e3, ← e2]
      exact h
  | @rootRecvEx M N v c d l r ms' qs qs' _value =>
      intro h
      have e3 : childChansM (splitChildrenByTerm v ms').1
            + childChansM (splitChildrenByTerm v ms').2
          = childChansM ms' := childChansM_split v ms'
      have e1 : treeChansM (.root (M.eval (.pure (.pair v (Term.chan c) .ex .L)))
            (recvExChildren v c d N ms' qs' (l ++ r)) qs)
          = (childChansM (splitChildrenByTerm v ms').1
              + childChansM (splitChildrenByTerm v ms').2)
            + ({chanIndex c} + {chanIndex d} + childChansM l + childChansM r + subChansM qs'
                + subChansM qs) := by
        simp only [recvExChildren, treeChansM_root, treeChansM_node, childChansM_insertChild,
          childChansM_mergeChildren, childChansM_append, ← Multiset.singleton_add]
        abel
      have e2 : treeChansM (.root (M.eval (.recv (Term.chan c) .ex))
            (l ++ (c, .node d (N.eval (.app (.send (Term.chan d) .ex) v .ex)) ms' qs') :: r) qs)
          = childChansM ms'
            + ({chanIndex c} + {chanIndex d} + childChansM l + childChansM r + subChansM qs'
                + subChansM qs) := by
        simp only [treeChansM_root, treeChansM_node, childChansM_append, childChansM_cons,
          ← Multiset.singleton_add]
        abel
      rw [e1, e3, ← e2]
      exact h
  | @nodeRecvEx M N p v c d l r ms' qs qs' _value =>
      intro h
      have e3 : childChansM (splitChildrenByTerm v ms').1
            + childChansM (splitChildrenByTerm v ms').2
          = childChansM ms' := childChansM_split v ms'
      have e1 : treeChansM (.node p (M.eval (.pure (.pair v (Term.chan c) .ex .L)))
            (recvExChildren v c d N ms' qs' (l ++ r)) qs)
          = (childChansM (splitChildrenByTerm v ms').1
              + childChansM (splitChildrenByTerm v ms').2)
            + ({chanIndex p} + {chanIndex c} + {chanIndex d} + childChansM l + childChansM r
                + subChansM qs' + subChansM qs) := by
        simp only [recvExChildren, treeChansM_root, treeChansM_node, childChansM_insertChild,
          childChansM_mergeChildren, childChansM_append, ← Multiset.singleton_add]
        abel
      have e2 : treeChansM (.node p (M.eval (.recv (Term.chan c) .ex))
            (l ++ (c, .node d (N.eval (.app (.send (Term.chan d) .ex) v .ex)) ms' qs') :: r) qs)
          = childChansM ms'
            + ({chanIndex p} + {chanIndex c} + {chanIndex d} + childChansM l + childChansM r
                + subChansM qs' + subChansM qs) := by
        simp only [treeChansM_root, treeChansM_node, childChansM_append, childChansM_cons,
          ← Multiset.singleton_add]
        abel
      rw [e1, e3, ← e2]
      exact h
  | @rootSendIm M N o c d l r ms' qs qs' _implicit =>
      intro h
      have e : treeChansM (.root (M.eval (.pure (Term.chan c)))
            (l ++ (c, .node d (N.eval (.pure (.pair o (Term.chan d) .im .L))) ms' qs') :: r) qs)
          = treeChansM (.root (M.eval (.app (.send (Term.chan c) .im) o .im))
              (l ++ (c, .node d (N.eval (.recv (Term.chan d) .im)) ms' qs') :: r) qs) := by
        simp only [treeChansM_root, treeChansM_node, childChansM_append, childChansM_cons]
      rw [e]
      exact h
  | @nodeSendIm M N p o c d l r ms' qs qs' _implicit =>
      intro h
      have e : treeChansM (.node p (M.eval (.pure (Term.chan c)))
            (l ++ (c, .node d (N.eval (.pure (.pair o (Term.chan d) .im .L))) ms' qs') :: r) qs)
          = treeChansM (.node p (M.eval (.app (.send (Term.chan c) .im) o .im))
              (l ++ (c, .node d (N.eval (.recv (Term.chan d) .im)) ms' qs') :: r) qs) := by
        simp only [treeChansM_root, treeChansM_node, childChansM_append, childChansM_cons]
      rw [e]
      exact h
  | @rootRecvIm M N o c d l r ms' qs qs' _implicit =>
      intro h
      have e : treeChansM (.root (M.eval (.pure (.pair o (Term.chan c) .im .L)))
            (l ++ (c, .node d (N.eval (.pure (Term.chan d))) ms' qs') :: r) qs)
          = treeChansM (.root (M.eval (.recv (Term.chan c) .im))
              (l ++ (c, .node d (N.eval (.app (.send (Term.chan d) .im) o .im)) ms' qs') :: r)
              qs) := by
        simp only [treeChansM_root, treeChansM_node, childChansM_append, childChansM_cons]
      rw [e]
      exact h
  | @nodeRecvIm M N p o c d l r ms' qs qs' _implicit =>
      intro h
      have e : treeChansM (.node p (M.eval (.pure (.pair o (Term.chan c) .im .L)))
            (l ++ (c, .node d (N.eval (.pure (Term.chan d))) ms' qs') :: r) qs)
          = treeChansM (.node p (M.eval (.recv (Term.chan c) .im))
              (l ++ (c, .node d (N.eval (.app (.send (Term.chan d) .im) o .im)) ms' qs') :: r)
              qs) := by
        simp only [treeChansM_root, treeChansM_node, childChansM_append, childChansM_cons]
      rw [e]
      exact h
  | @nodeForward M N p v c d l r ms' qs qs' _value _occursP =>
      intro h
      have e3 : childChansM (splitChildrenByTerm v (l ++ r)).1
            + childChansM (splitChildrenByTerm v (l ++ r)).2
          = childChansM l + childChansM r := by
        rw [childChansM_split, childChansM_append]
      have e1 : treeChansM (.node p (N.eval (.pure (.pair v (Term.chan d) .ex .L)))
            (forwardChildren v c d M ms' (l ++ r) qs) qs')
          = (childChansM (splitChildrenByTerm v (l ++ r)).1
              + childChansM (splitChildrenByTerm v (l ++ r)).2)
            + ({chanIndex p} + {chanIndex c} + {chanIndex d} + childChansM ms' + subChansM qs'
                + subChansM qs) := by
        simp only [forwardChildren, treeChansM_root, treeChansM_node, childChansM_insertChild,
          childChansM_mergeChildren, ← Multiset.singleton_add]
        abel
      have e2 : treeChansM (.node p (M.eval (.app (.send (Term.chan c) .ex) v .ex))
            (l ++ (c, .node d (N.eval (.recv (Term.chan d) .ex)) ms' qs') :: r) qs)
          = (childChansM l + childChansM r)
            + ({chanIndex p} + {chanIndex c} + {chanIndex d} + childChansM ms' + subChansM qs'
                + subChansM qs) := by
        simp only [treeChansM_root, treeChansM_node, childChansM_append, childChansM_cons,
          ← Multiset.singleton_add]
        abel
      rw [e1, e3, ← e2]
      exact h
  | @rootChild m c child child' l r qs _st avoids ih =>
      intro h
      have esrc : treeChansM (.root m (l ++ (c, child) :: r) qs)
          = ({chanIndex c} + (childChansM l + childChansM r + subChansM qs))
            + treeChansM child := by
        simp only [treeChansM_root, childChansM_append, childChansM_cons,
          ← Multiset.singleton_add]
        abel
      have etgt : treeChansM (.root m (l ++ (c, child') :: r) qs)
          = ({chanIndex c} + (childChansM l + childChansM r + subChansM qs))
            + treeChansM child' := by
        simp only [treeChansM_root, childChansM_append, childChansM_cons,
          ← Multiset.singleton_add]
        abel
      rw [esrc] at h
      rw [etgt]
      refine nodupM_replace h (ih (Multiset.nodup_add.mp h).2.1) ?_
      intro x hx hnx
      rw [← esrc, mem_treeChansM]
      exact avoids x (mem_treeChansM.mp hx) (fun h' => hnx (mem_treeChansM.mpr h'))
  | @nodeChild p m c child child' l r qs _st avoids ih =>
      intro h
      have esrc : treeChansM (.node p m (l ++ (c, child) :: r) qs)
          = ({chanIndex p} + {chanIndex c} + (childChansM l + childChansM r + subChansM qs))
            + treeChansM child := by
        simp only [treeChansM_node, childChansM_append, childChansM_cons,
          ← Multiset.singleton_add]
        abel
      have etgt : treeChansM (.node p m (l ++ (c, child') :: r) qs)
          = ({chanIndex p} + {chanIndex c} + (childChansM l + childChansM r + subChansM qs))
            + treeChansM child' := by
        simp only [treeChansM_node, childChansM_append, childChansM_cons,
          ← Multiset.singleton_add]
        abel
      rw [esrc] at h
      rw [etgt]
      refine nodupM_replace h (ih (Multiset.nodup_add.mp h).2.1) ?_
      intro x hx hnx
      rw [← esrc, mem_treeChansM]
      exact avoids x (mem_treeChansM.mp hx) (fun h' => hnx (mem_treeChansM.mpr h'))
  | @rootSubtree m ms sub sub' l r _st avoids ih =>
      intro h
      have esrc : treeChansM (.root m ms (l ++ sub :: r))
          = (childChansM ms + subChansM l + subChansM r) + treeChansM sub := by
        simp only [treeChansM_root, subChansM_append, subChansM_cons]
        abel
      have etgt : treeChansM (.root m ms (l ++ sub' :: r))
          = (childChansM ms + subChansM l + subChansM r) + treeChansM sub' := by
        simp only [treeChansM_root, subChansM_append, subChansM_cons]
        abel
      rw [esrc] at h
      rw [etgt]
      refine nodupM_replace h (ih (Multiset.nodup_add.mp h).2.1) ?_
      intro x hx hnx
      rw [← esrc, mem_treeChansM]
      exact avoids x (mem_treeChansM.mp hx) (fun h' => hnx (mem_treeChansM.mpr h'))
  | @nodeSubtree p m ms sub sub' l r _st avoids ih =>
      intro h
      have esrc : treeChansM (.node p m ms (l ++ sub :: r))
          = ({chanIndex p} + (childChansM ms + subChansM l + subChansM r))
            + treeChansM sub := by
        simp only [treeChansM_node, subChansM_append, subChansM_cons, ← Multiset.singleton_add]
        abel
      have etgt : treeChansM (.node p m ms (l ++ sub' :: r))
          = ({chanIndex p} + (childChansM ms + subChansM l + subChansM r))
            + treeChansM sub' := by
        simp only [treeChansM_node, subChansM_append, subChansM_cons, ← Multiset.singleton_add]
        abel
      rw [esrc] at h
      rw [etgt]
      refine nodupM_replace h (ih (Multiset.nodup_add.mp h).2.1) ?_
      intro x hx hnx
      rw [← esrc, mem_treeChansM]
      exact avoids x (mem_treeChansM.mp hx) (fun h' => hnx (mem_treeChansM.mpr h'))
  | @rootExpr m m' ms qs _dst =>
      intro h
      have e : treeChansM (.root m' ms qs) = treeChansM (.root m ms qs) := by
        simp only [treeChansM_root]
      rw [e]
      exact h
  | @nodeExpr p m m' ms qs _dst =>
      intro h
      have e : treeChansM (.node p m' ms qs) = treeChansM (.node p m ms qs) := by
        simp only [treeChansM_node]
      rw [e]
      exact h

/-- Lemma 5.87, root half: a valid, channel-distinct spawning tree steps to a valid,
channel-distinct tree. -/
theorem Typed.fidelity {t t' : Tree} (ty : Typed t) (dist : Distinct t) (st : Step t t') :
    Typed t' ∧ Distinct t' :=
  ⟨(fidelity_mutual st).1 ty dist, st.distinct dist⟩

/-- Lemma 5.87, node half: the parent endpoint keeps its polarity and protocol, and channel
distinctness is preserved. -/
theorem TypedAt.fidelity {ry : Bool} {Ay : Term} {t t' : Tree}
    (ty : TypedAt ry Ay t) (dist : Distinct t) (st : Step t t') :
    TypedAt ry Ay t' ∧ Distinct t' :=
  ⟨(fidelity_mutual st).2 ry Ay ty dist, st.distinct dist⟩

/-- Lemma 5.87 iterated along multi-step reduction, root half. -/
theorem Typed.fidelity_red {t t' : Tree} (ty : Typed t) (dist : Distinct t) (red : Red t t') :
    Typed t' ∧ Distinct t' := by
  induction red with
  | refl => exact ⟨ty, dist⟩
  | tail _ st ih => exact ih.1.fidelity ih.2 st

/-- Lemma 5.87 iterated along multi-step reduction, node half. -/
theorem TypedAt.fidelity_red {ry : Bool} {Ay : Term} {t t' : Tree}
    (ty : TypedAt ry Ay t) (dist : Distinct t) (red : Red t t') :
    TypedAt ry Ay t' ∧ Distinct t' := by
  induction red with
  | refl => exact ⟨ty, dist⟩
  | tail _ st ih => exact ih.1.fidelity ih.2 st

end TLLC.Spawning
