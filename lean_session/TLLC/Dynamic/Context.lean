import TLLC.Syntax
import TLLC.ARS

/-!
# Dynamic (linear) contexts

Port of `coq_session/dyn_ctx.v`. A dynamic context `Ctx` is a list of *optional* typed slots
(`Option (Term × Srt)`): `none` is a consumed/absent slot (Coq `_: Δ`), `some (m, s)` is a slot
holding type `m` at sort `s` (Coq `m .{s} Δ`, with the `U`/`L` shorthands `m :U Δ` / `m :L Δ`).

This file ports the structural relations used throughout the Dynamic level:
`Merge` (the linear split `Δ1 ∘ Δ2 => Δ`, written here `Merge Δ1 Δ2 Δ`), `Key` (`Δ ▷ s`, the
"all slots are at least sort `s`" predicate), `Empty` (all slots null), `Has` (linear de Bruijn
lookup), and `Just` (the single-linear-slot lookup used by channel variables).

Coq → Lean lemma name map (subject-inductive dot-notation, SStruct-aligned):
`key_impure`→`Key.impure`, `key_empty`→`Empty.key`, `empty_split`→`Merge.empty_split`,
`merge_empty`→`Merge.empty_image`, `merge_emptyL/R`→`Merge.emptyL/emptyR`,
`empty_merge_self`→`Empty.merge_self`, `just_empty`→`Just.empty`, `empty_just`→`Empty.not_just`,
`pure_just`→`Just.not_pure`, `pure_merge_self`→`Key.merge_self`, `key_merge`→`Merge.key_image`,
`pure_split`→`Merge.pure_split`, `merge_sym`→`Merge.sym`, `merge_inj`→`Merge.inj`,
`merge_pureL/R`→`Merge.pureL/pureR`, `merge_splitL/R`→`Merge.splitL/splitR`,
`merge_distr`→`Merge.distr`.
-/

namespace TLLC.Dynamic
open Autosubst Autosubst.Notation

/-- Dynamic context: a list of optional typed slots (Coq `dyn_ctx := seq (elem term)`). -/
abbrev Ctx := List (Option (Term × Srt))

/-- A slot holding type `m` at sort `s` (Coq `m .{s} Γ`). -/
scoped notation:67 m " :⟨" s "⟩ " Δ:67 => (Option.some (m, s)) :: Δ
/-- An unrestricted slot (Coq `m :U Γ`). -/
scoped notation:67 m " :U " Δ:67 => (Option.some (m, Srt.U)) :: Δ
/-- A linear slot (Coq `m :L Γ`). -/
scoped notation:67 m " :L " Δ:67 => (Option.some (m, Srt.L)) :: Δ

/-- Linear context split (Coq `merge`, `Δ1 ∘ Δ2 => Δ`). -/
@[aesop safe [constructors]]
inductive Merge : Ctx → Ctx → Ctx → Prop where
  | nil :
    Merge [] ([]) ([])
  | left {Δ1 Δ2 Δ} (m) :
    Merge Δ1 Δ2 Δ →
    Merge (m :U Δ1) (m :U Δ2) (m :U Δ)
  | right1 {Δ1 Δ2 Δ} (m) :
    Merge Δ1 Δ2 Δ →
    Merge (m :L Δ1) (none :: Δ2) (m :L Δ)
  | right2 {Δ1 Δ2 Δ} (m) :
    Merge Δ1 Δ2 Δ →
    Merge (none :: Δ1) (m :L Δ2) (m :L Δ)
  | null {Δ1 Δ2 Δ} :
    Merge Δ1 Δ2 Δ →
    Merge (none :: Δ1) (none :: Δ2) (none :: Δ)

/-- All slots are at least sort `s` (Coq `key`, `Δ ▷ s`). -/
@[aesop safe [constructors]]
inductive Key : Ctx → Srt → Prop where
  | nil {s} :
    Key [] s
  | U {Δ} (m) :
    Key Δ Srt.U →
    Key (m :U Δ) Srt.U
  | L {Δ s} (m) :
    Key Δ Srt.L →
    Key (m :⟨s⟩ Δ) Srt.L
  | null {Δ s} :
    Key Δ s →
    Key (none :: Δ) s

@[inherit_doc] scoped notation:40 Δ:41 " ▷ " s:41 => Key Δ s

/-- Every slot is null (Coq `dyn_empty`). -/
@[aesop safe [constructors]]
inductive Empty : Ctx → Prop where
  | nil :
    Empty []
  | null {Δ} :
    Empty Δ →
    Empty (none :: Δ)

/-- Linear de Bruijn lookup with shifting (Coq `dyn_has`). -/
inductive Has : Ctx → Nat → Srt → Term → Prop where
  | zero {Δ A s} :
    Δ ▷ Srt.U →
    Has (A :⟨s⟩ Δ) 0 s (A⟨(id : Nat → Nat); ↑⟩)
  | succ {Δ A B x s} :
    Has Δ x s A →
    Has (B :U Δ) (x + 1) s (A⟨(id : Nat → Nat); ↑⟩)
  | null {Δ A x s} :
    Has Δ x s A →
    Has (none :: Δ) (x + 1) s (A⟨(id : Nat → Nat); ↑⟩)

/-- Single-linear-slot lookup used by channel variables (Coq `dyn_just`). -/
inductive Just : Ctx → Nat → Term → Prop where
  | zero {Δ A} :
    Empty Δ →
    Just (A :L Δ) 0 (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)
  | null {Δ A x} :
    Just Δ x A →
    Just (none :: Δ) (x + 1) (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)

/-! ## Key lemmas -/

/-- Every context has key `L` (Coq `key_impure`). -/
lemma Key.impure : ∀ {Δ : Ctx}, Δ ▷ Srt.L
  | [] => .nil
  | none :: _ => .null Key.impure
  | some (_, _) :: _ => .L _ Key.impure

/-- An empty context has every key (Coq `key_empty`). -/
lemma Empty.key {Δ s} (emp : Empty Δ) : Δ ▷ s := by
  induction emp with
  | nil => exact .nil
  | null _ ih => exact .null ih

/-! ## Empty / merge interaction -/

/-- An empty merge result splits into empty components (Coq `empty_split`). -/
lemma Merge.empty_split {Δ1 Δ2 Δ} (mrg : Merge Δ1 Δ2 Δ) : Empty Δ → Empty Δ1 ∧ Empty Δ2 := by
  induction mrg with
  | nil => intro _; exact ⟨.nil, .nil⟩
  | left _ _ => intro emp; cases emp
  | right1 _ _ => intro emp; cases emp
  | right2 _ _ => intro emp; cases emp
  | null _ ih => intro emp; cases emp with | null e => obtain ⟨e1, e2⟩ := ih e; exact ⟨.null e1, .null e2⟩

/-- Merging empty components yields an empty result (Coq `merge_empty`). -/
lemma Merge.empty_image {Δ1 Δ2 Δ} (mrg : Merge Δ1 Δ2 Δ) : Empty Δ1 → Empty Δ2 → Empty Δ := by
  induction mrg with
  | nil => intro _ _; exact .nil
  | left _ _ => intro emp1 _; cases emp1
  | right1 _ _ => intro emp1 _; cases emp1
  | right2 _ _ => intro _ emp2; cases emp2
  | null _ ih => intro emp1 emp2; cases emp1 with | null e1 => cases emp2 with | null e2 => exact .null (ih e1 e2)

/-- An empty left component makes the merge an identity on the right (Coq `merge_emptyL`). -/
lemma Merge.emptyL {Δ1 Δ2 Δ} (mrg : Merge Δ1 Δ2 Δ) : Empty Δ1 → Δ2 = Δ := by
  induction mrg with
  | nil => intro _; rfl
  | left _ _ => intro emp; cases emp
  | right1 _ _ => intro emp; cases emp
  | right2 _ _ ih => intro emp; cases emp with | null e => rw [ih e]
  | null _ ih => intro emp; cases emp with | null e => rw [ih e]

/-- An empty right component makes the merge an identity on the left (Coq `merge_emptyR`). -/
lemma Merge.emptyR {Δ1 Δ2 Δ} (mrg : Merge Δ1 Δ2 Δ) : Empty Δ2 → Δ1 = Δ := by
  induction mrg with
  | nil => intro _; rfl
  | left _ _ => intro emp; cases emp
  | right1 _ _ ih => intro emp; cases emp with | null e => rw [ih e]
  | right2 _ _ => intro emp; cases emp
  | null _ ih => intro emp; cases emp with | null e => rw [ih e]

/-- An empty context self-merges (Coq `empty_merge_self`). -/
lemma Empty.merge_self {Δ} (emp : Empty Δ) : Merge Δ Δ Δ := by
  induction emp with
  | nil => exact .nil
  | null _ ih => exact .null ih

/-! ## Just / empty / key interaction -/

/-- A `Just` lookup exposes an empty splitter (Coq `just_empty`). -/
lemma Just.empty {Δ x A} (js : Just Δ x A) : ∃ Δ0, Empty Δ0 ∧ Merge Δ0 Δ Δ := by
  induction js with
  | zero emp => exact ⟨none :: _, .null emp, .right2 _ (Empty.merge_self emp)⟩
  | null _ ih => obtain ⟨Δ0, e, mrg⟩ := ih; exact ⟨none :: Δ0, .null e, .null mrg⟩

/-- An empty context admits no `Just` lookup (Coq `empty_just`). -/
lemma Empty.not_just {Δ x A} (emp : Empty Δ) : ¬ Just Δ x A := by
  induction emp generalizing x A with
  | nil => intro js; cases js
  | null _ ih => intro js; cases js with | null js' => exact ih js'

/-- A `Just` lookup forbids key `U` (Coq `pure_just`). -/
lemma Just.not_pure {Δ x A} (js : Just Δ x A) : ¬ Δ ▷ Srt.U := by
  induction js with
  | zero _ => intro k; cases k
  | null _ ih => intro k; cases k with | null k' => exact ih k'

/-! ## Pure (key `U`) lemmas -/

/-- A pure context self-merges (Coq `pure_merge_self`). -/
lemma Key.merge_self : ∀ {Δ : Ctx}, Δ ▷ Srt.U → Merge Δ Δ Δ
  | [], _ => .nil
  | none :: _, k => by cases k with | null k' => exact .null (Key.merge_self k')
  | some (_, _) :: _, k => by cases k with | U _ k' => exact .left _ (Key.merge_self k')

/-- Merge preserves keys (Coq `key_merge`). -/
lemma Merge.key_image {Δ1 Δ2 Δ s} (mrg : Merge Δ1 Δ2 Δ) (k1 : Δ1 ▷ s) (k2 : Δ2 ▷ s) : Δ ▷ s := by
  induction mrg with
  | nil => exact k1
  | left m _ ih =>
    cases k1 with
    | U _ k1' => cases k2 with | U _ k2' => exact .U m (ih k1' k2')
    | L _ k1' => cases k2 with | L _ k2' => exact .L m (ih k1' k2')
  | right1 m _ ih => cases k1 with | L _ k1' => cases k2 with | null k2' => exact .L m (ih k1' k2')
  | right2 m _ ih => cases k1 with | null k1' => cases k2 with | L _ k2' => exact .L m (ih k1' k2')
  | null _ ih => cases k1 with | null k1' => cases k2 with | null k2' => exact .null (ih k1' k2')

/-- A pure merge result splits into pure components (Coq `pure_split`). -/
lemma Merge.pure_split {Δ1 Δ2 Δ} (mrg : Merge Δ1 Δ2 Δ) : Δ ▷ Srt.U → Δ1 ▷ Srt.U ∧ Δ2 ▷ Srt.U := by
  induction mrg with
  | nil => intro _; exact ⟨.nil, .nil⟩
  | left _ _ ih => intro k; cases k with | U _ k' => obtain ⟨k1, k2⟩ := ih k'; exact ⟨.U _ k1, .U _ k2⟩
  | right1 _ _ => intro k; cases k
  | right2 _ _ => intro k; cases k
  | null _ ih => intro k; cases k with | null k' => obtain ⟨k1, k2⟩ := ih k'; exact ⟨.null k1, .null k2⟩

/-! ## Merge structural lemmas -/

/-- Merge is symmetric (Coq `merge_sym`). -/
lemma Merge.sym {Δ1 Δ2 Δ} (mrg : Merge Δ1 Δ2 Δ) : Merge Δ2 Δ1 Δ := by
  induction mrg with
  | nil => exact .nil
  | left m _ ih => exact .left m ih
  | right1 m _ ih => exact .right2 m ih
  | right2 m _ ih => exact .right1 m ih
  | null _ ih => exact .null ih

/-- Merge is functional in its result (Coq `merge_inj`). -/
lemma Merge.inj {Δ1 Δ2 Δx Δy} (mrg1 : Merge Δ1 Δ2 Δx) (mrg2 : Merge Δ1 Δ2 Δy) : Δx = Δy := by
  induction mrg1 generalizing Δy with
  | nil => cases mrg2; rfl
  | left _ _ ih => cases mrg2 with | left _ m2 => rw [ih m2]
  | right1 _ _ ih => cases mrg2 with | right1 _ m2 => rw [ih m2]
  | right2 _ _ ih => cases mrg2 with | right2 _ m2 => rw [ih m2]
  | null _ ih => cases mrg2 with | null m2 => rw [ih m2]

/-- A pure left component makes the merge an identity on the right (Coq `merge_pureL`). -/
lemma Merge.pureL {Δ1 Δ2 Δ} (mrg : Merge Δ1 Δ2 Δ) : Δ1 ▷ Srt.U → Δ = Δ2 := by
  induction mrg with
  | nil => intro _; rfl
  | left _ _ ih => intro k; cases k with | U _ k' => rw [ih k']
  | right1 _ _ => intro k; cases k
  | right2 _ _ ih => intro k; cases k with | null k' => rw [ih k']
  | null _ ih => intro k; cases k with | null k' => rw [ih k']

/-- A pure right component makes the merge an identity on the left (Coq `merge_pureR`). -/
lemma Merge.pureR {Δ1 Δ2 Δ} (mrg : Merge Δ1 Δ2 Δ) : Δ2 ▷ Srt.U → Δ = Δ1 := by
  induction mrg with
  | nil => intro _; rfl
  | left _ _ ih => intro k; cases k with | U _ k' => rw [ih k']
  | right1 _ _ ih => intro k; cases k with | null k' => rw [ih k']
  | right2 _ _ => intro k; cases k
  | null _ ih => intro k; cases k with | null k' => rw [ih k']

/-- Left split-rotation of a nested merge (Coq `merge_splitL`). -/
lemma Merge.splitL {Δ1 Δ2 Δ} (mrg : Merge Δ1 Δ2 Δ) :
    ∀ {Δa Δb}, Merge Δa Δb Δ1 → ∃ Δc, Merge Δa Δ2 Δc ∧ Merge Δc Δb Δ := by
  induction mrg with
  | nil => intro _ _ m2; cases m2; exact ⟨[], .nil, .nil⟩
  | left m _ ih => intro _ _ m2; cases m2 with
    | left _ m2' => obtain ⟨Δc, ha, hb⟩ := ih m2'; exact ⟨m :U Δc, .left m ha, .left m hb⟩
  | right1 m _ ih => intro _ _ m2; cases m2 with
    | right1 _ m2' => obtain ⟨Δc, ha, hb⟩ := ih m2'; exact ⟨m :L Δc, .right1 m ha, .right1 m hb⟩
    | right2 _ m2' => obtain ⟨Δc, ha, hb⟩ := ih m2'; exact ⟨none :: Δc, .null ha, .right2 m hb⟩
  | right2 m _ ih => intro _ _ m2; cases m2 with
    | null m2' => obtain ⟨Δc, ha, hb⟩ := ih m2'; exact ⟨m :L Δc, .right2 m ha, .right1 m hb⟩
  | null _ ih => intro _ _ m2; cases m2 with
    | null m2' => obtain ⟨Δc, ha, hb⟩ := ih m2'; exact ⟨none :: Δc, .null ha, .null hb⟩

/-- Right split-rotation of a nested merge (Coq `merge_splitR`). -/
lemma Merge.splitR {Δ1 Δ2 Δ} (mrg : Merge Δ1 Δ2 Δ) :
    ∀ {Δa Δb}, Merge Δa Δb Δ1 → ∃ Δc, Merge Δb Δ2 Δc ∧ Merge Δc Δa Δ := by
  induction mrg with
  | nil => intro _ _ m2; cases m2; exact ⟨[], .nil, .nil⟩
  | left m _ ih => intro _ _ m2; cases m2 with
    | left _ m2' => obtain ⟨Δc, ha, hb⟩ := ih m2'; exact ⟨m :U Δc, .left m ha, .left m hb⟩
  | right1 m _ ih => intro _ _ m2; cases m2 with
    | right1 _ m2' => obtain ⟨Δc, ha, hb⟩ := ih m2'; exact ⟨none :: Δc, .null ha, .right2 m hb⟩
    | right2 _ m2' => obtain ⟨Δc, ha, hb⟩ := ih m2'; exact ⟨m :L Δc, .right1 m ha, .right1 m hb⟩
  | right2 m _ ih => intro _ _ m2; cases m2 with
    | null m2' => obtain ⟨Δc, ha, hb⟩ := ih m2'; exact ⟨m :L Δc, .right2 m ha, .right1 m hb⟩
  | null _ ih => intro _ _ m2; cases m2 with
    | null m2' => obtain ⟨Δc, ha, hb⟩ := ih m2'; exact ⟨none :: Δc, .null ha, .null hb⟩

/-- Distributivity of merge over two nested merges (Coq `merge_distr`). -/
lemma Merge.distr {Γ1 Γ2 Γ Δ11 Δ12 Δ21 Δ22}
    (mrg0 : Merge Γ1 Γ2 Γ) (mrg1 : Merge Δ11 Δ12 Γ1) (mrg2 : Merge Δ21 Δ22 Γ2) :
    ∃ Δ1 Δ2, Merge Δ1 Δ2 Γ ∧ Merge Δ11 Δ21 Δ1 ∧ Merge Δ12 Δ22 Δ2 := by
  obtain ⟨Δ4, mrg3, mrg4⟩ := mrg0.splitL mrg1
  obtain ⟨Δ5, mrg5, mrg6⟩ := mrg3.sym.splitL mrg2
  obtain ⟨Δ6, mrg7, mrg8⟩ := mrg4.splitL mrg6.sym
  exact ⟨Δ5, Δ6, mrg8.sym, mrg5.sym, mrg7.sym⟩

end TLLC.Dynamic
