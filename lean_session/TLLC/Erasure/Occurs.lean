import TLLC.Erasure.Subst
import TLLC.Dynamic.Occurs

/-!
# Erasure and channel occurrences

Port of `coq_session/era_occurs.v`: the channel-occurrence machinery for the erasure relation. This
file mirrors the dynamic occurrence file `TLLC/Dynamic/Occurs.lean` (`coq_session/dyn_occurs.v`),
threading the erased term `m'` alongside the source `m`. It REUSES `Dynamic.occurs`,
`Dynamic.CvarPos` and `Dynamic.Iren` directly (it does not re-port them).

It ports:

* `era_dyn_occurs` (here `Erased.dyn_occurs`): erasure preserves the channel-occurrence count —
  `Θ ⨾ Γ ⨾ Δ ⊢ m ~ m' : A → occurs i m = x → occurs i m' = x`. Proved by induction on the erasure
  derivation: each erased subterm has the same `occurs` count as the corresponding source subterm by
  IH, and the `.box` placed in irrelevant slots contributes `0` exactly like the erased-away source
  subterm (which, being irrelevant, is not counted by `occurs` either — `occurs` on `.im` app/pair
  counts only the relevant component).
* `era_type_occurs0`/`era_type_occurs1` (here `Erased.occurs0`/`occurs1`): if `i` is absent/present
  in `Θ` then it occurs `0`/`1` times in BOTH `m` and `m'`. Proved by routing through the dynamic
  facts `Dynamic.Typed.occurs0`/`occurs1` (via `Erased.toDyn`) and transferring the count to `m'`
  with `Erased.dyn_occurs`.
* `era_occurs_iren` (here `Erased.occurs_iren`): a channel-renamed term whose renaming omits `i` has
  `i`-occurrence `0`, for both source and erased images.
* `era_occurs_cren_id` (here `Erased.occurs_cren_id`): reconstructs an erasure derivation on the
  pre-image of a channel renaming `ξ` that is the identity off `{i, j}`, given that neither `i` nor
  `j` occurs in `m`/`m'`.
-/

namespace TLLC.Erasure
open Autosubst Autosubst.Notation
open TLLC.Dynamic
open scoped TLLC.Static TLLC.Dynamic

/-- Erasure preserves the channel-occurrence count (Coq `era_dyn_occurs`). -/
lemma Erased.dyn_occurs {Θ Γ Δ m m' A i x}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ m ~ m' : A) : occurs i m = x → occurs i m' = x := by
  induction er generalizing i x with
  | var => intro e; exact e
  | lamIm _ _ _ ih => intro e; simp only [occurs] at e ⊢; exact ih e
  | lamEx _ _ _ ih => intro e; simp only [occurs] at e ⊢; exact ih e
  | appIm _ _ ihm => intro e; simp only [occurs] at e ⊢; exact ihm e
  | appEx _ _ _ _ ihm ihn =>
    intro e; simp only [occurs] at e ⊢
    rw [ihm rfl, ihn rfl]; exact e
  | pairIm _ _ _ ihn => intro e; simp only [occurs] at e ⊢; exact ihn e
  | pairEx _ _ _ _ _ ihm ihn =>
    intro e; simp only [occurs] at e ⊢
    rw [ihm rfl, ihn rfl]; exact e
  | projIm _ _ _ _ _ ihm ihn =>
    intro e; simp only [occurs] at e ⊢
    rw [ihm rfl, ihn rfl]; exact e
  | projEx _ _ _ _ _ ihm ihn =>
    intro e; simp only [occurs] at e ⊢
    rw [ihm rfl, ihn rfl]; exact e
  | one => intro e; exact e
  | tt => intro e; exact e
  | ff => intro e; exact e
  | ite _ _ _ _ _ _ ihm ihn1 ihn2 =>
    intro e; simp only [occurs] at e ⊢
    rw [ihm rfl, ihn1 rfl, ihn2 rfl]; exact e
  | pure _ ihm => intro e; simp only [occurs] at e ⊢; exact ihm e
  | mlet _ _ _ _ _ ihm ihn =>
    intro e; simp only [occurs] at e ⊢
    rw [ihm rfl, ihn rfl]; exact e
  | chan => intro e; exact e
  | fork _ ihm => intro e; simp only [occurs] at e ⊢; exact ihm e
  | recv _ _ ihm => intro e; simp only [occurs] at e ⊢; exact ihm e
  | send _ _ ihm => intro e; simp only [occurs] at e ⊢; exact ihm e
  | close _ ihm => intro e; simp only [occurs] at e ⊢; exact ihm e
  | conv _ _ _ ihm => intro e; exact ihm e

/-- If `i` is absent in `Θ`, it occurs `0` times in both the source and the erased term (Coq
    `era_type_occurs0`). -/
lemma Erased.occurs0 {Θ Γ Δ m m' A i}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ m ~ m' : A) (h : CvarPos Θ i false) :
    occurs i m = 0 ∧ occurs i m' = 0 := by
  have oc : occurs i m = 0 := er.toDyn.occurs0 h
  exact ⟨oc, er.dyn_occurs oc⟩

/-- If `i` is present in `Θ`, it occurs `1` time in both the source and the erased term (Coq
    `era_type_occurs1`). -/
lemma Erased.occurs1 {Θ Γ Δ m m' A i}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ m ~ m' : A) (h : CvarPos Θ i true) :
    occurs i m = 1 ∧ occurs i m' = 1 := by
  have oc : occurs i m = 1 := er.toDyn.occurs1 h
  exact ⟨oc, er.dyn_occurs oc⟩

/-- A channel-renamed term whose renaming omits `i` has `i`-occurrence `0`, for both the source and
    the erased image (Coq `era_occurs_iren`). -/
lemma Erased.occurs_iren {Θ Γ Δ A i ξ} {m m' : Term}
    (er : Θ ⨾ Γ ⨾ Δ ⊢ m⟨ξ; (id : Nat → Nat)⟩ ~ m'⟨ξ; (id : Nat → Nat)⟩ : A) (h : Iren i ξ) :
    occurs i (m⟨ξ; (id : Nat → Nat)⟩) = 0 ∧ occurs i (m'⟨ξ; (id : Nat → Nat)⟩) = 0 := by
  have oc : occurs i (m⟨ξ; (id : Nat → Nat)⟩) = 0 := er.toDyn.occurs_iren h
  exact ⟨oc, er.dyn_occurs oc⟩

-- Coq `era_occurs_cren_id` (`era_occurs.v:80`) is OMITTED as dead code: `grep` over `coq_session`
-- confirms it is never referenced anywhere (only its own definition), matching the project's policy
-- of skipping confirmed-unused lemmas. It would reconstruct an erasure on a channel-renaming
-- pre-image (via the now-available `Static.Typed.crename_inv`), but nothing downstream needs it.

end TLLC.Erasure
